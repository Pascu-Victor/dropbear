/* WOS connection-local key-exchange, authentication and session broker.
 * The network worker discards its authority before reading client packets.
 * No worker-supplied hash is signed: fresh server ephemeral state and the first
 * session ID are generated and retained by this process.
 */
#include "includes.h"
#include "svr-kex-broker.h"

#if DROPBEAR_SVR_KEX_BROKER
#include "algo.h"
#include "auth.h"
#include "atomicio.h"
#include "bignum.h"
#include "dbutil.h"
#include "dbrandom.h"
#include "kex.h"
#include "packet.h"
#include "runopts.h"
#include "session.h"
#include "ssh.h"

#define BROKER_FRAME_MAX (RECV_MAX_PAYLOAD_LEN + TRANS_MAX_PAYLOAD_LEN + 16384)
#define BROKER_KEX_REQUEST 1
#define BROKER_AUTH_REQUEST 2
#define BROKER_PREPARE_COMMAND 3
#define BROKER_RELEASE_SESSION 4
#define BROKER_SPAWN 5
#define BROKER_IO 6
#define BROKER_SIGNAL 7
#define BROKER_PTY 8
#define BROKER_WINDOW_CHANGE 9
#define BROKER_IO_MAX 16384
#define BROKER_PERMITOPEN_MAX 1024

#if DROPBEAR_SVR_PAM_AUTH
#error "The WOS authentication broker does not support interactive PAM exchanges"
#endif

#if DROPBEAR_VFORK || DROPBEAR_X11FWD
#error "The WOS session broker requires fork and does not yet support X11 sessions"
#endif

static int request_fd = -1;
static int response_fd = -1;
static pid_t broker_pid = -1;
static int monitor_process;
static unsigned int relay_count;
static struct ChanSess connection_environment;

struct PreparedSession {
	unsigned int id;
	unsigned int channel;
	struct ChanSess command;
	int command_ready;
	int fd[3]; /* broker-owned stdin writer, stdout reader, stderr reader */
};
static struct PreparedSession *prepared_sessions[MAX_CHANNELS];
static unsigned int next_session_id;

struct RelayChunk {
	unsigned int pos, len;
	unsigned char data[BROKER_IO_MAX];
};
struct BrokerRelay {
	int fd[3]; /* worker adapters: stdin reader, stdout writer, stderr writer */
	int eof[3];
	struct RelayChunk chunk[3];
	struct exitinfo exit;
};

static void close_stream(int *fd) {
	if (*fd >= 0) close(*fd);
	*fd = -1;
}

static void release_relay(struct ChanSess *session) {
	unsigned int i;
	if (!session->broker_relay) return;
	for (i = 0; i < 3; i++) close_stream(&session->broker_relay->fd[i]);
	m_free(session->broker_relay);
	relay_count--;
}

static void free_prepared_command(struct ChanSess *command) {
	m_free(command->cmd);
	m_free(command->original_command);
}

/* A PTY is one bidirectional descriptor, not two independently owned FDs.
 * Clear every alias before close so a later allocation cannot be closed twice. */
static void close_session_stream(struct PreparedSession *entry, unsigned int stream) {
	if (entry->command.tty && stream < 2) {
		entry->fd[0] = entry->fd[1] = -1;
		close_stream(&entry->command.master);
	} else {
		close_stream(&entry->fd[stream]);
	}
}

static void release_prepared_session(unsigned int slot) {
	struct PreparedSession *entry = prepared_sessions[slot];
	if (entry) {
		unsigned int i;
		/* Channel release explicitly notifies our unreaped child. Kernel final
		 * master close separately revokes terminal ownership and notifies its
		 * foreground group; never signal a slave-supplied group from the broker. */
		if (entry->command.tty && entry->command.pid > 0 && entry->command.exit.exitpid == -1)
			(void)kill(entry->command.pid, SIGHUP);
		for (i = 0; i < 3; i++) close_session_stream(entry, i);
		close_stream(&entry->command.slave);
		svr_session_pty_logout(&entry->command);
		m_free(entry->command.tty);
		m_free(entry->command.term);
		m_free(entry->command.broker_agent_path);
		free_prepared_command(&entry->command);
		m_free(prepared_sessions[slot]);
	}
}

int svr_kex_broker_is_monitor(void) {
	return monitor_process;
}

static int normal_dh(void) {
#if DROPBEAR_NORMAL_DH
	return ses.newkeys->algo_kex->mode == DROPBEAR_KEX_NORMAL_DH;
#else
	return 0;
#endif
}

static int pq_hybrid(void) {
#if DROPBEAR_PQHYBRID
	return ses.newkeys->algo_kex->mode == DROPBEAR_KEX_PQHYBRID;
#else
	return 0;
#endif
}

/* Protocol blobs can contain a whole KEXINIT transcript, exceeding the
 * ordinary SSH text-string limit. Bound them by this private frame instead. */
static buffer *read_blob(buffer *frame) {
	unsigned int len = buf_getint(frame);
	if (len > BROKER_FRAME_MAX || len > frame->len - frame->pos) {
		dropbear_exit("KEX broker blob length invalid");
	}
	buffer *blob = buf_getptrcopy(frame, len);
	buf_incrpos(frame, len);
	return blob;
}

static void put_optional_string(buffer *frame, const char *value) {
	buf_putbyte(frame, value != NULL);
	if (value) {
		buf_putstring(frame, value, strlen(value));
	}
}

static char *read_optional_string(buffer *frame) {
	unsigned int len;
	char *value;
	if (!buf_getbool(frame)) {
		return NULL;
	}
	value = buf_getstring(frame, &len);
	if (strlen(value) != len) {
		dropbear_exit("Authentication broker string contains NUL");
	}
	return value;
}

/* Only broker-owned policy is serialized. No password hash is exported. */
static void put_authenticated_identity(buffer *frame) {
	unsigned int group;
	if (!ses.authstate.pw_groups_valid || ses.authstate.pw_group_count == 0
			|| ses.authstate.pw_group_count > NGROUPS_MAX) {
		dropbear_exit("Authentication broker group snapshot missing");
	}
	buf_putint(frame, ses.authstate.pw_uid);
	buf_putint(frame, ses.authstate.pw_gid);
	buf_putint(frame, ses.authstate.pw_group_count);
	for (group = 0; group < ses.authstate.pw_group_count; group++) {
		buf_putint(frame, ses.authstate.pw_groups[group]);
	}
	put_optional_string(frame, ses.authstate.username);
	put_optional_string(frame, ses.authstate.pw_name);
	put_optional_string(frame, ses.authstate.pw_dir);
	put_optional_string(frame, ses.authstate.pw_shell);
#if DROPBEAR_SVR_PUBKEY_OPTIONS_BUILT
	struct PubKeyOptions *options = ses.authstate.pubkey_options;
	put_optional_string(frame, ses.authstate.pubkey_info);
	buf_putbyte(frame, options != NULL);
	if (options) {
		unsigned int flags = !!options->no_port_forwarding_flag
			| (!!options->no_agent_forwarding_flag << 1)
			| (!!options->no_x11_forwarding_flag << 2)
			| (!!options->no_pty_flag << 3);
#if DROPBEAR_SK_ECDSA || DROPBEAR_SK_ED25519
		flags |= (!!options->no_touch_required_flag << 4)
			| (!!options->verify_required_flag << 5);
#endif
		buf_putint(frame, flags);
		put_optional_string(frame, options->forced_command);
		buf_putbyte(frame, options->permit_open_destinations != NULL);
		if (options->permit_open_destinations) {
			m_list_elem *item;
			unsigned int count = 0;
			for (item = options->permit_open_destinations->first; item; item = item->next) {
				if (++count > BROKER_PERMITOPEN_MAX) {
					dropbear_exit("Authentication broker permitopen limit exceeded");
				}
			}
			buf_putint(frame, count);
			for (item = options->permit_open_destinations->first; item; item = item->next) {
				struct PermitTCPFwdEntry *entry = item->item;
				put_optional_string(frame, entry->host);
				buf_putint(frame, entry->port);
			}
		}
	}
#endif
}

static struct AuthState read_authenticated_identity(buffer *frame) {
	struct AuthState identity = {0};
	unsigned int group;
	identity.pw_uid = buf_getint(frame);
	identity.pw_gid = buf_getint(frame);
	identity.pw_group_count = buf_getint(frame);
	if (identity.pw_group_count == 0 || identity.pw_group_count > NGROUPS_MAX) {
		dropbear_exit("Authentication broker group count invalid");
	}
	for (group = 0; group < identity.pw_group_count; group++) {
		identity.pw_groups[group] = buf_getint(frame);
	}
	identity.pw_groups_valid = 1;
	identity.username = read_optional_string(frame);
	identity.pw_name = read_optional_string(frame);
	identity.pw_dir = read_optional_string(frame);
	identity.pw_shell = read_optional_string(frame);
	if (!identity.username || !identity.pw_name || !identity.pw_dir || !identity.pw_shell) {
		dropbear_exit("Authentication broker identity incomplete");
	}
#if DROPBEAR_SVR_PUBKEY_OPTIONS_BUILT
	identity.pubkey_info = read_optional_string(frame);
	if (buf_getbool(frame)) {
		unsigned int flags = buf_getint(frame);
		struct PubKeyOptions *options = m_malloc(sizeof(*options));
		identity.pubkey_options = options;
		if (flags & ~63U) {
			dropbear_exit("Authentication broker policy flags invalid");
		}
		options->no_port_forwarding_flag = !!(flags & 1);
		options->no_agent_forwarding_flag = !!(flags & 2);
		options->no_x11_forwarding_flag = !!(flags & 4);
		options->no_pty_flag = !!(flags & 8);
#if DROPBEAR_SK_ECDSA || DROPBEAR_SK_ED25519
		options->no_touch_required_flag = !!(flags & 16);
		options->verify_required_flag = !!(flags & 32);
#endif
		options->forced_command = read_optional_string(frame);
		if (buf_getbool(frame)) {
			unsigned int count = buf_getint(frame), i;
			if (count > BROKER_PERMITOPEN_MAX) {
				dropbear_exit("Authentication broker permitopen limit exceeded");
			}
			options->permit_open_destinations = list_new();
			for (i = 0; i < count; i++) {
				struct PermitTCPFwdEntry *entry = m_malloc(sizeof(*entry));
				entry->host = read_optional_string(frame);
				entry->port = buf_getint(frame);
				if (!entry->host) {
					dropbear_exit("Authentication broker permitopen host missing");
				}
				list_append(options->permit_open_destinations, entry);
			}
		}
	}
#endif
	return identity;
}

static buffer *authenticate_request(buffer *frame) {
	buffer *reply;
	if (!ses.session_id || ses.authstate.authdone) {
		dropbear_exit("Authentication broker phase rejected");
	}
	if (ses.payload) {
		buf_burn_free(ses.payload);
	}
	ses.payload = read_blob(frame);
	ses.payload_beginning = 0;
	if (frame->pos != frame->len || ses.payload->len > RECV_MAX_PAYLOAD_LEN
			|| buf_getbyte(ses.payload) != SSH_MSG_USERAUTH_REQUEST) {
		dropbear_exit("Authentication broker request invalid");
	}
	buf_setpos(ses.writepayload, 0);
	buf_setlen(ses.writepayload, 0);
	/* This process owns account lookup, authorized_keys/options, attempt limits,
	 * and proof verification against its own first exchange session ID. */
	recv_msg_userauth_request();
	buf_burn_free(ses.payload);
	ses.payload = NULL;
	reply = buf_new(BROKER_FRAME_MAX);
	buf_putbufstring(reply, ses.writepayload);
	buf_putint(reply, ses.authstate.failcount);
	buf_putbyte(reply, ses.authstate.authtypes);
	if (ses.authstate.authdone) {
		put_authenticated_identity(reply);
	}
	return reply;
}

/* IDs and channel numbers form a private immutable binding. An id of zero
 * can only reserve a channel which does not already have a broker record. */
static unsigned int session_slot(unsigned int id, unsigned int channel) {
	unsigned int slot = MAX_CHANNELS, empty = MAX_CHANNELS, i;
	for (i = 0; i < MAX_CHANNELS; i++) {
		if (!prepared_sessions[i]) {
			if (empty == MAX_CHANNELS) empty = i;
		} else if (id && prepared_sessions[i]->id == id) {
			if (prepared_sessions[i]->channel != channel) {
				dropbear_exit("Session broker channel binding changed");
			}
			slot = i;
		} else if (prepared_sessions[i]->channel == channel) {
			dropbear_exit("Session broker duplicate channel binding");
		}
	}
	if (id && slot == MAX_CHANNELS) {
		dropbear_exit("Session broker unknown session");
	}
	if (!id) slot = empty;
	return slot;
}

static struct PreparedSession *publish_session(unsigned int slot, unsigned int channel) {
	struct PreparedSession *entry = prepared_sessions[slot];
	unsigned int i;
	if (!entry) {
		if (next_session_id == UINT_MAX) dropbear_exit("Session broker identifier exhausted");
		entry = m_malloc(sizeof(*entry));
		entry->id = ++next_session_id;
		entry->channel = channel;
		entry->command.master = entry->command.slave = -1;
		entry->command.exit.exitpid = -1;
		for (i = 0; i < 3; i++) entry->fd[i] = -1;
		prepared_sessions[slot] = entry;
	}
	return entry;
}

static buffer *prepare_command_request(buffer *frame) {
	unsigned int id = buf_getint(frame), channel = buf_getint(frame);
	unsigned int slot, type_len;
	struct ChanSess candidate = {0};
	buffer *request = read_blob(frame), *reply = buf_new(BROKER_FRAME_MAX);
	char *type;
	int iscmd, issubsys, accepted = 0;
	if (!ses.authstate.authdone || frame->pos != frame->len
			|| request->len > RECV_MAX_PAYLOAD_LEN
			|| buf_getbyte(request) != SSH_MSG_CHANNEL_REQUEST
			|| buf_getint(request) != channel) {
		dropbear_exit("Session broker command envelope invalid");
	}
	slot = session_slot(id, channel);
	type = buf_getstring(request, &type_len);
	(void)buf_getbool(request); /* SSH want-reply stays in the worker. */
	iscmd = type_len == 4 && memcmp(type, "exec", 4) == 0;
	issubsys = type_len == 9 && memcmp(type, "subsystem", 9) == 0;
	if (slot != MAX_CHANNELS && (!prepared_sessions[slot] || !prepared_sessions[slot]->command.pid)
			&& (iscmd || issubsys
			|| (type_len == 5 && memcmp(type, "shell", 5) == 0))) {
		accepted = svr_prepare_session_command(&candidate, request, iscmd || issubsys, issubsys)
			== DROPBEAR_SUCCESS;
	}
	m_free(type);
	buf_burn_free(request);
	buf_putbyte(reply, accepted);
	if (accepted) {
		struct PreparedSession *entry = publish_session(slot, channel);
		free_prepared_command(&entry->command);
		entry->command.cmd = candidate.cmd;
		entry->command.original_command = candidate.original_command;
		entry->command.cmd_is_sftp_subsystem = candidate.cmd_is_sftp_subsystem;
		entry->command_ready = 1;
		buf_putint(reply, entry->id);
		put_optional_string(reply, entry->command.cmd);
		put_optional_string(reply, entry->command.original_command);
		buf_putbyte(reply, entry->command.cmd_is_sftp_subsystem);
	} else {
		free_prepared_command(&candidate);
	}
	return reply;
}

static buffer *pty_session_request(buffer *frame, int resize) {
	unsigned int id = buf_getint(frame), channel = buf_getint(frame), slot, type_len;
	struct ChanSess candidate = {0};
	struct PreparedSession *entry;
	buffer *request = read_blob(frame), *reply = buf_new(BROKER_FRAME_MAX);
	char *type;
	int accepted = 0;
	candidate.master = candidate.slave = -1;
	if (!ses.authstate.authdone || frame->pos != frame->len
			|| request->len > RECV_MAX_PAYLOAD_LEN
			|| buf_getbyte(request) != SSH_MSG_CHANNEL_REQUEST
			|| buf_getint(request) != channel) dropbear_exit("Session broker PTY envelope invalid");
	slot = session_slot(id, channel);
	entry = slot == MAX_CHANNELS ? NULL : prepared_sessions[slot];
	type = buf_getstring(request, &type_len);
	(void)buf_getbool(request);
	if (resize) {
		if (entry && type_len == 13 && memcmp(type, "window-change", 13) == 0)
			accepted = svr_session_window_change(&entry->command, request) == DROPBEAR_SUCCESS;
	} else if (slot != MAX_CHANNELS && (!entry || (!entry->command.pid && !entry->command.tty))
			&& type_len == 7 && memcmp(type, "pty-req", 7) == 0) {
		accepted = svr_prepare_session_pty(&candidate, request) == DROPBEAR_SUCCESS;
		if (accepted) {
			entry = publish_session(slot, channel);
			entry->command.master = candidate.master;
			entry->command.slave = candidate.slave;
			entry->command.term = candidate.term;
			entry->command.tty = candidate.tty;
		}
	}
	m_free(type);
	buf_burn_free(request);
	buf_putbyte(reply, accepted);
	if (accepted && !resize) {
		buf_putint(reply, entry->id);
		buf_putstring(reply, entry->command.term, strlen(entry->command.term));
		buf_putstring(reply, entry->command.tty, strlen(entry->command.tty));
	}
	return reply;
}

static buffer *release_session_request(buffer *frame) {
	unsigned int id = buf_getint(frame), i;
	buffer *reply = buf_new(1);
	if (!ses.authstate.authdone || id == 0 || frame->pos != frame->len) {
		dropbear_exit("Session broker release invalid");
	}
	for (i = 0; i < MAX_CHANNELS; i++) {
		if (prepared_sessions[i] && prepared_sessions[i]->id == id) {
			release_prepared_session(i);
			buf_putbyte(reply, 1);
			return reply;
		}
	}
	dropbear_exit("Session broker release has unknown identity");
	return NULL;
}

/* Set up every descriptor before publishing or forking. */
static int session_pipes(int fds[3][2]) {
	unsigned int i, j;
	for (i = 0; i < 3; i++) for (j = 0; j < 2; j++) fds[i][j] = -1;
	for (i = 0; i < 3; i++) {
		if (pipe(fds[i]) < 0) goto fail;
		for (j = 0; j < 2; j++) {
			if (fds[i][j] >= FD_SETSIZE || fcntl(fds[i][j], F_SETFD, FD_CLOEXEC) < 0) goto fail;
			ses.maxfd = MAX(ses.maxfd, fds[i][j]);
		}
	}
	return DROPBEAR_SUCCESS;
fail:
	for (i = 0; i < 3; i++) for (j = 0; j < 2; j++) close_stream(&fds[i][j]);
	return DROPBEAR_FAILURE;
}

static struct PreparedSession *read_session(buffer *frame) {
	unsigned int id = buf_getint(frame), i;
	if (!id || !ses.authstate.authdone) dropbear_exit("Session broker identity invalid");
	for (i = 0; i < MAX_CHANNELS; i++) {
		if (prepared_sessions[i] && prepared_sessions[i]->id == id) return prepared_sessions[i];
	}
	dropbear_exit("Session broker unknown identity");
	return NULL;
}

static void reap_sessions(void) {
	int status;
	pid_t pid;
	unsigned int i;
	while ((pid = waitpid(-1, &status, WNOHANG)) > 0) {
		for (i = 0; i < MAX_CHANNELS; i++) {
			struct PreparedSession *entry = prepared_sessions[i];
			struct exitinfo *ex;
			if (!entry || entry->command.pid != pid || entry->command.exit.exitpid != -1) continue;
			ex = &entry->command.exit;
			dropbear_log(LOG_INFO, "Broker session reaped id=%u pid=%ld status=0x%x", entry->id, (long)pid, status);
			ex->exitpid = pid;
			ex->exitstatus = WIFEXITED(status) ? WEXITSTATUS(status) : 0;
			ex->exitsignal = WIFSIGNALED(status) ? WTERMSIG(status) : -1;
#if defined(WCOREDUMP)
			ex->exitcore = WIFSIGNALED(status) && WCOREDUMP(status);
#endif
			break;
		}
	}
}

static buffer *spawn_session_request(buffer *frame) {
	struct PreparedSession *entry = read_session(frame);
	char *agent_path = read_optional_string(frame);
	buffer *reply = buf_new(1);
	int fds[3][2] = {{-1, -1}, {-1, -1}, {-1, -1}};
	int is_pty = entry->command.tty != NULL;
	pid_t pid;
	unsigned int i, j;
	if (frame->pos != frame->len || (agent_path && strlen(agent_path) > 4096)) {
		dropbear_exit("Session broker spawn envelope invalid");
	}
	if (!entry->command_ready || entry->command.pid != 0
			|| (is_pty && (entry->command.master < 0 || entry->command.slave < 0))
			|| (agent_path && !svr_pubkey_allows_agentfwd())
			|| (!is_pty && session_pipes(fds) != DROPBEAR_SUCCESS)) {
		m_free(agent_path);
		buf_putbyte(reply, 0);
		return reply;
	}
	pid = fork();
	if (pid == 0) {
		/* No helper/session/control descriptor survives into the login child,
		 * even if account switching or environment setup fails before exec. */
		if (!is_pty && (dup2(fds[0][0], STDIN_FILENO) < 0 || dup2(fds[1][1], STDOUT_FILENO) < 0
				|| dup2(fds[2][1], STDERR_FILENO) < 0)) _exit(127);
		for (i = 3; i <= ses.maxfd; i++) {
			if (!is_pty || (int)i != entry->command.slave) close(i);
		}
		entry->command.master = -1;
		request_fd = response_fd = -1;
		if (signal(SIGCHLD, SIG_DFL) == SIG_ERR) _exit(127);
		entry->command.connection_string = connection_environment.connection_string;
		entry->command.client_string = connection_environment.client_string;
		entry->command.broker_agent_path = agent_path;
		if (is_pty) svr_exec_pty_child(&entry->command);
		/* Non-PTY login commands must not share the privileged broker SID. */
		if (setsid() < 0) _exit(127);
		svr_exec_session_child(&entry->command);
		_exit(127);
	}
	m_free(agent_path);
	if (pid < 0) {
		for (i = 0; i < 3; i++) for (j = 0; j < 2; j++) close_stream(&fds[i][j]);
		buf_putbyte(reply, 0);
		return reply;
	}
	dropbear_log(LOG_INFO, "Broker session spawned id=%u pid=%ld", entry->id, (long)pid);
	entry->command.pid = pid;
	entry->command.exit.exitpid = -1;
	if (is_pty) {
		close_stream(&entry->command.slave);
		entry->fd[0] = entry->fd[1] = entry->command.master;
		setnonblocking(entry->command.master);
	} else {
		for (i = 0; i < 3; i++) {
			entry->fd[i] = fds[i][i == 0 ? 1 : 0];
			close(fds[i][i == 0 ? 0 : 1]);
			setnonblocking(entry->fd[i]);
		}
	}
	buf_putbyte(reply, 1);
	return reply;
}

static void put_exit(buffer *reply, const struct exitinfo *ex) {
	buf_putbyte(reply, ex->exitpid != -1);
	if (ex->exitpid != -1) {
		buf_putint(reply, ex->exitstatus);
		buf_putint(reply, ex->exitsignal);
		buf_putbyte(reply, ex->exitcore);
	}
}

static buffer *session_io_request(buffer *frame) {
	struct PreparedSession *entry = read_session(frame);
	buffer *input = read_blob(frame), *reply = buf_new(2 * BROKER_IO_MAX + 64);
	int input_eof = buf_getbool(frame);
	unsigned int capacity[2], consumed = 0, i;
	capacity[0] = buf_getint(frame);
	capacity[1] = buf_getint(frame);
	if (!entry->command.pid || frame->pos != frame->len || input->len > BROKER_IO_MAX
			|| capacity[0] > BROKER_IO_MAX || capacity[1] > BROKER_IO_MAX) {
		dropbear_exit("Session broker IO envelope invalid");
	}
	if (entry->fd[0] >= 0 && input->len) {
		ssize_t n = write(entry->fd[0], input->data, input->len);
		if (n > 0) consumed = n;
		else if (n < 0 && errno != EAGAIN && errno != EINTR) {
			dropbear_log(LOG_INFO, "Broker stdin closed id=%u errno=%d", entry->id, errno);
			close_session_stream(entry, 0);
		}
	}
	if (input_eof && consumed == input->len) close_session_stream(entry, 0);
	buf_putint(reply, consumed);
	buf_putbyte(reply, entry->fd[0] < 0);
	buf_burn_free(input);
	for (i = 0; i < 2; i++) {
		unsigned char data[BROKER_IO_MAX];
		ssize_t n = 0;
		int *fd = &entry->fd[i+1];
		if (*fd >= 0 && capacity[i]) {
			n = read(*fd, data, capacity[i]);
			if (n < 0 && errno != EINTR && errno != EAGAIN)
				dropbear_log(LOG_INFO, "Broker output closed id=%u stream=%u errno=%d", entry->id, i, errno);
			if (n == 0 || (n < 0 && errno != EINTR
					&& (errno != EAGAIN || entry->command.exit.exitpid != -1))) close_session_stream(entry, i+1);
		}
		buf_putstring(reply, (const char *)data, n > 0 ? n : 0);
		buf_putbyte(reply, *fd < 0);
	}
	put_exit(reply, &entry->command.exit);
	return reply;
}

static buffer *signal_session_request(buffer *frame) {
	struct PreparedSession *entry = read_session(frame);
	buffer *request = read_blob(frame), *reply = buf_new(1);
	char *name, *type;
	unsigned int len, type_len, i;
	int sig = 0, accepted = 0;
	if (frame->pos != frame->len || buf_getbyte(request) != SSH_MSG_CHANNEL_REQUEST
			|| buf_getint(request) != entry->channel) dropbear_exit("Session broker signal envelope invalid");
	type = buf_getstring(request, &type_len);
	(void)buf_getbool(request);
	name = buf_getstring(request, &len);
	if (type_len == 6 && memcmp(type, "signal", 6) == 0 && request->pos == request->len
			&& entry->command.pid > 0 && entry->command.exit.exitpid == -1
			&& !svr_opts.forced_command && !svr_pubkey_has_forced_command()
			&& !(DROPBEAR_SVR_MULTIUSER && !DROPBEAR_SVR_DROP_PRIVS)) {
		for (i = 0; signames[i].name; i++) {
			if (strlen(signames[i].name) == len && memcmp(name, signames[i].name, len) == 0) {
				sig = signames[i].signal;
				break;
			}
		}
		/* This PID has not been reaped; it cannot be reused during the call. */
		if (sig) accepted = kill(entry->command.pid, sig) == 0;
	}
	m_free(name);
	m_free(type);
	buf_burn_free(request);
	buf_putbyte(reply, accepted);
	return reply;
}

static buffer *read_frame(int fd, int allow_eof) {
	unsigned char bytes[4];
	buffer header = {bytes, 4, 0, 4};
	buffer *frame;
	unsigned int len;
	size_t count = atomicio(read, fd, bytes, sizeof(bytes));
	if (count == 0 && allow_eof) {
		return NULL;
	}
	if (count != sizeof(bytes)) {
		dropbear_exit("KEX broker frame header failed");
	}
	len = buf_getint(&header);
	if (len == 0 || len > BROKER_FRAME_MAX) {
		dropbear_exit("KEX broker frame length invalid");
	}
	frame = buf_new(len);
	if (atomicio(read, fd, buf_getwriteptr(frame, len), len) != len) {
		dropbear_exit("KEX broker frame truncated");
	}
	buf_setlen(frame, len);
	return frame;
}

static void write_frame(int fd, const buffer *frame) {
	unsigned char bytes[4];
	buffer header = {bytes, 0, 0, 4};
	if (frame->len == 0 || frame->len > BROKER_FRAME_MAX) {
		dropbear_exit("KEX broker response length invalid");
	}
	buf_putint(&header, frame->len);
	if (atomicio(vwrite, fd, bytes, sizeof(bytes)) != sizeof(bytes)
			|| atomicio(vwrite, fd, frame->data, frame->len) != frame->len) {
		dropbear_exit("KEX broker write failed");
	}
}

static algo_type *read_algorithm(buffer *frame, algo_type *catalog) {
	unsigned int len;
	char *name = buf_getstring(frame, &len);
	algo_type *found = NULL;
	for (; catalog->name; catalog++) {
		if (catalog->usable && strlen(catalog->name) == len
				&& memcmp(catalog->name, name, len) == 0) {
			found = catalog;
			break;
		}
	}
	m_free(name);
	if (!found) {
		dropbear_exit("KEX broker algorithm rejected");
	}
	return found;
}

static void check_hash_prefix(buffer *prefix) {
	unsigned int i;
	for (i = 0; i < 4; i++) {
		buffer *value = read_blob(prefix);
		if (i == 0 && !ses.remoteident) {
			/* The broker forks before client input. Retain the first complete,
			 * bounded identification and pin it for every subsequent exchange. */
			if (value->len < 6 || value->len > 255 || memchr(value->data, 0, value->len)
					|| memchr(value->data, '\r', value->len) || memchr(value->data, '\n', value->len)
					|| (memcmp(value->data, "SSH-2.", 6) != 0
						&& (value->len < 9 || memcmp(value->data, "SSH-1.99-", 9) != 0)))
				dropbear_exit("KEX broker client identification invalid");
			ses.remoteident = m_malloc(value->len + 1);
			memcpy(ses.remoteident, value->data, value->len);
			ses.remoteident[value->len] = '\0';
		}
		const char *ident = i == 0 ? ses.remoteident : LOCAL_IDENT;
		unsigned int limit = i == 2 ? RECV_MAX_PAYLOAD_LEN : TRANS_MAX_PAYLOAD_LEN;
		if ((i < 2 && (value->len != strlen(ident)
				|| memcmp(value->data, ident, value->len) != 0))
				|| (i >= 2 && (value->len < 17 || value->len > limit
					|| value->data[0] != SSH_MSG_KEXINIT))) {
			dropbear_exit("KEX broker transcript rejected");
		}
		buf_free(value);
	}
	if (prefix->pos != prefix->len) {
		dropbear_exit("KEX broker transcript has trailing bytes");
	}
}

/* Replace inherited private key objects before dropping the worker identity. */
static void retain_public_hostkeys(void) {
	sign_key *public_keys = new_sign_key();
	algo_type *sig;
	for (sig = sigalgs; sig->name; sig++) {
		enum signkey_type type = signkey_type_from_signature(sig->val);
		void **old = signkey_key_ptr(svr_opts.hostkey, type);
		void **copy = signkey_key_ptr(public_keys, type);
		buffer *encoded;
		if (!old || !*old || !copy || *copy) {
			continue;
		}
		encoded = buf_new(MAX_PUBKEY_SIZE);
		buf_put_pub_key(encoded, svr_opts.hostkey, type);
		buf_setpos(encoded, 4);
		if (buf_get_pub_key(encoded, public_keys, &type) != DROPBEAR_SUCCESS) {
			dropbear_exit("KEX broker public key copy failed");
		}
		buf_free(encoded);
	}
	sign_key_free(svr_opts.hostkey);
	svr_opts.hostkey = public_keys;
}

static void broker_loop(int input, int output) {
	buffer *frame;
	enum signature_type first_signature = DROPBEAR_SIGNATURE_NONE;
	monitor_process = 1;
	request_fd = input;
	response_fd = output;
	svr_make_connection_string(&connection_environment);
	/* No network, listener slot, or worker signal pipe remains in the broker. */
	signal(SIGCHLD, SIG_DFL);
	signal(SIGTERM, SIG_DFL);
	signal(SIGINT, SIG_DFL);
	signal(SIGHUP, SIG_DFL);
	signal(SIGPIPE, SIG_IGN);
	close(ses.sock_in);
	if (ses.sock_out != ses.sock_in) {
		close(ses.sock_out);
	}
	ses.sock_in = ses.sock_out = -1;
	close(ses.signal_pipe[0]);
	close(ses.signal_pipe[1]);
	close(svr_ses.childpipe);
	svr_ses.childpipe = -1;
	if (ses.kexhashbuf) buf_burn_free(ses.kexhashbuf);
	ses.kexhashbuf = NULL;
	/* The network worker sends the configured banner before forwarding auth. */
	if (svr_opts.banner) {
		buf_free(svr_opts.banner);
		svr_opts.banner = NULL;
	}
	seedrandom();

	while ((frame = read_frame(input, 1)) != NULL) {
		DEF_MP_INT(dh_e);
		buffer *q_c = NULL;
		buffer *secret, *reply;
		algo_type *kex, *sig;
		unsigned char operation = buf_getbyte(frame);
		reap_sessions();
		if (operation >= BROKER_AUTH_REQUEST && operation <= BROKER_WINDOW_CHANGE) {
			if (operation == BROKER_AUTH_REQUEST) reply = authenticate_request(frame);
			else if (operation == BROKER_PREPARE_COMMAND) reply = prepare_command_request(frame);
			else if (operation == BROKER_RELEASE_SESSION) reply = release_session_request(frame);
			else if (operation == BROKER_SPAWN) reply = spawn_session_request(frame);
			else if (operation == BROKER_IO) reply = session_io_request(frame);
			else if (operation == BROKER_SIGNAL) reply = signal_session_request(frame);
			else reply = pty_session_request(frame, operation == BROKER_WINDOW_CHANGE);
			buf_burn_free(frame);
			write_frame(output, reply);
			buf_burn_free(reply);
			continue;
		}
		if (operation != BROKER_KEX_REQUEST) {
			dropbear_exit("KEX broker operation rejected");
		}
		kex = read_algorithm(frame, sshkex);
		sig = read_algorithm(frame, sigalgs);
		if (!kex->data || (first_signature != DROPBEAR_SIGNATURE_NONE
				&& first_signature != sig->val)) {
			dropbear_exit("KEX broker algorithm transition rejected");
		}
		first_signature = sig->val;
		ses.newkeys->algo_kex = kex->data;
		ses.newkeys->algo_signature = sig->val;
		ses.newkeys->algo_hostkey = signkey_type_from_signature(sig->val);
		ses.kexhashbuf = read_blob(frame);
		check_hash_prefix(ses.kexhashbuf);
		ses.kexhashbuf = buf_resize(ses.kexhashbuf, ses.kexhashbuf->len + KEXHASHBUF_MAX_INTS);
		if (normal_dh()) {
			m_mp_init(&dh_e);
			if (buf_getmpint(frame, &dh_e) != DROPBEAR_SUCCESS) {
				dropbear_exit("KEX broker DH input rejected");
			}
		} else {
			q_c = read_blob(frame);
		}
		if (frame->pos != frame->len) {
			dropbear_exit("KEX broker request has trailing bytes");
		}
		buf_setpos(ses.writepayload, 0);
		buf_setlen(ses.writepayload, 0);
		svr_compute_kex_reply(&dh_e, q_c);
		mp_clear(&dh_e);
		if (q_c) {
			buf_free(q_c);
		}
		buf_burn_free(frame);
		secret = buf_new(MAX_KEX_PARTS);
		if (ses.dh_K) {
			buf_putmpint(secret, ses.dh_K);
			mp_clear(ses.dh_K);
			m_free(ses.dh_K);
			ses.dh_K = NULL;
		} else if (ses.dh_K_bytes) {
			buf_putbytes(secret, ses.dh_K_bytes->data, ses.dh_K_bytes->len);
			buf_burn_free(ses.dh_K_bytes);
			ses.dh_K_bytes = NULL;
		} else {
			dropbear_exit("KEX broker missing shared secret");
		}
		reply = buf_new(BROKER_FRAME_MAX);
		buf_putbufstring(reply, ses.writepayload);
		buf_putbufstring(reply, ses.hash);
		buf_putbufstring(reply, ses.session_id);
		buf_putbufstring(reply, secret);
		buf_burn_free(secret);
		buf_burn_free(ses.hash);
		ses.hash = NULL;
		write_frame(output, reply);
		buf_burn_free(reply);
	}
	for (unsigned int i = 0; i < MAX_CHANNELS; i++) {
		release_prepared_session(i);
	}
	sign_key_free(svr_opts.hostkey);
	close(input);
	close(output);
	_exit(0);
}

/* WOS process/PRCTL ABI: return the raw negative errno, not libc errno. */
static long worker_control(unsigned long option, unsigned long value) {
	register unsigned long arg3 __asm__("r8") = 0;
	register unsigned long arg4 __asm__("r9") = 0;
	register unsigned long arg5 __asm__("r10") = 0;
	long result;
	__asm__ __volatile__("syscall" : "=a"(result)
		: "a"(3UL), "D"(36UL), "S"(option), "d"(value), "r"(arg3), "r"(arg4), "r"(arg5)
		: "rcx", "r11", "memory");
	return result;
}

static void drop_network_worker(uid_t uid, gid_t gid) {
	uid_t real_uid, effective_uid, saved_uid;
	gid_t real_gid, effective_gid, saved_gid;
	/* NNP and service sealing do not discard SET_UID/SET_GID needed below. */
	/* Privileged setgid/setuid clear all three IDs in WOS; getres* verifies it.
	 * WOS does not currently implement the libc setres* entrypoints. */
	if (worker_control(38, 1) != 0 || worker_control(0x574f5303, 0) != 0
			|| setgroups(0, NULL) < 0 || setgid(gid) < 0
			|| setuid(uid) < 0 || worker_control(0x574f5302, 0) != 0
			|| worker_control(4, 0) != 0 || chdir("/") < 0)
		dropbear_exit("Network worker credential drop failed");
	umask(0077);
	if (getresuid(&real_uid, &effective_uid, &saved_uid) < 0
			|| getresgid(&real_gid, &effective_gid, &saved_gid) < 0
			|| real_uid != uid || effective_uid != uid || saved_uid != uid
			|| real_gid != gid || effective_gid != gid || saved_gid != gid
			|| getgroups(0, NULL) != 0 || worker_control(39, 0) != 1
			|| worker_control(0x574f5301, 0) != 0 || worker_control(0x574f5304, 0) != 256
			|| worker_control(3, 0) != 0 || umask(0077) != 0077)
		dropbear_exit("Network worker credential verification failed");
}

void svr_kex_broker_start(void) {
	int request[2], response[2];
	pid_t pid;
	uid_t worker_uid;
	gid_t worker_gid;
	struct passwd *worker = getpwnam(DROPBEAR_SVR_BROKER_USER);
	if (!worker || worker->pw_uid == 0 || worker->pw_gid == 0 || getuid() != 0)
		dropbear_exit("Dedicated network worker account unavailable");
	worker_uid = worker->pw_uid;
	worker_gid = worker->pw_gid;
	if (request_fd >= 0 || ses.session_id || ses.remoteident || !ses.newkeys || pipe(request) < 0) {
		dropbear_exit("KEX broker creation failed");
	}
	if (pipe(response) < 0) {
		close(request[0]);
		close(request[1]);
		dropbear_exit("KEX broker creation failed");
	}
	for (unsigned int i = 0; i < 2; i++) {
		if (request[i] >= FD_SETSIZE || response[i] >= FD_SETSIZE)
			dropbear_exit("KEX broker descriptor exceeds session bound");
		ses.maxfd = MAX(ses.maxfd, MAX(request[i], response[i]));
	}
	if (fcntl(request[1], F_SETFD, FD_CLOEXEC) < 0
			|| fcntl(request[0], F_SETFD, FD_CLOEXEC) < 0
			|| fcntl(response[1], F_SETFD, FD_CLOEXEC) < 0
			|| fcntl(response[0], F_SETFD, FD_CLOEXEC) < 0) {
		dropbear_exit("KEX broker descriptor setup failed");
	}
	pid = fork();
	if (pid < 0) {
		dropbear_exit("KEX broker fork failed");
	}
	if (pid == 0) {
		close(request[1]);
		close(response[0]);
		/* Establish the broker boundary before the parent discards authority. */
		char ready = 'S';
		if (setsid() < 0 || atomicio(vwrite, response[1], &ready, 1) != 1) _exit(127);
		broker_loop(request[0], response[1]);
	}
	close(request[0]);
	close(response[1]);
	request_fd = request[1];
	response_fd = response[0];
	broker_pid = pid;
	char ready = 0;
	if (atomicio(read, response_fd, &ready, 1) != 1 || ready != 'S'
			|| getsid(pid) != pid || getpgid(pid) != pid)
		dropbear_exit("Broker session isolation failed");
	retain_public_hostkeys();
	drop_network_worker(worker_uid, worker_gid);
	dropbear_log(LOG_INFO, "KEX broker started pid=%ld worker_uid=%lu worker_gid=%lu", (long)pid,
		(unsigned long)worker_uid, (unsigned long)worker_gid);
}

void svr_kex_broker_exchange(mp_int *dh_e, buffer *q_c) {
	buffer *request, *response, *reply, *session_id, *secret;
	algo_type *kex;
	const char *signature_name;
	if (ses.dh_K || ses.dh_K_bytes || ses.hash) {
		dropbear_exit("KEX broker overlapping exchange state");
	}
	if (request_fd < 0) {
		dropbear_exit("KEX broker was not initialized before client input");
	}
	for (kex = sshkex; kex->name; kex++) {
		if (kex->usable && kex->data == ses.newkeys->algo_kex) {
			break;
		}
	}
	if (!kex->name) {
		dropbear_exit("KEX broker unknown negotiated algorithm");
	}
	signature_name = signature_name_from_type(ses.newkeys->algo_signature, NULL);
	request = buf_new(BROKER_FRAME_MAX);
	buf_putbyte(request, BROKER_KEX_REQUEST);
	buf_putstring(request, kex->name, strlen(kex->name));
	buf_putstring(request, signature_name, strlen(signature_name));
	buf_putbufstring(request, ses.kexhashbuf);
	if (normal_dh()) {
		buf_putmpint(request, dh_e);
	} else {
		buf_putbufstring(request, q_c);
	}
	buf_burn_free(ses.kexhashbuf);
	ses.kexhashbuf = NULL;
	write_frame(request_fd, request);
	buf_burn_free(request);
	response = read_frame(response_fd, 0);
	reply = read_blob(response);
	ses.hash = read_blob(response);
	session_id = read_blob(response);
	secret = read_blob(response);
	if (response->pos != response->len || ses.hash->len != ses.newkeys->algo_kex->hash_desc->hashsize
			|| session_id->len == 0 || session_id->len > 64) {
		dropbear_exit("KEX broker response invalid");
	}
	if (ses.session_id) {
		if (ses.session_id->len != session_id->len
				|| memcmp(ses.session_id->data, session_id->data, session_id->len) != 0) {
			dropbear_exit("KEX broker session ID changed");
		}
		buf_free(session_id);
	} else {
		ses.session_id = session_id;
	}
	if (pq_hybrid()) {
		ses.dh_K_bytes = secret;
	} else {
		m_mp_alloc_init_multi(&ses.dh_K, NULL);
		if (buf_getmpint(secret, ses.dh_K) != DROPBEAR_SUCCESS || secret->pos != secret->len) {
			dropbear_exit("KEX broker shared secret invalid");
		}
		buf_burn_free(secret);
	}
	buf_putbytes(ses.writepayload, reply->data, reply->len);
	buf_free(reply);
	buf_burn_free(response);
}

void svr_kex_broker_authenticate(void) {
	buffer view = *ses.payload;
	buffer *request, *response, *reply;
	struct AuthState identity = {0};
	unsigned int failures;
	unsigned char methods, type;
	if (request_fd < 0 || response_fd < 0 || !ses.session_id || ses.authstate.authdone) {
		dropbear_exit("Authentication broker unavailable");
	}
	request = buf_new(BROKER_FRAME_MAX);
	buf_putbyte(request, BROKER_AUTH_REQUEST);
	buf_setpos(&view, ses.payload_beginning);
	buf_putstring(request, (const char *)buf_getptr(&view, view.len - view.pos), view.len - view.pos);
	write_frame(request_fd, request);
	buf_burn_free(request);
	response = read_frame(response_fd, 0);
	reply = read_blob(response);
	type = buf_getbyte(reply);
	failures = buf_getint(response);
	methods = buf_getbyte(response);
	if (type == SSH_MSG_USERAUTH_SUCCESS) {
		if (reply->len != 1) {
			dropbear_exit("Authentication broker success reply invalid");
		}
		identity = read_authenticated_identity(response);
	} else if (type != SSH_MSG_USERAUTH_FAILURE && type != SSH_MSG_USERAUTH_PK_OK) {
		dropbear_exit("Authentication broker reply type invalid");
	}
	if (response->pos != response->len) {
		dropbear_exit("Authentication broker reply has trailing bytes");
	}
	buf_burn_free(response);
	if (type == SSH_MSG_USERAUTH_SUCCESS) {
		/* The worker has never performed account lookup. Install only the fully
		 * decoded broker identity before the existing session transition. */
		if (ses.authstate.username || ses.authstate.pw_name || ses.authstate.pw_passwd) {
			dropbear_exit("Authentication broker identity already installed");
		}
		identity.failcount = failures;
		identity.authtypes = methods;
		ses.authstate = identity;
		send_msg_userauth_success();
	} else {
		ses.authstate.failcount = failures;
		ses.authstate.authtypes = methods;
		CHECKCLEARTOWRITE();
		buf_putbytes(ses.writepayload, reply->data, reply->len);
		encrypt_packet();
	}
	buf_free(reply);
}

int svr_kex_broker_prepare_command(struct Channel *channel, struct ChanSess *session) {
	buffer *request, *response;
	struct ChanSess candidate = {0};
	unsigned int id;
	int accepted;
	if (request_fd < 0 || response_fd < 0 || !ses.authstate.authdone) {
		dropbear_exit("Session broker unavailable");
	}
	request = buf_new(BROKER_FRAME_MAX);
	buf_putbyte(request, BROKER_PREPARE_COMMAND);
	buf_putint(request, session->broker_session_id);
	buf_putint(request, channel->index);
	buf_putstring(request, (const char *)ses.payload->data + ses.payload_beginning,
		ses.payload->len - ses.payload_beginning);
	write_frame(request_fd, request);
	buf_burn_free(request);
	response = read_frame(response_fd, 0);
	accepted = buf_getbool(response);
	if (accepted) {
		id = buf_getint(response);
		candidate.cmd = read_optional_string(response);
		candidate.original_command = read_optional_string(response);
		candidate.cmd_is_sftp_subsystem = buf_getbool(response);
		if (!id || (session->broker_session_id && id != session->broker_session_id)
				|| (candidate.cmd_is_sftp_subsystem && !candidate.cmd)) {
			dropbear_exit("Session broker command identity invalid");
		}
		candidate.broker_session_id = id;
	}
	if (response->pos != response->len) {
		dropbear_exit("Session broker command reply has trailing bytes");
	}
	buf_burn_free(response);
	if (!accepted) return DROPBEAR_FAILURE;
	free_prepared_command(session);
	session->cmd = candidate.cmd;
	session->original_command = candidate.original_command;
	session->cmd_is_sftp_subsystem = candidate.cmd_is_sftp_subsystem;
	session->broker_session_id = candidate.broker_session_id;
	return DROPBEAR_SUCCESS;
}

static buffer *session_rpc(buffer *request) {
	buffer *reply;
	if (request_fd < 0 || response_fd < 0) dropbear_exit("Session broker unavailable");
	write_frame(request_fd, request);
	buf_burn_free(request);
	reply = read_frame(response_fd, 0);
	return reply;
}

static int worker_pty_request(struct Channel *channel, struct ChanSess *session, int resize) {
	buffer *request = buf_new(BROKER_FRAME_MAX), *reply;
	int accepted;
	buf_putbyte(request, resize ? BROKER_WINDOW_CHANGE : BROKER_PTY);
	buf_putint(request, session->broker_session_id);
	buf_putint(request, channel->index);
	buf_putstring(request, (const char *)ses.payload->data + ses.payload_beginning,
		ses.payload->len - ses.payload_beginning);
	reply = session_rpc(request);
	accepted = buf_getbool(reply);
	if (accepted && !resize) {
		unsigned int id = buf_getint(reply);
		if (!id || (session->broker_session_id && session->broker_session_id != id)
				|| session->term || session->tty) dropbear_exit("Session broker PTY identity invalid");
		session->broker_session_id = id;
		session->term = buf_getstring(reply, NULL);
		session->tty = buf_getstring(reply, NULL);
		/* The worker holds public metadata and relay pipes, never a PTY FD. */
	}
	if (reply->pos != reply->len) dropbear_exit("Session broker PTY reply invalid");
	buf_burn_free(reply);
	return accepted ? DROPBEAR_SUCCESS : DROPBEAR_FAILURE;
}

int svr_kex_broker_pty(struct Channel *channel, struct ChanSess *session) {
	return worker_pty_request(channel, session, 0);
}

int svr_kex_broker_window_change(struct Channel *channel, struct ChanSess *session) {
	return worker_pty_request(channel, session, 1);
}

int svr_kex_broker_spawn(struct Channel *channel, struct ChanSess *session) {
	int fds[3][2], accepted;
	unsigned int i, j;
	buffer *request, *reply;
	char *agent_path = NULL;
	struct BrokerRelay *relay;
	if (!session->broker_session_id || session->broker_relay || session->pid) return DROPBEAR_FAILURE;
	if (session_pipes(fds) != DROPBEAR_SUCCESS) return DROPBEAR_FAILURE;
	request = buf_new(BROKER_FRAME_MAX);
	buf_putbyte(request, BROKER_SPAWN);
	buf_putint(request, session->broker_session_id);
#if DROPBEAR_SVR_AGENTFWD
	if (session->agentlistener) {
		size_t size = strlen(session->agentdir) + strlen(session->agentfile) + 2;
		agent_path = m_malloc(size);
		snprintf(agent_path, size, "%s/%s", session->agentdir, session->agentfile);
	}
#endif
	put_optional_string(request, agent_path);
	m_free(agent_path);
	reply = session_rpc(request);
	accepted = buf_getbool(reply);
	if (reply->pos != reply->len) dropbear_exit("Session broker spawn reply invalid");
	buf_free(reply);
	if (!accepted) {
		for (i = 0; i < 3; i++) for (j = 0; j < 2; j++) close_stream(&fds[i][j]);
		return DROPBEAR_FAILURE;
	}
	relay = m_malloc(sizeof(*relay));
	relay->exit.exitpid = -1;
	for (i = 0; i < 3; i++) {
		relay->fd[i] = fds[i][i == 0 ? 0 : 1];
		for (j = 0; j < 2; j++) setnonblocking(fds[i][j]);
	}
	channel->writefd = fds[0][1];
	channel->readfd = fds[1][0];
	channel->errfd = fds[2][0];
	channel->bidir_fd = 0;
	/* A running marker, not a PID. Signal/status operations use private ID. */
	session->pid = 1;
	session->broker_relay = relay;
	relay_count++;
	return DROPBEAR_SUCCESS;
}

int svr_kex_broker_signal(const struct ChanSess *session) {
	buffer *request = buf_new(BROKER_FRAME_MAX), *reply;
	int accepted;
	buf_putbyte(request, BROKER_SIGNAL);
	buf_putint(request, session->broker_session_id);
	buf_putstring(request, (const char *)ses.payload->data + ses.payload_beginning,
		ses.payload->len - ses.payload_beginning);
	reply = session_rpc(request);
	accepted = buf_getbool(reply);
	if (reply->pos != reply->len) dropbear_exit("Session broker signal reply invalid");
	buf_free(reply);
	return accepted ? DROPBEAR_SUCCESS : DROPBEAR_FAILURE;
}

void svr_kex_broker_timeout(struct timeval *timeout) {
	if (relay_count && (timeout->tv_sec > 0 || timeout->tv_usec > 10000)) {
		timeout->tv_sec = 0;
		timeout->tv_usec = 10000;
	}
}

/* A slow child gets no more input until it consumes the retained chunk; a slow
 * SSH receiver advertises no output capacity until its adapter drains. Every
 * FD operation is nonblocking and each RPC has a bounded request and response. */
void svr_kex_broker_io(void) {
	unsigned int index, i;
	if (!relay_count) return;
	for (index = 0; index < ses.chansize; index++) {
		struct Channel *channel = ses.channels[index];
		struct ChanSess *session;
		struct BrokerRelay *relay;
		struct RelayChunk *input;
		buffer *request, *reply;
		unsigned int consumed;
		int input_closed;
		if (!channel || channel->type != &svrchansess) continue;
		session = channel->typedata;
		relay = session->broker_relay;
		if (!relay) continue;
		input = &relay->chunk[0];
		if (relay->fd[0] >= 0 && input->len == 0) {
			ssize_t n = read(relay->fd[0], input->data, BROKER_IO_MAX);
			if (n > 0) input->len = n;
			else if (n == 0 || (errno != EINTR && errno != EAGAIN)) {
				relay->eof[0] = 1;
				close_stream(&relay->fd[0]);
			}
		}
		request = buf_new(BROKER_IO_MAX + 32);
		buf_putbyte(request, BROKER_IO);
		buf_putint(request, session->broker_session_id);
		buf_putstring(request, (const char *)input->data + input->pos, input->len - input->pos);
		buf_putbyte(request, relay->eof[0]);
		for (i = 1; i < 3; i++) {
			buf_putint(request, relay->chunk[i].len == 0 ? BROKER_IO_MAX : 0);
		}
		reply = session_rpc(request);
		consumed = buf_getint(reply);
		input_closed = buf_getbool(reply);
		if (consumed > input->len - input->pos) dropbear_exit("Session broker input count invalid");
		input->pos += consumed;
		if (input_closed) {
			close_stream(&relay->fd[0]);
			relay->eof[0] = 1;
			input->pos = input->len;
		}
		if (input->pos == input->len) input->pos = input->len = 0;
		for (i = 1; i < 3; i++) {
			struct RelayChunk *chunk = &relay->chunk[i];
			unsigned int len = buf_getint(reply);
			/* Stream blobs use the bounded IO limit, not SSH text-string limits.
			 * PTYs can return a full chunk where ordinary pipes return less. */
			if (len > BROKER_IO_MAX || (len && chunk->len)) dropbear_exit("Session broker output capacity exceeded");
			if (len) {
				memcpy(chunk->data, buf_getptr(reply, len), len);
				chunk->len = len;
			}
			buf_incrpos(reply, len);
			relay->eof[i] = buf_getbool(reply);
		}
		if (buf_getbool(reply)) {
			relay->exit.exitpid = 1; /* existence marker; never used as a signal target */
			relay->exit.exitstatus = buf_getint(reply);
			relay->exit.exitsignal = (int)buf_getint(reply);
			relay->exit.exitcore = buf_getbool(reply);
		}
		if (reply->pos != reply->len) dropbear_exit("Session broker IO reply has trailing bytes");
		buf_burn_free(reply);
		for (i = 1; i < 3; i++) {
			struct RelayChunk *chunk = &relay->chunk[i];
			if (relay->fd[i] >= 0 && chunk->len) {
				ssize_t n = write(relay->fd[i], chunk->data + chunk->pos, chunk->len - chunk->pos);
				if (n > 0) chunk->pos += n;
				else if (n < 0 && errno != EINTR && errno != EAGAIN) close_stream(&relay->fd[i]);
			}
			if (chunk->pos == chunk->len || relay->fd[i] < 0) chunk->pos = chunk->len = 0;
			if (relay->eof[i] && chunk->len == 0) close_stream(&relay->fd[i]);
		}
		if (relay->exit.exitpid != -1 && relay->fd[1] < 0 && relay->fd[2] < 0) {
			/* All output has entered the adapter pipes before common-channel
			 * enables flushing. Its existing window rules drain those pipes. */
			session->exit = relay->exit;
			ses.channel_signal_pending = 1;
		}
	}
}

void svr_kex_broker_release_session(struct ChanSess *session) {
	unsigned int id = session->broker_session_id;
	buffer *request, *response;
	release_relay(session);
	session->broker_session_id = 0;
	if (!id || request_fd < 0 || response_fd < 0) return;
	request = buf_new(5);
	buf_putbyte(request, BROKER_RELEASE_SESSION);
	buf_putint(request, id);
	write_frame(request_fd, request);
	buf_free(request);
	response = read_frame(response_fd, 0);
	if (buf_getbyte(response) != 1 || response->pos != response->len) {
		dropbear_exit("Session broker release reply invalid");
	}
	buf_free(response);
}

void svr_kex_broker_cleanup(void) {
	if (request_fd >= 0) {
		close(request_fd);
		request_fd = -1;
	}
	if (response_fd >= 0) {
		close(response_fd);
		response_fd = -1;
	}
	/* EOF lets the broker finish bounded crypto and release its private state.
	 * The worker must not wait indefinitely during connection teardown. */
	if (broker_pid > 0) {
		waitpid(broker_pid, NULL, WNOHANG);
		broker_pid = -1;
	}
}

void svr_kex_broker_checkchild(pid_t pid) {
	if (pid == broker_pid) {
		broker_pid = -1;
		dropbear_exit("KEX broker exited");
	}
}
#endif

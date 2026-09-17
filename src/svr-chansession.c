/*
 * Dropbear - a SSH2 server
 *
 * Copyright (c) 2002,2003 Matt Johnston
 * All rights reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE. */

#include "agentfwd.h"
#include "auth.h"
#include "buffer.h"
#include "channel.h"
#include "chansession.h"
#include "dbrandom.h"
#include "dbutil.h"
#include "includes.h"
#include "packet.h"
#include "runopts.h"
#include "session.h"
#include "ssh.h"
#include "sshpty.h"
#include "svr-kex-broker.h"
#include "termcodes.h"
#include "x11fwd.h"

enum {
    WOS_SYSCALL_PROCESS = 3,
    WOS_PROC_SETWKITARGET = 28,
};

static const uint32_t wos_wki_target_flag_local = 1U << 1;
static const uint32_t wos_wki_target_flag_noinherit = 1U << 2;

static unsigned long wos_syscall5(unsigned long callnum, unsigned long a1, unsigned long a2, unsigned long a3, unsigned long a4,
                                  unsigned long a5) {
    register unsigned long r8_reg __asm__("r8") = a4;
    register unsigned long r9_reg __asm__("r9") = a5;
    unsigned long result;
    __asm__ __volatile__("syscall"
                         : "=a"(result)
                         : "a"(callnum), "D"(a1), "S"(a2), "d"(a3), "r"(r8_reg), "r"(r9_reg)
                         : "rcx", "r11", "memory");
    return result;
}

static void pin_session_local(void) {
	const uint32_t flags = wos_wki_target_flag_local | wos_wki_target_flag_noinherit;
	unsigned long result = wos_syscall5(WOS_SYSCALL_PROCESS, WOS_PROC_SETWKITARGET, 0, 0, flags, 0);
	if ((long)result < 0) {
		dropbear_log(LOG_WARNING, "WOS setwkitarget(local,noinherit) failed: %ld", (long)result);
	}
}

/* Handles sessions (either shells or programs) requested by the client */

static int sessioncommand(struct Channel* channel, struct ChanSess* chansess, int iscmd, int issubsys);
#if !DROPBEAR_SVR_KEX_BROKER
static int sessionpty(struct ChanSess* chansess);
#endif
static int sessionsignal(const struct ChanSess* chansess);
static int noptycommand(struct Channel* channel, struct ChanSess* chansess);
static int ptycommand(struct Channel* channel, struct ChanSess* chansess);
#if !DROPBEAR_SVR_KEX_BROKER
static int sessionwinchange(const struct ChanSess* chansess);
#endif
static void addchildpid(struct ChanSess* chansess, pid_t pid);
static void sesssigchild_handler(int val);
static void closechansess(const struct Channel* channel);
static void cleanupchansess(const struct Channel* channel);
static int newchansess(struct Channel* channel);
static void chansessionrequest(struct Channel* channel);
static int sesscheckclose(struct Channel* channel);

static void send_exitsignalstatus(const struct Channel* channel);
static void send_msg_chansess_exitstatus(const struct Channel* channel, const struct ChanSess* chansess);
static void send_msg_chansess_exitsignal(const struct Channel* channel, const struct ChanSess* chansess);
static int get_termmodes(const struct ChanSess* chansess, buffer* request);

const struct ChanType svrchansess = {
    "session",          /* name */
    newchansess,        /* inithandler */
    sesscheckclose,     /* checkclosehandler */
    chansessionrequest, /* reqhandler */
    closechansess,      /* closehandler */
    cleanupchansess     /* cleanup */
};

/* Returns whether the channel is ready to close. The child process
   must not be running (has never started, or has exited) */
static int sesscheckclose(struct Channel* channel) {
    struct ChanSess* chansess = (struct ChanSess*)channel->typedata;
    TRACE(("sesscheckclose, pid %d, exitpid %d", chansess->pid, chansess->exit.exitpid))

    if (chansess->exit.exitpid != -1) {
        channel->flushing = 1;
    }
    return chansess->pid == 0 || chansess->exit.exitpid != -1;
}

/* Handler for childs exiting, store the state for return to the client */

/* There's a particular race we have to watch out for: if the forked child
 * executes, exits, and this signal-handler is called, all before the parent
 * gets to run, then the childpids[] array won't have the pid in it. Hence we
 * use the svr_ses.lastexit struct to hold the exit, which is then compared by
 * the parent when it runs. This work correctly at least in the case of a
 * single shell spawned (ie the usual case) */
void svr_chansess_checksignal(void) {
    int status;
    pid_t pid;

    if (!ses.channel_signal_pending) {
        return;
    }

    while ((pid = waitpid(-1, &status, WNOHANG)) > 0) {
        svr_kex_broker_checkchild(pid);
        unsigned int i;
        struct exitinfo* ex = NULL;
        TRACE(("svr_chansess_checksignal : pid %d", pid))

        ex = NULL;
        /* find the corresponding chansess */
        for (i = 0; i < svr_ses.childpidsize; i++) {
            if (svr_ses.childpids[i].pid == pid) {
                TRACE(("found match session"));
                ex = &svr_ses.childpids[i].chansess->exit;
                break;
            }
        }

        /* If the pid wasn't matched, then we might have hit the race mentioned
         * above. So we just store the info for the parent to deal with */
        if (ex == NULL) {
            TRACE(("using lastexit"));
            ex = &svr_ses.lastexit;
        }

#ifdef __WOS__
        dropbear_log(LOG_WARNING, "wos child-exit pid=%d status=0x%x matched=%d", pid, status, ex != &svr_ses.lastexit);
#endif

        ex->exitpid = pid;
        if (WIFEXITED(status)) {
            ex->exitstatus = WEXITSTATUS(status);
        }
        if (WIFSIGNALED(status)) {
            ex->exitsignal = WTERMSIG(status);
#if !defined(AIX) && defined(WCOREDUMP)
            ex->exitcore = WCOREDUMP(status);
#else
            ex->exitcore = 0;
#endif
        } else {
            /* we use this to determine how pid exited */
            ex->exitsignal = -1;
        }
    }
}

static void sesssigchild_handler(int UNUSED(dummy)) {
    struct sigaction sa_chld;

    const int saved_errno = errno;

    /* Make sure that the main select() loop wakes up */
    while (1) {
        /* isserver is just a random byte to write. We can't do anything
        about an error so should just ignore it */
        if (write(ses.signal_pipe[1], &ses.isserver, 1) == 1 || errno != EINTR) {
            break;
        }
    }

    sa_chld.sa_handler = sesssigchild_handler;
    sa_chld.sa_flags = SA_NOCLDSTOP;
    sigemptyset(&sa_chld.sa_mask);
    sigaction(SIGCHLD, &sa_chld, NULL);

    errno = saved_errno;
}

/* send the exit status or the signal causing termination for a session */
static void send_exitsignalstatus(const struct Channel* channel) {
    struct ChanSess* chansess = (struct ChanSess*)channel->typedata;

    if (chansess->exit.exitpid >= 0) {
        if (chansess->exit.exitsignal > 0) {
            send_msg_chansess_exitsignal(channel, chansess);
        } else {
            send_msg_chansess_exitstatus(channel, chansess);
        }
    }
}

/* send the exitstatus to the client */
static void send_msg_chansess_exitstatus(const struct Channel* channel, const struct ChanSess* chansess) {
    dropbear_assert(chansess->exit.exitpid != -1);
    dropbear_assert(chansess->exit.exitsignal == -1);

    CHECKCLEARTOWRITE();

    buf_putbyte(ses.writepayload, SSH_MSG_CHANNEL_REQUEST);
    buf_putint(ses.writepayload, channel->remotechan);
    buf_putstring(ses.writepayload, "exit-status", 11);
    buf_putbyte(ses.writepayload, 0); /* boolean FALSE */
    buf_putint(ses.writepayload, chansess->exit.exitstatus);

    encrypt_packet();
}

/* send the signal causing the exit to the client */
static void send_msg_chansess_exitsignal(const struct Channel* channel, const struct ChanSess* chansess) {
    int i;
    char* signame = NULL;
    dropbear_assert(chansess->exit.exitpid != -1);
    dropbear_assert(chansess->exit.exitsignal > 0);

    TRACE(("send_msg_chansess_exitsignal %d", chansess->exit.exitsignal))

    CHECKCLEARTOWRITE();

    /* we check that we can match a signal name, otherwise
     * don't send anything */
    for (i = 0; signames[i].name != NULL; i++) {
        if (signames[i].signal == chansess->exit.exitsignal) {
            signame = signames[i].name;
            break;
        }
    }

    if (signame == NULL) {
        return;
    }

    buf_putbyte(ses.writepayload, SSH_MSG_CHANNEL_REQUEST);
    buf_putint(ses.writepayload, channel->remotechan);
    buf_putstring(ses.writepayload, "exit-signal", 11);
    buf_putbyte(ses.writepayload, 0); /* boolean FALSE */
    buf_putstring(ses.writepayload, signame, strlen(signame));
    buf_putbyte(ses.writepayload, chansess->exit.exitcore);
    buf_putstring(ses.writepayload, "", 0); /* error msg */
    buf_putstring(ses.writepayload, "", 0); /* lang */

    encrypt_packet();
}

/* set up a session channel */
static int newchansess(struct Channel* channel) {
    struct ChanSess* chansess;

    TRACE(("new chansess %p", (void*)channel))

    dropbear_assert(channel->typedata == NULL);

    chansess = (struct ChanSess*)m_malloc(sizeof(struct ChanSess));
    chansess->cmd = NULL;
    chansess->cmd_is_sftp_subsystem = 0;
    chansess->original_command = NULL;
    chansess->connection_string = NULL;
    chansess->client_string = NULL;
    chansess->pid = 0;

    /* pty details */
    chansess->master = -1;
    chansess->slave = -1;
    chansess->tty = NULL;
    chansess->term = NULL;

    chansess->exit.exitpid = -1;

    channel->typedata = chansess;

#if DROPBEAR_X11FWD
    chansess->x11listener = NULL;
    chansess->x11authprot = NULL;
    chansess->x11authcookie = NULL;
#endif

#if DROPBEAR_SVR_AGENTFWD
    chansess->agentlistener = NULL;
    chansess->agentfile = NULL;
    chansess->agentdir = NULL;
#endif

    /* Will drop to DROPBEAR_PRIO_NORMAL if a non-tty command starts */
    channel->prio = DROPBEAR_PRIO_LOWDELAY;

    return 0;
}

static struct logininfo* chansess_login_alloc(const struct ChanSess* chansess) {
    struct logininfo* li;
#if DROPBEAR_SVR_KEX_BROKER
    /* Accounting uses the authenticated identity, never a later passwd lookup. */
    li = login_alloc_entry(chansess->pid, NULL, svr_ses.remotehost, chansess->tty);
    strlcpy(li->username, ses.authstate.username, sizeof(li->username));
    li->uid = ses.authstate.pw_uid;
#else
    li = login_alloc_entry(chansess->pid, ses.authstate.username, svr_ses.remotehost, chansess->tty);
#endif
    return li;
}

void svr_session_pty_logout(const struct ChanSess* chansess) {
    struct logininfo* li;
    if (!chansess->tty || chansess->pid <= 0) return;
    li = chansess_login_alloc(chansess);
    svr_raise_gid_utmp();
    login_logout(li);
    svr_restore_gid();
    login_free_entry(li);
}

/* send exit status message before the channel is closed */
static void closechansess(const struct Channel* channel) {
    struct ChanSess* chansess;

    TRACE(("enter closechansess"))

    chansess = (struct ChanSess*)channel->typedata;

    if (chansess == NULL) {
        TRACE(("leave closechansess: chansess == NULL"))
        return;
    }

    send_exitsignalstatus(channel);
    TRACE(("leave closechansess"))
}

/* clean a session channel */
static void cleanupchansess(const struct Channel* channel) {
    struct ChanSess* chansess;
    unsigned int i;
    TRACE(("enter closechansess"))

    chansess = (struct ChanSess*)channel->typedata;

    if (chansess == NULL) {
        TRACE(("leave closechansess: chansess == NULL"))
        return;
    }

    svr_kex_broker_release_session(chansess);
    m_free(chansess->cmd);
    m_free(chansess->term);
    m_free(chansess->original_command);

    if (chansess->tty) {
#if !DROPBEAR_SVR_KEX_BROKER
        svr_session_pty_logout(chansess);
        pty_release(chansess->tty);
#endif
        m_free(chansess->tty);
    }

#if DROPBEAR_X11FWD
    x11cleanup(chansess);
#endif

#if DROPBEAR_SVR_AGENTFWD
    svr_agentcleanup(chansess);
#endif

    /* clear child pid entries */
    for (i = 0; i < svr_ses.childpidsize; i++) {
        if (svr_ses.childpids[i].chansess == chansess) {
            dropbear_assert(svr_ses.childpids[i].pid > 0);
            TRACE(("closing pid %d", svr_ses.childpids[i].pid))
            TRACE(("exitpid is %d", chansess->exit.exitpid))
            svr_ses.childpids[i].pid = -1;
            svr_ses.childpids[i].chansess = NULL;
        }
    }

    m_free(chansess);

    TRACE(("leave closechansess"))
}

/* Handle requests for a channel. These can be execution requests,
 * or x11/authagent forwarding. These are passed to appropriate handlers */
static void chansessionrequest(struct Channel* channel) {
    char* type = NULL;
    unsigned int typelen;
    unsigned char wantreply;
    int ret = 1;
    struct ChanSess* chansess;

    TRACE(("enter chansessionrequest"))

    type = buf_getstring(ses.payload, &typelen);
    wantreply = buf_getbool(ses.payload);

    if (typelen > MAX_NAME_LEN) {
        TRACE(("leave chansessionrequest: type too long")) /* XXX send error?*/
        goto out;
    }

    chansess = (struct ChanSess*)channel->typedata;
    dropbear_assert(chansess != NULL);
    TRACE(("type is %s", type))

    if (strcmp(type, "window-change") == 0) {
#if DROPBEAR_SVR_KEX_BROKER
        ret = svr_kex_broker_window_change(channel, chansess);
#else
        ret = sessionwinchange(chansess);
#endif
    } else if (strcmp(type, "shell") == 0) {
        ret = sessioncommand(channel, chansess, 0, 0);
    } else if (strcmp(type, "pty-req") == 0) {
#if DROPBEAR_SVR_KEX_BROKER
        ret = svr_kex_broker_pty(channel, chansess);
#else
        ret = sessionpty(chansess);
#endif
    } else if (strcmp(type, "exec") == 0) {
        ret = sessioncommand(channel, chansess, 1, 0);
    } else if (strcmp(type, "subsystem") == 0) {
        ret = sessioncommand(channel, chansess, 1, 1);
#if DROPBEAR_X11FWD
    } else if (strcmp(type, "x11-req") == 0) {
        ret = x11req(chansess);
#endif
#if DROPBEAR_SVR_AGENTFWD
    } else if (strcmp(type, "auth-agent-req@openssh.com") == 0) {
        ret = svr_agentreq(chansess);
#endif
    } else if (strcmp(type, "signal") == 0) {
        ret = sessionsignal(chansess);
    } else {
        /* etc, todo "env", "subsystem" */
    }

out:

    if (wantreply) {
        if (ret == DROPBEAR_SUCCESS) {
            send_msg_channel_success(channel);
        } else {
            send_msg_channel_failure(channel);
        }
    }

    m_free(type);
    TRACE(("leave chansessionrequest"))
}

/* Send a signal to a session's process as requested by the client*/
static int sessionsignal(const struct ChanSess* chansess) {
    TRACE(("sessionsignal"))
#if DROPBEAR_SVR_KEX_BROKER
    if (chansess->broker_relay) {
        return svr_kex_broker_signal(chansess);
    }
#endif

    int sig = 0;
    char* signame = NULL;
    int i;

    if (chansess->pid == 0) {
        TRACE(("sessionsignal: done no pid"))
        /* haven't got a process pid yet */
        return DROPBEAR_FAILURE;
    }

    if (svr_opts.forced_command || svr_pubkey_has_forced_command()) {
        TRACE(("disallowed signal for forced_command"));
        return DROPBEAR_FAILURE;
    }

    if (DROPBEAR_SVR_MULTIUSER && !DROPBEAR_SVR_DROP_PRIVS) {
        TRACE(("disallow signal without drop privs"));
        return DROPBEAR_FAILURE;
    }

    signame = buf_getstring(ses.payload, NULL);

    for (i = 0; signames[i].name != NULL; i++) {
        if (strcmp(signames[i].name, signame) == 0) {
            sig = signames[i].signal;
            break;
        }
    }

    m_free(signame);

    TRACE(("sessionsignal: pid %d signal %d", (int)chansess->pid, sig))
    if (sig == 0) {
        /* failed */
        return DROPBEAR_FAILURE;
    }

    if (kill(chansess->pid, sig) < 0) {
        TRACE(("sessionsignal: kill() errored"))
        return DROPBEAR_FAILURE;
    }

    return DROPBEAR_SUCCESS;
}

/* Let the process know that the window size has changed, as notified from the
 * client. Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
#if !DROPBEAR_SVR_KEX_BROKER
static int sessionwinchange(const struct ChanSess* chansess) {
    int termc, termr, termw, termh;

    if (chansess->master < 0) {
        /* haven't got a pty yet */
        return DROPBEAR_FAILURE;
    }

    termc = buf_getint(ses.payload);
    termr = buf_getint(ses.payload);
    termw = buf_getint(ses.payload);
    termh = buf_getint(ses.payload);

    pty_change_window_size(chansess->master, termr, termc, termw, termh);

    return DROPBEAR_SUCCESS;
}

#endif

static int get_termmodes(const struct ChanSess* chansess, buffer* request) {
    struct termios termio;
    unsigned char opcode;
    unsigned int value;
    const struct TermCode* termcode;
    unsigned int len;

    TRACE(("enter get_termmodes"))

    /* Term modes */
    /* We'll ignore errors and continue if we can't set modes.
     * We're ignoring baud rates since they seem evil */
    if (tcgetattr(chansess->master, &termio) == -1) {
        return DROPBEAR_FAILURE;
    }

    len = buf_getint(request);
    TRACE(("term mode str %d p->l %d p->p %d", len, request->len, request->pos));
    if (len != request->len - request->pos) {
        dropbear_exit("Bad term mode string");
    }

    if (len == 0) {
        TRACE(("leave get_termmodes: empty terminal modes string"))
        return DROPBEAR_SUCCESS;
    }

    while (((opcode = buf_getbyte(request)) != 0x00) && opcode <= 159) {
        /* must be before checking type, so that value is consumed even if
         * we don't use it */
        value = buf_getint(request);

        /* handle types of code */
        if (opcode > MAX_TERMCODE) {
            continue;
        }
        termcode = &termcodes[(unsigned int)opcode];

        switch (termcode->type) {
            case TERMCODE_NONE:
                break;

            case TERMCODE_CONTROLCHAR:
                termio.c_cc[termcode->mapcode] = value;
                break;

            case TERMCODE_INPUT:
                if (value) {
                    termio.c_iflag |= termcode->mapcode;
                } else {
                    termio.c_iflag &= ~(termcode->mapcode);
                }
                break;

            case TERMCODE_OUTPUT:
                if (value) {
                    termio.c_oflag |= termcode->mapcode;
                } else {
                    termio.c_oflag &= ~(termcode->mapcode);
                }
                break;

            case TERMCODE_LOCAL:
                if (value) {
                    termio.c_lflag |= termcode->mapcode;
                } else {
                    termio.c_lflag &= ~(termcode->mapcode);
                }
                break;

            case TERMCODE_CONTROL:
                if (value) {
                    termio.c_cflag |= termcode->mapcode;
                } else {
                    termio.c_cflag &= ~(termcode->mapcode);
                }
                break;
        }
    }
    if (tcsetattr(chansess->master, TCSANOW, &termio) < 0) {
        dropbear_log(LOG_INFO, "Error setting terminal attributes");
        return DROPBEAR_FAILURE;
    }
    TRACE(("leave get_termmodes"))
    return DROPBEAR_SUCCESS;
}

#if DROPBEAR_SVR_KEX_BROKER
static void read_window(buffer* request, struct winsize* window) {
    memset(window, 0, sizeof(*window));
    window->ws_col = buf_getint(request);
    window->ws_row = buf_getint(request);
    window->ws_xpixel = buf_getint(request);
    window->ws_ypixel = buf_getint(request);
}

int svr_session_window_change(const struct ChanSess* chansess, buffer* request) {
    struct winsize window;
    if (chansess->master < 0 || request->len - request->pos != 16) return DROPBEAR_FAILURE;
    read_window(request, &window);
    return ioctl(chansess->master, TIOCSWINSZ, &window) == 0 ? DROPBEAR_SUCCESS : DROPBEAR_FAILURE;
}

/* Validate the entire body before allocating a terminal or changing ownership.
 * The caller publishes this empty candidate only after all setup succeeds. */
int svr_prepare_session_pty(struct ChanSess* candidate, buffer* request) {
    unsigned int termlen, modes_pos, length;
    struct winsize window;
    char name[65], *term;
    if (!svr_kex_broker_is_monitor() || !svr_pubkey_allows_pty()) return DROPBEAR_FAILURE;
    if (request->len - request->pos < 4) return DROPBEAR_FAILURE;
    termlen = buf_getint(request);
    if (termlen > MAX_TERM_LEN || termlen > request->len - request->pos) return DROPBEAR_FAILURE;
    if (memchr(buf_getptr(request, termlen), 0, termlen)) return DROPBEAR_FAILURE;
    term = m_malloc(termlen + 1);
    memcpy(term, buf_getptr(request, termlen), termlen);
    term[termlen] = '\0';
    buf_incrpos(request, termlen);
    if (request->len - request->pos < 20) goto invalid;
    read_window(request, &window);
    modes_pos = request->pos;
    length = buf_getint(request);
    if (length != request->len - request->pos) goto invalid;
    if (length) {
        for (;;) {
            unsigned char opcode;
            if (request->pos == request->len) goto invalid;
            opcode = buf_getbyte(request);
            /* SSH stops at END or an opcode reserved for future encodings. */
            if (opcode == 0 || opcode >= 160) break;
            if (request->len - request->pos < 4) goto invalid;
            buf_incrpos(request, 4);
        }
    }
    if (!pty_allocate(&candidate->master, &candidate->slave, name, sizeof(name))) goto invalid;
    if (candidate->master >= FD_SETSIZE || candidate->slave >= FD_SETSIZE
            || fcntl(candidate->master, F_SETFD, FD_CLOEXEC) < 0
            || fcntl(candidate->slave, F_SETFD, FD_CLOEXEC) < 0) goto allocated_failure;
    ses.maxfd = MAX(ses.maxfd, MAX(candidate->master, candidate->slave));
    if (fchown(candidate->slave, ses.authstate.pw_uid, ses.authstate.pw_gid) < 0
            || fchmod(candidate->slave, 0600) < 0
            || ioctl(candidate->master, TIOCSWINSZ, &window) < 0) goto allocated_failure;
    buf_setpos(request, modes_pos);
    if (get_termmodes(candidate, request) != DROPBEAR_SUCCESS) goto allocated_failure;
    candidate->term = term;
    candidate->tty = m_strdup(name);
    return DROPBEAR_SUCCESS;

allocated_failure:
    close(candidate->slave);
    close(candidate->master);
    candidate->slave = candidate->master = -1;
invalid:
    m_free(term);
    return DROPBEAR_FAILURE;
}
#endif

/* Set up a session pty which will be used to execute the shell or program.
 * The pty is allocated now, and kept for when the shell/program executes.
 * Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
#if !DROPBEAR_SVR_KEX_BROKER
static int sessionpty(struct ChanSess* chansess) {
    unsigned int termlen;
    char namebuf[65];
    struct passwd* pw = NULL;

    TRACE(("enter sessionpty"))

    if (!svr_pubkey_allows_pty()) {
        TRACE(("leave sessionpty : pty forbidden by public key option"))
        return DROPBEAR_FAILURE;
    }

    chansess->term = buf_getstring(ses.payload, &termlen);
    if (termlen > MAX_TERM_LEN) {
        /* TODO send disconnect ? */
        TRACE(("leave sessionpty: term len too long"))
        return DROPBEAR_FAILURE;
    }

    /* allocate the pty */
    if (chansess->master != -1) {
        dropbear_exit("Multiple pty requests");
    }
    if (pty_allocate(&chansess->master, &chansess->slave, namebuf, 64) == 0) {
        TRACE(("leave sessionpty: failed to allocate pty"))
        return DROPBEAR_FAILURE;
    }

    chansess->tty = m_strdup(namebuf);
    if (!chansess->tty) {
        dropbear_exit("Out of memory"); /* TODO disconnect */
    }

#if DROPBEAR_SVR_KEX_BROKER
    struct passwd retained = {0};
    retained.pw_uid = ses.authstate.pw_uid;
    retained.pw_gid = ses.authstate.pw_gid;
    pw = &retained;
#else
    pw = getpwnam(ses.authstate.pw_name);
    if (!pw) dropbear_exit("getpwnam failed after succeeding previously");
#endif
    pty_setowner(pw, chansess->tty);

    /* Set up the rows/col counts */
    sessionwinchange(chansess);

    /* Read the terminal modes */
    (void)get_termmodes(chansess, ses.payload);

    TRACE(("leave sessionpty"))
    return DROPBEAR_SUCCESS;
}

#endif

#if !DROPBEAR_VFORK
void svr_make_connection_string(struct ChanSess* chansess) {
    char *local_ip, *local_port, *remote_ip, *remote_port;
    size_t len;
    get_socket_address(ses.sock_in, &local_ip, &local_port, &remote_ip, &remote_port, 0);

    /* "remoteip remoteport localip localport" */
    len = strlen(local_ip) + strlen(remote_ip) + 20;
    chansess->connection_string = m_malloc(len);
    snprintf(chansess->connection_string, len, "%s %s %s %s", remote_ip, remote_port, local_ip, local_port);

    /* deprecated but bash only loads .bashrc if SSH_CLIENT is set */
    /* "remoteip remoteport localport" */
    len = strlen(remote_ip) + 20;
    chansess->client_string = m_malloc(len);
    snprintf(chansess->client_string, len, "%s %s %s", remote_ip, remote_port, local_port);

    m_free(local_ip);
    m_free(local_port);
    m_free(remote_ip);
    m_free(remote_port);
}
#endif

/* Handle a command request from the client. This is used for both shell
 * and command-execution requests, and passes the command to
 * noptycommand or ptycommand as appropriate.
 * Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
int svr_prepare_session_command(struct ChanSess* chansess, buffer* request, int iscmd, int issubsys) {
    unsigned int cmdlen = 0;
    dropbear_assert(chansess->cmd == NULL && chansess->original_command == NULL);

    if (iscmd) {
        /* "exec" */
        if (chansess->cmd == NULL) {
            chansess->cmd = buf_getstring(request, &cmdlen);

            if (cmdlen > MAX_CMD_LEN || strlen(chansess->cmd) != cmdlen) {
                m_free(chansess->cmd);
                /* TODO - send error - too long ? */
                TRACE(("leave sessioncommand, command too long %d", cmdlen))
                return DROPBEAR_FAILURE;
            }
        }
        if (issubsys) {
#if DROPBEAR_SFTPSERVER
            if ((cmdlen == 4) && strncmp(chansess->cmd, "sftp", 4) == 0) {
                char* expand_path = expand_homedir_path(SFTPSERVER_PATH);
                m_free(chansess->cmd);
                chansess->cmd = m_strdup(expand_path);
                chansess->cmd_is_sftp_subsystem = 1;
                m_free(expand_path);
            } else
#endif
            {
                m_free(chansess->cmd);
                TRACE(("leave sessioncommand, unknown subsystem"))
                return DROPBEAR_FAILURE;
            }
        }
    }

    if (request->pos != request->len) {
        m_free(chansess->cmd);
        return DROPBEAR_FAILURE;
    }

    /* take global command into account */
    if (svr_opts.forced_command) {
        if (chansess->cmd) {
            chansess->original_command = chansess->cmd;
        } else {
            chansess->original_command = m_strdup("");
        }
        chansess->cmd_is_sftp_subsystem = 0;
        chansess->cmd = m_strdup(svr_opts.forced_command);
    } else {
        /* take public key option 'command' into account */
        char* cmd_before_pubkey_options = chansess->cmd;
        svr_pubkey_set_forced_command(chansess);
        if (chansess->cmd != cmd_before_pubkey_options) {
            chansess->cmd_is_sftp_subsystem = 0;
        }
    }

    return DROPBEAR_SUCCESS;
}

static int sessioncommand(struct Channel* channel, struct ChanSess* chansess, int iscmd, int issubsys) {
    int ret;
    if (chansess->pid != 0) {
        return DROPBEAR_FAILURE;
    }
#if DROPBEAR_SVR_KEX_BROKER
    (void)iscmd;
    (void)issubsys;
    ret = svr_kex_broker_prepare_command(channel, chansess);
#else
    m_free(chansess->original_command);
    chansess->cmd_is_sftp_subsystem = 0;
    ret = svr_prepare_session_command(chansess, ses.payload, iscmd, issubsys);
#endif
    if (ret != DROPBEAR_SUCCESS) {
        return ret;
    }

#if LOG_COMMANDS
    if (chansess->cmd) {
        dropbear_log(LOG_INFO, "User %s executing '%s'", ses.authstate.pw_name, chansess->cmd);
    } else {
        dropbear_log(LOG_INFO, "User %s executing login shell", ses.authstate.pw_name);
    }
#endif

    /* uClinux will vfork(), so there'll be a race as
    connection_string is freed below. */
#if !DROPBEAR_VFORK
    svr_make_connection_string(chansess);
#endif

    if (chansess->term == NULL) {
        /* no pty */
        ret = noptycommand(channel, chansess);
        if (ret == DROPBEAR_SUCCESS) {
            channel->prio = DROPBEAR_PRIO_NORMAL;
            update_channel_prio();
        }
    } else {
        /* want pty */
        ret = ptycommand(channel, chansess);
    }

#if !DROPBEAR_VFORK
    m_free(chansess->connection_string);
    m_free(chansess->client_string);
#endif

    if (ret == DROPBEAR_FAILURE) {
        m_free(chansess->cmd);
    }
    TRACE(("leave sessioncommand, ret %d", ret))
    return ret;
}

/* Execute a command and set up redirection of stdin/stdout/stderr without a
 * pty.
 * Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
static int noptycommand(struct Channel* channel, struct ChanSess* chansess) {
    int ret;

    TRACE(("enter noptycommand"))
#if DROPBEAR_SVR_KEX_BROKER
    return svr_kex_broker_spawn(channel, chansess);
#endif
    ret = spawn_command(svr_exec_session_child, chansess, &channel->writefd, &channel->readfd, &channel->errfd, &chansess->pid);

    if (ret == DROPBEAR_FAILURE) {
        return ret;
    }

    ses.maxfd = MAX(ses.maxfd, channel->writefd);
    ses.maxfd = MAX(ses.maxfd, channel->readfd);
    ses.maxfd = MAX(ses.maxfd, channel->errfd);
    channel->bidir_fd = 0;

    addchildpid(chansess, chansess->pid);

    if (svr_ses.lastexit.exitpid != -1) {
        unsigned int i;
        TRACE(("parent side: lastexitpid is %d", svr_ses.lastexit.exitpid))
        /* The child probably exited and the signal handler triggered
         * possibly before we got around to adding the childpid. So we fill
         * out its data manually */
        for (i = 0; i < svr_ses.childpidsize; i++) {
            if (svr_ses.childpids[i].pid == svr_ses.lastexit.exitpid) {
                TRACE(("found match for lastexitpid"))
                svr_ses.childpids[i].chansess->exit = svr_ses.lastexit;
                svr_ses.lastexit.exitpid = -1;
                break;
            }
        }
    }

    TRACE(("leave noptycommand"))
    return DROPBEAR_SUCCESS;
}

/* Execute a command or shell within a pty environment, and set up
 * redirection as appropriate.
 * Returns DROPBEAR_SUCCESS or DROPBEAR_FAILURE */
void svr_exec_pty_child(struct ChanSess* chansess) {
    struct logininfo* li = NULL;
#if DO_MOTD
    buffer* motdbuf = NULL;
    int len;
    struct stat sb;
    char* hushpath = NULL;
#endif
    /* child */

    TRACE(("back to normal sigchld"))
    /* Revert to normal sigchld handling */
    if (signal(SIGCHLD, SIG_DFL) == SIG_ERR) {
        dropbear_exit("signal() error");
    }

    /* redirect stdin/stdout/stderr */
    if (chansess->master >= 0) close(chansess->master);
    chansess->master = -1;
    chansess->pid = getpid();

    pty_make_controlling_tty(&chansess->slave, chansess->tty);

    if ((dup2(chansess->slave, STDIN_FILENO) < 0) || (dup2(chansess->slave, STDOUT_FILENO) < 0)) {
        TRACE(("leave ptycommand: error redirecting filedesc"))
        _exit(127);
    }

    /* write the utmp/wtmp login record - must be after changing the
     * terminal used for stdout with the dup2 above, otherwise
     * the wtmp login will not be recorded */
    li = chansess_login_alloc(chansess);

    svr_raise_gid_utmp();
    login_login(li);
    svr_restore_gid();

    login_free_entry(li);

    /* Can now dup2 stderr. Messages from login_login() have gone
    to the parent stderr */
    if (dup2(chansess->slave, STDERR_FILENO) < 0) {
        TRACE(("leave ptycommand: error redirecting filedesc"))
        _exit(127);
    }

    if (chansess->slave > STDERR_FILENO) close(chansess->slave);
    chansess->slave = -1;

#if DO_MOTD
    if (svr_opts.domotd && !chansess->cmd) {
        /* don't show the motd if ~/.hushlogin exists */

        /* 12 == strlen("/.hushlogin\0") */
        len = strlen(ses.authstate.pw_dir) + 12;

        hushpath = m_malloc(len);
        snprintf(hushpath, len, "%s/.hushlogin", ses.authstate.pw_dir);

        if (stat(hushpath, &sb) < 0) {
            char* expand_path = NULL;
            /* more than a screenful is stupid IMHO */
            motdbuf = buf_new(MOTD_MAXSIZE);
            expand_path = expand_homedir_path(MOTD_FILENAME);
            if (buf_readfile(motdbuf, expand_path) == DROPBEAR_SUCCESS) {
                /* incase it is full size, add LF at last position */
                if (motdbuf->len == motdbuf->size) motdbuf->data[motdbuf->len - 1] = 10;
                buf_setpos(motdbuf, 0);
                while (motdbuf->pos != motdbuf->len) {
                    len = motdbuf->len - motdbuf->pos;
                    len = write(STDOUT_FILENO, buf_getptr(motdbuf, len), len);
                    if (len < 0 && errno == EINTR) continue;
                    if (len <= 0) break;
                    buf_incrpos(motdbuf, len);
                }
            }
            m_free(expand_path);
            buf_free(motdbuf);
        }
        m_free(hushpath);
    }
#endif /* DO_MOTD */

    svr_exec_session_child(chansess);
    /* not reached */

}

static int ptycommand(struct Channel* channel, struct ChanSess* chansess) {
#if DROPBEAR_SVR_KEX_BROKER
    return svr_kex_broker_spawn(channel, chansess);
#else
    pid_t pid;


    TRACE(("enter ptycommand"))

    /* we need to have a pty allocated */
    if (chansess->master == -1 || chansess->tty == NULL) {
        dropbear_log(LOG_WARNING, "No pty was allocated, couldn't execute");
        return DROPBEAR_FAILURE;
    }

#if DROPBEAR_VFORK
    pid = vfork();
#else
    pid = fork();
#endif
    if (pid < 0) return DROPBEAR_FAILURE;

    if (pid == 0) {
        svr_exec_pty_child(chansess);
        _exit(127);

    } else {
        /* parent */
        TRACE(("continue ptycommand: parent"))
        chansess->pid = pid;

        /* add a child pid */
        addchildpid(chansess, pid);

        close(chansess->slave);
        channel->writefd = chansess->master;
        channel->readfd = chansess->master;
        /* don't need to set stderr here */
        ses.maxfd = MAX(ses.maxfd, chansess->master);
        channel->bidir_fd = 0;

        setnonblocking(chansess->master);
    }

    TRACE(("leave ptycommand"))
    return DROPBEAR_SUCCESS;
#endif
}

/* Add the pid of a child to the list for exit-handling */
static void addchildpid(struct ChanSess* chansess, pid_t pid) {
    unsigned int i;
    for (i = 0; i < svr_ses.childpidsize; i++) {
        if (svr_ses.childpids[i].pid == -1) {
            break;
        }
    }

    /* need to increase size */
    if (i == svr_ses.childpidsize) {
        svr_ses.childpids = (struct ChildPid*)m_realloc(svr_ses.childpids, sizeof(struct ChildPid) * (svr_ses.childpidsize + 1));
        svr_ses.childpidsize++;
    }

    TRACE(("addchildpid %d pid %d for chansess %p", i, pid, chansess))
    svr_ses.childpids[i].pid = pid;
    svr_ses.childpids[i].chansess = chansess;
}

/* Clean up, drop to user privileges, set up the environment and execute
 * the command/shell. This function does not return. */
void svr_exec_session_child(const void* user_data) {
    const struct ChanSess* chansess = user_data;
    char* usershell = NULL;
    char* cp = NULL;
    char* envcp = getenv("LANG");
    if (envcp != NULL) {
        cp = m_strdup(envcp);
    }

    /* with uClinux we'll have vfork()ed, so don't want to overwrite the
     * hostkey. can't think of a workaround to clear it */
#if !DROPBEAR_VFORK
    /* wipe the hostkey */
    sign_key_free(svr_opts.hostkey);
    svr_opts.hostkey = NULL;

    /* overwrite the prng state */
    seedrandom();
#endif

    /* clear environment if -e was not set */
    /* if we're debugging using valgrind etc, we need to keep the LD_PRELOAD
     * etc. This is hazardous, so should only be used for debugging. */
    if (!svr_opts.pass_on_env) {
#ifndef DEBUG_VALGRIND
#ifdef HAVE_CLEARENV
        clearenv();
#else  /* don't HAVE_CLEARENV */
        /* Yay for posix. */
        if (environ) {
            environ[0] = NULL;
        }
#endif /* HAVE_CLEARENV */
#endif /* DEBUG_VALGRIND */
    }

#if !DROPBEAR_SVR_DROP_PRIVS
    svr_switch_user();
#else
    /* Broker children inherit the broker's authority, never the worker drop. */
    if (svr_kex_broker_is_monitor()) svr_switch_user();
#endif

    /* set env vars */
    addnewvar("USER", ses.authstate.pw_name);
    addnewvar("LOGNAME", ses.authstate.pw_name);
    addnewvar("HOME", ses.authstate.pw_dir);
    addnewvar("SHELL", get_user_shell());
    if (getuid() == 0) {
        addnewvar("PATH", DEFAULT_ROOT_PATH);
    } else {
        addnewvar("PATH", DEFAULT_PATH);
    }
    if (cp != NULL) {
        addnewvar("LANG", cp);
        m_free(cp);
    }
    if (chansess->term != NULL) {
        addnewvar("TERM", chansess->term);
    }

    if (chansess->tty) {
        addnewvar("SSH_TTY", chansess->tty);
    }

    if (chansess->connection_string) {
        addnewvar("SSH_CONNECTION", chansess->connection_string);
    }

    if (chansess->client_string) {
        addnewvar("SSH_CLIENT", chansess->client_string);
    }

    if (chansess->original_command) {
        addnewvar("SSH_ORIGINAL_COMMAND", chansess->original_command);
    }
#if DROPBEAR_SVR_PUBKEY_OPTIONS_BUILT
    if (ses.authstate.pubkey_info != NULL) {
        addnewvar("SSH_PUBKEYINFO", ses.authstate.pubkey_info);
    }
#endif

    /* change directory */
    if (chdir(ses.authstate.pw_dir) < 0) {
        int e = errno;
        if (chdir("/") < 0) {
            dropbear_exit("chdir(\"/\") failed");
        }
        fprintf(stderr, "Failed chdir '%s': %s\n", ses.authstate.pw_dir, strerror(e));
    }

#if DROPBEAR_X11FWD
    /* set up X11 forwarding if enabled */
    x11setauth(chansess);
#endif
#if DROPBEAR_SVR_AGENTFWD
    /* set up agent env variable */
#if DROPBEAR_SVR_KEX_BROKER
    if (svr_kex_broker_is_monitor()) {
        if (chansess->broker_agent_path) addnewvar("SSH_AUTH_SOCK", chansess->broker_agent_path);
    } else
#endif
    svr_agentset(chansess);
#endif

    pin_session_local();

    if (chansess->cmd_is_sftp_subsystem) {
        char* argv[2];
        argv[0] = chansess->cmd;
        argv[1] = NULL;
        run_command(chansess->cmd, argv, ses.maxfd);
    } else {
        usershell = m_strdup(get_user_shell());
        run_shell_command(chansess->cmd, ses.maxfd, usershell);
    }

    /* The child closed inherited logging FDs before broker-side setup. Keep
     * exec failures visible on its own stderr without exporting environment. */
    fprintf(stderr, "Session exec failed: %s\n", strerror(errno));
    dropbear_exit("Child failed");
}

/* Set up the general chansession environment, in particular child-exit
 * handling */
void svr_chansessinitialise() {
    struct sigaction sa_chld;

    /* single child process intially */
    svr_ses.childpids = (struct ChildPid*)m_malloc(sizeof(struct ChildPid));
    svr_ses.childpids[0].pid = -1; /* unused */
    svr_ses.childpids[0].chansess = NULL;
    svr_ses.childpidsize = 1;
    svr_ses.lastexit.exitpid = -1; /* Nothing has exited yet */
    sa_chld.sa_handler = sesssigchild_handler;
    sa_chld.sa_flags = SA_NOCLDSTOP;
    sigemptyset(&sa_chld.sa_mask);
    if (sigaction(SIGCHLD, &sa_chld, NULL) < 0) {
        dropbear_exit("signal() error");
    }
}

/* add a new environment variable, allocating space for the entry */
void addnewvar(const char* param, const char* var) {
    char* newvar = NULL;
    int plen, vlen;

    plen = strlen(param);
    vlen = strlen(var);

    newvar = m_malloc(plen + vlen + 2); /* 2 is for '=' and '\0' */
    memcpy(newvar, param, plen);
    newvar[plen] = '=';
    memcpy(&newvar[plen + 1], var, vlen);
    newvar[plen + vlen + 1] = '\0';
    /* newvar is leaked here, but that's part of putenv()'s semantics */
    if (putenv(newvar) < 0) {
        dropbear_exit("environ error");
    }
}

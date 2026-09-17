#ifndef DROPBEAR_SVR_KEX_BROKER_H
#define DROPBEAR_SVR_KEX_BROKER_H

#include "includes.h"
#include "buffer.h"

struct Channel;
struct ChanSess;

#if DROPBEAR_SVR_KEX_BROKER
void svr_kex_broker_start(void);
void svr_kex_broker_exchange(mp_int *dh_e, buffer *q_c);
void svr_kex_broker_cleanup(void);
void svr_kex_broker_checkchild(pid_t pid);
int svr_kex_broker_is_monitor(void);
void svr_kex_broker_authenticate(void);
int svr_kex_broker_prepare_command(struct Channel *channel, struct ChanSess *session);
void svr_kex_broker_release_session(struct ChanSess *session);
int svr_kex_broker_spawn(struct Channel *channel, struct ChanSess *session);
int svr_kex_broker_signal(const struct ChanSess *session);
int svr_kex_broker_pty(struct Channel *channel, struct ChanSess *session);
int svr_kex_broker_window_change(struct Channel *channel, struct ChanSess *session);
void svr_kex_broker_io(void);
void svr_kex_broker_timeout(struct timeval *timeout);
#else
#define svr_kex_broker_cleanup() ((void)0)
#define svr_kex_broker_checkchild(pid) ((void)(pid))
#define svr_kex_broker_is_monitor() 0
#define svr_kex_broker_release_session(session) ((void)(session))
#endif

#endif

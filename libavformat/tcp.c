/*
 * TCP protocol
 * Copyright (c) 2002 Fabrice Bellard
 *
 * This file is part of FFmpeg.
 *
 * FFmpeg is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * FFmpeg is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with FFmpeg; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */
#include "avformat.h"
#include "libavutil/avassert.h"
#include "libavutil/parseutils.h"
#include "libavutil/opt.h"
#include "libavutil/time.h"
#include "libavutil/application.h"
#include "libavutil/dns_cache.h"

#include "internal.h"
#include "network.h"
#include "os_support.h"
#include "url.h"
#if HAVE_POLL_H
#include <poll.h>
#endif
#if HAVE_PTHREADS
#include <pthread.h>
#endif

typedef struct TCPContext {
    const AVClass *class;
    int fd;
    int listen;
    int open_timeout;
    int rw_timeout;
    int listen_timeout;
    int recv_buffer_size;
    int send_buffer_size;
    int tcp_nodelay;
#if !HAVE_WINSOCK2_H
    int tcp_mss;
#endif /* !HAVE_WINSOCK2_H */
} TCPContext;

#define FAST_OPEN_FLAG 0x20000000

#define OFFSET(x) offsetof(TCPContext, x)
#define D AV_OPT_FLAG_DECODING_PARAM
#define E AV_OPT_FLAG_ENCODING_PARAM
static const AVOption options[] = {
    { "listen",          "Listen for incoming connections",  OFFSET(listen),         AV_OPT_TYPE_INT, { .i64 = 0 },     0,       2,       .flags = D|E },
    { "timeout",     "set timeout (in microseconds) of socket I/O operations", OFFSET(rw_timeout),     AV_OPT_TYPE_INT, { .i64 = -1 },         -1, INT_MAX, .flags = D|E },
    { "connect_timeout",  "set connect timeout (in microseconds) of socket", OFFSET(open_timeout),     AV_OPT_TYPE_INT, { .i64 = -1 },         -1, INT_MAX, .flags = D|E },
    { "listen_timeout",  "Connection awaiting timeout (in milliseconds)",      OFFSET(listen_timeout), AV_OPT_TYPE_INT, { .i64 = -1 },         -1, INT_MAX, .flags = D|E },
    { "send_buffer_size", "Socket send buffer size (in bytes)",                OFFSET(send_buffer_size), AV_OPT_TYPE_INT, { .i64 = -1 },         -1, INT_MAX, .flags = D|E },
    { "recv_buffer_size", "Socket receive buffer size (in bytes)",             OFFSET(recv_buffer_size), AV_OPT_TYPE_INT, { .i64 = -1 },         -1, INT_MAX, .flags = D|E },
    { "tcp_nodelay", "Use TCP_NODELAY to disable nagle's algorithm",           OFFSET(tcp_nodelay), AV_OPT_TYPE_BOOL, { .i64 = 0 },             0, 1, .flags = D|E },
#if !HAVE_WINSOCK2_H
    { "tcp_mss",     "Maximum segment size for outgoing TCP packets",          OFFSET(tcp_mss),     AV_OPT_TYPE_INT, { .i64 = -1 },         -1, INT_MAX, .flags = D|E },
#endif /* !HAVE_WINSOCK2_H */
    { NULL }
};

static const AVClass tcp_class = {
    .class_name = "tcp",
    .item_name  = av_default_item_name,
    .option     = options,
    .version    = LIBAVUTIL_VERSION_INT,
};

static void customize_fd(void *ctx, int fd)
{
    TCPContext *s = ctx;
    /* Set the socket's send or receive buffer sizes, if specified.
       If unspecified or setting fails, system default is used. */
    if (s->recv_buffer_size > 0) {
        if (setsockopt (fd, SOL_SOCKET, SO_RCVBUF, &s->recv_buffer_size, sizeof (s->recv_buffer_size))) {
            ff_log_net_error(ctx, AV_LOG_WARNING, "setsockopt(SO_RCVBUF)");
        }
    }
    if (s->send_buffer_size > 0) {
        if (setsockopt (fd, SOL_SOCKET, SO_SNDBUF, &s->send_buffer_size, sizeof (s->send_buffer_size))) {
            ff_log_net_error(ctx, AV_LOG_WARNING, "setsockopt(SO_SNDBUF)");
        }
    }
    if (s->tcp_nodelay > 0) {
        if (setsockopt (fd, IPPROTO_TCP, TCP_NODELAY, &s->tcp_nodelay, sizeof (s->tcp_nodelay))) {
            ff_log_net_error(ctx, AV_LOG_WARNING, "setsockopt(TCP_NODELAY)");
        }
    }
#if !HAVE_WINSOCK2_H
    if (s->tcp_mss > 0) {
        if (setsockopt (fd, IPPROTO_TCP, TCP_MAXSEG, &s->tcp_mss, sizeof (s->tcp_mss))) {
            ff_log_net_error(ctx, AV_LOG_WARNING, "setsockopt(TCP_MAXSEG)");
        }
    }
#endif /* !HAVE_WINSOCK2_H */
}

/* return non zero if error */
static int tcp_open(URLContext *h, const char *uri, int flags)
{
    struct addrinfo hints = { 0 }, *ai, *cur_ai;
    struct addrinfo *cur_v4_ai = NULL;
    struct addrinfo *cur_v6_ai = NULL;
    int port, fd = -1;
    TCPContext *s = h->priv_data;
    const char *p;
    char buf[256];
    int ret;
    char hostname[1024],proto[1024],path[1024];
    char portstr[10];
    AVAppTcpIOControl control = {0};
    DnsCacheEntry *dns_entry = NULL;
    int64_t dns_time = 0;
    int64_t tcp_time = 0;
    char ipbuf[MAX_IP_LEN];
    struct sockaddr_in *ipaddr;
    char *c_ipaddr = NULL;

    if (s->open_timeout < 0) {
        s->open_timeout = 15000000;
    }

    s->app_ctx = (AVApplicationContext *)av_dict_strtoptr(s->app_ctx_intptr);

    if (s->fastopen) {
        s->tcp_connected = 0;
        strcpy(s->uri, uri);
        return 0;
    }

    av_url_split(proto, sizeof(proto), NULL, 0, hostname, sizeof(hostname),
        &port, path, sizeof(path), uri);
    if (strcmp(proto, "tcp"))
        return AVERROR(EINVAL);
    if (port <= 0 || port >= 65536) {
        av_log(h, AV_LOG_ERROR, "Port missing in uri\n");
        return AVERROR(EINVAL);
    }
    p = strchr(uri, '?');
    if (p) {
        if (av_find_info_tag(buf, sizeof(buf), "listen", p)) {
            char *endptr = NULL;
            s->listen = strtol(buf, &endptr, 10);
            /* assume if no digits were found it is a request to enable it */
            if (buf == endptr)
                s->listen = 1;
        }
        if (av_find_info_tag(buf, sizeof(buf), "timeout", p)) {
            s->rw_timeout = strtol(buf, NULL, 10);
            if (s->rw_timeout >= 0) {
                s->open_timeout = s->rw_timeout;
            }
        }
        if (av_find_info_tag(buf, sizeof(buf), "listen_timeout", p)) {
            s->listen_timeout = strtol(buf, NULL, 10);
        }
    }
    if (s->rw_timeout >= 0 ) {
        h->rw_timeout = s->rw_timeout;
    }

    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    snprintf(portstr, sizeof(portstr), "%d", port);
    if (s->listen)
        hints.ai_flags |= AI_PASSIVE;

    if (s->dns_cache_timeout > 0) {
        if (s->dns_cache_clear) {
            av_log(NULL, AV_LOG_INFO, "will delete dns cache entry, uri = %s\n", uri);
            remove_dns_cache_entry(uri);
        } else {
            dns_entry = get_dns_cache_reference(uri);
            if (dns_entry && dns_entry->res && dns_entry->res->ai_family == AF_INET6 && !s->enable_ipv6) {
                release_dns_cache_reference(uri, &dns_entry);
                remove_dns_cache_entry(uri);
                av_log(NULL, AV_LOG_INFO, "will delete dns cache entry because ipv6 fallback, uri = %s\n", uri);
                dns_entry = NULL;
            }
        }
    }
    av_application_on_dns_will_open(s->app_ctx, hostname);
    dns_time = av_gettime();
    if (!dns_entry) {
#ifdef HAVE_PTHREADS
        ret = ijk_tcp_getaddrinfo_nonblock(hostname, portstr, &hints, &ai, s->addrinfo_timeout, &h->interrupt_callback, s->addrinfo_one_by_one);
#else
        if (s->addrinfo_timeout > 0)
            av_log(h, AV_LOG_WARNING, "Ignore addrinfo_timeout without pthreads support.\n");
        if (!hostname[0])
            ret = getaddrinfo(NULL, portstr, &hints, &ai);
        else
            ret = getaddrinfo(hostname, portstr, &hints, &ai);
#endif

        if (ret) {
            av_log(h, AV_LOG_ERROR,
                "Failed to resolve hostname %s: %s\n",
                    hostname, gai_strerror(ret));
            dns_time = (av_gettime() - dns_time) / 1000;
            if (ret == ETIMEDOUT) {
                ret = AVERROR_DNS_TIMEOUT;
            } else {
                ret = AVERROR_DNS_ERROR;
            }
            av_application_on_dns_did_open(s->app_ctx, hostname, NULL, DNS_TYPE_LOCAL_DNS, dns_time, s->dash_audio_tcp, WRAP_UNKNOWN_FAMILY,  ret);
            return ret;
        }

        cur_ai = ai;
    } else {
        av_log(NULL, AV_LOG_INFO, "hit dns cache uri = %s\n", uri);
        cur_ai = dns_entry->res;
    }
    dns_time = (av_gettime() - dns_time) / 1000;

    while (cur_ai->ai_next && cur_ai->ai_next->ai_addr) {
        if (cur_ai->ai_family == AF_INET && cur_v4_ai == NULL) {
            ipaddr = (struct sockaddr_in *)cur_ai->ai_addr;
            c_ipaddr = (char *)inet_ntop(AF_INET, &ipaddr->sin_addr, ipbuf, MAX_IP_LEN);
            if (!strcmp(c_ipaddr, "0.0.0.0")) {
                cur_ai = cur_ai->ai_next;
                continue;
            }
            cur_v4_ai = cur_ai;
        } else if (cur_ai->ai_family == AF_INET6 && cur_v6_ai == NULL) {
            cur_v6_ai = cur_ai;
        }
        if ((s->enable_ipv6 && cur_v6_ai != NULL) || cur_v4_ai != NULL) {
            break;
        }
        cur_ai = cur_ai->ai_next;
    }

    if ((s->enable_ipv6 || cur_v4_ai == NULL) && cur_v6_ai != NULL) {
        cur_ai = cur_v6_ai;
    } else if (cur_v4_ai != NULL) {
        cur_ai = cur_v4_ai;
    }


#if HAVE_STRUCT_SOCKADDR_IN6
    // workaround for IOS9 getaddrinfo in IPv6 only network use hardcode IPv4 address can not resolve port number.
    if (cur_ai->ai_family == AF_INET6){
        struct sockaddr_in6 * sockaddr_v6 = (struct sockaddr_in6 *)cur_ai->ai_addr;
        if (!sockaddr_v6->sin6_port){
            sockaddr_v6->sin6_port = htons(port);
        }
        c_ipaddr = (char *)inet_ntop(AF_INET6, &sockaddr_v6->sin6_addr, ipbuf, MAX_IP_LEN);
        av_log(NULL, AV_LOG_INFO, "cur ipv6 c_ipaddr = %s\n", c_ipaddr);
    }
#endif
    if (cur_ai->ai_family != AF_INET6 && cur_ai && cur_ai->ai_addr) {
        ipaddr = (struct sockaddr_in *)cur_ai->ai_addr;
        c_ipaddr = (char *)inet_ntop(AF_INET, &ipaddr->sin_addr, ipbuf, MAX_IP_LEN);
        av_log(NULL, AV_LOG_INFO, "cur ipv4 c_ipaddr = %s\n", c_ipaddr);
    }
    if (dns_entry) {
        av_application_on_dns_did_open(s->app_ctx, hostname, c_ipaddr, DNS_TYPE_DNS_CACHE, dns_time, s->dash_audio_tcp, cur_ai->ai_family, 0);
    } else {
        if (strstr(uri, c_ipaddr)) {
            av_application_on_dns_did_open(s->app_ctx, hostname, c_ipaddr, DNS_TYPE_NO_USE, dns_time, s->dash_audio_tcp, cur_ai->ai_family, 0);
        } else {
            av_application_on_dns_did_open(s->app_ctx, hostname, c_ipaddr, DNS_TYPE_LOCAL_DNS, dns_time, s->dash_audio_tcp, cur_ai->ai_family, 0);
        }
    }

    if (s->listen > 0) {
        while (cur_ai && fd < 0) {
            fd = ff_socket(cur_ai->ai_family,
                           cur_ai->ai_socktype,
                           cur_ai->ai_protocol);
            if (fd < 0) {
                ret = ff_neterrno();
                cur_ai = cur_ai->ai_next;
            }
        }
        if (fd < 0)
            goto fail1;
        customize_fd(s, fd);
    }

    if (s->listen == 2) {
        // multi-client
        if ((ret = ff_listen(fd, cur_ai->ai_addr, cur_ai->ai_addrlen)) < 0)
            goto fail1;
    } else if (s->listen == 1) {
        // single client
        if ((ret = ff_listen_bind(fd, cur_ai->ai_addr, cur_ai->ai_addrlen,
                                  s->listen_timeout, h)) < 0)
            goto fail1;
        // Socket descriptor already closed here. Safe to overwrite to client one.
        fd = ret;
    } else {
        ret = ff_connect_parallel(ai, s->open_timeout / 1000, 3, h, &fd, customize_fd, s);
        if (ret < 0)
            goto fail1;
    }

    h->is_streamed = 1;
    s->fd = fd;

    if (dns_entry) {
        release_dns_cache_reference(uri, &dns_entry);
    } else {
        freeaddrinfo(ai);
    }
    return 0;

 fail1:
    if (fd >= 0)
        closesocket(fd);

    if (dns_entry) {
        av_log(NULL, AV_LOG_ERROR, "hit dns cache but connect fail uri = %s, ip = %s\n", uri , control.ip);
        release_dns_cache_reference(uri, &dns_entry);
        remove_dns_cache_entry(uri);
    } else {
        freeaddrinfo(ai);
    }

    return ret;
}

static int tcp_accept(URLContext *s, URLContext **c)
{
    TCPContext *sc = s->priv_data;
    TCPContext *cc;
    int ret;
    av_assert0(sc->listen);
    if ((ret = ffurl_alloc(c, s->filename, s->flags, &s->interrupt_callback)) < 0)
        return ret;
    cc = (*c)->priv_data;
    ret = ff_accept(sc->fd, sc->listen_timeout, s);
    if (ret < 0) {
        ffurl_closep(c);
        return ret;
    }
    cc->fd = ret;
    return 0;
}

static int tcp_read(URLContext *h, uint8_t *buf, int size)
{
    TCPContext *s = h->priv_data;
    int ret;
    int nread = 0;

    if (!(h->flags & AVIO_FLAG_NONBLOCK)) {
        ret = ff_network_wait_fd_timeout(s->fd, 0, h->rw_timeout, &h->interrupt_callback);
        if (ret) {
            if (ret == AVERROR(ETIMEDOUT)) {
                ret = AVERROR_TCP_READ_TIMEOUT;
            }
            return ret;
        }
    }
    ret = recv(s->fd, buf, size, 0);
    if (ret == 0)
        return AVERROR_EOF;
    if (ret > 0) {
        if (s->app_ctx) {
            if (s->dash_audio_tcp && s->app_ctx->dash_audio_recv_buffer_size > 0 && s->app_ctx->dash_audio_recv_buffer_size != s->recv_buffer_size) {
                s->recv_buffer_size = s->app_ctx->dash_audio_recv_buffer_size;
                setsockopt (s->fd, SOL_SOCKET, SO_RCVBUF, &s->recv_buffer_size, sizeof (s->recv_buffer_size));
            } else if (s->dash_video_tcp && s->app_ctx->dash_video_recv_buffer_size > 0 && s->app_ctx->dash_video_recv_buffer_size != s->recv_buffer_size) {
                s->recv_buffer_size = s->app_ctx->dash_video_recv_buffer_size;
                setsockopt (s->fd, SOL_SOCKET, SO_RCVBUF, &s->recv_buffer_size, sizeof (s->recv_buffer_size));
            }
        }
#ifdef FIONREAD
        ioctl(s->fd, FIONREAD, &nread);
#endif

#ifdef SO_NREAD
        int avail;
        socklen_t avail_len = sizeof(avail);
        if (nread <= 0 && !getsockopt(s->fd, SOL_SOCKET, SO_NREAD, &avail, &avail_len)) {
            nread = avail;
        }
#endif // SO_NREAD

        if (s->dash_audio_tcp) {
            av_application_did_io_tcp_read(s->app_ctx, (void*)h, ret, nread, TCP_STREAM_TYPE_DASH_AUDIO);
        } else if (s->dash_video_tcp) {
            av_application_did_io_tcp_read(s->app_ctx, (void*)h, ret, nread, TCP_STREAM_TYPE_DASH_VIDEO);
        } else {
            av_application_did_io_tcp_read(s->app_ctx, (void*)h, ret, nread, TCP_STREAM_TYPE_NORMAL);
        }
    }
    return ret < 0 ? ff_neterrno() : ret;
}

static int tcp_write(URLContext *h, const uint8_t *buf, int size)
{
    TCPContext *s = h->priv_data;
    int ret;

    if (!(h->flags & AVIO_FLAG_NONBLOCK)) {
        ret = ff_network_wait_fd_timeout(s->fd, 1, h->rw_timeout, &h->interrupt_callback);
        if (ret) {
            if (ret == AVERROR(ETIMEDOUT)) {
                ret = AVERROR_TCP_WRITE_TIMEOUT;
            }
            return ret;
        }
    }

    if (s->fastopen && !s->tcp_connected && av_stristart(buf, "GET", NULL)) {
        ret = tcp_fast_open(h, buf, s->uri, 0);
        if (!ret) {
            s->tcp_connected = 1;
            if (!s->fastopen_success) {
                ret = send(s->fd, buf, size, MSG_NOSIGNAL);
                if (ret > 0) {
                    s->fastopen_success = 1;
                }
                return ret < 0 ? ff_neterrno() : ret;
            }
            return ret;
        } else {
            av_log(NULL, AV_LOG_WARNING, "tcp_fast_open is error ret = %d\n", ret);
            return ret;
        }
    }

    ret = send(s->fd, buf, size, MSG_NOSIGNAL);
    return ret < 0 ? ff_neterrno() : ret;
}

static int tcp_shutdown(URLContext *h, int flags)
{
    TCPContext *s = h->priv_data;
    int how;

    if (flags & AVIO_FLAG_WRITE && flags & AVIO_FLAG_READ) {
        how = SHUT_RDWR;
    } else if (flags & AVIO_FLAG_WRITE) {
        how = SHUT_WR;
    } else {
        how = SHUT_RD;
    }

    return shutdown(s->fd, how);
}

static int tcp_close(URLContext *h)
{
    TCPContext *s = h->priv_data;
    closesocket(s->fd);
    return 0;
}

static int tcp_get_file_handle(URLContext *h)
{
    TCPContext *s = h->priv_data;
    return s->fd;
}

static int tcp_get_window_size(URLContext *h)
{
    TCPContext *s = h->priv_data;
    int avail;
    socklen_t avail_len = sizeof(avail);

#if HAVE_WINSOCK2_H
    /* SO_RCVBUF with winsock only reports the actual TCP window size when
    auto-tuning has been disabled via setting SO_RCVBUF */
    if (s->recv_buffer_size < 0) {
        return AVERROR(ENOSYS);
    }
#endif

    if (getsockopt(s->fd, SOL_SOCKET, SO_RCVBUF, &avail, &avail_len)) {
        return ff_neterrno();
    }
    return avail;
}

const URLProtocol ff_tcp_protocol = {
    .name                = "tcp",
    .url_open            = tcp_open,
    .url_accept          = tcp_accept,
    .url_read            = tcp_read,
    .url_write           = tcp_write,
    .url_close           = tcp_close,
    .url_get_file_handle = tcp_get_file_handle,
    .url_get_short_seek  = tcp_get_window_size,
    .url_shutdown        = tcp_shutdown,
    .priv_data_size      = sizeof(TCPContext),
    .flags               = URL_PROTOCOL_FLAG_NETWORK,
    .priv_data_class     = &tcp_class,
};

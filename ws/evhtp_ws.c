/*
 * Most of the websocket code comes from this unfinished fork:
 *
 *   https://github.com/zerotao/libevhtp/tree/libevhtp2
 *
 * It was reintegrated into libevhtp by the authors of Rampart
 * with sooooo much gratitude for not having to do this from scratch
 *    -ajf
 *
 * Changes and additions, Copyright (c) 2021 Aaron Flin and released
 * under the MIT License.
 *
 * ----------------------------------------------------------------------------
 *
 * While this looks nothing like the original code, my initial point of
 * reference was from Marcin Kelar's parser. His license is included here.
 *
 * Marcin originally had his code under the GPL license, I kept seeing his code
 * referenced in other projects, but could not find the original (more
 * specifically, the original license). I ended up finding his email
 * address and asked if I could use it with a less restrictive license.
 * He responded immediately and said yes, and he did! That's an awesome
 * example of the OSS world. Thank you very much Mr. Kelar.
 *
 * The MIT License (MIT)
 *
 * Copyright (c) 2012-2014 Marcin Kelar
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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *
 * The original API can be found here:
 * https://github.com/OrionExplorer/c-websocket
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>
#include <assert.h>

#include "../include/internal.h"
#include "../include/evhtp.h"
#include "base.h"
#include "sha1.h"
#include "evhtp_ws.h"

#define EVHTP_WS_MAGIC       "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
#define EVHTP_WS_MAGIC_SZ    36
#define PARSER_STACK_MAX     8192


#define MIN_READ(a, b)                    ((a) < (b) ? (a) : (b))
#define HAS_EXTENDED_PAYLOAD_HDR(__frame) ((__frame)->len >= 126)
#define EXTENDED_PAYLOAD_HDR_LEN(__sz) \
    ((__sz >= 126) ? ((__sz == 126) ? 16 : 64) : 0)


static uint32_t __MASK[] = {
    0x000000ff,
    0x0000ff00,
    0x00ff0000,
    0xff000000
};

static uint32_t __SHIFT[] = {
    0, 8, 16, 24
};

static uint64_t ntoh64(const uint64_t input)
{
    /* Network byte order (big-endian) to host byte order conversion */
    const uint8_t *data = (const uint8_t *)&input;
    uint64_t rval;

    rval = ((uint64_t)data[0] << 56) |
           ((uint64_t)data[1] << 48) |
           ((uint64_t)data[2] << 40) |
           ((uint64_t)data[3] << 32) |
           ((uint64_t)data[4] << 24) |
           ((uint64_t)data[5] << 16) |
           ((uint64_t)data[6] <<  8) |
           ((uint64_t)data[7] <<  0);

    return rval;
}

void htp__request_free_(evhtp_request_t * request);

/* Validate opcode according to RFC 6455 */
static int ws_validate_opcode(evhtp_ws_parser * p, evhtp_request_t * req, uint8_t byte)
{
    /* RFC 6455: RSV bits must be 0 unless extension negotiated */
    uint8_t rsv = (byte >> 4) & 0x7;
    if (rsv != 0) {
        fprintf(stderr,"Warning: websockets - invalid RSV bits %d (must be 0)\n", rsv);
        return -1;
    }

    uint8_t opcode = byte & 0xF;
    
    /* Check for valid opcodes */
    if(opcode != OP_CONT && opcode != OP_TEXT &&
       opcode != OP_BIN  && opcode != OP_PING &&
       opcode != OP_PONG && opcode != OP_CLOSE) {
        fprintf(stderr,"Warning: websockets - invalid opcode %d\n", opcode);
        return -1;
    }

    /* Check continuation frame consistency */
    if(req->ws_cont && opcode != OP_CONT) {
        fprintf(stderr,"Warning: websockets - expecting a continue frame but got opcode %d\n", opcode);
        return -1;
    }

    if (!req->ws_cont && opcode == OP_CONT) {
        fprintf(stderr,"Warning: websockets - not expecting a continue frame but got opcode OP_CONT\n");
        return -1;
    }

    return 0;
}

/* Set payload length and validate control frame size */
static int ws_set_payload_len(evhtp_ws_parser * p, uint64_t payload_len)
{
    p->frame.payload_len = payload_len;
    p->content_len       = payload_len;
    p->orig_content_len  = payload_len;

    /* RFC 6455: Control frames must have payload <= 125 bytes */
    if ((p->frame.hdr.opcode & 0x8) != 0 && payload_len > 125) {
        fprintf(stderr,"Warning: websockets - control frame payload length %llu exceeds 125 bytes\n", 
                (unsigned long long)payload_len);
        return -1;
    }

    return 0;
}

/* Demask data in place */
static void ws_demask_data(char * data, size_t len, uint32_t masking_key, uint64_t * content_idx)
{
    size_t z;
    for (z = 0; z < len; z++) {
        int           j = (*content_idx) % 4;
        unsigned char xformed_oct;

        xformed_oct = (masking_key & __MASK[j]) >> __SHIFT[j];
        data[z]     = (unsigned char)data[z] ^ xformed_oct;

        (*content_idx) += 1;
    }
}

/* Process OP_CLOSE status code from payload */
static int ws_process_close_status(evhtp_ws_parser * p, const char * data, size_t len, size_t * i)
{
    if (MIN_READ((const char *)(data + len) - &data[*i], 2) < 2) {
        return 0; /* Need more data */
    }

    uint64_t index = p->content_idx;
    uint32_t mkey  = p->frame.masking_key;
    int      j1    = index % 4;
    int      j2    = (index + 1) % 4;
    int      m1    = (mkey & __MASK[j1]) >> __SHIFT[j1];
    int      m2    = (mkey & __MASK[j2]) >> __SHIFT[j2];
    char     buf[2];

    buf[0]         = data[*i] ^ m1;
    buf[1]         = data[*i + 1] ^ m2;
    p->status_code = ntohs(*(uint16_t *)buf);
    p->content_len -= 2;
    p->content_idx += 2;
    *i += 2;

    return 1; /* Success */
}

ssize_t
evhtp_ws_parser_run(evhtp_request_t *req, evhtp_ws_hooks * hooks,
                    const char * data, size_t len) {
    uint8_t      byte;
    size_t       i=0;
    const char * p_start;
    const char * p_end;
    uint64_t     to_read;
    evhtp_ws_parser * p = req->ws_parser;

    if (!hooks) {
        return (ssize_t)len;
    }	

    //printf("\nparser run, len=%d state=%d\n", (int)len, (int)p->state);
    while(i<len)
    {
        byte = (uint8_t)data[i];
        switch (p->state) {
            case ws_s_start:
                memset(&p->frame, 0, sizeof(p->frame));

                p->state            = ws_s_fin_rsv_opcode;
                p->content_len      = 0;
                p->orig_content_len = 0;
                p->content_idx      = 0;
                p->status_code      = 0;

                if (hooks->on_msg_start) {
                    if ((hooks->on_msg_start)(p)) {
                        return i;
                    }
                }
            /* fall-through */
            case ws_s_fin_rsv_opcode:
                p->frame.hdr.fin    = (byte & 0x80)? 1:0;
                p->frame.hdr.opcode = (byte & 0xF);

                //printf("parser run, opcode=%d ws_cont=%d\n", (int)p->frame.hdr.opcode, (int) req->ws_cont);

                if (ws_validate_opcode(p, req, byte) < 0) {
                    return -1;
                }

                req->ws_cont = !p->frame.hdr.fin;

                p->state = ws_s_mask_payload_len;
                i++;
                break;
            case ws_s_mask_payload_len:
                p->frame.hdr.mask   = ((byte & 0x80) ? 1 : 0);
                p->frame.hdr.len    = (byte & 0x7F);
                i++;
                switch (EXTENDED_PAYLOAD_HDR_LEN(p->frame.hdr.len)) {
                    case 0:
                        if (ws_set_payload_len(p, p->frame.hdr.len) < 0) {
                            return -1;
                        }

                        if (p->frame.hdr.mask == 1) {
                            p->state = ws_s_masking_key;
                            break;
                        }

                        p->state = ws_s_payload;
                        break;
                    case 16:
                        p->state = ws_s_ext_payload_len_16;
                        break;
                    case 64:
                        p->state = ws_s_ext_payload_len_64;
                        break;
                    default:
                        return -1;
                } /* switch */
                break;
            case ws_s_ext_payload_len_16:
                if (MIN_READ((const char *)(data + len) - &data[i], 2) < 2) {
                    return i;
                }

                if (ws_set_payload_len(p, ntohs(*(uint16_t *)&data[i])) < 0) {
                    return -1;
                }

                //printf("16 - content_len = %d\n",  (int)p->content_len);

                i += 2;

                if (p->frame.hdr.mask == 1) {
                    p->state = ws_s_masking_key;
                    break;
                }

                p->state = ws_s_payload;
                break;
            case ws_s_ext_payload_len_64:
                if (MIN_READ((const char *)(data + len) - &data[i], 8) < 8) {
                    return i;
                }

                if (ws_set_payload_len(p, ntoh64(*(uint64_t *)&data[i])) < 0) {
                    return -1;
                }
                //printf("64 - content_len = %d\n",  (int)p->content_len);

                i += 8;

                if (p->frame.hdr.mask == 1) {
                    p->state = ws_s_masking_key;
                    break;
                }

                p->state = ws_s_payload;
                break;
            case ws_s_masking_key:
            {
                int min= MIN_READ((const char *)(data + len) - &data[i], 4);
                if (min < 4) 
                {
                    return i;
                }
                p->frame.masking_key = *(uint32_t *)&data[i];
                i += 4;
                p->state = ws_s_payload;
                if(min==4) // i==len, so go directly to finish.
                    goto fini;
                break;
            }
            case ws_s_payload:

                /* op_close case */
                if (p->frame.hdr.opcode == OP_CLOSE && p->status_code == 0) {
                    int result = ws_process_close_status(p, data, len, &i);
                    if (result == 0) {
                        return i; /* Need more data */
                    }
                    /* RFC states that there could be a message after the
                     * OP_CLOSE 2 byte header, so just drop down and attempt
                     * to parse it.
                     */
                }

                /* check for data */
                p_start = &data[i];
                p_end   = (const char *)(data + len);
                to_read = MIN_READ(p_end - p_start, p->content_len);
                if (to_read > 0) {
                    /* demask data in place */
                    char *unmasked = (char *)p_start;
                    ws_demask_data(unmasked, to_read, p->frame.masking_key, &p->content_idx);

                    if (hooks->on_msg_data) {
                        if ((hooks->on_msg_data)(p, unmasked, to_read)) {
                            return -1;
                        }
                    }
                    p->content_len -= to_read;
                    i += to_read;
                }
                else if (p->content_len > 0) {
                    // Expected payload but no data available in buffer - wait for more data
                    return i;
                }
                // If to_read == 0 and content_len == 0, frame is complete, continue to fini

                fini:
        
                //printf("length=%d, fin= %d\n", (int)p->content_len, (int)p->frame.hdr.fin);

                /* did we get it all? */
                if (p->content_len == 0)
                {
                    /* this is the end, set it to restart if another frame is coming (p->frame.hdr.fin==0) 
                       or for the next request                                                              */
                    p->state = ws_s_start;
                    if(p->frame.hdr.fin == 1 )
                    {
                        req->ws_cont = 0;
                        /*currently, this always returns 0 */
                        (void)(hooks->on_msg_fini)(p);
                        return i;
                    }
                }
                break;
        } /* switch */

    } /* while */

    return i;
}         /* evhtp_ws_parser_run */

int
evhtp_ws_gen_handshake(evhtp_kvs_t * hdrs_in, evhtp_kvs_t * hdrs_out) {
    const char * ws_key;
    const char * upgrade;
    char       * magic_w_ws_key;
    size_t       magic_w_ws_key_len;
    size_t       ws_key_len;
    sha1_ctx     sha;
    char       * out        = NULL;
    size_t       out_bytes  = 0;
    char         digest[20] = { 0 };

    if (!hdrs_in || !hdrs_out) {
        return -1;
    }

    if (!(ws_key = evhtp_kv_find(hdrs_in, "sec-webSocket-key"))) {
        return -1;
    }

    if ((ws_key_len = strlen(ws_key)) == 0) {
        return -1;
    }

    magic_w_ws_key_len = EVHTP_WS_MAGIC_SZ + ws_key_len + 1;

    if (!(magic_w_ws_key = calloc(magic_w_ws_key_len, 1))) {
        return -1;
    }

    memcpy(magic_w_ws_key, ws_key, ws_key_len);
    memcpy((void *)(magic_w_ws_key + ws_key_len),
           EVHTP_WS_MAGIC, EVHTP_WS_MAGIC_SZ);

    sha1_init(&sha);
    sha1_update(&sha, (uint8_t *)magic_w_ws_key, magic_w_ws_key_len - 1);
    sha1_finalize(&sha, (uint8_t *)digest);

    if (base_encode(base64_rfc, digest,
                    20, (void **)&out, &out_bytes) == -1) {
        free(magic_w_ws_key);
        return -1;
    }

    out = realloc(out, out_bytes + 1);
    out[out_bytes] = '\0';

    evhtp_kvs_add_kv(hdrs_out,
                     evhtp_kv_new("Sec-WebSocket-Accept", out, 1, 1));
    free(out);
    free(magic_w_ws_key);

    if ((upgrade = evhtp_kv_find(hdrs_in, "Upgrade"))) {
        evhtp_kvs_add_kv(hdrs_out,
                         evhtp_kv_new("Upgrade", upgrade, 1, 1));
    }

    evhtp_kvs_add_kv(hdrs_out,
                     evhtp_kv_new("Connection", "Upgrade", 1, 1));
    return 0;
} /* evhtp_ws_gen_handshake */

/* use and prepend existing evbuffer with websocket header */
struct evbuffer * evhtp_ws_add_header(struct evbuffer *buf, uint8_t opcode)
{
    size_t          len = evbuffer_get_length(buf),
                    bufsz = 10;
    uint8_t         pbuf[bufsz];

    pbuf[0] = opcode | 0x80;

    if (len <= 125) {
        pbuf[1]= (uint8_t) len;
        bufsz = 2;
    } else if (len > 125 && len <= 65535) {
        pbuf[1] = 126;
        bufsz = 4;
        pbuf[2] = (uint8_t) (len>>8);
        pbuf[3] = (uint8_t) (len & 0xff);
    } else {
        pbuf[1] = 127;
        pbuf[2] = (uint8_t) (len>>56 & 0xff);
        pbuf[3] = (uint8_t) (len>>48 & 0xff);
        pbuf[4] = (uint8_t) (len>>40 & 0xff);
        pbuf[5] = (uint8_t) (len>>32 & 0xff);
        pbuf[6] = (uint8_t) (len>>24 & 0xff);
        pbuf[7] = (uint8_t) (len>>16 & 0xff);
        pbuf[8] = (uint8_t) (len>> 8 & 0xff);
        pbuf[9] = (uint8_t) (len & 0xff);
        bufsz = 10;
    }
    // outgoing data is not masked, so send as is, prepended with header
    if(evbuffer_prepend(buf, pbuf, bufsz))
        return NULL;

    return buf;
}

evhtp_ws_parser *
evhtp_ws_parser_new(void) {
    evhtp_ws_parser *p = calloc(sizeof(evhtp_ws_parser), 1);
    if(!p)
    {
        fprintf(stderr, "calloc err, evhtp_ws line %d\n", __LINE__);
        exit(1);
    }
    return p;
}

void
evhtp_ws_parser_set_userdata(evhtp_ws_parser * p, void * usrdata) {
    assert(p != NULL);

    p->usrdata = usrdata;
}

void *
evhtp_ws_parser_get_userdata(evhtp_ws_parser * p) {
    assert(p != NULL);

    return p->usrdata;
}
/* send a text message to websocket client */
EVHTP_EXPORT int evhtp_ws_send_text(evhtp_connection_t * conn, const char * data, size_t len)
{
    struct evbuffer * buf;

    if (!conn || !data || !conn->bev) {
        return -1;
    }

    buf = evbuffer_new();
    if (!buf) {
        return -1;
    }

    evbuffer_add(buf, data, len);
    
    if (!evhtp_ws_add_header(buf, OP_TEXT)) {
        evbuffer_free(buf);
        return -1;
    }

    bufferevent_write_buffer(conn->bev, buf);
    evbuffer_free(buf);

    return 0;
}

/* send a binary message to websocket client */
EVHTP_EXPORT int evhtp_ws_send_binary(evhtp_connection_t * conn, const void * data, size_t len)
{
    struct evbuffer * buf;

    if (!conn || !data || !conn->bev) {
        return -1;
    }

    buf = evbuffer_new();
    if (!buf) {
        return -1;
    }

    evbuffer_add(buf, data, len);
    
    if (!evhtp_ws_add_header(buf, OP_BIN)) {
        evbuffer_free(buf);
        return -1;
    }

    bufferevent_write_buffer(conn->bev, buf);
    evbuffer_free(buf);

    return 0;
}

/* set a flag to disconnect after we are done parsing */
void evhtp_ws_disconnect(evhtp_connection_t * conn)
{
    if (conn && conn->request) {
        conn->request->disconnect = 1;
    }
}

/* the actual disconnect code, done at the appropriate time */
void evhtp_ws_do_disconnect(evhtp_request_t  * req)
{
    evhtp_connection_t * c;
    struct evbuffer *b;

    if (!req)
        return;

    c = evhtp_request_get_connection(req);

    if(!c)
        return;

    /* still run the callback for disconnect */
    if (c->hooks && c->hooks->on_event) {
        (c->hooks->on_event)(c, BEV_EVENT_EOF, c->hooks->on_event_arg);
    }

    if(c->bev)
    {
         b = bufferevent_get_input(c->bev);
         evbuffer_drain(b, evbuffer_get_length(b));
    }

    if (req->ws_parser)
    {
        if(req->ws_parser->pingev)
        {
            event_del(req->ws_parser->pingev);
            event_free(req->ws_parser->pingev);
        }
        free(req->ws_parser);
    }
    evhtp_safe_free(c, evhtp_connection_free);
}

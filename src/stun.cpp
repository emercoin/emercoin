/*
 * Get External IP address by STUN protocol
 *
 * Based on project Minimalistic STUN client "ministun"
 * https://code.google.com/p/ministun/
 *
 * This program is free software, distributed under the terms of
 * the GNU General Public License Version 2. See the LICENSE file
 * at the top of the source tree.
 *
 * STUN is described in RFC3489 and it is based on the exchange
 * of UDP packets between a client and one or more servers to
 * determine the externally visible address (and port) of the client
 * once it has gone through the NAT boxes that connect it to the
 * outside.
 * The simplest request packet is just the header defined in
 * struct stun_header, and from the response we may just look at
 * one attribute, STUN_MAPPED_ADDRESS, that we find in the response.
 * By doing more transactions with different server addresses we
 * may determine more about the behaviour of the NAT boxes, of
 * course - the details are in the RFC.
 *
 * All STUN packets start with a simple header made of a type,
 * length (excluding the header) and a 16-byte random transaction id.
 * Following the header we may have zero or more attributes, each
 * structured as a type, length and a value (whose format depends
 * on the type, but often contains addresses).
 * Of course all fields are in network format.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#ifdef WIN32
#include <winsock2.h>
#include <stdint.h>
#else
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#endif
#include <unistd.h>
#include <time.h>
#include <errno.h>

#include "random.h"
#include "ministun.h"
#include "shutdown.h"

/*---------------------------------------------------------------------*/
struct StunSrv {
  char     name[46];
  uint16_t port;
};

// STUN server list from auto-generated file gen-stun-list.c
static struct StunSrv StunSrvList[] = {
#include "gen-stun-list.c"
};

static const int StunSrvListQty = sizeof(StunSrvList) / sizeof(StunSrv);

/*---------------------------------------------------------------------*/
/* wrapper to send an STUN message */
static int stun_send(int s, struct sockaddr_in *dst, struct stun_header *resp)
{
    return sendto(s, (const char *)resp, ntohs(resp->msglen) + sizeof(*resp), 0,
		      (struct sockaddr *)dst, sizeof(*dst));
}

/* helper function to generate a random request id */
static void stun_req_id(struct stun_header *req) {
  // fill rand to req->id.id[1..3]
  GetRandBytes((uint8_t *)&(req->id.id[1]), 3 * sizeof(unsigned int));
  req->id.id[0] = STUN_XORMAGIC; // Set magic for RFC5389
}

/* Extract the STUN_MAPPED_ADDRESS from the stun response.
 * This is used as a callback for stun_handle_response
 * when called from stun_request.
 */
static int stun_get_mapped(struct stun_attr *attr, void *arg)
{
  struct stun_addr *addr = (struct stun_addr *)(attr + 1);
  struct sockaddr_in *sa = (struct sockaddr_in *)arg;
  int rc = 0;
  if(ntohs(attr->len) != 8)
    return rc;

  uint32_t xor_mask;

  switch(ntohs(attr->attr)) {
    case STUN_MAPPED_ADDRESS:
      if(sa->sin_addr.s_addr == 0) {
        rc = 1;
	xor_mask = 0;
      }
      break;
    case STUN_XORMAPPEDADDRESS:
      rc = 2;
      xor_mask = STUN_XORMAGIC;
      break;
    case STUN_XORMAPPEDADDRESS2:
      rc = 4;
      xor_mask = STUN_XORMAGIC;
      break;
    default: break;
  }

  if(rc) {
     sa->sin_port        = addr->port ^ xor_mask;
     sa->sin_addr.s_addr = addr->addr ^ xor_mask;
  }

  return rc;
}


/* handle an incoming STUN message.
 *
 * Do some basic sanity checks on packet size and content,
 * try to extract a bit of information, and possibly reply.
 * At the moment this only processes BIND requests, and returns
 * the externally visible address of the request.
 * If a callback is specified, invoke it with the attribute.
 */
static int stun_handle_packet(int s, struct sockaddr_in *src,
	unsigned char *data, size_t len, void *arg)
{
  struct stun_header *hdr = (struct stun_header *)data;
  struct stun_attr *attr;
  int ret = 0;
  size_t x;

  /* On entry, 'len' is the length of the udp payload. After the
   * initial checks it becomes the size of unprocessed options,
   * while 'data' is advanced accordingly.
   */
  if (len < sizeof(struct stun_header))
    return -20;

  len -= sizeof(struct stun_header);
  data += sizeof(struct stun_header);
  x = ntohs(hdr->msglen);	/* len as advertised in the message */
  if(x < len)
  len = x;

  while (len) {
    if (len < sizeof(struct stun_attr)) {
      ret = -21;
      break;
    }
    attr = (struct stun_attr *)data;
    /* compute total attribute length */
    x = ntohs(attr->len) + sizeof(struct stun_attr);
    if (x > len) {
      ret = -22;
      break;
    }
    ret |= stun_get_mapped(attr, arg);
    /* Clear attribute id: in case previous entry was a string,
     * this will act as the terminator for the string.
     */
    attr->attr = 0;
    data += x;
    len -= x;
  } // while
  /* Null terminate any string.
   * XXX NOTE, we write past the size of the buffer passed by the
   * caller, so this is potentially dangerous. The only thing that
   * saves us is that usually we read the incoming message in a
   * much larger buffer
   */
  *data = '\0';

  /* Now prepare to generate a reply, which at the moment is done
   * only for properly formed (len == 0) STUN_BINDREQ messages.
   */

  return ret;
}
/*---------------------------------------------------------------------*/

static int StunRequest2(int sock, struct sockaddr_in *server, struct sockaddr_in *mapped) {

  struct stun_header *req;
  unsigned char reqdata[1024];

  req = (struct stun_header *)reqdata;
  stun_req_id(req);
  int reqlen = 0;
  req->msgtype = 0;
  req->msglen = 0;
  req->msglen = htons(reqlen);
  req->msgtype = htons(STUN_BINDREQ);

  unsigned char reply_buf[1024];
  fd_set rfds;
  struct timeval to = { STUN_TIMEOUT, 0 };
  struct sockaddr_in src;
#ifdef WIN32
  int srclen;
#else
  socklen_t srclen;
#endif

  int res = stun_send(sock, server, req);
  if(res < 0)
    return -10;
  FD_ZERO(&rfds);
  FD_SET(sock, &rfds);
  res = select(sock + 1, &rfds, NULL, NULL, &to);
  if (res <= 0) 	/* timeout or error */
    return -11;
  memset(&src, 0, sizeof(src));
  srclen = sizeof(src);
  /* XXX pass -1 in the size, because stun_handle_packet might
   * write past the end of the buffer.
   */
  res = recvfrom(sock, (char *)reply_buf, sizeof(reply_buf) - 1,
		0, (struct sockaddr *)&src, &srclen);
  if (res <= 0)
    return -12;
  memset(mapped, 0, sizeof(struct sockaddr_in));
  return stun_handle_packet(sock, &src, reply_buf, res, mapped);
} // StunRequest2

/*---------------------------------------------------------------------*/
static int StunRequest(const char *host, uint16_t port, struct sockaddr_in *mapped, uint16_t src_port) {
  struct hostent *hostinfo = gethostbyname(host);
  if(hostinfo == NULL)
      return -1;

  struct sockaddr_in server, client;
  memset(&server, 0, sizeof(server));
  memset(&client, 0, sizeof(client));

  server.sin_family = client.sin_family = AF_INET;
  server.sin_addr = *(struct in_addr*) hostinfo->h_addr;
  server.sin_port = htons(port);

  int sock = socket(AF_INET, SOCK_DGRAM, 0);
  if(sock < 0)
    return -2;

  client.sin_addr.s_addr = htonl(INADDR_ANY);
  client.sin_port = htons(src_port);

  int rc = -3;
   if(bind(sock, (struct sockaddr*)&client, sizeof(client)) >= 0)
     rc = StunRequest2(sock, &server, mapped);

  close(sock);
  return rc;
} // StunRequest

/*---------------------------------------------------------------------*/
// Input: random value to generate the pair (pos, step) for pseudorandom
// traversal over the server list
// Output:
//  - mapped: populate struct struct mapped (ipV4 only)
//  - srv: set pointer to server name, which return successful answer
// Retval:
// bits 0-7 = STUN tokens set, 8-32 = attempt number
// Negative return - unable to figure out IP address
int GetExternalIPbySTUN(struct sockaddr_in *mapped, const char **srv, uint16_t src_port) {
  uint32_t rnd;
  GetRandBytes((uint8_t *)&rnd, sizeof(rnd));
  uint16_t pos  = rnd >> 16;
  uint16_t step, a, b, t;
  // Select step relative prime to StunSrvListQty using Euclid algorithm
  do {
      a = step = ++rnd;
      b = StunSrvListQty;
      do {
          t = b;
          b = a % b;
          a = t;
      } while(b != 0);
  } while(a != 1);

  int attempt; // runs in 8 birs offset, for keep flags in low byte
  for(attempt = 256; attempt < 64 * 256; attempt += 256) {
    if(ShutdownRequested())
      break;
    pos = (pos + step) % StunSrvListQty;
    int rc = StunRequest(*srv = StunSrvList[pos].name, StunSrvList[pos].port, mapped, src_port);
    if(rc > 0)
      return attempt | rc;
  }
  return -1;
}

/*---------------------------------------------------------------------*/



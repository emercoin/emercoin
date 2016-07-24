/*
 * Simple DNS server for Emercoin project
 *
 * Lookup for names like "dns:some-nake" in the local nameindex database.
 * Database is updates from blockchain, and keeps NMC-transactions.
 *
 * Supports standard RFC1034 UDP DNS protocol only
 *
 * Supported fields: A, AAAA, NS, PTR, MX, TXT, CNAME
 * Does not support: SOA, WKS, SRV
 * Does not support recursive query, authority zone and namezone transfers.
 * 
 *
 * Author: maxihatop
 *
 * This code can be used according BSD license:
 * http://en.wikipedia.org/wiki/BSD_licenses
 *
 */

#include <stdio.h>
#include <unistd.h>
#include <stdint.h>
#include <sys/types.h>
#include <stdlib.h>

#include <string.h>

#ifdef WIN32
#include <winsock2.h>
#else
#include <arpa/inet.h>
#include <netinet/in.h>
#endif

#include <ctype.h>

#include "namecoin.h"
#include "util.h"
#include "emcdns.h"
#include "hooks.h"
extern CHooks* hooks;

/*---------------------------------------------------*/

#define BUF_SIZE (512 + 512)
#define MAX_OUT  512	// Old DNS restricts UDP to 512 bytes
#define MAX_TOK  64	// Maximal TokenQty in the vsl_list, like A=IP1,..,IPn
#define MAX_DOM  10	// Maximal domain level

#define VAL_SIZE (MAX_VALUE_LENGTH + 16)
#define DNS_PREFIX "dns"
#define REDEF_SYM  '~'

/*---------------------------------------------------*/

#ifdef WIN32
int inet_pton(int af, const char *src, void *dst)
{
  struct sockaddr_storage ss;
  int size = sizeof(ss);
  char src_copy[INET6_ADDRSTRLEN+1];

  ZeroMemory(&ss, sizeof(ss));
  /* stupid non-const API */
  strncpy (src_copy, src, INET6_ADDRSTRLEN+1);
  src_copy[INET6_ADDRSTRLEN] = 0;

  if (WSAStringToAddress(src_copy, af, NULL, (struct sockaddr *)&ss, &size) == 0) {
    switch(af) {
      case AF_INET:
    *(struct in_addr *)dst = ((struct sockaddr_in *)&ss)->sin_addr;
    return 1;
      case AF_INET6:
    *(struct in6_addr *)dst = ((struct sockaddr_in6 *)&ss)->sin6_addr;
    return 1;
    }
  }
  return 0;
}
#endif

/*---------------------------------------------------*/

EmcDns::EmcDns() : m_port(0) {
} // EmcDns::EmcDns

/*---------------------------------------------------*/

EmcDns::~EmcDns() {
  Reset(NULL, 0, NULL, NULL, NULL, 0);
} // EmcDns::~EmcDns


/*---------------------------------------------------*/

int EmcDns::Reset(const char *bind_ip, uint16_t port_no, 
  const char *gw_suffix, const char *allowed_suff, const char *local_fname, uint8_t verbose) {
  if(m_port != 0) {
    // reset current object to initial state
#ifndef WIN32
    shutdown(m_sockfd, SHUT_RDWR);
#endif
    closesocket(m_sockfd);
    Sleep(100); // Allow 0.1s external thread to exit
#ifndef WIN32
    // pthread_join(m_thread, NULL);
#endif
    free(m_value);
    free(m_dap_ht);
    m_port = 0;
    if(m_verbose > 0)
	 printf("EmcDns::Reset: Destroyed OK\n");
  }

  // Initialize new object here
  if(port_no != 0) { 
    // Set object to a new state
    memset(this, 0, sizeof(EmcDns)); // Clear previous state
    m_verbose = verbose;

    // Create and socket
    int ret = socket(PF_INET, SOCK_DGRAM, 0);
    if(ret < 0) {
      return -2; // Cannot create socket
    } else {
      m_sockfd = ret;
    }

    m_address.sin_family = AF_INET;
    m_address.sin_port = htons(port_no);

    if(!inet_pton(AF_INET, bind_ip, &m_address.sin_addr.s_addr)) 
      m_address.sin_addr.s_addr = htonl(INADDR_ANY);

    if(bind(m_sockfd, (struct sockaddr *) &m_address,
                     sizeof (struct sockaddr_in)) < 0) {
      char buf[80];
      sprintf(buf, "EmcDns::Reset: Cannot bind to port %u", port_no);
      perror(buf);
      closesocket(m_sockfd);
      return -3; // Cannot bind socket
    }

    // Create temporary local buf on stack
    int local_len = 0;
    char local_tmp[1 << 15]; // max 32Kb
    FILE *flocal;
    uint8_t local_qty = 0;
    if(local_fname != NULL && (flocal = fopen(local_fname, "r")) != NULL) {
      char *rd = local_tmp;
      while(rd < local_tmp + (1 << 15) - 200 && fgets(rd, 200, flocal)) {
	if(*rd < '0' || *rd == ';')
	  continue;
	char *p = strchr(rd, '=');
	if(p == NULL)
	  continue;
	rd = strchr(p, 0);
        while(*--rd < 040) 
	  *rd = 0;
	rd += 2;
	local_qty++;
      } // while rd
      local_len = rd - local_tmp;
      fclose(flocal);
    }

    // Allocate memory
    int allowed_len = allowed_suff == NULL? 0 : strlen(allowed_suff);
    m_gw_suf_len    = gw_suffix    == NULL? 0 : strlen(gw_suffix);

    // Compute dots in the gw-suffix
    m_gw_suf_dots = 0;
    if(m_gw_suf_len)
      for(const char *p = gw_suffix; *p; p++)
        if(*p == '.') 
	  m_gw_suf_dots++;

    // If no memory, DAP inactive - this is not critical problem
    m_dap_ht  = (allowed_len | m_gw_suf_len)? (DNSAP*)calloc(EMCDNS_DAPSIZE, sizeof(DNSAP)) : NULL; 
    m_daprand = GetRand(0xffffffff) | 1; 

    m_value  = (char *)malloc(VAL_SIZE + BUF_SIZE + 2 + 
	    m_gw_suf_len + allowed_len + local_len + 4);
 
    if(m_value == NULL) {
      perror("EmcDns::Reset: Cannot allocate buffer");
      closesocket(m_sockfd);
      return -5; // no memory for buffers
    }

    m_buf    = (uint8_t *)(m_value + VAL_SIZE);
    m_bufend = m_buf + MAX_OUT;
    char *varbufs = m_value + VAL_SIZE + BUF_SIZE + 2;

    m_gw_suffix = m_gw_suf_len?
      strcpy(varbufs, gw_suffix) : NULL;
    
    // Create array of allowed TLD-suffixes
    if(allowed_len) {
      m_allowed_base = strcpy(varbufs + m_gw_suf_len + 1, allowed_suff);
      uint8_t pos = 0, step = 0; // pos, step for double hashing
      for(char *p = m_allowed_base + allowed_len; p > m_allowed_base; ) {
	char c = *--p;
	if(c ==  '|' || c <= 040) {
	  *p = pos = step = 0;
	  continue;
	}
	if(c == '.') {
	  if(p[1] > 040) { // if allowed domain is not empty - save it into ht
	    step |= 1;
	    if(m_verbose > 3)
	      printf("\tEmcDns::Reset: Insert TLD=%s: pos=%u step=%u\n", p + 1, pos, step);
	    do 
	      pos += step;
            while(m_ht_offset[pos] != 0);
	    m_ht_offset[pos] = p + 1 - m_allowed_base;
	    m_allowed_qty++;
	  }
	  *p = pos = step = 0;
	  continue;
	}
        pos  = ((pos >> 7) | (pos << 1)) + c;
	step = ((step << 5) - step) ^ c; // (step * 31) ^ c
      } // for
    } // if(allowed_len)

    if(local_len) {
      char *p = m_local_base = (char*)memcpy(varbufs + m_gw_suf_len + 1 + allowed_len + 1, local_tmp, local_len) - 1;
      // and populate hashtable with offsets
      while(++p < m_local_base + local_len) {
	char *p_eq = strchr(p, '=');
	if(p_eq == NULL)
	  break;
        char *p_h = p_eq;
        *p_eq++ = 0; // CLR = and go to data
        uint8_t pos = 0, step = 0; // pos, step for double hashing
	while(--p_h >= p) {
          pos  = ((pos >> 7) | (pos << 1)) + *p_h;
	  step = ((step << 5) - step) ^ *p_h; // (step * 31) ^ c
        } // while
	step |= 1;
	if(m_verbose > 3)
	  printf("\tEmcDns::Reset: Insert Local:[%s]->[%s] pos=%u step=%u\n", p, p_eq, pos, step);
	do 
	  pos += step;
        while(m_ht_offset[pos] != 0);
	m_ht_offset[pos] = m_local_base - p; // negative value - flag LOCAL
	p = strchr(p_eq, 0); // go to the next local record
      } // while
    } //  if(local_len)

    // Create own listener, only if GUI; 
    // Otherwise, Run() will be called from AppInit2
#ifdef QT_GUI
    // Create listener thread
    if (!CreateThread(StatRun, this))
    {
      perror("EmcDns::Reset: Cannot create thread");
      closesocket(m_sockfd);
      free(m_value);
      return -6; // cannot create inner thread
    }
#endif

    if(m_verbose > 0)
	 printf("EmcDns::Reset: Created/Attached: %s:%u; Qty=%u:%u\n", 
		 m_address.sin_addr.s_addr == INADDR_ANY? "INADDR_ANY" : bind_ip, 
		 port_no, m_allowed_qty, local_qty);
  } // if(port_no != 0)
  
  return m_port = port_no;
} // EmcDns::Reset

/*---------------------------------------------------*/

void EmcDns::StatRun(void *p) {
  EmcDns *obj = (EmcDns*)p;
  obj->Run();
  ExitThread(0);
} // EmcDns::StatRun

/*---------------------------------------------------*/
void EmcDns::Run() {
  if(m_verbose > 2) printf("EmcDns::Run: started\n");
  for( ; ; ) {
    m_addrLen = sizeof(m_clientAddress);
    m_rcvlen  = recvfrom(m_sockfd, (char *)m_buf, BUF_SIZE, 0,
	            (struct sockaddr *) &m_clientAddress, &m_addrLen);
    if(m_rcvlen <= 0)
	break;

    DNSAP *dap = NULL;

    if(m_dap_ht == NULL || (dap = CheckDAP(m_clientAddress.sin_addr.s_addr)) != NULL) {
      m_buf[BUF_SIZE] = 0; // Set terminal for infinity QNAME
      HandlePacket();

      sendto(m_sockfd, (const char *)m_buf, m_snd - m_buf, MSG_NOSIGNAL,
	             (struct sockaddr *) &m_clientAddress, m_addrLen);

      if(dap != NULL)
        dap->ed_size += (m_snd - m_buf) >> 6;
    } // dap check
  } // for

  if(m_verbose > 2) printf("EmcDns::Run: Received Exit packet_len=%d\n", m_rcvlen);

} //  EmcDns::Run

/*---------------------------------------------------*/

void EmcDns::HandlePacket() {
  if(m_verbose > 2) printf("EmcDns::HandlePacket: Handle packet_len=%d\n", m_rcvlen);

  m_hdr = (DNSHeader *)m_buf;
  // Decode input header from network format
  m_hdr->Transcode();

  m_rcv = m_buf + sizeof(DNSHeader);
  m_rcvend = m_snd = m_buf + m_rcvlen;

  if(m_verbose > 3) {
    printf("\tEmcDns::HandlePacket: msgID  : %d\n", m_hdr->msgID);
    printf("\tEmcDns::HandlePacket: Bits   : %04x\n", m_hdr->Bits);
    printf("\tEmcDns::HandlePacket: QDCount: %d\n", m_hdr->QDCount);
    printf("\tEmcDns::HandlePacket: ANCount: %d\n", m_hdr->ANCount);
    printf("\tEmcDns::HandlePacket: NSCount: %d\n", m_hdr->NSCount);
    printf("\tEmcDns::HandlePacket: ARCount: %d\n", m_hdr->ARCount);
  }
  // Assert following 3 counters and bits are zero
//*  uint16_t zCount = m_hdr->ANCount | m_hdr->NSCount | m_hdr->ARCount | (m_hdr->Bits & (m_hdr->QR_MASK | m_hdr->TC_MASK));
  uint16_t zCount = m_hdr->ANCount | m_hdr->NSCount | (m_hdr->Bits & (m_hdr->QR_MASK | m_hdr->TC_MASK));

  // Clear answer counters - maybe contains junk from client
  //* m_hdr->ANCount = m_hdr->NSCount = m_hdr->ARCount = 0;
  m_hdr->ANCount = m_hdr->NSCount = m_hdr->ARCount = 0;
  m_hdr->Bits   |= m_hdr->QR_MASK; // Change Q->R

  do {
    // check flags QR=0 and TC=0
    if(m_hdr->QDCount == 0 || zCount != 0) {
      m_hdr->Bits |= 1; // Format error, expected request
      break;
    }

    uint16_t opcode = m_hdr->Bits & m_hdr->OPCODE_MASK;

    if(opcode != 0) {
      m_hdr->Bits |= 4; // Not implemented; handle standard query only
      break;
    }

    if(!IsSynchronized()) {
      m_hdr->Bits |= 2; // Server failure - not available valud nameindex DB yet
      break;
    }

    // Handle questions here
    for(uint16_t qno = 0; qno < m_hdr->QDCount && m_snd < m_bufend; qno--) {
      uint16_t rc = HandleQuery();
      if(rc) {
	m_hdr->Bits |= rc;
	break;
      }
    }
  } while(false);

  // Remove AR-section from request, if exist
  int ar_len = m_rcvend - m_rcv;

  if(ar_len < 0) {
      m_hdr->Bits |= 1; // Format error, RCV pointer is over
  }

  if(ar_len > 0) {
    memmove(m_rcv, m_rcvend, m_snd - m_rcvend);
    m_snd -= ar_len;
  }

  // Truncate answer, if needed
  if(m_snd >= m_bufend) {
    m_hdr->Bits |= m_hdr->TC_MASK;
    m_snd = m_buf + MAX_OUT;
  }
  // Encode output header into network format
  m_hdr->Transcode();
} // EmcDns::HandlePacket

/*---------------------------------------------------*/
uint16_t EmcDns::HandleQuery() {
  // Decode qname
  uint8_t key[BUF_SIZE];				// Key, transformed to dot-separated LC
  uint8_t *key_end = key;
  uint8_t *domain_ndx[MAX_DOM];				// indexes to domains
  uint8_t **domain_ndx_p = domain_ndx;			// Ptr to end

  // m_rcv is pointer to QNAME
  // Set reference to domain label
  m_label_ref = (m_rcv - m_buf) | 0xc000;

  // Convert DNS request (QNAME) to dot-separated printed domaon name in LC
  // Fill domain_ndx - indexes for domain entries
  uint8_t dom_len;
  while((dom_len = *m_rcv++) != 0) {
    // wrong domain length | key too long, over BUF_SIZE | too mant domains, max is MAX_DOM
    if((dom_len & 0xc0) || key_end >= key + BUF_SIZE || domain_ndx_p >= domain_ndx + MAX_DOM)
      return 1; // Invalid request
    *domain_ndx_p++ = key_end;
    do {
      *key_end++ = tolower(*m_rcv++);
    } while(--dom_len);
    *key_end++ = '.'; // Set DOT at domain end
  }
  *--key_end = 0; // Remove last dot, set EOLN

  if(m_verbose > 3) 
    printf("EmcDns::HandleQuery: Translated domain name: [%s]; DomainsQty=%u\n", key, domain_ndx_p - domain_ndx);

  uint16_t qtype  = *m_rcv++; qtype  = (qtype  << 8) + *m_rcv++; 
  uint16_t qclass = *m_rcv++; qclass = (qclass << 8) + *m_rcv++;

  if(m_verbose > 0) 
    printf("EmcDns::HandleQuery: Key=%s QType=%x QClass=%x\n", key, qtype, qclass);

  if(qclass != 1)
    return 4; // Not implemented - support INET only

  // If thid is puplic gateway, gw-suffix can be specified, like 
  // emcdnssuffix=.xyz.com
  // Followind block cuts this suffix, if exist.
  // If received domain name "xyz.com" only, keyp is empty string

  if(m_gw_suf_len) { // suffix defined [public DNS], need to cut
    uint8_t *p_suffix = key_end - m_gw_suf_len;
    if(p_suffix >= key && strcmp((const char *)p_suffix, m_gw_suffix) == 0) {
      *p_suffix = 0; // Cut suffix m_gw_sufix
      key_end = p_suffix;
      domain_ndx_p -= m_gw_suf_dots; 
    } else 
    // check special - if suffix == GW-site, e.g., request: emergate.net
    if(p_suffix == key - 1 && strcmp((const char *)p_suffix + 1, m_gw_suffix + 1) == 0) {
      *++p_suffix = 0; // Set empty search key
      key_end = p_suffix;
      domain_ndx_p = domain_ndx;
    } 
  } // if(m_gw_suf_len)

  // Search for TLD-suffix, like ".coin"
  // If name without dot, like "www", this is candidate for local search
  // Compute 2-hash params for TLD-suffix or local name

  uint8_t pos = 0, step = 0; // pos, step for double hashing

  uint8_t *p = key_end;

  if(m_verbose > 3) 
    printf("EmcDns::HandleQuery: After TLD-suffix cut: [%s]\n", key);

  while(p > key) {
    uint8_t c = *--p;
    if(c == '.')
      break; // this is TLD-suffix
    pos  = ((pos >> 7) | (pos << 1)) + *p;
    step = ((step << 5) - step) ^ *p; // (step * 31) ^ c
  }

  step |= 1; // Set even step for 2-hashing

  if(p == key && m_local_base != NULL) {
    // no TLD suffix, try to search local 1st
    if(LocalSearch(p, pos, step) > 0)
      p = NULL; // local search is OK, do not perform nameindex search
  }

  // If local search is unsuccessful, try to search in the nameindex DB.
  if(p) {
    // Check domain by tld filters, if activated. Otherwise, pass to nameindex as is.
    if(m_allowed_qty) { // Activated TLD-filter
      if(*p != '.') {
        if(m_verbose > 3) 
  	  printf("EmcDns::HandleQuery: TLD-suffix is not specified in given key=%s; return NXDOMAIN\n", p, key);
	return 3; // TLD-suffix is not specified, so NXDOMAIN
      } 
      p++; // Set PTR after dot, to the suffix
      do {
        pos += step;
        if(m_ht_offset[pos] == 0) {
          if(m_verbose > 3) 
  	    printf("EmcDns::HandleQuery: TLD-suffix=[.%s] in given key=%s is not allowed; return NXDOMAIN\n", p, key);
	  return 3; // Reached EndOfList, so NXDOMAIN
        } 
      } while(m_ht_offset[pos] < 0 || strcmp((const char *)p, m_allowed_base + m_ht_offset[pos]) != 0);
    } // if(m_allowed_qty)

    uint8_t **cur_ndx_p, **prev_ndx_p = domain_ndx_p - 2;
    if(prev_ndx_p < domain_ndx) 
      prev_ndx_p = domain_ndx;
#if 0
    else {
      // 2+ domain level. 
      // Try to adjust TLD suffix for peering GW-site, like opennic.coin
      if(strncmp((const char *)(*prev_ndx_p), "opennic.", 8) == 0)
        strcpy((char*)domain_ndx_p[-1], "*"); // substitute TLD to '*'; don't modify domain_ndx_p[0], for keep TLD size for REF
    }
#endif
 
    // Search in the nameindex db. Possible to search filtered indexes, or even pure names, like "dns:www"

    bool step_next;
    do {
      cur_ndx_p = prev_ndx_p;
      if(Search(*cur_ndx_p) <= 0) // Result saved into m_value
	return 3; // empty answer, not found, return NXDOMAIN
      if(cur_ndx_p == domain_ndx)
	break; // This is 1st domain (last in the chain), go to answer
      // Try to search allowance in SD=list for step down
      prev_ndx_p = cur_ndx_p - 1;
      int domain_len = *cur_ndx_p - *prev_ndx_p - 1;
      char val2[VAL_SIZE];
      char *tokens[MAX_TOK];
      step_next = false;
      int sdqty = Tokenize("SD", ",", tokens, strcpy(val2, m_value));
      while(--sdqty >= 0 && !step_next)
        step_next = strncmp((const char *)*prev_ndx_p, tokens[sdqty], domain_len) == 0;

      // if no way down - maybe, we can create REF-answer from NS-records
      if(step_next == false && TryMakeref(m_label_ref + (*cur_ndx_p - key)))
	return 0;
      // if cannot create REF - just ANSWER for parent domain (ignore prefix)
    } while(step_next);
    
  } // if(p) - ends of DB search 

  // There is generate ANSWER section
  { // Extract TTL
    char val2[VAL_SIZE];
    char *tokens[MAX_TOK];
    int ttlqty = Tokenize("TTL", NULL, tokens, strcpy(val2, m_value));
    m_ttl = ttlqty? atoi(tokens[0]) : 24 * 3600;
  }
  
  if(qtype == 0xff) { // ALL Q-types
    char val2[VAL_SIZE];
    // List values for ANY:    A NS CNA PTR MX AAAA
    const uint16_t q_all[] = { 1, 2, 5, 12, 15, 28, 0 };
    for(const uint16_t *q = q_all; *q; q++)
      Answer_ALL(*q, strcpy(val2, m_value));
  } else 
      Answer_ALL(qtype, m_value);
  return 0;
} // EmcDns::HandleQuery

/*---------------------------------------------------*/
int EmcDns::TryMakeref(uint16_t label_ref) {
  char val2[VAL_SIZE];
  char *tokens[MAX_TOK];
  int ttlqty = Tokenize("TTL", NULL, tokens, strcpy(val2, m_value));
  m_ttl = ttlqty? atoi(tokens[0]) : 24 * 3600;
  uint16_t orig_label_ref = m_label_ref;
  m_label_ref = label_ref;
  Answer_ALL(2, strcpy(val2, m_value));
  m_label_ref = orig_label_ref;
  m_hdr->NSCount = m_hdr->ANCount;
  m_hdr->ANCount = 0;
  printf("EmcDns::TryMakeref: Generated REF NS=%u\n", m_hdr->NSCount);
  return m_hdr->NSCount;
} //  EmcDns::TryMakeref
/*---------------------------------------------------*/

int EmcDns::Tokenize(const char *key, const char *sep2, char **tokens, char *buf) {
  int tokensN = 0;

  // Figure out main separator. If not defined, use |
  char mainsep[2];
  if(*buf == '~') {
    buf++;
    mainsep[0] = *buf++;
  } else
     mainsep[0] = '|';
  mainsep[1] = 0;

  for(char *token = strtok(buf, mainsep);
    token != NULL; 
      token = strtok(NULL, mainsep)) {
      // printf("Token:%s\n", token);
      char *val = strchr(token, '=');
      if(val == NULL)
	  continue;
      *val = 0;
      if(strcmp(key, token)) {
	  *val = '=';
	  continue;
      }
      val++;
      // Uplevel token found, tokenize value if needed
      // printf("Found: key=%s; val=%s\n", key, val);
      if(sep2 == NULL || *sep2 == 0) {
	tokens[tokensN++] = val;
	break;
      }
     
      // if needed. redefine sep2
      char sepulka[2];
      if(*val == '~') {
	  val++;
	  sepulka[0] = *val++;
	  sepulka[1] = 0;
	  sep2 = sepulka;
      }
      // Tokenize value
      for(token = strtok(val, sep2); 
	 token != NULL && tokensN < MAX_TOK; 
	   token = strtok(NULL, sep2)) {
	  // printf("Subtoken=%s\n", token);
	  tokens[tokensN++] = token;
      }
      break;
  } // for - big tokens (MX, A, AAAA, etc)
  return tokensN;
} // EmcDns::Tokenize

/*---------------------------------------------------*/

void EmcDns::Answer_ALL(uint16_t qtype, char *buf) {
  const char *key;
  switch(qtype) {
      case  1 : key = "A";      break;
      case  2 : key = "NS";     break;
      case  5 : key = "CNAME";  break;
      case 12 : key = "PTR";    break;
      case 15 : key = "MX";     break;
      case 16 : key = "TXT";    break;
      case 28 : key = "AAAA";   break;
      default: return;
  } // swithc

  char *tokens[MAX_TOK];
  int tokQty = Tokenize(key, ",", tokens, buf);

  if(m_verbose > 0) printf("EmcDns::Answer_ALL(QT=%d, key=%s); TokenQty=%d\n", qtype, key, tokQty);

  // Shuffle tokens for randomization output order
  for(int i = tokQty; i > 1; ) {
    int randndx = GetRand(i);
    char *tmp = tokens[randndx];
    --i;
    tokens[randndx] = tokens[i];
    tokens[i] = tmp;
  }

  for(int tok_no = 0; tok_no < tokQty; tok_no++) {
      if(m_verbose > 1) 
	printf("\tEmcDns::Answer_ALL: Token:%u=[%s]\n", tok_no, tokens[tok_no]);
      Out2(m_label_ref);
      Out2(qtype); // A record, or maybe something else
      Out2(1); //  INET
      Out4(m_ttl);
      switch(qtype) {
	case 1 : Fill_RD_IP(tokens[tok_no], AF_INET);  break;
	case 28: Fill_RD_IP(tokens[tok_no], AF_INET6); break;
	case 2 :
	case 5 :
	case 12: Fill_RD_DName(tokens[tok_no], 0, 0); break; // NS,CNAME,PTR
	case 15: Fill_RD_DName(tokens[tok_no], 2, 0); break; // MX
	case 16: Fill_RD_DName(tokens[tok_no], 0, 1); break; // TXT
	default: break;
      } // swithc
  } // for
  m_hdr->ANCount += tokQty;
} // EmcDns::Answer_A 

/*---------------------------------------------------*/

void EmcDns::Fill_RD_IP(char *ipddrtxt, int af) {
  uint16_t out_sz;
  switch(af) {
      case AF_INET : out_sz = 4;  break;
      case AF_INET6: out_sz = 16; break;
      default: return;
  }
  Out2(out_sz);
  if(inet_pton(af, ipddrtxt, m_snd)) 
    m_snd += out_sz;
  else
    m_snd -= 2, m_hdr->ANCount--;
#if 0  
  return;

  in_addr_t inetaddr = inet_addr(ipddrtxt);
  Out2(htons(sizeof(inetaddr)));
  Out4(inetaddr);
#endif
} // EmcDns::Fill_RD_IP

/*---------------------------------------------------*/

void EmcDns::Fill_RD_DName(char *txt, uint8_t mxsz, int8_t txtcor) {
  uint8_t *snd0 = m_snd;
  m_snd += 3 + mxsz; // skip SZ and sz0
  uint8_t *tok_sz = m_snd - 1;
  uint16_t mx_pri = 1; // Default MX priority
  char c;

  uint8_t *bufend = m_snd + 255;

  if(m_bufend < bufend)
    bufend = m_bufend;

  do {
    c = *m_snd++ = *txt++;
    if(c == '.') {
      *tok_sz = m_snd - tok_sz - 2;
      tok_sz  = m_snd - 1;
    }
    if(c == ':' && mxsz) { // split for MX only
      c = m_snd[-1] = 0;
      mx_pri = atoi(txt);
    }
  } while(c && m_snd < bufend);

  *tok_sz = m_snd - tok_sz - 2;

  // Remove trailing \0 at end of text
  m_snd -= txtcor;

  uint16_t len = m_snd - snd0 - 2;
  *snd0++ = len >> 8;
  *snd0++ = len;
  if(mxsz) {
    *snd0++ = mx_pri >> 8;
    *snd0++ = mx_pri;
  }
} // EmcDns::Fill_RD_DName

/*---------------------------------------------------*/
/*---------------------------------------------------*/

int EmcDns::Search(uint8_t *key) {
  if(m_verbose > 1) 
    printf("EmcDns::Search(%s)\n", key);

  string value;
  if (!hooks->getNameValue(string("dns:") + (const char *)key, value))
    return 0;

  strcpy(m_value, value.c_str());
  return 1;
} //  EmcDns::Search

/*---------------------------------------------------*/

int EmcDns::LocalSearch(const uint8_t *key, uint8_t pos, uint8_t step) {
  if(m_verbose > 1) 
    printf("EmcDns::LocalSearch(%s, %u, %u) called\n", key, pos, step);
    do {
      pos += step;
      if(m_ht_offset[pos] == 0) {
        if(m_verbose > 3) 
  	  printf("EmcDns::LocalSearch: Local key=[%s] not found; go to nameindex search\n", key);
         return 0; // Reached EndOfList 
      } 
    } while(m_ht_offset[pos] > 0 || strcmp((const char *)key, m_local_base - m_ht_offset[pos]) != 0);

  strcpy(m_value, strchr(m_local_base - m_ht_offset[pos], 0) + 1);

  return 1;
} // EmcDns::LocalSearch


/*---------------------------------------------------*/
// Returns x>0 = hash index to update size; x<0 = disable;
DNSAP *EmcDns::CheckDAP(uint32_t ip_addr) { 
  uint32_t hash = ip_addr * m_daprand;
  hash ^= hash >> 16;
  hash += hash >> 8;
  DNSAP *dap = m_dap_ht + (hash & (EMCDNS_DAPSIZE - 1));
  uint16_t timestamp = time(NULL) >> 6; // time in 64s ticks
  uint16_t dt = timestamp - dap->timestamp;
  dap->ed_size = (dt > 15? 0 : dap->ed_size >> dt) + 1;
  dap->timestamp = timestamp;
  return (dap->ed_size <= EMCDNS_DAPTRESHOLD)? dap : NULL;
} // EmcDns::CheckDAP 


/*
 * Simple DNS server for EmerCoin project
 *
 * Lookup for names like "dns:some-name" in the local nameindex database.
 * Database is updated from blockchain, and keeps NMC-transactions.
 *
 * Supports standard RFC1034 UDP DNS protocol only
 *
 * Supported fields: A, AAAA, NS, PTR, MX, TXT, CNAME
 * Does not support: SOA, WKS
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
// for MinGW build
#ifndef MSG_NOSIGNAL
# define MSG_NOSIGNAL 0
#endif
#else
#include <arpa/inet.h>
#include <netinet/in.h>
#endif

#include <ctype.h>

#include <namecoin.h>
#include <emcdns.h>
#include <random.h>
#include <validation.h>
#include <base58.h>
#include <netbase.h>
#include <key_io.h>
#include <util/validation.h>
#include <wallet/wallet.h>

#ifdef _MSC_VER
    #include <malloc.h>  // For Microsoft Visual C++
#else
    #include <alloca.h>  // For GCC, Clang & MinGW
#endif

/*---------------------------------------------------*/
/*
 * m_verbose legend:
 * 0 = disabled
 * 1 = error
 * 2 = start/stop, set domains, etc
 * 3 = single statistic message for packet received
 * 4 = handle packets, DAP blocking
 * 5 = details for handle packets
 * 6 = more details, debug info
 */
/*---------------------------------------------------*/

#define MAX_OUT  512	// Old DNS restricts UDP to 512 bytes; keep compatible
#define BUF_SIZE (2 * MAX_OUT)
#define MAX_TOK  64	// Maximal TokenQty in the vsl_list, like A=IP1,..,IPn
#define MAX_DOM  20	// Maximal domain level; min 10 is needed for NAPTR E164
#define MAX_ENUM 40	// Maximal ENUM domain levels; min 10 is needed for NAPTR E164
#define MAX_DOMTOKENS 40 // MAx of (MAX_DOM, MAX_ENUM)

#define VAL_SIZE (MAX_VALUE_LENGTH + 16)
#define DNS_PREFIX "dns"
#define REDEF_SYM  '~'

// HT offset contains it for ENUM SPFUN
#define ENUM_FLAG	(1 << 14)
#define QTYPE_ADDL      (1 << 15) // Additional with specified qtype
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

const char *inet_ntop(int af, const void *src, char *dst, socklen_t size) {
  if(size > 16) size = 16;
  uint8_t *p = (uint8_t *)src;
  const char *rc = dst;
  while(size--)
    dst += sprintf(dst, "%02x:", *p++);
  dst[-1] = 0;
  return rc;
}

char *strsep(char **s, const char *ct)
{
    char *sstart = *s;
    char *end;

    if (sstart == NULL)
        return NULL;

    end = strpbrk(sstart, ct);
    if (end)
        *end++ = '\0';
    *s = end;
    return sstart;
}
#endif

/*---------------------------------------------------*/
const static char *decodeQtype(uint16_t x) {
  switch(x) {
      case 1: return "A";
      case 2: return "NS";
      case 5: return "CNAME";
      case 6:    return "-SOA";
      case 12: return "PTR";
      case 15: return "MX";
      case 16 :return "TXT";
      case 28: return "AAAA";
      case 33:   return "SRV";
      case 52:   return "TLSA";
      case 257:   return "CAA";
      case 35:   return "-NAPTR";
      case 0xff: return "-ALL";
      default:   return "-?";
  }
};
/*---------------------------------------------------*/

EmcDns::EmcDns(const char *bind_ip, uint16_t port_no,
	  const char *gw_suffix, const char *allowed_suff, const char *local_fname,
	  uint32_t dapsize, uint32_t daptreshold,
	  const char *enums, const char *tollfree, uint8_t verbose)
    : m_status(-1), m_flags(0), m_thread(StatRun, this) {

    // Clear vars [m_hdr..m_verbose)
    memset(&m_hdr, 0, &m_verbose - (uint8_t *)&m_hdr); // Clear previous state
    m_verbose = verbose;

    // Create and bind socket IPv6, if possible
    int ret = socket(PF_INET6, SOCK_DGRAM, 0);
    if(ret < 0) {
        // Cannot create IPv46 - try IPv4
        // Create and bind socket - IPv4 Only
        ret = socket(PF_INET, SOCK_DGRAM, 0);
        if(ret < 0)
            throw runtime_error("EmcDns::EmcDns: Cannot create ipv4 socket");
        m_sockfd = ret;

        struct sockaddr_in sin;
        const int sinlen = sizeof(struct sockaddr_in);
        memset(&sin, 0, sinlen);
        sin.sin_port = htons(port_no);
        sin.sin_family = AF_INET;

        if(*bind_ip == 0 || inet_pton(AF_INET, bind_ip, &sin.sin_addr) != 1) {
            sin.sin_addr.s_addr = INADDR_ANY;
            bind_ip = NULL;
        }

        if(::bind(m_sockfd, (struct sockaddr *)&sin, sinlen) < 0) {
            char buf[80];
            sprintf(buf, "EmcDns::EmcDns: Cannot bind to IPv4 port %u", port_no);
            throw runtime_error(buf);
        }
    } else {
        // Setup IPv46 socket
        m_sockfd = ret;
        struct sockaddr_in6 sin6;
        const int sin6len = sizeof(struct sockaddr_in6);
        memset(&sin6, 0, sin6len);
        sin6.sin6_port = htons(port_no);
        sin6.sin6_family = AF_INET6;

        if(*bind_ip == 0 || inet_pton(AF_INET6, bind_ip, &sin6.sin6_addr) != 1) {
            sin6.sin6_addr = in6addr_any;
            bind_ip = NULL;
        }
        int no = 0;
#ifdef WIN32
        if(setsockopt(m_sockfd, IPPROTO_IPV6, IPV6_V6ONLY, (char *)&no, sizeof(no)) < 0)
#else
        if(setsockopt(m_sockfd, IPPROTO_IPV6, IPV6_V6ONLY, (void *)&no, sizeof(no)) < 0)
#endif
            throw runtime_error("EmcDns::EmcDns: Cannot switch socket to IPV4 compatibility mode");

        if(::bind(m_sockfd, (struct sockaddr *)&sin6, sin6len) < 0) {
            char buf[80];
            sprintf(buf, "EmcDns::EmcDns: Cannot bind to IPv46 port %u", port_no);
            throw runtime_error(buf);
        }
    } // IPv46

    // Upload Local DNS entries
    // Create temporary local buf on stack
    int local_len = 0;
    char local_tmp[1 << 15]; // max 32Kb
    FILE *flocal;
    uint8_t local_qty = 0;
    if(local_fname != NULL && (flocal = fopen(local_fname, "r")) != NULL) {
      char *rd = local_tmp;
      while(rd < local_tmp + sizeof(local_tmp) - 2000 && fgets(rd, 2000, flocal)) {
	if(*rd < '.' || *rd == ';')
	  continue;
	char *p = strchr(rd, '=');
	if(p == NULL)
	  continue;
        if(*rd == '.')
          m_flags |= FLAG_LOCAL_SD; // Future local search for subdomains, too
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
    int gw_suf_len  = m_gw_suf_len = gw_suffix == NULL? 0 : strlen(gw_suffix);

    // Activate DAP only if specidied dapsize
    // If no memory, DAP is inactive - this is not critical problem
    if(dapsize) {
      dapsize += dapsize - 1;
      do m_dapmask = dapsize; while(dapsize &= dapsize - 1); // compute mask as 2^N
      m_dap_ht = (DNSAP*)calloc(m_dapmask, sizeof(DNSAP));
      m_dapmask--;
      GetRandBytes((uint8_t *)&m_daprand, sizeof(m_daprand));
      m_daprand |= 1;
      m_dap_treshold = daptreshold;
    }

    // Common buffers structure:
    m_buf = (uint8_t *)malloc(
              BUF_SIZE // I/O buf,               1K
            + BUF_SIZE // Sanity check O-buf,    1K
            + VAL_SIZE // Sanity check outvalue, 20K
            + VAL_SIZE // Blockchain value,      20K
            + 2        // ?
            + gw_suf_len + allowed_len + local_len + 4);

    if(m_buf == NULL)
      throw runtime_error("EmcDns::EmcDns: Cannot allocate buffer");

    // Assign data buffers inside m_value hyper-array
    m_value = (char *)m_buf + BUF_SIZE + BUF_SIZE + VAL_SIZE;
    char *varbufs = (char *)m_buf + 2 * (VAL_SIZE + BUF_SIZE) + 2;

    // Temporary use m_value for parse enum-verifiers and toll-free lists, if exist

    if(enums && *enums) {
      char *str = strcpy(m_value, enums);
      Verifier empty_ver;
      while(char *p_tok = strsep(&str, "|,"))
        if(*p_tok) {
	  if(m_verbose > 1)
	  LogPrintf("    EmcDns::EmcDns: enumtrust=%s\n", p_tok);
          m_verifiers[string(p_tok)] = empty_ver;
	}
    } // ENUMs completed


    if(gw_suf_len) {
      // Copy suffix to local storage
      m_gw_suffix = strcpy(varbufs, gw_suffix);
      // Try to search translation to internal suffix, like ".e164.org|.enum"
      m_gw_suffix_replace = strchr(m_gw_suffix, '|');
      if(m_gw_suffix_replace) {
        m_gw_suf_len = m_gw_suffix_replace - m_gw_suffix; // adjust to a real suffix
        *m_gw_suffix_replace++ = 0; // set ptr to ".enum"
        m_gw_suffix_replace_len = strlen(m_gw_suffix_replace);
        m_gw_suf_dots = -1;
      } else
        m_gw_suffix_replace = m_gw_suffix + gw_suf_len; // pointer to \0
      // Compute dots in the gw-suffix
      for(const char *p = m_gw_suffix; *p; p++)
        if(*p == '.')
          m_gw_suf_dots++;
      if(m_verbose > 1)
	 LogPrintf("EmcDns::EmcDns: Setup translate GW-suffix: [%s:%d]->[%s] Ncut=%d\n",
                 m_gw_suffix, m_gw_suf_len, m_gw_suffix_replace, m_gw_suf_dots);
    }

    // Create array of allowed TLD-suffixes
    if(allowed_len) {
      m_allowed_base = strcpy(varbufs + gw_suf_len + 1, allowed_suff);
      uint8_t pos = 0, step = 0; // pos, step for double hashing
      for(char *p = m_allowed_base + allowed_len; p > m_allowed_base; ) {
	char c = *--p;
	if(c ==  '|' || c <= 040) {
	  *p = pos = step = 0;
	  continue;
	}
        // Separator for allowed TLD definitions like:
        // emcdnsallowed=40$enum|.coin|~freenum|!rus
	if(c == '.' || c == '$' || c == '~' || c == '!') {
	  if(p[1] > 040) { // if allowed domain is not empty - save it into ht
	    step |= 1;
	    do
	      pos += step;
            while(m_ht_offset[pos] != 0);
	    m_ht_offset[pos] = p + 1 - m_allowed_base;
           const char *dnstype = NULL;
            switch(c) {
              case '.':
                dnstype = "DNS-no-sig";
                *p = 0200 | MAX_DOM; // Set flag signature-no-check (sigOK)
                break;
              case '!':
                dnstype = "DNS-sig";
                *p = MAX_DOM;
                break;
              case '~':
                dnstype = "ENUM-no-sig";
                *p = 0200 | MAX_ENUM; // Set flag signature-no-check (sigOK)
                m_ht_offset[pos] |= ENUM_FLAG;
                break;
              case '$':
                dnstype = "ENUM-sig";
                *p = MAX_ENUM;
                m_ht_offset[pos] |= ENUM_FLAG;
                break;
            } // switch
            // Compute actual subdomain chain lenght
            char *pp = p; // ref to $/./!/~
            while(--pp >= m_allowed_base && *pp >= '0' && *pp <= '9');
            if(++pp < p)
              *p = (*p & 0200) | atoi(pp);
            m_allowed_qty++;
	    if(m_verbose > 1)
	      LogPrintf("EmcDns::EmcDns: Insert %s TLD=%s:%u\n", dnstype, p + 1, *p & 0177);
	  }
	  pos = step = 0;
	  continue;
	} // domain char [.!$~]
        pos  = ((pos >> 7) | (pos << 1)) + c;
	step = ((step << 5) - step) ^ c; // (step * 31) ^ c
      } // for
    } // if(allowed_len)

    if(local_len) {
      char *p = m_local_base = (char*)memcpy(varbufs + gw_suf_len + 1 + allowed_len + 1, local_tmp, local_len) - 1;
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
	if(m_verbose > 1)
	  LogPrintf("    EmcDns::EmcDns: Insert Local:[%s]->[%s] pos=%u step=%u\n", p, p_eq, pos, step);
	do
	  pos += step;
        while(m_ht_offset[pos] != 0);
	m_ht_offset[pos] = m_local_base - p; // negative value - flag LOCAL
	p = strchr(p_eq, 0); // go to the next local record
      } // while
    } //  if(local_len)

    if(m_verbose > 1)
	 LogPrintf("EmcDns::EmcDns: Created/Attached: [%s]:%u; TLD=%u Local=%u\n",
		 (bind_ip == NULL)? "INADDR_ANY" : bind_ip,
		 port_no, m_allowed_qty, local_qty);

    // Hack - pass TF file list through m_value to HandlePacket()

    if(tollfree && *tollfree) {
      if(m_verbose > 1)
	LogPrintf("    EmcDns::EmcDns: Setup deferred toll-free=%s\n", tollfree);
      strcpy(m_value, tollfree);
    } else
      m_value[0] = 0;

    m_self_ns = gArgs.GetArg("-selfns", "localhost");
    if(m_self_ns.size() > 512) {
	LogPrintf("    EmcDns::EmcDns: too long selfns=%s; ignored\n", m_self_ns.c_str());
        m_self_ns.clear();
    }

    m_status = 1; // Active, and maybe download
} // EmcDns::EmcDns
/*---------------------------------------------------*/
void EmcDns::AddTF(char *tf_tok) {
  // Skip comments and empty lines
  if(tf_tok[0] < '0')
    return;

  // Clear TABs and SPs at the end of the line
  char *end = strchr(tf_tok, 0);
  while(*--end <= 040) {
    *end = 0;
    if(end <= tf_tok)
      return;
  }

  if(tf_tok[0] == '=') {
    if(tf_tok[1])
      m_tollfree.push_back(TollFree(tf_tok + 1));
  } else
      if(!m_tollfree.empty())
        m_tollfree.back().e2u.push_back(string(tf_tok));

  if(m_verbose > 1)
    LogPrintf("    EmcDns::AddTF: Added token [%s] tf/e2u=%u:%u\n", tf_tok, m_tollfree.size(), m_tollfree.back().e2u.size());
} // EmcDns::AddTF

/*---------------------------------------------------*/

EmcDns::~EmcDns() {
    // reset current object to initial state
#ifndef WIN32
    shutdown(m_sockfd, SHUT_RDWR);
#endif
    CloseSocket(m_sockfd);
    MilliSleep(100); // Allow 0.1s my thread to exit
    // m_thread.join();
    free(m_buf);
    free(m_dap_ht);
    if(m_verbose > 1)
	 LogPrintf("EmcDns::~EmcDns: Destroyed OK\n");
} // EmcDns::~EmcDns


/*---------------------------------------------------*/

void EmcDns::StatRun(void *p) {
  EmcDns *obj = (EmcDns*)p;
  obj->Run();
//emercoin  ExitThread(0);
} // EmcDns::StatRun

/*---------------------------------------------------*/
void EmcDns::Run() {
  if(m_verbose > 1) LogPrintf("EmcDns::Run: started\n");

  while(m_status < 0) // not initied yet
    MilliSleep(133);

  for( ; ; ) {
    struct sockaddr_in6 sin6;
    socklen_t sin6len = sizeof(struct sockaddr_in6);

    m_rcvlen = recvfrom(m_sockfd, (char *)m_buf, BUF_SIZE, 0,
	            (struct sockaddr *)&sin6, &sin6len);
    if(m_rcvlen <= 0)
	break;

    if(m_dap_ht) {
      uint32_t now = time(NULL);
      if(((now ^ m_daprand) & 0xfffff) == 0) {// ~weekly update daprand
        GetRandBytes((uint8_t *)&m_daprand, sizeof(m_daprand));
        m_daprand |= 1;
      }
      m_timestamp = now >> EMCDNS_DAPSHIFTDECAY; // time in 256s (~4 min)
    }
    if(CheckDAP(&sin6.sin6_addr, sin6len, m_rcvlen >> 5)) {
      m_buf[BUF_SIZE] = 0; // Set terminal for infinity QNAME
      uint16_t rc = HandlePacket();
      uint16_t add_temp = rc == 0? 0 : 100;
      if(rc != 0xDead) {
        uint32_t packet_len = m_snd - m_buf;
        sendto(m_sockfd, (const char *)m_buf, packet_len, MSG_NOSIGNAL,
	             (struct sockaddr *)&sin6, sin6len);
        add_temp += packet_len >> 5; // Add temp for long answer
      } else
          add_temp += 50;
      CheckDAP(&sin6.sin6_addr, sin6len, add_temp); // More heat!
      rc4ok_addentropy(m_rcvlen);
    } // dap check
  } // for

  if(m_verbose > 1) LogPrintf("EmcDns::Run: Received Exit packet_len=%d\n", m_rcvlen);

} //  EmcDns::Run

/*---------------------------------------------------*/

int EmcDns::HandlePacket() {
  if(m_verbose > 3) LogPrintf("*    EmcDns::HandlePacket: Handle packet_len=%d\n", m_rcvlen);

  m_hdr = (DNSHeader *)m_buf;
  // Decode input header from network format
  m_hdr->Transcode();

  m_rcv = m_buf + sizeof(DNSHeader);
  m_rcvend = m_snd = m_buf + m_rcvlen;
  m_obufend = m_snd + MAX_OUT; // ptr to output bufend - 512b from m_rcvend

  if(m_verbose > 4) {
    LogPrintf("    EmcDns::HandlePacket: msgID  : %d\n", m_hdr->msgID);
    LogPrintf("    EmcDns::HandlePacket: Bits   : %04x\n", m_hdr->Bits);
    LogPrintf("    EmcDns::HandlePacket: QDCount: %d\n", m_hdr->QDCount);
    LogPrintf("    EmcDns::HandlePacket: ANCount: %d\n", m_hdr->ANCount);
    LogPrintf("    EmcDns::HandlePacket: NSCount: %d\n", m_hdr->NSCount);
    LogPrintf("    EmcDns::HandlePacket: ARCount: %d\n", m_hdr->ARCount);
  }
  // Assert following 3 counters and bits are zero
  uint16_t zCount = m_hdr->ANCount | m_hdr->NSCount | (m_hdr->Bits & (m_hdr->QR_MASK | m_hdr->TC_MASK));

  // Clear answer counters - maybe contains junk from client
  m_hdr->ANCount = m_hdr->NSCount = m_hdr->ARCount = 0;
  m_hdr->Bits &= m_hdr->RD_MASK;
  m_hdr->Bits |= m_hdr->QR_MASK | m_hdr->AA_MASK;

  uint16_t rc;

  do {
    // check flags QR=0 and TC=0
    if(m_hdr->QDCount == 0 || zCount != 0) {
      rc = 1; // Format error, expected request
      break;
    }

    uint16_t opcode = m_hdr->Bits & m_hdr->OPCODE_MASK;
    if(opcode != 0) {
      rc = 4; // Not implemented; handle standard query only
      break;
    }

    if(m_status) {
      if((m_status = ::ChainstateActive().IsInitialBlockDownload()) != 0) {
        rc = 2; // Server failure - not available valid nameindex DB yet
        break;
      } else {
	// Fill deferred toll-free default entries
        char *tf_str = m_value;
        // Iterate the list of Toll-Free fnames; can be fnames and NVS records
        while(char *tf_fname = strsep(&tf_str, "|")) {
          if(m_verbose > 1)
	    LogPrintf("    EmcDns::HandlePacket: handle deferred toll-free=%s\n", tf_fname);
          if(tf_fname[0] == '@') { // this is NVS record
            string value;
            if(hooks->getNameValue(string(tf_fname + 1), value)) {
              char *tf_val = strcpy(m_value, value.c_str());
              while(char *tf_tok = strsep(&tf_val, "\r\n"))
	        AddTF(tf_tok);
	    }
          } else { // This is file
	    FILE *tf = fopen(tf_fname, "r");
 	    if(tf != NULL) {
	      while(fgets(m_value, VAL_SIZE, tf))
	        AddTF(m_value);
	      fclose(tf);
	    }
          } // if @
        } // while tf_name
      } // m_status #2
    } // m_status #1

    // Handle questions here
    for(uint16_t qno = 0; qno < m_hdr->QDCount && m_snd < m_obufend; qno++) {
      if(m_verbose > 5)
        LogPrintf("    EmcDns::HandlePacket: qno=%u m_hdr->QDCount=%u\n", qno, m_hdr->QDCount);
      rc = HandleQuery();
      if(rc) {
	if(rc == 0xDead)
	  return rc; // DAP or another error - lookup interrupted, don't answer
	break;
      }
    }
  } while(false);

  // Remove AR-section from request, if exist
  int ar_len = m_rcvend - m_rcv;

  if(ar_len < 0)
      rc |= 1; // Format error, RCV pointer is over

  m_hdr->Bits |= rc;

  if(ar_len > 0) {
    memmove(m_rcv, m_rcvend, m_snd - m_rcvend);
    m_snd -= ar_len;
  }

  // Add an empty EDNS RR record for NOERROR answers only
  if((m_hdr->Bits & 0xf) == 0)
    Answer_OPT();

  // Truncate answer, if needed
  if(m_snd >= m_buf + MAX_OUT) {
    m_hdr->Bits |= m_hdr->TC_MASK;
    m_snd = m_buf + MAX_OUT;
  }
  // Encode output header into network format
  m_hdr->Transcode();
  return rc; // answer ready
} // EmcDns::HandlePacket

/*---------------------------------------------------*/
uint16_t EmcDns::HandleQuery() {
  // Decode qname
  uint8_t key[BUF_SIZE];				// Key, transformed to dot-separated LC
  uint8_t *key_end = key;
  uint8_t *domain_ndx[MAX_DOMTOKENS];			// indexes to domains
  uint8_t **domain_ndx_p = domain_ndx;			// Ptr to the end

  // m_rcv is pointer to QNAME
  // Set reference to domain label
  m_label_ref = (m_rcv - m_buf) | 0xc000;

  // Convert DNS request (QNAME) to dot-separated printed domain name in LC
  // Fill domain_ndx - indexes for domain entries
  uint8_t dom_len;
  while((dom_len = *m_rcv++) != 0) {
    // wrong domain length | key too long, over BUF_SIZE | too many domains, max is MAX_DOMTOKENS
    if((dom_len & 0xc0) || key_end >= key + BUF_SIZE || domain_ndx_p >= domain_ndx + MAX_DOMTOKENS)
      return 1; // Invalid request
    *domain_ndx_p++ = key_end;
    do {
      unsigned char c = *m_rcv++;
      if(c <= 'Z')
        c |= 040; // Tolower capital chars, do not need "_"
      *key_end++ = c;
    } while(--dom_len);
    *key_end++ = '.'; // Set DOT at domain end
  } //  while(dom_len)

  uint16_t qtype  = *m_rcv++; qtype  = (qtype  << 8) + *m_rcv++;
  uint16_t qclass = *m_rcv++; qclass = (qclass << 8) + *m_rcv++;

  if(qclass != 1)
    return 4; // Not implemented - support INET only

  *--key_end = 0; // Remove last dot, set EOLN

  if(m_verbose > 4)
    LogPrintf("EmcDns::HandleQuery: Translated domain name: [%s]; DomainsQty=%d\n", key, (int)(domain_ndx_p - domain_ndx));

  // If this is public gateway, gw-suffix can be specified, like
  // emcdnssuffix=.xyz.com
  // Following block cuts this suffix, if exists.
  // If received domain name "xyz.com" only, key is empty string
  if(m_gw_suf_len) { // suffix defined [public DNS], need to cut/replace
    uint8_t *p_suffix = key_end - m_gw_suf_len;
    if(p_suffix >= key && strcmp((const char *)p_suffix, m_gw_suffix) == 0) {
      strcpy((char*)p_suffix, m_gw_suffix_replace);
      key_end = p_suffix + m_gw_suffix_replace_len;
      domain_ndx_p -= m_gw_suf_dots;
    } else
    // check special - if suffix == GW-site, e.g., request: emergate.net
    if(p_suffix == key - 1 && strcmp((const char *)p_suffix + 1, m_gw_suffix + 1) == 0) {
      *++p_suffix = 0; // Set empty search key
      key_end = p_suffix;
      domain_ndx_p = domain_ndx;
    }
  } // if(m_gw_suf_len)

  if(!CheckDAP(key, key - key_end, 0)) {
    if(m_verbose > 3)
      LogPrintf("    EmcDns::HandleQuery: Aborted domain %s by DAP mintemp=%u\n", key, m_mintemp);
    return 0xDead; // Botnet detected, abort query processing
  }

  if(m_verbose > 2)
    LogPrintf("EmcDns::HandleQuery: Key=%s QType=0x%x[%s] mintemp=%u\n", key, qtype, decodeQtype(qtype), m_mintemp);

  // Search for TLD-suffix, like ".coin"
  // If name without dot, like "www", this is candidate for local search
  // Compute 2-hash params for TLD-suffix or local name

  uint8_t pos0 = 0, step0 = 0; // pos, step for double hashing LocalSearch
  uint8_t pos     , step  = 0; // pos, step for double hashing TLD

  uint8_t *p0 = key_end, *p_tld = key;

  if(m_verbose > 4)
    LogPrintf("EmcDns::HandleQuery: After GW-suffix cut: [%s]\n", key);

  while(p0 > key) {
    uint8_t c = *--p0;
    if(c == '.' && step == 0) {
      // this is TLD-suffix - fix TLD params for it
      pos = pos0; step = step0 | 1;
      p_tld = p0;
    } // if(c == '.')
    pos0  = ((pos0 >> 7) | (pos0 << 1)) + c;
    step0 = ((step0 << 5) - step0) ^ c; // (step * 31) ^ c
    if(c == '.' && (m_flags & FLAG_LOCAL_SD) && LocalSearch(p0, pos0, step0 | 1) > 0) { // search there with SDs, like SD.emer.emc
      p_tld = NULL; // local search is OK, do not perform nameindex search
      break;
    }
  } // while(p0 > key)

  step0 |= 1; // Set odd step for 2-hashing

  // Try to search local (like emer.emc) 1st - it has priority over nameindex
  if(p_tld != NULL && LocalSearch(key, pos0, step0) > 0)
    p_tld = NULL; // local search is OK, do not perform nameindex search

  char maxlen_domchain = MAX_DOM | 0200; // default len=20, no SIG check
  // If local search is unsuccessful, try to search in the nameindex DB.
  if(p_tld) {
    if(step == 0) { // pure dotless name, like "coin"
      pos = pos0;
      step = step0;
    }
    // Check domain by tld filters, if activated. Otherwise, pass to nameindex as is.
    if(m_allowed_qty) { // Activated TLD-filter
      if(*p_tld != '.') {
        if(m_verbose > 0)
          LogPrintf("EmcDns::HandleQuery: TLD-suffix=[.%s] is not specified in given key=%s; return NXDOMAIN\n", p_tld, key);
	return 3; // TLD-suffix is not specified, so NXDOMAIN
      }
      p_tld++; // Set PTR after dot, to the suffix lile .[coin]
      const char *allowed_tld;
      do {
        pos += step;
        if(m_ht_offset[pos] == 0) {
          if(m_verbose > 0)
  	    LogPrintf("EmcDns::HandleQuery: TLD-suffix=[.%s] in given key=%s is not allowed; return REFUSED\n", p_tld, key);
	  return 5; // Reached EndOfList, so REFUSED
        }
        allowed_tld = m_allowed_base + (m_ht_offset[pos] & ~ENUM_FLAG);
      } while(m_ht_offset[pos] < 0 || strcmp((const char *)p_tld, allowed_tld) != 0);

      maxlen_domchain = allowed_tld[-1];
      // ENUM SPFUN works only if TLD-filter is active and if requested NAPTR. Otherwise - NXDOMAIN
      if(m_ht_offset[pos] & ENUM_FLAG)
        return qtype == 0x23? SpfunENUM(maxlen_domchain, domain_ndx, domain_ndx_p) : 3;

    } // if(m_allowed_qty)

    bool check_domain_sig = !(maxlen_domchain & 0200);
    maxlen_domchain &= ~0200; // Drop flag SigOK

    // Is not needed, already checked when domain_ndx_p increased
    if(domain_ndx_p - domain_ndx > maxlen_domchain) {
      if(m_verbose > 0)
        LogPrintf("EmcDns::HandleQuery: Requested domain [%s] has too long chain=%d, disallowed for TLD-suffix=[.%s] maxlen=%d; return REFUSED\n",
                key, domain_ndx_p - domain_ndx, p_tld, maxlen_domchain);
      return 5; // Too long subdomains chain, so REFUSED
    }

    uint8_t **cur_ndx_p, **prev_ndx_p = domain_ndx_p - 2;
    if(prev_ndx_p < domain_ndx)
      prev_ndx_p = domain_ndx;
    // Search in the nameindex db. Possible to search filtered indexes, or even pure names, like "dns:www"
    bool step_next;
    do { // Search from up domain to down; start from 2-lvl, like www.[flibusta.lib]
      cur_ndx_p = prev_ndx_p;
      int search_rc = Search(*cur_ndx_p, check_domain_sig); // Result saved into m_value
      if(search_rc <= 0) {
        // 1 = success
        // 0 = unsuccessful
        // Neg value - how many unsuccessfull attempts in privileged domain sigcheck iterations
	CheckDAP(key, key - key_end, 240 - search_rc); // allowed 4/2 false searches for non-exists domain
	return 3; // empty answer, not found, return NXDOMAIN
      }
      if(cur_ndx_p == domain_ndx)
	break; // This is 1st domain (last in the chain, no more subdomains), go to answer
      // Try to search allowance in SD=list for next step down subdomain, like [www]
      prev_ndx_p = cur_ndx_p - 1;
      int domain_len = *cur_ndx_p - *prev_ndx_p - 1;
      char val2[VAL_SIZE];
      char *tokens[MAX_TOK];
      step_next = false;
      int sdqty = Tokenize("SD", ",", tokens, strcpy(val2, m_value));
      while(--sdqty >= 0 && !step_next)
        step_next = strncmp((const char *)*prev_ndx_p, tokens[sdqty], domain_len) == 0 || tokens[sdqty][0] == '*';

      // if no way down - maybe, we can create REF-answer from NS-records
      if(step_next == false && TryMakeref(m_label_ref + (*cur_ndx_p - key)))
	return 0;
      // if cannot create REF - just ANSWER for 3rd+ subsomain domain (ignore prefix/subdomain)
      check_domain_sig = false; // Do not check signatures for child subdomains
    } while(step_next);

  } // if(p_tld) - ends of DB search

  char val2[VAL_SIZE];
  // There is generate ANSWER section
  { // Extract TTL
    char *tokens[MAX_TOK];
    int ttlqty = Tokenize("TTL", NULL, tokens, strcpy(val2, m_value));
    m_ttl = ttlqty? atoi(tokens[0]) : 3600; // 1 hour default TTL
  }

  // List values for ANY:    A NS CNA PTR MX AAAA
  const uint16_t q_all[] = { 1, 2, 5, 12, 15, 28, 0 };

  switch(qtype) {
    case 0xff:	// ALL
      for(const uint16_t *q = q_all; *q; q++)
        Answer_ALL(*q, strcpy(val2, m_value));
      break;
    case 1:	// A
    case 12:	// PTR
    case 15:	// MX
    case 28:	// AAAA
    case 33:	// SRV
    case 52:	// TLSA
    case 257:	// CAA
      Answer_ALL(qtype, strcpy(val2, m_value));
      // Not found A/AAAA - try lookup for CNAME in the default section
      // Quoth RFC 1034, Section 3.6.2:
      // If a CNAME RR is present at a node, no other data should be present;
      // Not found A/AAAA/CNAME - try lookup for CNAME in the default section
      if(m_hdr->ANCount == 0)
        Answer_ALL(5, strcpy(val2, m_value));
      if(m_hdr->ANCount != 0)
	break;
      // Add Authority/Additional section here, if still no answer
      // Fill AUTH+ADDL section according https://www.ietf.org/rfc/rfc1034.txt, sec 6.2.6
//      m_hdr->Bits &= ~m_hdr->AA_MASK;
      qtype = 2 | QTYPE_ADDL;
      // go to default below [[fallthrough]]
    default:
      // All other, including (CNAME, NS)
      Answer_ALL(qtype, m_value);
      break;
  } // switch
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
  LogPrintf("EmcDns::TryMakeref: Generated REF NS=%u\n", m_hdr->NSCount);
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
      // LogPrintf("Token:%s\n", token);
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
      // LogPrintf("Found: key=%s; val=%s\n", key, val);
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
	  // LogPrintf("Subtoken=%s\n", token);
	  tokens[tokensN++] = token;
      }
      break;
  } // for - big tokens (MX, A, AAAA, etc)
  return tokensN;
} // EmcDns::Tokenize

/*---------------------------------------------------*/

void EmcDns::Answer_ALL(uint16_t qtype, char *buf) {
  uint16_t needed_addl = qtype & QTYPE_ADDL;
  qtype ^= needed_addl;
  const char *key = decodeQtype(qtype);
  if(key[0] == '-')
      return; // Do not handle special or undef keys

  char *tokens[MAX_TOK+32];
  int tokQty = Tokenize(key, ",", tokens, buf);

  if(qtype == 2 || qtype == 5 || qtype == 12) {
      // Special handling for NS, CNAME, and PTR records:
      // If the value is "@", replace it with the locally configured self-NS names.
      char *self_list = (char *)0x1; // Cannot use NULL, because of strsep sets it to NULL at the end
      int orig_tokQty = tokQty;
      for(int tok_no = 0; tok_no < orig_tokQty; tok_no++)
          if(tokens[tok_no][0] == '@') {
              if(self_list == (char *)0x1) {
                  // Expand '@' just once
                  self_list = (char *)memcpy(alloca(m_self_ns.length() + 1), m_self_ns.c_str(), m_self_ns.length() + 1);
                  while(char *tok = strsep(&self_list, ",|;"))
                      if(tokQty < MAX_TOK + 32)
                          tokens[tokQty++] = tok;
              }
              tokens[tok_no][0] = 0; // Mark as deleted
          } // for + if(@)
  } // if NS, CNAME, PTR

  if(m_verbose > 4) LogPrintf("EmcDns::Answer_ALL(QT=%d, key=%s); TokenQty=%d\n", qtype, key, tokQty);

  // Shuffle tokens for randomization output order
  for(int i = tokQty; i > 1; ) {
    int randndx = GetRandInt(i);
    char *tmp = tokens[randndx];
    --i;
    tokens[randndx] = tokens[i];
    tokens[i] = tmp;
  }

  int actual_tokQty = tokQty;
  for(int tok_no = 0; tok_no < tokQty; tok_no++) {
      if(tokens[tok_no][0] == 0) {
          actual_tokQty--;
          continue;
      }
      if(m_verbose > 4)
	LogPrintf("    EmcDns::Answer_ALL: Token:%u=[%s]\n", tok_no, tokens[tok_no]);
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
        case 33: Fill_RD_SRV(tokens[tok_no]);         break; // SRV
        case 52: Fill_RD_TLSA(tokens[tok_no]);        break; // TLSA
        case 257: Fill_RD_CAA(tokens[tok_no]);        break; // CAA
	default: break;
      } // switch
  } // for

  if(needed_addl) // Fill ADDL section (NS in NSCount)
    m_hdr->NSCount += actual_tokQty;
  else
    m_hdr->ANCount += actual_tokQty;
} // EmcDns::Answer_ALL

/*---------------------------------------------------*/
/*
NAME 	domain name 	MUST be 0 (root domain)
TYPE 	u_int16_t 	OPT (41)
CLASS 	u_int16_t 	requestor's UDP payload size
TTL 	u_int32_t 	extended RCODE and flags
RDLEN 	u_int16_t 	length of all RDATA
RDATA 	octet stream 	{attribute,value} pairs
*/
void EmcDns::Answer_OPT() {
  *m_snd++ = 0; // Name: =0
  Out2(41);     // Type: OPT record 0x29
  Out2(MAX_OUT);// Class: Out size
  Out4(0);      // TTL - all zeroes
  Out2(0);      // RDLEN
  m_hdr->ARCount++;
} // EmcDns::Answer_OPT
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
    m_snd -= 12, m_hdr->ANCount--; // 12 = clear this 2 and 10 bytes at caller
} // EmcDns::Fill_RD_IP

/*---------------------------------------------------*/

int EmcDns::Fill_RD_DName(char *txt, uint8_t mxsz, int8_t txtcor) {
  uint8_t *snd0 = m_snd;
  m_snd += 3 + mxsz; // skip SZ and sz0
  uint8_t *tok_sz = m_snd - 1;
  uint16_t mx_pri = 1; // Default MX priority
  char c;

  int label_ref = (tok_sz - m_buf - (m_rcvend - m_rcv)) | 0xc000;

  int tok_len = 0;
  if(txtcor) {
    // This is TXT field
    while(m_snd < m_obufend && (c = *txt++) != 0) {
      *m_snd++ = c;
      if(++tok_len == 255) {
        *tok_sz = tok_len;
        tok_sz = m_snd;
        m_snd++;
        tok_len = 0;
      }
    } // while - TXT field
  } else {
    // This is domain field
    const char *errmsg = NULL;
    while(m_snd < m_obufend && (c = *txt++) != 0) {
     if(c == ':' && mxsz) { // split for MX only
        mx_pri = atoi(txt);
        break;
      }
      if(c == '.') {
        if(tok_len == 0) {
            errmsg = "MalformedEmptyDomain";
            break;
        }
        *tok_sz = tok_len;
        tok_sz = m_snd;
        *m_snd++ = 0;
        tok_len = 0;
        continue;
      }
      *m_snd++ = c;
       if(++tok_len == 64) {  // check for rfc1035 2.3.1 (label length)
        errmsg = "SizeOfDomainLabelOver63";
        break;
      }
    } // while - domain field
    if(errmsg) {
      tok_len = strlen(errmsg);
      memcpy((char *)tok_sz + 1, errmsg, tok_len);
      m_snd = tok_sz + 1 + tok_len;
      m_hdr->Bits |= 2; // SERVFAIL - Server failed to complete the DNS request
    }
    // Terminate token chain with last 0,
    // if not empty (empty will be below)
    if(tok_len)
        *m_snd++ = 0;
  } // else - domain field

  // Complete last tolen (empty, too)
  *tok_sz = tok_len;

  uint16_t len = m_snd - snd0 - 2;
  *snd0++ = len >> 8;
  *snd0++ = len;
  if(mxsz) {
    *snd0++ = mx_pri >> 8;
    *snd0++ = mx_pri;
  }
  return label_ref;
} // EmcDns::Fill_RD_DName

/*---------------------------------------------------*/
// SRV record input format: SRV=Pref:Prio:domain:port:domain-TXT
// Wire format: RDlen[2] Pri[2] Wei[2] Port[2] Domain[*]
void EmcDns::Fill_RD_SRV(char *txt) {
  uint8_t *snd0 = m_snd;
  do {
    uint16_t pri = atoi(txt);
    txt = strchr(txt, ':');
    if(txt == NULL)
        break;
    txt++;
    uint16_t wei = atoi(txt);
    txt = strchr(txt, ':');
    if(txt == NULL)
        break;
    txt++;
    m_snd += 4; // allow space for prio/weight
    // Pseudo-MX processing
    Fill_RD_DName(txt, 2, 0);
    // Result fop pseudo-MX:
    // [MX_len] [Prio(port)] [domain]
    uint16_t mx_len = (snd0[4] << 8) | snd0[5];
    uint8_t *snd_end = m_snd;
    m_snd = snd0;
    Out2(mx_len + 4);      // RDlen MX len + 4 (Pri+Wei)
    Out2(pri); // Pri
    Out2(wei); // Wei
    m_snd = snd_end;
    return;
  } while(0);
  m_hdr->Bits |= 2; // SERVFAIL - Server failed to complete the DNS request
  m_snd = snd0;
} // EmcDns::Fill_RD_SRV

/*---------------------------------------------------*/
static unsigned GetHex(uint8_t c) {
  int rc = c - '0';
  if(rc >= 0) {
    if(rc > 9)
        rc = (c | 040) - 'a' + 10;
  }
  return rc;
} // GetHex
/*---------------------------------------------------*/
// TLSA record input format: TLSA=Usage:Selector:Matching:TXT
// Wire format: Usage[1] Selector[1] Matching[1] TXT[*]
void EmcDns::Fill_RD_TLSA(char *txt) {
  uint8_t *snd0 = m_snd;
  m_snd += 2; // Allocate space for RR_size
  do {
    uint8_t usage = atoi(txt);
    txt = strchr(txt, ':');
    if(txt == NULL)
        break;
    txt++;
    *m_snd++ = usage;
    uint8_t selector = atoi(txt);
    txt = strchr(txt, ':');
    if(txt == NULL)
        break;
    txt++;
    *m_snd++ = selector;
    uint8_t matching = atoi(txt);
    txt = strchr(txt, ':');
    if(txt == NULL)
        break;
    txt++;
    *m_snd++ = matching;
    // Decode hex data, pack to binary
    unsigned data1, data2;
    while(*txt != 0) {
      data1 = GetHex(*txt++);
      data2 = GetHex(*txt++);
      if((data1 | data2) > 0xf)
          goto hex_failure;
      *m_snd++ = (data1 << 4) | data2;
    }
    uint16_t len = m_snd - snd0 - 2;
    *snd0++ = len >> 8;
    *snd0   = len;
    return;
  } while(0);
  hex_failure:
  m_hdr->Bits |= 2; // SERVFAIL - Server failed to complete the DNS request
  m_snd = snd0;
} // EmcDns::Fill_RD_TLSA

/*---------------------------------------------------*/
// CAA record input format: CAA=flag tag value
// Wire format: flag[1] tag_len[1] tag[tag_len] value[*]
// https://www.rfc-editor.org/rfc/rfc6844#section-5.1
void EmcDns::Fill_RD_CAA(char *txt) {
  uint8_t *snd0 = m_snd;
  m_snd += 2; // Allocate space for RR_size
  *m_snd++ = atoi(txt); // save flags
  uint8_t *taglen;
  uint16_t len;
  const char *max_txt_tagend;
  // Skip possible spaces before flags
  while(*txt <= ' ') {
      if(*txt == 0)
          goto bad_data;
      txt++;
  }
  // Skip flags intvalue
  while(*txt >= '0' && *txt <= '9')
      txt++;
  // Skip spaces before tag
  while(*txt <= ' ') {
      if(*txt == 0)
          goto bad_data;
      txt++;
  }
  taglen = m_snd;
  m_snd++;
  // Copy tag
  max_txt_tagend = txt + 255;
  char c;
  while((c = *txt++) > ' ') {
      if(txt > max_txt_tagend || !isalnum(c))
          goto bad_data;
      *m_snd++ = c;
  }
  *taglen = m_snd - taglen - 1;

  // Skip spaces before value
  while(*txt <= ' ' && *txt != 0)
      txt++;
  // Copy value
  while((c = *txt++) != 0)
      *m_snd++ = c;

  len = m_snd - snd0 - 2;
  *snd0++ = len >> 8;
  *snd0   = len;
  return;

  bad_data:
  m_hdr->Bits |= 2; // SERVFAIL - Server failed to complete the DNS request
  m_snd = snd0;
} // EmcDns::Fill_RD_CAA

/*---------------------------------------------------*/

int EmcDns::Search(uint8_t *key, bool check_domain_sig) {
  if(m_verbose > 4)
    LogPrintf("EmcDns::Search(%s, check_domain_sig=%d)\n", key, check_domain_sig);

  char search_key[BUF_SIZE];
  string value;
  if(check_domain_sig) {
      // Search iteration with sigcheck
      if(m_verifiers.empty())
          return 0; // Cannot check any signature without verifiers list
      // Iterate over query numbers, start from 0, up to 32K
      int16_t qno = -1;
      do {
        if(++qno > 100)
          return -250; // Exhaust 100 attempts, stop search, increase temp to 2 searches only
        snprintf(search_key, sizeof(search_key), DNS_PREFIX ":%s:%d", (const char *)key, qno);
        if(m_verbose > 4)
            LogPrintf("EmcDns::SIG-Search(%s)\n", search_key);
        if(!hooks->getNameValue(string(search_key), value))
            return -qno * 2; // Record not found, stop search, NXDOMAIN and increase DAP
        size_t sig_begin = value.find("SIG=");
        if(sig_begin == std::string::npos)
            continue; // No signature in this DNS record
        sig_begin += 3; // step over "SIG", set ptr to "=" after SIG
        size_t sig_end = value.find((value[0] == '~')? value[1] : '|', sig_begin);
        if(sig_end == std::string::npos)
            sig_end = value.length();
        // Extract signature to m_value
        memcpy(m_value, value.c_str() + sig_begin, sig_end - sig_begin);
        m_value[sig_end - sig_begin] = 0; // EOLN for signature in the buffer
      } while(!CheckEnumSigList(search_key, m_value, '!'));
  } else {
      // No sigcheck search
      snprintf(search_key, sizeof(search_key), DNS_PREFIX ":%s", (const char *)key);
      if (!hooks->getNameValue(string(search_key), value))
          return 0; // Record not found, stop search, NXDOMAIN
  }

  strcpy(m_value, value.c_str());
  return 1;
} //  EmcDns::Search

/*---------------------------------------------------*/

int EmcDns::LocalSearch(const uint8_t *key, uint8_t pos, uint8_t step) {
  if(m_local_base == NULL)
    return 0; // empty local, no sense to search
  if(m_verbose > 6)
    LogPrintf("EmcDns::LocalSearch(%s, %u, %u) called\n", key, pos, step);
  do {
    pos += step;
    if(m_ht_offset[pos] == 0) {
      if(m_verbose > 6)
        LogPrintf("EmcDns::LocalSearch: Local key=[%s] not found\n", key);
      return 0; // Reached EndOfList
    }
  } while(m_ht_offset[pos] > 0 || strcmp((const char *)key, m_local_base - m_ht_offset[pos]) != 0);

  strcpy(m_value, strchr(m_local_base - m_ht_offset[pos], 0) + 1);

  return 1;
} // EmcDns::LocalSearch


/*---------------------------------------------------*/
#define ROLADD(h,s,x)   h = ((h << s) | (h >> (32 - s))) + (x)
// Returns true - can handle packet; false = ignore
bool EmcDns::CheckDAP(void *key, int len, uint16_t inctemp) {
  if(m_dap_ht == NULL)
    return true; // Filter is inactive

  uint32_t ip_addr = 0;
  if(len < 0) { // domain string
    for(int i = 0; i < -len; i++)
      ROLADD(ip_addr, 6, ((const char *)key)[i]);
  } else { // IP addr
    for(int i = 0; i < (len / 4); i++)
      ROLADD(ip_addr, 1, ((const uint32_t *)key)[i]);
  }

  inctemp++;
  uint32_t hash = m_daprand, mintemp = ~0;

  int used_ndx[EMCDNS_DAPBLOOMSTEP];
  for(int bloomstep = 0; bloomstep < EMCDNS_DAPBLOOMSTEP; bloomstep++) {
    int ndx, att = 0;
    do {
      ++att;
      hash *= ip_addr;
      hash ^= hash >> 16;
      hash += hash >> 7;
      ndx = (hash ^ att) & m_dapmask; // always positive
      for(int i = 0; i < bloomstep; i++)
	if(ndx == used_ndx[i])
	  ndx = -1;
    } while(ndx < 0);

    DNSAP *dap = &m_dap_ht[used_ndx[bloomstep] = ndx];
    uint16_t dt = m_timestamp - dap->timestamp;
    uint32_t new_temp = (dt > 15? 0 : dap->temp >> dt) + inctemp;
    dap->temp = (new_temp > 0xffff)? 0xffff : new_temp;
    dap->timestamp = m_timestamp;
    if(new_temp < mintemp)
      mintemp = new_temp;
  } // for

  m_mintemp = mintemp; // Save for logging
  bool rc = mintemp < m_dap_treshold;
  if(m_verbose > 5 || (!rc && m_verbose > 3)) {
    char buf[80], outbuf[120];
    snprintf(outbuf, sizeof(outbuf), "EmcDns::CheckDAP: IP=[%s] inctemp=%u, mintemp=%u dap_treshold=%u rc=%d\n",
		    len < 0? (const char *)key : inet_ntop(len == 4? AF_INET : AF_INET6, key, buf, len),
                    inctemp, mintemp, m_dap_treshold, rc);
    LogPrintf(outbuf);
  }
  return rc;
} // EmcDns::CheckDAP

/*---------------------------------------------------*/
// Handle Special function - phone number in the E.164 format
// to support ENUM service
int EmcDns::SpfunENUM(uint8_t len, uint8_t **domain_start, uint8_t **domain_end) {
  int dom_length = domain_end - domain_start;
  const char *tld = (const char*)domain_end[-1];

  bool sigOK = len & 0200; // If set no-check-sig, then signature already quasi-checked: OK
  len &= 0177; // Cut flag no-check-sig

  if(m_verbose > 3)
    LogPrintf("    EmcDns::SpfunENUM: Domain=[%s] N=%u TLD=[%s] Len=%u sigOK=%u\n",
	    (const char*)*domain_start, dom_length, tld, len, sigOK);

  do {
    if(dom_length < 2)
      break; // no domains for phone number - NXDOMAIN


    if(!sigOK && m_verifiers.empty() && m_tollfree.empty())
      break; // no verifier/toll-free/open_zone - no sense to search

    if(len > 64)
        len = 64; // Max phone num lenght=64
    // convert reversed domain record to ITU-T number
    char itut_num[68], *pitut = itut_num, *pitutend = itut_num + len;
    for(const uint8_t *p = domain_end[-1]; --p >= *domain_start; )
      if(*p >= '0' && *p <= '9') {
	*pitut++ = *p;
        if(pitut >= pitutend)
	  break;
      }
    *pitut = 0; // EOLN at phone number end

    if(pitut == itut_num)
      break; // Empty phone number - NXDOMAIN

    if(m_verbose > 4)
      LogPrintf("    EmcDns::SpfunENUM: ITU-T num=[%s]\n", itut_num);

    // Iterate all available ENUM-records, and build joined answer from them
    if(sigOK || !m_verifiers.empty()) {
      for(int16_t qno = 0; qno >= 0; qno++) {
        char q_str[160];
        sprintf(q_str, "%s:%s:%u", tld, itut_num, qno);
        if(m_verbose > 4)
          LogPrintf("    EmcDns::SpfunENUM Search(%s)\n", q_str);

        string value;
        if(!hooks->getNameValue(string(q_str), value))
          break;

        strcpy(m_value, value.c_str());
        Answer_ENUM(q_str, sigOK); // Body passed through m_value
      } // for
    } // if

    // If nothing found in the ENUM - try to search in the Toll-Free
    m_ttl = 24 * 3600; // 24h by default
    boost::xpressive::smatch nameparts;
    for(vector<TollFree>::const_iterator tf = m_tollfree.begin();
	      m_hdr->ANCount == 0 && tf != m_tollfree.end();
	      tf++) {
      bool matched = regex_match(string(itut_num), nameparts, tf->regex);
      // bool matched = regex_search(string(itut_num), nameparts, tf->regex);
      if(m_verbose > 4)
          LogPrintf("    EmcDns::SpfunENUM TF-match N=[%s] RE=[%s] -> %u\n", itut_num, tf->regex_str.c_str(), matched);
      if(matched)
        for(vector<string>::const_iterator e2u = tf->e2u.begin(); e2u != tf->e2u.end(); e2u++)
          HandleE2U(strcpy(m_value, e2u->c_str()));
    } // tf processing

    // For ENUM reuqest, there is lot of unsucessful requests from same PBX.
    // Thus, for ENUM, we do not create "unsuccessful request penalty", and return 0-code as same as OK.
    // But, we set flag NXDOMAIN here directly within answer
    if(m_hdr->ANCount == 0)
        m_hdr->Bits |= 3; // NXDOMAIN, if no answer exists
    return 0;
  } while(false);

  return 3; // NXDOMAIN
} // EmcDns::SpfunENUM

/*---------------------------------------------------*/

#define ENC3(a, b, c) (a | (b << 8) | (c << 16))

/*---------------------------------------------------*/
// Generate answewr for found EMUM NVS record
void EmcDns::Answer_ENUM(const char *q_str, bool sigOK) {
  // DIG checks NAPTR answer for regex, and prints error, if undef variable applied:
  // BAD: strcpy(m_value, "SIG=ver:enum|H+P0LucJJVRbPhKWotFS2Zr5o40501M4U1SmZ6ClDXUnBY6oQg1k9Kk+J+iLFcZ/FbUTk/rbt/169GtPt7vdTDY=\nE2U+sip=100|11|!^.*$!sip:\\1@postmet.com!");
  // GOOD strcpy(m_value, "SIG=ver:enum|H+P0LucJJVRbPhKWotFS2Zr5o40501M4U1SmZ6ClDXUnBY6oQg1k9Kk+J+iLFcZ/FbUTk/rbt/169GtPt7vdTDY=\nE2U+sip=100|11|!^(.)*$!sip:\\1@postmet.com!");
  // GOOD strcpy(m_value, "SIG=ver:enum|H+P0LucJJVRbPhKWotFS2Zr5o40501M4U1SmZ6ClDXUnBY6oQg1k9Kk+J+iLFcZ/FbUTk/rbt/169GtPt7vdTDY=\nE2U+sip=100|11|!^.*$!sip:\\\\1@postmet.com!");
  char *str_val = m_value;
  const char *pttl;
  char *e2u[VAL_SIZE / 4]; // 20kb max input, and min 4 bytes per token
  uint16_t e2uN = 0;

  m_ttl = 24 * 3600; // 24h by default

  // Tokenize lines in the NVS-value.
  // There can be prefixes SIG=, TTL=, E2U
  while(char *tok = strsep(&str_val, "\n\r"))
    switch((*(uint32_t*)tok & 0xffffff) | 0x202020) {
	case ENC3('e', '2', 'u'):
	  e2u[e2uN++] = tok;
	  continue;

	case ENC3('t', 't', 'l'):
	  pttl = strchr(tok + 3, '=');
	  if(pttl)
	    m_ttl = atoi(pttl + 1);
	  continue;

	case ENC3('s', 'i', 'g'):
	  if(!sigOK)
	    sigOK = CheckEnumSigList(q_str, strchr(tok + 3, '='), '|');
	  continue;

	default:
	  continue;
    } // while + switch

  if(!sigOK)
    return; // This ENUM-record does not contain a valid signature

  // Generate ENUM-answers here
  for(uint16_t e2undx = 0; e2undx < e2uN; e2undx++)
    if(m_snd < m_obufend - 24)
      HandleE2U(e2u[e2undx]);

 } // EmcDns::Answer_ENUM

/*---------------------------------------------------*/
void EmcDns::OutS(const char *p) {
  int len = strlen(strcpy((char *)m_snd + 1, p));
  *m_snd = len;
  m_snd += len + 1;
} // EmcDns::OutS

/*---------------------------------------------------*/
 // Generate ENUM-answers for a single E2U entry
 // E2U+sip=100|10|!^(.*)$!sip:17771234567@in.callcentric.com!
void EmcDns::HandleE2U(char *e2u) {
  char *data = strchr(e2u, '=');
  if(data == NULL)
    return;

  // Cleanum sufix for service; Service started from E2U
  for(char *p = data; *--p <= 040; *p = 0) {}

  unsigned int ord, pref;
  char re[VAL_SIZE];

  *data++ = 0; // Remove '='

  if(sscanf(data, "%u | %u | %s", &ord, &pref, re) != 3)
    return;

  if(m_verbose > 5)
    LogPrintf("    EmcDns::HandleE2U: Parsed: %u %u %s %s\n", ord, pref, e2u, re);

  if(m_snd + strlen(re) + strlen(e2u) + 24 >= m_obufend)
    return;

  Out2(m_label_ref);
  Out2(0x23); // NAPTR record
  Out2(1); //  INET
  Out4(m_ttl);
  uint8_t *snd0 = m_snd; m_snd += 2;
  Out2(ord);
  Out2(pref);
  OutS("u");
  OutS(e2u);
  OutS(re);
  *m_snd++ = 0;

  uint16_t len = m_snd - snd0 - 2;
  *snd0++ = len >> 8;
  *snd0++ = len;

  m_hdr->ANCount++;
} //  EmcDns::HandleE2U

/*---------------------------------------------------*/
bool EmcDns::CheckEnumSigList(const char *q_str, char *siglist_str, char sig_separ) {
    char *comma_ptr;
    do {
      comma_ptr = strchr(siglist_str, ',');
      if(comma_ptr)
        *comma_ptr = 0; // Deploy EOLN over the comma (sigs separator)
      if(CheckEnumSig(q_str, siglist_str, sig_separ))
        return true;
    } while((siglist_str = comma_ptr) != 0);
    return false;
} // EmcDns::CheckEnumSigList

/*---------------------------------------------------*/
// q_str is DNS name, like "enum:17771234567:0" or "dns:signed.sig:0"
// sig_str is &signature[-1], i.e. 1st char will be skipped
// sig_separ is '|' for ENUM and '!' for DNS
bool EmcDns::CheckEnumSig(const char *q_str, char *sig_str, char sig_separ) {
    if(sig_str == NULL)
      return false;

    // skip 1st char (including EOLN) and SP/TABs in signature
    while(*++sig_str <= ' ');

    char *signature = strchr(sig_str, sig_separ);
    if(signature == NULL)
      return false;

    for(char *p = signature; *--p <= 040; *p = 0) {}
    *signature++ = 0;

    map<string, Verifier>::iterator it = m_verifiers.find(sig_str);
    if(it == m_verifiers.end())
      return false; // Unknown verifier - do not trust it

    Verifier &ver = it->second;

    uint32_t now = time(NULL);
    if(now > ver.forgot) {
      ver.forgot = now + 3 * 60;    // Remember status for 3 mins
      ver.mask = VERMASK_NOSRL + 1; // Read/check breaks will produce out-of-range mask
      // Remember time is expired - try to upgrade the ver-record
      do {
        CNameRecord nameRec;
        CTransactionRef tx;
        LOCK(cs_main);
        if(!pNameDB->ReadName(CNameVal(it->first.c_str(), it->first.c_str() + it->first.size()), nameRec))
	  break; // failed to read from name DB
        if(nameRec.vNameOp.size() < 1)
	  break; // no result returned
        if(!g_txindex || !g_txindex->FindTx(nameRec.vNameOp.back().txPos, tx))
          break; // failed to read from from disk
        NameTxInfo nti;
        if (!DecodeNameOutput(tx, nameRec.vNameOp.back().nOut, nti, true))
            break; // failed to decode name
        CTxDestination dest = DecodeDestination(nti.strAddress);
        if (!IsValidDestination(dest))
            break; // Invalid address

        const WitnessV0KeyHash *w0pkhash;
        const PKHash           *pkhash;
        if((w0pkhash = boost::get<WitnessV0KeyHash>(&dest)) != NULL)
          ver.keyID = CKeyID(*w0pkhash);
        else
        if((pkhash = boost::get<PKHash>(&dest)) != NULL)
          ver.keyID = CKeyID(*pkhash);
        else
          break; // We support p2[w]pkh only

	// Verifier has been read successfully, configure SRL if exist
	char valbuf[VAL_SIZE], *str_val = valbuf;
        memcpy(valbuf, &nti.value[0], nti.value.size());
        valbuf[nti.value.size()] = 0;

	// Proces Signatures Revocation list[s] in the format:
        // SRL=nBits|Templete
        // like:
	// SRL=5|srl:hello-%02x
	ver.mask = VERMASK_NOSRL;
        while(char *tok = strsep(&str_val, "\n\r"))
	  if(((*(uint32_t*)tok & 0xffffff) | 0x202020) == ENC3('s', 'r', 'l') && (tok = strchr(tok + 3, '='))) {
	    unsigned nbits = atoi(++tok);
            if(nbits > 30) nbits = 30;
	    tok = strchr(tok, '|');
	    if(tok != NULL) {
		do {
		  if(*++tok == 0)
		    break; // empty SRL, thus keep VERMASK_NOSRL
		  char *pp = strchr(tok, '%');
		  if(pp != NULL) {
		    if(*++pp == '0')
		      do ++pp; while(*pp >= '0' && *pp <= '9');
                    if(strchr("diouXx", *pp) == NULL)
			break; // Invalid char in the template
		    if(strchr(pp, '%'))
			break; // Not allowed 2nd % symbol
		  } else
		    nbits = 0; // Don't needed nbits/mask for no-bucket srl_tpl

                  ver.srl_tpl.assign(tok);
		  ver.mask = (1 << nbits) - 1;
		} while(false);
	    } // if(tok != NULL)
	    if(ver.mask != VERMASK_NOSRL)
	      break; // Mask found
	  } // while + if
      } while(false);
    } // if(now > ver.forgot)

    if(ver.mask > VERMASK_NOSRL)
      return false; // DB read error, or ver-list size > 64K

    while(*signature <= 040 && *signature)
      signature++;

    char *sig_end = strchr(signature, 0);
    while(*--sig_end <= 040)
        *sig_end = 0; // Cut SP\n\r at signature end

    bool fInvalid = false;
    vector<unsigned char> vchSig(DecodeBase64(signature, &fInvalid));

    if(fInvalid)
      return false;

    CHashWriter ss(SER_GETHASH, 0);
    ss << strMessageMagic;
    ss << string(q_str);

    CPubKey pubkey;
    if(!pubkey.RecoverCompact(ss.GetHash(), vchSig))
      return false;

    if(pubkey.GetID() != ver.keyID)
	return false; // Signature check did not passed

    if(ver.mask == VERMASK_NOSRL)
	return true; // This verifiyer does not have active SRL

    char valbuf[VAL_SIZE];

    // Compute a simple hash from q_str like enum:17771234567:0
    // This hash must be used by verifiyers for build buckets
    unsigned h = 0x5555;
    for(const char *p = q_str; *p; p++)
	h += (h << 5) + *p;
    sprintf(valbuf, ver.srl_tpl.c_str(), h & ver.mask);

    string value;
    if(!hooks->getNameValue(string(valbuf), value))
      return true; // Unable fetch SRL - as same as SRL does not exist

    // Is q_str missing in the SRL
    return value.find(q_str) == string::npos;
} // EmcDns::CheckEnumSig


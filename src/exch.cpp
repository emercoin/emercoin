#include <exch.h>
#include "clientversion.h"
#include "util.h"

using namespace std;
using namespace boost;
using namespace boost::asio;

//-----------------------------------------------------
ExchBox::ExchBox() {}

//-----------------------------------------------------
void ExchBox::Reset(const string &retAddr) {
  for(size_t i = 0; i < m_v_exch.size(); i++)
    delete m_v_exch[i];
  m_v_exch.clear();
  m_v_exch.push_back(new ExchCoinReform(retAddr));
} // ExchBox::Reset

//-----------------------------------------------------
ExchBox::~ExchBox() {
  for(size_t i = 0; i < m_v_exch.size(); i++)
    delete m_v_exch[i];
} // ExchBox::~ExchBox

//-----------------------------------------------------
//-----------------------------------------------------
Exch::Exch(const string &retAddr)
: m_retAddr(retAddr) {
  m_depAmo = m_outAmo = m_rate = m_limit = m_min = m_minerFee = 0.0;
}

//-----------------------------------------------------
// Get input path within server, like: /api/marketinfo/emc_btc.json
// Called from exchange-specific MarketInfo()
// Fill MarketInfo from exchange.
// Throws exception if error
const UniValue Exch::RawMarketInfo(const string &path) {
  m_rate = m_limit = m_min = m_minerFee = 0.0;
  m_pair.erase();
  return httpsFetch(path.c_str(), NULL);
} //  Exch::RawMarketInfo

//-----------------------------------------------------
// Returns extimated EMC to pay for specific pay_amount
// Must be called after MarketInfo
double Exch::EstimatedEMC(double pay_amount) const {
  return (m_rate <= 0.0)?
    m_rate : ceil(100.0 * (pay_amount + m_minerFee) / m_rate) / 100.0;
} // Exch::EstimatedEMC

//-----------------------------------------------------
// Connect to the server by https, fetch JSON and parse to UniValue
// Throws exception if error
UniValue Exch::httpsFetch(const char *get, const UniValue *post) {
  // Connect to exchange
  asio::io_service io_service;
  ssl::context context(io_service, ssl::context::sslv23);
  context.set_options(ssl::context::no_sslv2 | ssl::context::no_sslv3);
  asio::ssl::stream<asio::ip::tcp::socket> sslStream(io_service, context);
  SSL_set_tlsext_host_name(sslStream.native_handle(), Host().c_str());
  SSLIOStreamDevice<asio::ip::tcp> d(sslStream, true); // use SSL
  iostreams::stream< SSLIOStreamDevice<asio::ip::tcp> > stream(d);

  if(!d.connect(Host(), "443"))
    throw runtime_error("Couldn't connect to server");

  string postBody;
  const char *reqType = "GET ";

  if(post != NULL) {
    // This is POST request - prepare postBody
    reqType = "POST ";
    postBody = post->write(0, 0, 0) + '\n';
  } 

  LogPrint("exch", "DBG: Exch::httpsFetch: Req: method=[%s] path=[%s] H=[%s]\n", reqType, get, Host().c_str());

  // Send request
  stream << reqType << (get? get : "/") << " HTTP/1.1\r\n"
         << "Host: " << Host() << "\r\n"
         << "User-Agent: iTecoCoin-json-rpc/" << FormatFullVersion() << "\r\n";

  if(postBody.size()) {
    stream << "Content-Type: application/json\r\n"
           << "Content-Length: " << postBody.size() << "\r\n";
  }

  stream << "Connection: close\r\n"
         << "Accept: application/json\r\n\r\n" 
	 << postBody << std::flush;

  // Receive HTTP reply status
  int nProto = 0;
  int nStatus = ReadHTTPStatus(stream, nProto);

  if(nStatus >= 400)
    throw runtime_error(strprintf("Server returned HTTP error %d", nStatus));

  // Receive HTTP reply message headers and body
  map<string, string> mapHeaders;
  string strReply;
  ReadHTTPMessage(stream, mapHeaders, strReply, nProto, 4 * 1024);

  LogPrint("exch", "DBG: Exch::httpsFetch: Server returned HTTP: %d\n", nStatus);

  if(strReply.empty())
    throw runtime_error("No response from server");

  LogPrint("exch", "DBG: Exch::httpsFetch: Reply from server: [%s]\n", strReply.c_str());

  size_t json_beg = strReply.find('{');
  size_t json_end = strReply.rfind('}');
  if(json_beg == string::npos || json_end == string::npos)
    throw runtime_error("Reply is not JSON");

   // Parse reply
  UniValue valReply(UniValue::VSTR);

  if(!valReply.read(strReply.substr(json_beg, json_end - json_beg + 1), 0))
    throw runtime_error("Couldn't parse reply from server");

  const UniValue& reply = valReply.get_obj();

  if(reply.empty())
    throw runtime_error("Empty JSON reply");

  // Check for error message in the reply
  CheckERR(reply);

  return reply;

} // UniValue Exch::httpsFetch

//-----------------------------------------------------
// Check JSON-answer for "error" key, and throw error
// message, if exists
void Exch::CheckERR(const UniValue &reply) const {
  const UniValue& err = find_value(reply, "error");
  if(err.isStr())
    throw runtime_error(err.get_str().c_str());
} // Exch::CheckERR

//-----------------------------------------------------
// Extract raw key from txkey
// Return NULL if "Not my key" or invalid key
const char *Exch::RawKey(const string &txkey) const {
  const char *key = txkey.empty()? m_txKey.c_str() : txkey.c_str();
  if(strncmp(key, Name().c_str(), Name().length()) != 0) 
    return NULL; // Not my key
  key += Name().length();
  if(*key++ != ':')
    return NULL; // Not my key
  return key;
} // Exch::RawKey

//=====================================================

//-----------------------------------------------------
ExchCoinReform::ExchCoinReform(const string &retAddr)
: Exch::Exch(retAddr) {
}

//-----------------------------------------------------
ExchCoinReform::~ExchCoinReform() {}

//-----------------------------------------------------
const string& ExchCoinReform::Name() const { 
  static const string rc("CoinReform");
  return rc;
}

//-----------------------------------------------------
const string& ExchCoinReform::Host() const {
  static const string rc("www.coinreform.com");
  return rc;
}

//-----------------------------------------------------
// Get currency for exchnagge to, like btc, ltc, etc
// Fill MarketInfo from exchange.
// Returns empty string if OK, or error message, if error
string ExchCoinReform::MarketInfo(const string &currency) {
  try {
    //const UniValue mi(RawMarketInfo("/marketinfo/ltc_" + currency));
    const UniValue mi(RawMarketInfo("/api/marketinfo/emc_" + currency + ".json"));
    LogPrint("exch", "DBG: ExchCoinReform::MarketInfo(%s|%s) returns <%s>\n\n", Host().c_str(), currency.c_str(), mi.write(0, 0, 0).c_str());
    m_pair     = mi["pair"].get_str();
    m_rate     = atof(mi["rate"].get_str().c_str());
    m_limit    = atof(mi["limit"].get_str().c_str());
    m_min      = atof(mi["min"].get_str().c_str());
    m_minerFee = atof(mi["minerFee"].get_str().c_str());
    return "";
  } catch(std::exception &e) {
    return e.what();
  }
} // ExchCoinReform::MarketInfo
//coinReform
//{"pair":"EMC_BTC","rate":"0.00016236","limit":"0.01623600","min":"0.00030000","minerFee":"0.00050000"}

//-----------------------------------------------------
// Creatse SEND exchange channel for 
// Send "amount" in external currecny "to" address
// Fills m_depAddr..m_txKey, and updates m_rate
// Returns error text, or empty string, if OK
string ExchCoinReform::Send(const string &to, double amount) {
  if(amount < m_min)
   return strprintf("amount=%lf is less than minimum=%lf", amount, m_min);
  if(amount > m_limit)
   return strprintf("amount=%lf is greater than limit=%lf", amount, m_limit);

  // Cleanum output
  m_depAddr.erase();
  m_outAddr.erase();
  m_txKey.erase();
  m_depAmo = m_outAmo = 0.0;
  m_txKey.erase();

  try {
    UniValue Req(UniValue::VOBJ);
    Req.push_back(Pair("amount", amount));
    Req.push_back(Pair("withdrawal", to));
    Req.push_back(Pair("pair", m_pair));
    Req.push_back(Pair("refund_address", m_retAddr));
    // The public disclosure for RefID usage: https://bitcointalk.org/index.php?topic=362513
    Req.push_back(Pair("ref_id", "2f77783d"));

    UniValue Resp(httpsFetch("/api/sendamount", &Req));
    LogPrint("exch", "DBG: ExchCoinReform::Send(%s|%s) returns <%s>\n\n", Host().c_str(), m_pair.c_str(), Resp.write(0, 0, 0).c_str());
    m_rate     = atof(Resp["rate"].get_str().c_str());
    m_depAddr  = Resp["deposit"].get_str();			// Address to pay EMC
    m_outAddr  = Resp["withdrawal"].get_str();			// Address to pay from exchange
    m_depAmo   = atof(Resp["deposit_amount"].get_str().c_str());// amount in EMC
    m_outAmo   = atof(Resp["withdrawal_amount"].get_str().c_str());// Amount transferred to BTC
    m_txKey    = Name() + ':' + Resp["key"].get_str();		// TX reference key

    // Adjust deposit amount to 1EMCent, upward
    m_depAmo = ceil(m_depAmo * 100.0) / 100.0;

    return "";
  } catch(std::exception &e) { // something wrong at HTTPS
    return e.what();
  }
} // ExchCoinReform::Send

//-----------------------------------------------------
// Check status of existing transaction.
// If key is empty, used the last key
// Returns status (including err), or minus "-", if "not my" key
string ExchCoinReform::TxStat(const string &txkey, UniValue &details) {
  const char *key = RawKey(txkey);
  if(key == NULL)
      return "-"; // Not my key

  char buf[400];
  snprintf(buf, sizeof(buf), "/api/txstat/%s.json", key);
  try {
    details = httpsFetch(buf, NULL);
    LogPrint("exch", "DBG: ExchCoinReform::TxStat(%s|%s) returns <%s>\n\n", Host().c_str(), buf, details.write(0, 0, 0).c_str());
    return details["status"].get_str();
  } catch(std::exception &e) { // something wrong at HTTPS
    return e.what();
  }
} // ExchCoinReform::TxStat

//-----------------------------------------------------
// Cancel TX by txkey.
// If key is empty, used the last key
// Returns error text, or an empty string, if OK
// Returns minus "-", if "not my" key
string ExchCoinReform::Cancel(const string &txkey) {
  const char *key = RawKey(txkey);
  if(key == NULL)
      return "-"; // Not my key

  char buf[400];
  snprintf(buf, sizeof(buf), "/api/cancel/%s.json", key);
  try {
    UniValue Resp(httpsFetch(buf, NULL));
    LogPrint("exch", "DBG: ExchCoinReform::Cancel(%s|%s) returns <%s>\n\n", Host().c_str(), buf, Resp.write(0, 0, 0).c_str());
    m_txKey.erase(); // Preserve from double Cancel
    return m_txKey;
  } catch(std::exception &e) { // something wrong at HTTPS
    return e.what();
  }
} // ExchCoinReform::Cancel

//-----------------------------------------------------
// Check time in secs, left in the contract, created by prev Send()
// If key is empty, used the last key
// Returns time or zero, if contract expired
// Returns -1, if "not my" key
int ExchCoinReform::Remain(const string &txkey) {
  const char *key = RawKey(txkey);
  if(key == NULL)
      return -1; // Not my key

  char buf[400];
  snprintf(buf, sizeof(buf), "/api/timeremaining/%s.json", key);
  try {
    UniValue Resp(httpsFetch(buf, NULL));
    LogPrint("exch", "DBG: ExchCoinReform::Cancel(%s|%s) returns <%s>\n\n", Host().c_str(), buf, Resp.write(0, 0, 0).c_str());
    return Resp["seconds_remaining"].get_int();
  } catch(std::exception &e) { // something wrong at HTTPS
    return 0;
  }
} // ExchCoinReform::TimeLeft



//=====================================================
//
// ShapeShift
// <{"pair":"ltc_btc","rate":0.00320953,"minerFee":0.0012,"limit":256.45898362,"minimum":0.74136083,"maxLimit":641.14745904}
/*
    m_rate     = mi["rate"].get_real();
    m_limit    = mi["limit"].get_real();
    m_min      = mi["min"].get_real();
    m_minerFee = mi["minerFee"].get_real();
*/

//-----------------------------------------------------
//=====================================================
void exch_test() {
#if 0
  ExchBox eBox;
  eBox.Reset("ESgQZ4oU5TN6BRK3DqZX3qDSrQjPwWHP7t");
  do {
      Exch    *exch = eBox.m_v_exch[0];
      printf("exch_test()\nwork with exch=0, Name=%s URL=%s\n", exch->Name().c_str(), exch->Host().c_str());

      string err(exch->MarketInfo("btc"));
      //string err(exch->MarketInfo("zzQ"));
      printf("exch_test:MarketInfo returned: [%s]\n", err.c_str());
      if(!err.empty()) break;
      printf("exch_test:Values from exch: m_rate=%lf; m_limit=%lf; m_min=%lf; m_minerFee=%lf\n", 
	      exch->m_rate, exch->m_limit, exch->m_min, exch->m_minerFee);

      printf("\nexch_test:Tryint to send BTC\n");
      err = exch->Send("1Evqeh5pWphbWzmRAc4d3Wb82mAUBhWEVF", 0.001); // good addr
      // bad err = exch->Send("1Evqeh5pWphbWzmRAc4d3Wb82mAUBhWEVz", 0.001); // bad addr
      printf("exch_test:Send returned: [%s]\n", err.c_str());
      if(!err.empty()) break;
      printf("m_depAddr=%s, m_outAddr=%s m_depAmo=%lf m_outAmo=%lf m_txKey=%s\n",
	      exch->m_depAddr.c_str(), exch->m_outAddr.c_str(), exch->m_depAmo, exch->m_outAmo, exch->m_txKey.c_str());

      MilliSleep(1000);

      printf("\nexch_test:Checking TX status\n");
      UniValue Det(UniValue::VOBJ);
      err = exch->TxStat("", Det);
      printf("exch_test:TxStat returned: [%s]\n", err.c_str());
      printf("exch_test:TxStat Details: <%s>\n\n", Det.write(0, 0, 0).c_str());

      printf("exch_test:Remain=%d\n", exch->Remain(""));

      err = exch->Cancel("");
      printf("exch_test:Cancel returned: [%s]\n", err.c_str());

  } while(0);

  printf("exch_test:Quit from test\n");
  exit(0);
#endif
}

//-----------------------------------------------------

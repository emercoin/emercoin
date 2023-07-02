#include <namecoin.h>
#include <validation.h>
#include <rpc/server.h>
#include <wallet/wallet.h>
#include <base58.h>
#include <txmempool.h>
#include <rpc/util.h>
#include <wallet/rpcwallet.h>
#include <key_io.h>
#include <wallet/coincontrol.h>
#include <util/validation.h>
#include <consensus/validation.h>

#include <boost/format.hpp>
#include <boost/xpressive/xpressive_dynamic.hpp>
#include <fstream>

using namespace std;

map<CNameVal, set<COutPoint> > mapNamePending; // for pending tx
std::unique_ptr<CNameDB> pNameDB;
std::unique_ptr<CNameAddressDB> pNameAddressDB;

class CNamecoinHooks : public CHooks
{
public:
    virtual bool IsNameFeeEnough(const CTransactionRef& tx, const CAmount& txFee);
    virtual bool ConnectBlock(CBlockIndex* pindex, const vector<nameCheckResult>& vName);
    virtual bool ExtractAddress(const CScript& script, string& address);
    virtual bool CheckPendingNames(const CTransactionRef& tx);
    virtual void AddToPendingNames(const CTransactionRef& tx);
    virtual bool getNameValue(const string& sName, string& sValue);
    virtual bool DumpToTextFile();
};

CNameVal nameValFromValue(const UniValue& value) {
    string strName = value.get_str();
    unsigned char *strbeg = (unsigned char*)strName.c_str();
    return CNameVal(strbeg, strbeg + strName.size());
}

CNameVal toCNameVal(const std::string& str) {
    return nameValFromString(str);
}
CNameVal nameValFromString(const string& str) {
    unsigned char *strbeg = (unsigned char*)str.c_str();
    return CNameVal(strbeg, strbeg + str.size());
}

string stringFromNameVal(const CNameVal& nameVal) {
    string res;
    CNameVal::const_iterator vi = nameVal.begin();
    while (vi != nameVal.end()) {
        res += (char)(*vi);
        vi++;
    }
    return res;
}

string limitString(const string& inp, unsigned int size, string message = "")
{
    if (size == 0)
        return inp;
    string ret = inp;
    if (inp.size() > size)
    {
        ret.resize(size);
        ret += message;
    }

    return ret;
}

string encodeNameVal(const CNameVal& input, const string& format)
{
    string output;
    if      (format == "hex")    output = HexStr(input);
    else if (format == "base64") output = EncodeBase64(input.data(), input.size());
    else                         output = stringFromNameVal(input);
    return output;
}

// Calculate at which block will expire.
bool CalculateExpiresAt(CNameRecord& nameRec)
{
    if (nameRec.deleted()) {
        nameRec.nExpiresAt = 0;
        return true;
    }

    int64_t sum = 0;
    for(unsigned int i = nameRec.nLastActiveChainIndex; i < nameRec.vNameOp.size(); i++) {
        CTransactionRef tx;
        if (!g_txindex || !g_txindex->FindTx(nameRec.vNameOp[i].txPos, tx))
            return error("%s: could not read tx from disk", __func__);

        NameTxInfo nti;
        if (!DecodeNameOutput(tx, nameRec.vNameOp[i].nOut, nti))
            return error("%s: %s is not name tx, this should never happen", __func__, tx->GetHash().GetHex());

       sum += 175ULL * nti.nRentalDays; //days to blocks. 175 is average number of blocks per day
    }

    //limit to INT_MAX value
    sum += nameRec.vNameOp[nameRec.nLastActiveChainIndex].nHeight;
    nameRec.nExpiresAt = sum > INT_MAX ? INT_MAX : sum;

    return true;
}

// Tests if name is active. You can optionaly specify at which height it is/was active.
bool NameActive(const CNameVal& name, int currentBlockHeight = -1)
{
    CNameRecord nameRec;
    if (!pNameDB->ReadName(name, nameRec))
        return false;

    if (currentBlockHeight < 0)
        currentBlockHeight = ::ChainActive().Height();

    if (nameRec.deleted()) // last name op was name_delete
        return false;

    return currentBlockHeight <= nameRec.nExpiresAt;
}

// Returns minimum name operation fee rounded down to cents. Should be used during|before transaction creation.
// If you wish to calculate if fee is enough - use IsNameFeeEnough() function.
// Generaly:  GetNameOpFee() > IsNameFeeEnough().
CAmount GetNameOpFee(const CBlockIndex* pindex, const int nRentalDays, int op, const CNameVal& name, const CNameVal& value)
{
    if (op == OP_NAME_DELETE)
        return MIN_TX_FEE;

    const CBlockIndex* lastPoW = GetLastBlockIndex(pindex, false);

    CAmount txMinFee = nRentalDays * lastPoW->nMint / (365 * 100); // 1% PoW per 365 days

    if (op == OP_NAME_NEW)
        txMinFee += lastPoW->nMint / 100; // +1% PoW per operation itself

    txMinFee = sqrt(txMinFee / CENT) * CENT; // square root is taken of the number of cents.
    txMinFee += (int)((name.size() + value.size()) / 128) * CENT; // 1 cent per 128 bytes

    // Round up to CENT
    txMinFee += CENT - 1;
    txMinFee = (txMinFee / CENT) * CENT;

    // reduce fee by 100 in 0.7.0emc
    txMinFee = txMinFee / 100;

    // Fee should be at least MIN_TX_FEE
    txMinFee = max(txMinFee, MIN_TX_FEE);

    return txMinFee;
}

// scans nameindexV3 and return names with their last CNameOperation
// if nMax == 0 - it will scan all names
bool CNameDB::ScanNames(const CNameVal& name, unsigned int nMax,
        vector<
            pair<
                CNameVal,
                pair<CNameOperation, int>
            >
        > &nameScan)
{
    std::unique_ptr<CDBIterator> pcursor(NewIterator());
    pcursor->Seek(name);
    while (pcursor->Valid()) {
        CNameVal key;
        if (!pcursor->GetKey(key))
            return error("%s: failed to read key", __func__);

        CNameRecord value;
        if (!pcursor->GetValue(value))
            return error("%s: failed to read value", __func__);

        pcursor->Next();

        if (value.deleted() || value.vNameOp.empty())
            continue;
        nameScan.push_back(make_pair(key, make_pair(value.vNameOp.back(), value.nExpiresAt)));
    }

    return true;
}

CHooks* InitHook()
{
    return new CNamecoinHooks();
}

static bool IsNameFeeEnough(const std::vector<NameTxInfo> &vnti, const CBlockIndex* pindexBlock, const CAmount& txFee) {
    if(!vnti.empty())
        for(int nAttempts = 10; nAttempts > 0 && pindexBlock != nullptr; nAttempts--) {
            pindexBlock = GetLastBlockIndex(pindexBlock, false); // Adjust to last PoW block
            CAmount requiredFee = 0;

            for (const auto& nti : vnti)
                requiredFee += GetNameOpFee(pindexBlock, nti.nRentalDays, nti.op, nti.name, nti.value);

            if(txFee >= requiredFee)
                return true; // Fee is enough

            pindexBlock = pindexBlock->pprev; // Prepare to next iteration
        } // for nAttempts && if !vnti.empty()

    return false; // Exhaust 10 attempts to find PoW block with valid fee
} // static IsNameFeeEnough

bool CNamecoinHooks::IsNameFeeEnough(const CTransactionRef& tx, const CAmount& txFee)
{
    std::vector<NameTxInfo> vnti = DecodeNameTx(IsV8Enabled(::ChainActive().Tip(), Params().GetConsensus()), tx);
    return ::IsNameFeeEnough(vnti, ::ChainActive().Tip(), txFee);
} // CNamecoinHooks::IsNameFeeEnough

//returns first name operation. I.e. name_new from chain like name_new->name_update->name_update->...->name_update
bool GetFirstTxOfName(const CNameVal& name, CTransactionRef& tx)
{
    CNameRecord nameRec;
    if (!pNameDB->ReadName(name, nameRec) || nameRec.vNameOp.empty())
        return false;
    CNameOperation& nameOp = nameRec.vNameOp[nameRec.nLastActiveChainIndex];

    if (!g_txindex || !g_txindex->FindTx(nameOp.txPos, tx))
        return error("GetFirstTxOfName() : could not read tx from disk");

    return true;
}

bool GetLastTxOfName(const CNameVal& name, CTransactionRef& tx, CNameRecord& nameRec)
{
    if (!pNameDB->ReadName(name, nameRec))
        return false;
    if (nameRec.deleted() || nameRec.vNameOp.empty())
        return false;

    CNameOperation& txPos = nameRec.vNameOp.back();

    if (!g_txindex || !g_txindex->FindTx(txPos.txPos, tx))
        return error("GetLastTxOfName() : could not read tx from disk");
    return true;
}

UniValue sendtoname(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    RPCHelpMan{"sendtoname",
    "\nSend emercoins to current owner of specified name.\n",
    {
        {"name", RPCArg::Type::STR, RPCArg::Optional::NO, "Name to send emercoin to\n"},
        {"amount", RPCArg::Type::NUM, RPCArg::Optional::NO, "Amount of emercoin to send\n"},
        {"comment", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "A comment used to store what the transaction is for.\n"
        "                             This is not part of the transaction, just kept in your wallet."},
        {"comment_to", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "A comment to store the name of the person or organization\n"
        "                             to which you're sending the transaction. This is not part of the \n"
        "                             transaction, just kept in your wallet."},
    },
    RPCResult{
        "{\n"
        "  \"sending to\": \"value\",        (string)  Emercoin address coins was sent to\n"
        "  \"transaction\":  \"value\",        (string)  Hex string of created transaction\n"
        "}\n"
    },
    RPCExamples{
        HelpExampleCli("sendtoname", "myname 10") + HelpExampleRpc("sendtoname", "myname 10")},
    }.Check(request);

    ObserveSafeMode();

    if (::ChainstateActive().IsInitialBlockDownload())
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, "Emercoin is downloading blocks...");

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    CNameVal name = nameValFromValue(request.params[0]);

    // Amount
    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount < MIN_TXOUT_AMOUNT)
        throw JSONRPCError(RPC_INSUFFICIENT_SEND_AMOUNT, "Send amount too small");

    // Wallet comments
    mapValue_t mapValue;
    if (!request.params[2].isNull() && !request.params[2].get_str().empty())
        mapValue["comment"] = request.params[2].get_str();
    if (!request.params[3].isNull() && !request.params[3].get_str().empty())
        mapValue["to"] = request.params[3].get_str();

    string error;
    CTxDestination dest;
    if (!GetNameCurrentAddress(name, dest, error))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, error);

    CCoinControl coin_control;
    coin_control.m_avoid_address_reuse = GetAvoidReuseFlag(pwallet, NullUniValue);
    // We also enable partial spend avoidance if reuse avoidance is set.
    coin_control.m_avoid_partial_spends |= coin_control.m_avoid_address_reuse;

    EnsureWalletIsUnlocked(pwallet);

    bool fSubtractFeeFromAmount = false;
    CTransactionRef tx = SendMoney(*locked_chain, pwallet, dest, nAmount, fSubtractFeeFromAmount, coin_control, std::move(mapValue));

    UniValue res(UniValue::VOBJ);
    res.pushKV("sending to", EncodeDestination(dest));
    res.pushKV("transaction", tx->GetHash().GetHex());
    return res;
}

bool GetNameCurrentAddress(const CNameVal& name, CTxDestination& dest, string& error)
{
    if (!pNameDB->Exists(name)) {
        error = "Name not found";
        return false;
    }

    CTransactionRef tx;
    CNameRecord nameRec;
    if (!GetLastTxOfName(name, tx, nameRec)) {
        error = "Failed to read last name transaction";
        return false;
    }

    NameTxInfo nti;
    if (!DecodeNameOutput(tx, nameRec.vNameOp.back().nOut, nti, true)) {
        error = "Failed to decode last name transaction";
        return false;
    }

    dest = DecodeDestination(nti.strAddress);
    if (!IsValidDestination(dest)) {
        error = "Invalid address: 0" + nti.strAddress;
        return false;
    }

    if (!NameActive(name)) {
        stringstream ss;
        ss << "This name have expired. If you still wish to send money to it's last owner you can use this command:\n"
           << "sendtoaddress " << nti.strAddress << " <your_amount> ";
        error = ss.str();
        return false;
    }

    return true;
}

UniValue name_list(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() > 2)
        throw runtime_error(
                "name_list [name] [valuetype]\n"
                "list my own names.\n"
                "\nArguments:\n"
                "1. name      (string, required) Restrict output to specific name.\n"
                "2. valuetype (string, optional) If \"hex\" or \"base64\" is specified then it will print value in corresponding format instead of string.\n"
                );

    if (::ChainstateActive().IsInitialBlockDownload())
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, "Emercoin is downloading blocks...");

    CNameVal nameUniq = request.params.size() > 0 ? nameValFromValue(request.params[0]) : CNameVal();
    string outputType = request.params.size() > 1 ? request.params[1].get_str() : "";

    map<CNameVal, NameTxInfo> mapNames, mapPending;
    GetNameList(nameUniq, mapNames, mapPending, pwallet);

    UniValue oRes(UniValue::VARR);
    for (const auto& item : mapNames)
    {
        UniValue oName(UniValue::VOBJ);
        oName.pushKV("name", stringFromNameVal(item.second.name));
        oName.pushKV("value", encodeNameVal(item.second.value, outputType));
        if (item.second.fIsMine == false)
            oName.pushKV("transferred", true);
        oName.pushKV("address", item.second.strAddress);
        oName.pushKV("expires_in", item.second.nExpiresAt - ::ChainActive().Height());
        if (item.second.nExpiresAt - ::ChainActive().Height() <= 0)
            oName.pushKV("expired", true);

        oRes.push_back(oName);
    }
    return oRes;
}

// read wallet name txs and extract: name, value, rentalDays, nOut and nExpiresAt
void GetNameList(const CNameVal& nameUniq, std::map<CNameVal, NameTxInfo> &mapNames, std::map<CNameVal, NameTxInfo> &mapPending, CWallet* pwallet)
{
    LOCK2(cs_main, pwallet->cs_wallet);

    // add all names from wallet tx that are in blockchain
    for (const auto &item : pwallet->mapWallet) {
        CBlockIndex* pindexPrev;
        if (item.second.m_confirm.status == CWalletTx::CONFIRMED) {
            pindexPrev = LookupBlockIndex(item.second.m_confirm.hashBlock);
            assert(pindexPrev); // confirmed transaction should never point to non-existing block index
            pindexPrev = pindexPrev->pprev;
        } else
            pindexPrev = ::ChainActive().Tip();

        std::vector<NameTxInfo> vntiWallet = DecodeNameTx(IsV8Enabled(pindexPrev, Params().GetConsensus()), item.second.tx);
        for (const auto& ntiWallet : vntiWallet) {
            if (mapNames.count(ntiWallet.name)) // already added info about this name
                continue;

            CTransactionRef tx;
            CNameRecord nameRec;
            if (!GetLastTxOfName(ntiWallet.name, tx, nameRec))
                continue;

            NameTxInfo nti;
            if (!DecodeNameOutput(tx, nameRec.vNameOp.back().nOut, nti, true, pwallet))
                continue;

            if (nameUniq.size() > 0 && nameUniq != nti.name)
                continue;

            if (!pNameDB->Exists(nti.name))
                continue;

            nti.nExpiresAt = nameRec.nExpiresAt;
            mapNames[nti.name] = nti;
        }
    }

    // add all pending names
    for (const auto &item : mapNamePending) {
        const set<COutPoint>& sNameOut = item.second;
        if (!sNameOut.size())
            continue;

        // if there is a set of pending op on a single name - select last one, by nTime
        uint32_t nTime = 0;
        CTxMemPool::txiter it2;
        uint32_t nOut = UINT32_MAX;

        for (const auto& out : sNameOut) {
            auto it = mempool.mapTx.find(out.hash);
            if (it == mempool.mapTx.end())
                continue;

            if (it->GetTx().nTime > nTime) {
                nTime = it->GetTx().nTime;
                it2 = it;
                nOut = out.n;
            }
        }

        if (nOut == UINT32_MAX)
            continue;

        NameTxInfo nti;
        if (!DecodeNameOutput(it2->GetSharedTx(), nOut, nti, true, pwallet))
            continue;

        if (nameUniq.size() > 0 && nameUniq != nti.name)
            continue;

        mapPending[nti.name] = nti;
    }
}

UniValue name_debug(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "name_debug\n"
            "Dump pending transactions id in the debug file.\n");

    LogPrintf("Pending:\n----------------------------\n");

    {
        LOCK(cs_main);
        for (const auto& pairPending : mapNamePending) {
            string name = stringFromNameVal(pairPending.first);
            LogPrintf("%s :\n", name);
            for (const auto& nameOut : pairPending.second) {
                LogPrintf("    ");
                if (!pwallet->mapWallet.count(nameOut.hash))
                    LogPrintf("foreign ");
                LogPrintf("    %s %d\n", nameOut.hash.GetHex(), nameOut.n);
            }
        }
    }
    LogPrintf("----------------------------\n");
    return true;
}

UniValue name_show(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 3)
        throw runtime_error(
            "name_show <name> [valuetype] [filepath]\n"
            "Show values of a name.\n"
            "\nArguments:\n"
            "1. name      (string, required).\n"
            "2. valuetype (string, optional) If \"hex\" or \"base64\" is specified then it will print value in corresponding format instead of string.\n"
            "3. filepath  (string, optional) save name value in binary format in specified file (file will be overwritten!).\n"
            );

    if (::ChainstateActive().IsInitialBlockDownload())
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, "Emercoin is downloading blocks...");

    UniValue oName(UniValue::VOBJ);
    CNameVal name = nameValFromValue(request.params[0]);
    string outputType = request.params.size() > 1 ? request.params[1].get_str() : "";
    string sName = stringFromNameVal(name);
    NameTxInfo nti;
    {
        LOCK(cs_main);
        CNameRecord nameRec;
        if (!pNameDB->ReadName(name, nameRec))
            throw JSONRPCError(RPC_WALLET_ERROR, "failed to read from name DB");

        if (nameRec.vNameOp.size() < 1)
            throw JSONRPCError(RPC_WALLET_ERROR, "no result returned");

        CTransactionRef tx;
        if (!g_txindex || !g_txindex->FindTx(nameRec.vNameOp.back().txPos, tx))
            throw JSONRPCError(RPC_WALLET_ERROR, "failed to read from from disk");

        if (!DecodeNameOutput(tx, nameRec.vNameOp.back().nOut, nti, true))
            throw JSONRPCError(RPC_WALLET_ERROR, "failed to decode name");

        oName.pushKV("name", sName);
        oName.pushKV("value", encodeNameVal(nti.value, outputType));
        oName.pushKV("txid", tx->GetHash().GetHex());
        oName.pushKV("address", nti.strAddress);
        oName.pushKV("vout", (int)nti.nOut);
        oName.pushKV("expires_in", nameRec.nExpiresAt - ::ChainActive().Height());
        oName.pushKV("expires_at", nameRec.nExpiresAt);
        oName.pushKV("time", (boost::int64_t)tx->nTime);
        if (nameRec.deleted())
            oName.pushKV("deleted", true);
        else
            if (nameRec.nExpiresAt - ::ChainActive().Height() <= 0)
                oName.pushKV("expired", true);
    }

    if (request.params.size() > 2)
    {
        string filepath = request.params[2].get_str();
        ofstream file;
        file.open(filepath.c_str(), ios::out | ios::binary | ios::trunc);
        if (!file.is_open())
            throw JSONRPCError(RPC_PARSE_ERROR, "Failed to open file. Check if you have permission to open it.");

        file.write((const char*)&nti.value[0], nti.value.size());
        file.close();
    }

    return oName;
}

UniValue name_history(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 3)
        throw std::runtime_error (
            "name_history <name> [fullhistory] [valuetype]\n"
            "\nLook up the current and all past data for the given name.\n"
            "\nArguments:\n"
            "1. name        (string, required) the name to query for\n"
            "2. fullhistory (boolean, optional) shows full history, even if name is not active\n"
            "3. valuetype   (string, optional) If \"hex\" or \"base64\" is specified then it will print value in corresponding format instead of string.\n"
            "\nResult:\n"
            "[\n"
            "  {\n"
            "    \"txid\": \"xxxx\",            (string) transaction id"
            "    \"time\": xxxxx,               (numeric) transaction time"
            "    \"height\": xxxxx,             (numeric) height of block with this transaction"
            "    \"address\": \"xxxx\",         (string) address to which transaction was sent"
            "    \"address_is_mine\": \"xxxx\", (string) shows \"true\" if this is your address, otherwise not visible"
            "    \"operation\": \"xxxx\",       (string) name operation that was performed in this transaction"
            "    \"days_added\": xxxx,          (numeric) days added (1 day = 175 blocks) to name expiration time, not visible if 0"
            "    \"value\": xxxx,               (numeric) name value in this transaction; not visible when name_delete was used"
            "  }\n"
            "]\n"
            "\nExamples:\n"
            + HelpExampleCli ("name_history", "\"myname\"")
            + HelpExampleRpc ("name_history", "\"myname\"")
        );

    if (::ChainstateActive().IsInitialBlockDownload())
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, "Emercoin is downloading blocks...");

    CNameVal name = nameValFromValue(request.params[0]);
    bool fFullHistory = request.params.size() > 1 ? request.params[1].get_bool() : false;
    string outputType = request.params.size() > 2 ? request.params[2].get_str() : "";

    CNameRecord nameRec;
    {
        LOCK(cs_main);
        if (!pNameDB->ReadName(name, nameRec))
            throw JSONRPCError(RPC_DATABASE_ERROR, "failed to read from name DB");
    }

    if (nameRec.vNameOp.empty())
        throw JSONRPCError(RPC_DATABASE_ERROR, "record for this name exists, but transaction list is empty");

    if (!fFullHistory && !NameActive(name))
        throw JSONRPCError(RPC_MISC_ERROR, "record for this name exists, but this name is not active");

    UniValue res(UniValue::VARR);
    for (unsigned int i = fFullHistory ? 0 : nameRec.nLastActiveChainIndex; i < nameRec.vNameOp.size(); i++) {
        CTransactionRef tx;

        if (!g_txindex || !g_txindex->FindTx(nameRec.vNameOp[i].txPos, tx))
            throw JSONRPCError(RPC_DATABASE_ERROR, "could not read transaction from disk");

        NameTxInfo nti;
        if (!DecodeNameOutput(tx, nameRec.vNameOp[i].nOut, nti, true, pwallet))
            throw JSONRPCError(RPC_DATABASE_ERROR, "failed to decode name transaction");

        UniValue obj(UniValue::VOBJ);
        obj.pushKV("txid",             tx->GetHash().ToString());
        obj.pushKV("time",             (boost::int64_t)tx->nTime);
        obj.pushKV("height",           nameRec.vNameOp[i].nHeight);
        obj.pushKV("address",          nti.strAddress);
        obj.pushKV("vout",             (int)nti.nOut);
        if (nti.fIsMine)
            obj.pushKV("address_is_mine",  "true");
        obj.pushKV("operation",        stringFromOp(nti.op));
        if (nti.op == OP_NAME_UPDATE || nti.op == OP_NAME_NEW)
            obj.pushKV("days_added", nti.nRentalDays);
        if (nti.op == OP_NAME_UPDATE || nti.op == OP_NAME_NEW)
            obj.pushKV("value", encodeNameVal(nti.value, outputType));

        res.push_back(obj);
    }

    return res;
}

UniValue name_mempool(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() > 1)
        throw std::runtime_error (
            "name_mempool [valuetype]\n"
            "\nArguments:\n"
            "1. valuetype   (string, optional) If \"hex\" or \"base64\" is specified then it will print value in corresponding format instead of string.\n"
            "\nList pending name transactions in mempool.\n"
            "\nResult:\n"
            "[\n"
            "  {\n"
            "    \"name\": \"xxxx\",            (string) name"
            "    \"txid\": \"xxxx\",            (string) transaction id"
            "    \"time\": xxxxx,               (numeric) transaction time"
            "    \"address\": \"xxxx\",         (string) address to which transaction was sent"
            "    \"vout\": xxxxx,               (numeric) TX output number(n)"
            "    \"address_is_mine\": \"xxxx\", (string) shows \"true\" if this is your address, otherwise not visible"
            "    \"operation\": \"xxxx\",       (string) name operation that was performed in this transaction"
            "    \"days_added\": xxxx,          (numeric) days added (1 day = 175 blocks) to name expiration time, not visible if 0"
            "    \"value\": xxxx,               (numeric) name value in this transaction; not visible when name_delete was used"
            "  }\n"
            "]\n"
            "\nExamples:\n"
            + HelpExampleCli ("name_mempool", "" )
            + HelpExampleRpc ("name_mempool", "" )
        );

    string outputType = request.params.size() > 0 ? request.params[0].get_str() : "";

    UniValue res(UniValue::VARR);
    LOCK(mempool.cs);
    for (const auto& pairPending : mapNamePending) {
        string sName = stringFromNameVal(pairPending.first);
        for (const auto& nameOut : pairPending.second) {
            if (!mempool.exists(nameOut.hash))
                continue;

            const CTransactionRef& tx = mempool.get(nameOut.hash);

            NameTxInfo nti;
            if (!DecodeNameOutput(tx, nameOut.n, nti, true, pwallet))
                throw JSONRPCError(RPC_DATABASE_ERROR, "failed to decode name output");

            UniValue obj(UniValue::VOBJ);
            obj.pushKV("name",             sName);
            obj.pushKV("txid",             nameOut.hash.ToString());
            obj.pushKV("time",             (boost::int64_t)tx->nTime);
            obj.pushKV("address",          nti.strAddress);
            if (nti.fIsMine)
                obj.pushKV("address_is_mine",  "true");
            obj.pushKV("operation",        stringFromOp(nti.op));
            if (nti.op == OP_NAME_UPDATE || nti.op == OP_NAME_NEW)
                obj.pushKV("days_added", nti.nRentalDays);
            if (nti.op == OP_NAME_UPDATE || nti.op == OP_NAME_NEW)
                obj.pushKV("value", encodeNameVal(nti.value, outputType));

            res.push_back(obj);
        }
    }
    return res;
}

// used for sorting in name_filter by nHeight
bool mycompare2 (const UniValue& lhs, const UniValue& rhs)
{
    int pos = 2; //this should exactly match field name position in name_filter

    return lhs[pos].get_int() < rhs[pos].get_int();
}
UniValue name_filter(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() > 6)
        throw runtime_error(
                "name_filter [regexp] [maxage=0] [from=0] [nb=0] [stat] [valuetype]\n"
                "scan and filter names\n"
                "[regexp] : apply [regexp] on names, empty means all names\n"
                "[maxage] : look in last [maxage] blocks\n"
                "[from] : show results from number [from]\n"
                "[nb] : show [nb] results, 0 means all\n"
                "[stat] : show some stats instead of results\n"
                "[valuetype] : if \"hex\" or \"base64\" is specified then it will print value in corresponding format instead of string.\n"
                "name_filter \"\" 5 # list names updated in last 5 blocks\n"
                "name_filter \"^id/\" # list all names from the \"id\" namespace\n"
                "name_filter \"^id/\" 0 0 0 stat # display stats (number of names) on active names from the \"id\" namespace\n"
                );

    if (::ChainstateActive().IsInitialBlockDownload())
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, "Emercoin is downloading blocks...");

    int nCountFrom = 0;
    int nCountNb = 0;

    string strRegexp  = request.params.size() > 0 ? request.params[0].get_str() : "";
    int nMaxAge       = request.params.size() > 1 ? request.params[1].get_int() : 0;
    int nFrom         = request.params.size() > 2 ? request.params[2].get_int() : 0;
    int nNb           = request.params.size() > 3 ? request.params[3].get_int() : 0;
    bool fStat        = request.params.size() > 4 ? (request.params[4].get_str() == "stat" ? true : false) : false;
    string outputType = request.params.size() > 5 ? request.params[5].get_str() : "";

    vector<UniValue> oRes;

    CNameVal name;
    vector<pair<CNameVal, pair<CNameOperation,int> > > nameScan;
    {
        LOCK(cs_main);
        if (!pNameDB->ScanNames(name, 0, nameScan))
            throw JSONRPCError(RPC_WALLET_ERROR, "scan failed");
    }

    // compile regex once
    using namespace boost::xpressive;
    smatch nameparts;
    sregex cregex = sregex::compile(strRegexp);

    for (const auto& pairScan : nameScan) {
        string name = stringFromNameVal(pairScan.first);

        // regexp
        if(strRegexp != "" && !regex_search(name, nameparts, cregex))
            continue;

        CNameOperation txName = pairScan.second.first;

        CNameRecord nameRec;
        if (!pNameDB->ReadName(pairScan.first, nameRec))
            continue;

        // max age
        int nHeight = nameRec.vNameOp[nameRec.nLastActiveChainIndex].nHeight;
        if(nMaxAge != 0 && ::ChainActive().Height() - nHeight >= nMaxAge)
            continue;

        // from limits
        nCountFrom++;
        if(nCountFrom < nFrom + 1)
            continue;

        UniValue oName(UniValue::VOBJ);
        if (!fStat) {
            oName.pushKV("name", name);
            oName.pushKV("value", limitString(encodeNameVal(txName.value, outputType), 300, "\n...(value too large - use name_show to see full value)"));
            oName.pushKV("registered_at", nHeight); // pos = 2 in comparison function (above name_filter)
            int nExpiresIn = nameRec.nExpiresAt - ::ChainActive().Height();
            oName.pushKV("expires_in", nExpiresIn);
            if (nExpiresIn <= 0)
                oName.pushKV("expired", true);
        }
        oRes.push_back(oName);

        nCountNb++;
        // nb limits
        if(nNb > 0 && nCountNb >= nNb)
            break;
    }

    UniValue oRes2(UniValue::VARR);
    if (!fStat) {
        std::sort(oRes.begin(), oRes.end(), mycompare2); //sort by nHeight
        for (unsigned int idx = 0; idx < oRes.size(); idx++) {
            const UniValue& res = oRes[idx];
            oRes2.push_back(res);
        }
    } else {
        UniValue oStat(UniValue::VOBJ);
        oStat.pushKV("blocks",    ::ChainActive().Height());
        oStat.pushKV("count",     (int)oRes2.size());
        //oStat.pushKV("sha256sum", SHA256(oRes), true);
        return oStat;
    }

    return oRes2;
}

UniValue name_scan(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() > 4)
        throw runtime_error(
                "name_scan [start-name] [max-returned] [max-value-length=0] [valuetype]\n"
                "Scan all names, starting at [start-name] and returning [max-returned] number of entries (default 500)\n"
                "[max-value-length] : control how much of value is shown (0 = full value)\n"
                "[valuetype] : if \"hex\" or \"base64\" is specified then it will print value in corresponding format instead of a string.\n"
                );

    if (::ChainstateActive().IsInitialBlockDownload())
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, "Emercoin is downloading blocks...");

    CNameVal name      = request.params.size() > 0 ? nameValFromValue(request.params[0]) : CNameVal();
    int nMax           = request.params.size() > 1 ? request.params[1].get_int() : 500;
    int nMaxShownValue = request.params.size() > 2 ? request.params[2].get_int() : 0;
    string outputType  = request.params.size() > 3 ? request.params[3].get_str() : "";

    UniValue oRes(UniValue::VARR);

    vector<pair<CNameVal, pair<CNameOperation,int> > > nameScan;
    {
        LOCK(cs_main);
        if (!pNameDB->ScanNames(name, nMax, nameScan))
            throw JSONRPCError(RPC_WALLET_ERROR, "scan failed");
    }

    for (const auto& pairScan : nameScan) {
        UniValue oName(UniValue::VOBJ);
        string name = stringFromNameVal(pairScan.first);
        oName.pushKV("name", name);

        CNameOperation txName = pairScan.second.first;
        int nExpiresAt    = pairScan.second.second;
        CNameVal value = txName.value;

        oName.pushKV("value", limitString(encodeNameVal(value, outputType), nMaxShownValue, "\n...(value too large - use name_show to see full value)"));
        oName.pushKV("expires_in", nExpiresAt - ::ChainActive().Height());
        if (nExpiresAt - ::ChainActive().Height() <= 0)
            oName.pushKV("expired", true);

        oRes.push_back(oName);
    }

    return oRes;
}

UniValue name_scan_address(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 3)
        throw runtime_error(
                "name_scan_address <address> [max-value-length=0] [valuetype]\n"
                "Print names that belong to specific address\n"
                "[max-value-length] : control how much of name value is shown (0 = full value)\n"
                "[valuetype] : if \"hex\" or \"base64\" is specified then it will print value in corresponding format instead of a string.\n"
                );

    if (!fNameAddressIndex)
        throw JSONRPCError(RPC_DATABASE_ERROR, "Name-address index is not available. Add nameaddress=1 to emercoin.conf to enable it.");

    if (::ChainstateActive().IsInitialBlockDownload())
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, "Emercoin is downloading blocks...");

    string address     = request.params.size() > 0 ? request.params[0].get_str() : "";
    int nMaxShownValue = request.params.size() > 1 ? request.params[1].get_int() : 0;
    string outputType  = request.params.size() > 2 ? request.params[2].get_str() : "";

    LOCK(cs_main);
    UniValue oRes(UniValue::VARR);

    set<CNameVal> names;
    if (!pNameAddressDB->Read(address, names))
        throw JSONRPCError(RPC_WALLET_ERROR, "found nothing");

    for (const auto& name : names) {
        UniValue oName(UniValue::VOBJ);

        CNameRecord nameRec;
        if (!pNameDB->ReadName(name, nameRec))
            throw JSONRPCError(RPC_DATABASE_ERROR, "failed to read from name DB");

        CTransactionRef tx;
        if (!g_txindex || !g_txindex->FindTx(nameRec.vNameOp.back().txPos, tx))
            throw JSONRPCError(RPC_WALLET_ERROR, "failed to read from from disk");

        NameTxInfo nti;
        if (!DecodeNameOutput(tx, nameRec.vNameOp.back().nOut, nti))
            throw JSONRPCError(RPC_WALLET_ERROR, "failed to decode name");

        oName.pushKV("name", stringFromNameVal(name));
        oName.pushKV("value", limitString(encodeNameVal(nti.value, outputType), nMaxShownValue, "\n...(value too large - use name_show to see full value)"));
        oName.pushKV("txid", tx->GetHash().GetHex());
        oName.pushKV("address", nti.strAddress);
        oName.pushKV("expires_in", nameRec.nExpiresAt - ::ChainActive().Height());
        oName.pushKV("expires_at", nameRec.nExpiresAt);
        oName.pushKV("time", (boost::int64_t)tx->nTime);
        if (nameRec.deleted())
            oName.pushKV("deleted", true);
        else
            if (nameRec.nExpiresAt - ::ChainActive().Height() <= 0)
                oName.pushKV("expired", true);

        oRes.push_back(oName);
    }

    return oRes;
}

bool createNameScript(CScript& nameScript, const CNameVal& name, const CNameVal& value, int nRentalDays, int op, string& err_msg)
{
    if (op == OP_NAME_DELETE)
    {
        nameScript << op << OP_DROP << name << OP_DROP;
        return true;
    }

    NameTxInfo nti(name, value, nRentalDays, op, -1, err_msg);
    if (!checkNameValues(nti)) {
        err_msg = nti.err_msg;
        return false;
    }

    vector<unsigned char> vchRentalDays = CScriptNum(nRentalDays).getvch();

    //add name and rental days
    nameScript << op << OP_DROP << name << vchRentalDays << OP_2DROP;

    // split value in 520 bytes chunks and add it to script
    {
        unsigned int nChunks = ceil(value.size() / 520.0);

        for (unsigned int i = 0; i < nChunks; i++)
        {   // insert data
            vector<unsigned char>::const_iterator sliceBegin = value.begin() + i*520;
            vector<unsigned char>::const_iterator sliceEnd = min(value.begin() + (i+1)*520, value.end());
            vector<unsigned char> vchSubValue(sliceBegin, sliceEnd);
            nameScript << vchSubValue;
        }

            //insert end markers
        for (unsigned int i = 0; i < nChunks / 2; i++)
            nameScript << OP_2DROP;
        if (nChunks % 2 != 0)
            nameScript << OP_DROP;
    }
    return true;
}

UniValue name_new(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    RPCHelpMan{"name_new",
    "\nCreates new key->value pair which expires after specified number of days.\n"
    "Cost is square root of (1% of last PoW + 1% per year of last PoW).\n",
    {
        {"name", RPCArg::Type::STR, RPCArg::Optional::NO, "Name to create"},
        {"value", RPCArg::Type::STR, RPCArg::Optional::NO, "Value to write inside name"},
        {"days", RPCArg::Type::NUM, RPCArg::Optional::NO, "How many days this name will be active (1 day~=175 blocks)"},
        {"toaddress", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "Address of recipient. Empty string = transaction to yourself"},
        {"valuetype", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "Interpretation of value string. Can be \"hex\", \"base64\" or filepath.\n"
            "       not specified or empty - Write value as a unicode string.\n"
            "       \"hex\" or \"base64\" - Decode value string as a binary data in hex or base64 string format.\n"
            "       otherwise - Decode value string as a filepath from which to read the data."
        }
    },
    RPCResult{
        "{\n"
        "  (string)    Hex of created transaction\n"
        "}\n"
    },
    RPCExamples{
        HelpExampleCli("name_new", "myname abc 30") + HelpExampleRpc("name_new", "myname abc 30")},
    }.Check(request);

    ObserveSafeMode();

    UniValue names(UniValue::VARR);
    UniValue name(UniValue::VOBJ);
    name.pushKV("NEW", request.params[0]);
    name.pushKV("value", request.params[1]);
    name.pushKV("days", request.params[2].get_int());
    if (request.params.size() > 3)
        name.pushKV("toaddress", request.params[3].get_str());
    if (request.params.size() > 4)
        name.pushKV("valuetype", request.params[4].get_str());
    names.push_back(name);

    NameTxReturn ret = name_operation(names, pwallet);
    if (!ret.ok)
        throw JSONRPCError(ret.err_code, ret.err_msg);
    return ret.hex.GetHex();
}

UniValue name_update(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    RPCHelpMan{"name_update",
    "\nUpdate name value, add days to expiration time and possibly transfer a name to diffrent address.\n",
    {
        {"name", RPCArg::Type::STR, RPCArg::Optional::NO, "Name to update"},
        {"value", RPCArg::Type::STR, RPCArg::Optional::NO, "Value to write inside name"},
        {"days", RPCArg::Type::NUM, RPCArg::Optional::NO, "How many days this name will be active (1 day~=175 blocks)"},
        {"toaddress", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "Address of recipient. Empty string = transaction to yourself"},
        {"valuetype", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "Interpretation of value string. Can be \"hex\", \"base64\" or filepath.\n"
            "       not specified or empty - Write value as a unicode string.\n"
            "       \"hex\" or \"base64\" - Decode value string as a binary data in hex or base64 string format.\n"
            "       otherwise - Decode value string as a filepath from which to read the data."
        }
    },
    RPCResult{
        "{\n"
        "  (string)    Hex of created transaction\n"
        "}\n"
    },
    RPCExamples{
        HelpExampleCli("name_update", "myname abc 30") + HelpExampleRpc("name_update", "myname abc 30")},
    }.Check(request);

    ObserveSafeMode();

    UniValue names(UniValue::VARR);
    UniValue name(UniValue::VOBJ);
    name.pushKV("UPDATE", request.params[0]);
    name.pushKV("value", request.params[1]);
    name.pushKV("days", request.params[2].get_int());
    if (request.params.size() > 3)
        name.pushKV("toaddress", request.params[3].get_str());
    if (request.params.size() > 4)
        name.pushKV("valuetype", request.params[4].get_str());
    names.push_back(name);

    NameTxReturn ret = name_operation(names, pwallet);
    if (!ret.ok)
        throw JSONRPCError(ret.err_code, ret.err_msg);
    return ret.hex.GetHex();
}

UniValue name_delete(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    RPCHelpMan{"name_delete",
    "\nDelete a name if you own it. Others may do name_new after this command.\n",
    {
        {"name", RPCArg::Type::STR, RPCArg::Optional::NO, "Name to delete"},
    },
    RPCResult{
        "{\n"
        "  (string)    Hex of created transaction\n"
        "}\n"
    },
    RPCExamples{
        HelpExampleCli("name_delete", "myname") + HelpExampleRpc("name_delete", "myname")},
    }.Check(request);

    ObserveSafeMode();

    UniValue name(UniValue::VOBJ);
    name.pushKV("DELETE", request.params[0]);
    // days, value is not set

    UniValue names(UniValue::VARR);
    names.push_back(name);

    NameTxReturn ret = name_operation(names, pwallet);
    if (!ret.ok)
        throw JSONRPCError(ret.err_code, ret.err_msg);
    return ret.hex.GetHex();
}
/*---------------------------------------------------------------------------------------------*/
const static int  opndx2OP[]   = { OP_NAME_NEW, OP_NAME_UPDATE, OP_NAME_DELETE };
const static char name_OP[][8] = { "NEW",       "UPDATE",       "DELETE"       };
// Returns 0,1,2 for { "NEW", "UPDATE", "DELETE" } josn key
static int name_opndx(const UniValue &nameInfo) {
    int opndx = -1; // undef operation
    for(int i = 0; i < 3; i++)
        if(nameInfo.exists(name_OP[i])) {
            if(opndx >= 0)
                throw JSONRPCError(RPC_TYPE_ERROR, std::string("Opcode [NEW/UPDATE/DELETE] must be specified just once"));
            if (!nameInfo[name_OP[i]].isStr())
                throw JSONRPCError(RPC_TYPE_ERROR, std::string("Opcode [NEW/UPDATE/DELETE]  param must be a string"));
            opndx = i;
        }
    if(opndx < 0)
        throw JSONRPCError(RPC_TYPE_ERROR, std::string("Opcode [NEW/UPDATE/DELETE]  param must be specified"));
    return opndx;
} // name_OP

/*---------------------------------------------------------------------------------------------*/
UniValue name_updatemany(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    RPCHelpMan{"name_updatemany",
    "\nCreates, updates or deletes key->value pairs.\n",
    {
        {"names", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of name operations", {
            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "", {
                {"NEW/UPDATE/DELETE", RPCArg::Type::STR, RPCArg::Optional::NO, "NameOP and Name"},
                {"value", RPCArg::Type::STR, RPCArg::Optional::NO, "Value to write inside name"},
                {"days", RPCArg::Type::NUM, RPCArg::Optional::NO, "How many days this name will be active (1 day~=175 blocks)"},
                {"toaddress", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "Address of recipient. Empty string = transaction to yourself"},
                {"valuetype", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "Interpretation of value string. Can be \"hex\", \"base64\" or filepath.\n"
                    "       not specified or empty - Write value as a unicode string.\n"
                    "       \"hex\" or \"base64\" - Decode value string as a binary data in hex or base64 string format.\n"
                    "       otherwise - Decode value string as a filepath from which to read the data."
                },
            }}
        }}
    },
    RPCResult{
        "{\n"
        "  (string)    Hex of created transaction\n"
        "}\n"
    },
    RPCExamples{
        HelpExampleCli("name_updatemany", "\"[{\\\"NEW\\\":\\\"myname\\\", \\\"value\\\":\\\"Hello\\\", \\\"days\\\":3}]\"")
      + HelpExampleRpc("name_updatemany", "\"[{\\\"NEW\\\":\\\"myname\\\", \\\"value\\\":\\\"Hello\\\", \\\"days\\\":3}]\"")},
    }.Check(request);

    ObserveSafeMode();

    RPCTypeCheck(request.params, {UniValue::VARR}, true);
    UniValue names = request.params[0].get_array();

    // Check syntax
    for (size_t i = 0; i < names.size(); ++i) {
        const auto& nameInfo = names[i];
        if (!nameInfo.isObject())
            throw JSONRPCError(RPC_TYPE_ERROR, std::string("Invalid array element: it has to be string or object"));

        if(opndx2OP[name_opndx(nameInfo)] == OP_NAME_DELETE)
            continue; // DEL - do not need check days/value/toaddress/valuetype

        // NEW or UPDATE - must check days/value/toaddress/valuetype
        // This is not "Delete op - must be present value/days, and optional toaddress/valuetype"
        if (!nameInfo.exists("value"))
            throw JSONRPCError(RPC_TYPE_ERROR, std::string("You must specify value"));
        if (!nameInfo["value"].isStr())
            throw JSONRPCError(RPC_TYPE_ERROR, std::string("Value must be string"));

        if (!nameInfo.exists("days"))
            throw JSONRPCError(RPC_TYPE_ERROR, std::string("You must specify days"));
        if (!nameInfo["days"].isNum())
            throw JSONRPCError(RPC_TYPE_ERROR, std::string("Days must be an integer greater than 0"));

        if (nameInfo.exists("toaddress") && !nameInfo["toaddress"].isStr())
            throw JSONRPCError(RPC_TYPE_ERROR, std::string("Address must be a string"));

        if (nameInfo.exists("valuetype") && !nameInfo["valuetype"].isStr())
            throw JSONRPCError(RPC_TYPE_ERROR, std::string("Value type must be a string"));
    } // iterate names array

    NameTxReturn ret = name_operation(names, pwallet);
    if (!ret.ok)
        throw JSONRPCError(ret.err_code, ret.err_msg);

    return ret.hex.GetHex();
}

// this function does not verify the existance of json input fields - it just assumes that they were correctly set
NameTxReturn name_operation(UniValue names, CWallet* pwallet) {
    NameTxReturn ret;
    ret.err_code = RPC_INTERNAL_ERROR; // default value in case of abnormal exit
    ret.err_msg = "unkown error";
    ret.ok = false;

    if (::ChainstateActive().IsInitialBlockDownload()) {
        ret.err_code = RPC_CLIENT_IN_INITIAL_DOWNLOAD;
        ret.err_msg = "Emercoin is downloading blocks...";
        return ret;
    }

    auto locked_chain = pwallet->chain().lock();
    LOCK2(cs_main, pwallet->cs_wallet);

    bool fMultiName = IsV8Enabled(::ChainActive().Tip(), Params().GetConsensus());
    if (!fMultiName && names.size() > 1) {
        ret.err_code = RPC_INVALID_PARAMETER;
        ret.err_msg = "Multi-name are not enabled yet...";
        return ret;
    }

    CAmount nameFee = 0;
    std::set<CNameVal> dup_names; // Name duplicate within transaction is not allowed
    std::vector<CScript> vNameScript;

    // This TX will be convertee to TxRef, and passed to CreateTransaction.
    // Vinst of this TX will ve used for add to nameTX vins for spend name coins
    CMutableTransaction tmpTx;
    tmpTx.nVersion = NAMECOIN_TX_VERSION;

    for (size_t i = 0; i < names.size(); ++i) {
        const auto& nameInfo = names[i];
        // try to read inputs
        int opndx = name_opndx(nameInfo);

        // Extract name by op-key NEW/UPDATE/DELETE
        CNameVal name = nameValFromValue(nameInfo[name_OP[opndx]]);
        if(dup_names.count(name)) {
            ret.err_msg = "Name duplicate is not allowed";
            return ret;
        }
        dup_names.insert(name);

        int op = opndx2OP[opndx];
        // wait until other name operation on this name are completed
        if (mapNamePending.count(name) && mapNamePending[name].size()) {
            stringstream ss;
            ss << "there are " << mapNamePending[name].size() <<
                  " pending operations on that name, including " << mapNamePending[name].begin()->hash.GetHex();
            ret.err_msg = ss.str();
            return ret;
        }

        // check if op can be aplied to name remaining time
        if (NameActive(name)) {
            if (op == OP_NAME_NEW) {
                ret.err_msg = "name_new on an unexpired name";
                return ret;
            }
        } else {
            if (op == OP_NAME_UPDATE || op == OP_NAME_DELETE) {
                ret.err_msg = stringFromOp(op) + " on an expired name";
                return ret;
            }
        }

        CNameVal value;
        int      nRentalDays = 0;
        string   strAddress, strValueType;

        if(op != OP_NAME_DELETE) {
            value = nameValFromValue(nameInfo["value"]);
            if (value.empty()) {
                ret.err_msg = "value must not be empty";
                return ret;
            }
            nRentalDays = nameInfo["days"].get_int();
            if(nameInfo.exists("toaddress"))
                strAddress = nameInfo["toaddress"].get_str();
            if(nameInfo.exists("valuetype"))
                strValueType = nameInfo["valuetype"].get_str();

            // decode value or leave it as is
            if (!strValueType.empty()) {
                const string strValue(stringFromNameVal(value));
                if (strValueType == "hex") {
                    if (!IsHex(strValue)) {
                        ret.err_msg = "failed to decode value as hex";
                        return ret;
                    }
                    value = ParseHex(strValue);
                }
                else if (strValueType == "base64") {
                    bool fInvalid = false;
                    value = DecodeBase64(strValue.c_str(), &fInvalid);
                    if (fInvalid) {
                        ret.err_msg = "failed to decode value as base64";
                        return ret;
                    }
                } else { // decode as filepath
                    std::ifstream ifs;
                    ifs.open(strValue.c_str(), std::ios::binary | std::ios::ate);
                    if (!ifs) {
                        ret.err_msg = "failed to open file";
                        return ret;
                    }
                    std::streampos fileSize = ifs.tellg();
                    if (fileSize > MAX_VALUE_LENGTH) {
                        ret.err_msg = "file is larger than maximum allowed size";
                        return ret;
                    }

                    ifs.clear();
                    ifs.seekg(0, std::ios::beg);

                    value.resize(fileSize);
                    if (!ifs.read(reinterpret_cast<char*>(&value[0]), fileSize)) {
                        ret.err_msg = "failed to read file";
                        return ret;
                    }
                } // decode as filepath
            } // if (!strValueType.empty())
        } // if(op != OP_NAME_DELETE)

        if (op != OP_NAME_NEW) {
            // Fetch previous TX output and attach to this TX as input
            CTransactionRef prevTx;
            CNameRecord nameRec;
            if (!GetLastTxOfName(name, prevTx, nameRec)) {
                ret.err_msg = "could not find prev txIn with this name";
                return ret;
            }
            int prevTxnOut = nameRec.vNameOp.back().nOut;
            NameTxInfo prev_nti;
            if (!DecodeNameOutput(prevTx, prevTxnOut, prev_nti, true, pwallet)) {
                ret.err_msg = "failed to decode txIn UTXO";
                return ret;
            }

            if (!prev_nti.fIsMine) {
                ret.err_msg = "prev name tx is not yours or is not spendable";
                return ret;
            }
            // Attach name input into tmpTx, and add credit from this UTXO
            CInputCoin name_utxo(prevTx, prevTxnOut);
            tmpTx.vin.push_back(CTxIn(name_utxo.outpoint, CScript()));
            nameFee -= name_utxo.effective_value;
        } // if (op != OP_NAME_NEW)

        // create namescript
        CScript scriptPubKey;
        CScript nameScript;
        string prevMsg = ret.err_msg;
        if (!createNameScript(nameScript, name, value, nRentalDays, op, ret.err_msg)) {
            if (prevMsg == ret.err_msg)  // in case error message not changed, but error still occurred
                ret.err_msg = "failed to create name script";
            return ret;
        }

        // add destination to namescript
        if (!strAddress.empty() && strAddress != "legacy") {
            CTxDestination dest = DecodeDestination(strAddress);
            if (!IsValidDestination(dest)) {
                ret.err_code = RPC_INVALID_ADDRESS_OR_KEY;
                ret.err_msg = "emercoin address is invalid";
                return ret;
            }
            scriptPubKey = GetScriptForDestination(dest);
        } else {
            CPubKey vchPubKey;
            if(!pwallet->GetKeyFromPool(vchPubKey)) {
                ret.err_msg = "failed to get key from pool";
                return ret;
            }

            scriptPubKey = strAddress.empty()?
                GetScriptForDestination(WitnessV0KeyHash(PKHash(vchPubKey))) :
                GetScriptForDestination(PKHash(vchPubKey));
        }
        nameScript += scriptPubKey;

        // verify namescript
        NameTxInfo nti;
        if (!DecodeNameScript(nameScript, nti)) {
            ret.err_msg = nti.err_msg;
            return ret;
        }

        nameFee += GetNameOpFee(::ChainActive().Tip(), nRentalDays, op, name, value);
        vNameScript.push_back(nameScript);
    } // for nameOP/nameInfo list

    // set fee and send!
    std::vector<CRecipient> vecSend;
    CAmount nValue = 0;
    CAmount nNameTxoutAmount = 0;
    if (gArgs.IsArgSet("-nametxoutamount") &&
       (!ParseMoney(gArgs.GetArg("-nametxoutamount", ""), nNameTxoutAmount) || !MoneyRange(nNameTxoutAmount))
       ) {
        ret.err_msg = strprintf("Error: Unable to ParseMoney(-nametxoutamount)");
        return ret;
    }
    if(nNameTxoutAmount < MIN_TXOUT_AMOUNT)
        nNameTxoutAmount = MIN_TXOUT_AMOUNT;
    bool fSubtractFeeFromAmount = false;
    for (const auto& script : vNameScript) {
        CRecipient recipient = {script, nNameTxoutAmount, fSubtractFeeFromAmount};
        nValue += nNameTxoutAmount;
        vecSend.push_back(recipient);
    }

    CCoinControl coin_control;
    CAmount curBalance = pwallet->GetBalance(0, coin_control.m_avoid_address_reuse).m_mine_trusted;
    SendMoneyCheck(nValue, curBalance);

    // Create and send the transaction
    CAmount nFeeRequired;
    std::string strError;
    int nChangePosRet = -1;
    // Pass accumulated NameVINs into CreateTransaction(), get return final name TX
    CTransactionRef tx = MakeTransactionRef(std::move(tmpTx));

    if (!pwallet->CreateTransaction(nameFee, fMultiName, *locked_chain, vecSend, tx, nFeeRequired, nChangePosRet, strError, coin_control)) {
        if (!fSubtractFeeFromAmount && nValue + nFeeRequired > curBalance)
            ret.err_msg = strprintf("Error: This transaction requires a transaction fee of at least %s", FormatMoney(nFeeRequired));
        return ret;
    }
    CValidationState state;
    mapValue_t mapValue;
    if (!pwallet->CommitTransaction(tx, std::move(mapValue), {} /* orderForm */, state)) {
        ret.err_msg = strprintf("Error: The transaction was rejected! Reason given: %s", FormatStateMessage(state));
        return ret;
    }

    //success! collect info and return
    //emcTODOne - return a list of addresses? (currently addressed aren't used)
    // Used in GUI only, there is single address
    CTxDestination address;
    if (ExtractDestination(vNameScript[0], address)) {
        ret.address = EncodeDestination(address);
    }
    ret.hex = tx->GetHash();
    ret.ok = true;
    return ret;
} // name_operation

bool reindexNameIndex()
{
    if (!g_txindex)
        return error("createNameIndexes() : transaction index not available");

    LogPrintf("Scanning blockchain for names to create fast index...\n");
    LOCK(cs_main);
    CCoinsViewCache view(&::ChainstateActive().CoinsTip());
    int maxHeight = ::ChainActive().Height();
    if (maxHeight <= 0)
        return true;
    int reportDone = 0;
    for (int nHeight=0; nHeight<=maxHeight; nHeight++) {
        int percentageDone = (100*nHeight / maxHeight);
        if (reportDone < percentageDone/10) {
            // report every 10% step
            LogPrintf("[%d%%]...", percentageDone);
            reportDone = percentageDone/10;
        }
        if (nHeight % 10 == 0)
            uiInterface.ShowProgress("Creating name index (do not close app!)...", percentageDone, false);

        CBlockIndex* pindex = ::ChainActive()[nHeight];
        CBlock block;
        if (!ReadBlockFromDisk(block, pindex, Params().GetConsensus()))
            return error("%s: *** ReadBlockFromDisk failed at %d, hash=%s", __func__, pindex->nHeight, pindex->GetBlockHash().ToString());

        // collect name tx from block
        vector<nameCheckResult> vName;
        CDiskTxPos pos(pindex->GetBlockPos(), GetSizeOfCompactSize(block.vtx.size())); // start position
        for (unsigned int i=0; i<block.vtx.size(); i++) {
            const CTransactionRef& tx = block.vtx[i];
            if (tx->IsCoinStake() || tx->IsCoinBase()) {
                pos.nTxOffset += ::GetSerializeSize(tx, SER_DISK, CLIENT_VERSION);  // set next tx position
                continue;
            }

            // calculate tx fee
            CAmount input = 0;
            for (const auto& txin : tx->vin) {
                if (txin.prevout.hash != randpaytx) {
                    CTransactionRef txPrev;
                    uint256 hashBlock = uint256();
                    if (!GetTransaction(txin.prevout.hash, txPrev, Params().GetConsensus(), hashBlock))
                        return error("createNameIndexes() : prev transaction not found");

                    input += txPrev->vout[txin.prevout.n].nValue;
                }
            }
            CAmount fee = input - tx->GetValueOut();

            CheckNameTx(tx, pindex, vName, pos, fee);                           // collect valid names from tx to vName
            pos.nTxOffset += ::GetSerializeSize(tx, SER_DISK, CLIENT_VERSION);  // set next tx position
        }

        // execute name operations, if any
        if (!vName.empty())
            hooks->ConnectBlock(pindex, vName);
    }
    return true;
}

bool reindexNameAddressIndex()
{
    LogPrintf("Scanning blockchain for names to create secondary (address->name) index...\n");
    LOCK(cs_main);

    vector<pair<CNameVal, pair<CNameOperation,int> > > nameScan;
    if (!pNameDB->ScanNames(CNameVal(), 0, nameScan))
        return error("createNameAddressFile() : scan failed");

    int maxHeight = nameScan.size()-1;
    if (maxHeight <= 0)
        return true;
    int reportDone = 0;
    for (int nHeight=0; nHeight<=maxHeight; nHeight++) {
        int percentageDone = (100*nHeight / maxHeight);
        if (reportDone < percentageDone/10) {
            // report every 10% step
            LogPrintf("[%d%%]...", percentageDone);
            reportDone = percentageDone/10;
        }
        uiInterface.ShowProgress("Creating nameadress index (do not close app!)...", percentageDone, false);


        const CNameVal& name = nameScan[nHeight].first;
        const CNameOperation& nameOp = nameScan[nHeight].second.first;

        CTransactionRef tx;
        if (!g_txindex || !g_txindex->FindTx(nameOp.txPos, tx))
            return error("createNameAddressFile() : could not read tx from disk - your blockchain or nameindexV3 are probably corrupt");

        NameTxInfo nti;
        if (!DecodeNameOutput(tx, nameOp.nOut, nti, true))
            return error("createNameAddressFile() : failed to decode name - your blockchain or nameindexV3 are probably corrupt");

        if (nti.strAddress != "" && nti.op != OP_NAME_DELETE)
            pNameAddressDB->WriteSingleName(nti.strAddress, name);
    }
    return true;
}

bool CNamecoinHooks::CheckPendingNames(const CTransactionRef& tx)
{
    if (tx->vout.size() < 1)
        return error("%s: no output in tx %s\n", __func__, tx->GetHash().ToString());

    std::vector<NameTxInfo> vnti = DecodeNameTx(IsV8Enabled(::ChainActive().Tip(), Params().GetConsensus()), tx);
    if (vnti.empty())
        return error("%s: could not decode name script in tx %s\n", __func__, tx->GetHash().ToString());

    for (const auto& nti : vnti) {
        if (mapNamePending.count(nti.name)) {
            LogPrintf("%s: there is already a pending operation on this name %s\n", __func__, stringFromNameVal(nti.name));
            return false;
        }
    }
    return true;
}

void CNamecoinHooks::AddToPendingNames(const CTransactionRef& tx)
{
    if (tx->vout.size() < 1) {
        LogPrintf("%s : no output in tx %s\n", __func__, tx->GetHash().ToString());
        return;
    }

    std::vector<NameTxInfo> vnti = DecodeNameTx(IsV8Enabled(::ChainActive().Tip(), Params().GetConsensus()), tx);
    if (vnti.empty()) {
        LogPrintf("%s : could not decode name script in tx %s\n", __func__, tx->GetHash().ToString());
        return;
    }

    for (const auto& nti : vnti) {
        mapNamePending[nti.name].insert( COutPoint(tx->GetHash(), nti.nOut) );
        LogPrintf("%s: added %s %s from tx %s\n", __func__, stringFromOp(nti.op), stringFromNameVal(nti.name), tx->GetHash().ToString());
    }
}

static bool CheckName(const NameTxInfo& nti, const CTransactionRef& tx, int nHeight, nameCheckResult& nameResult, const CDiskTxPos& pos) {
    const CNameVal& name = nti.name;
    const char *errtxt = NULL;

    //check if last known tx on this name matches any of inputs of this tx
    CNameRecord nameRec;
    bool found = false;
    NameTxInfo prev_nti;
    if (pNameDB->ReadName(name, nameRec) && !nameRec.vNameOp.empty() && !nameRec.deleted()) {
        CTransactionRef lastKnownNameTx;
        if (!g_txindex || !g_txindex->FindTx(nameRec.vNameOp.back().txPos, lastKnownNameTx)) {
            errtxt = "failed to read last name tx";
            goto reterr;
        }
        uint256 lasthash = lastKnownNameTx->GetHash();
        if (!DecodeNameOutput(lastKnownNameTx, nameRec.vNameOp.back().nOut, prev_nti, true)) {
            errtxt = "failed to decode existing previous name tx. Your blockchain or nameindexV3 may be corrupt";
            goto reterr;
        }
        for (const auto &in : tx->vin) // this scans all scripts of tx.vin
            if(in.prevout.n == prev_nti.nOut && in.prevout.hash == lasthash) {
                found = true;
                break;
            }
    }

    switch (nti.op)
    {
        case OP_NAME_NEW:
        {
            if (NameActive(name, nHeight)) {
                if (nHeight > RELEASE_HEIGHT) {
                    errtxt = "name_new on an unexpired name";
                    goto reterr;
                }
                return false;
            }
            break;
        }
        case OP_NAME_UPDATE:
        {
            if (!found || (prev_nti.op != OP_NAME_NEW && prev_nti.op != OP_NAME_UPDATE)) {
                errtxt = "name_update without previous new or update tx";
                goto reterr;
            }

            if (prev_nti.name != name) {
                errtxt = "name_update name mismatch";
                goto reterr;
            }

            if (!NameActive(name, nHeight)) {
                errtxt = "name_update on an expired name";
                goto reterr;
            }
            break;
        }
        case OP_NAME_DELETE:
        {
            if (!found || (prev_nti.op != OP_NAME_NEW && prev_nti.op != OP_NAME_UPDATE)) {
                errtxt = "name_delete without previous new or update tx";
                goto reterr;
            }

            if (prev_nti.name != name) {
                errtxt = "name_delete name mismatch";
                goto reterr;
            }

            if (!NameActive(name, nHeight)) {
                errtxt = "name_delete on expired name";
                goto reterr;
            }
            break;
        }
        default:
            errtxt = "unknown name operation";
            goto reterr;
    }

    // all checks passed - record tx information to vName. It will be sorted by nTime and writen to nameindexV3 at the end of ConnectBlock
    nameResult.nTime = tx->nTime;
    nameResult.name = name;
    nameResult.op = nti.op;
    nameResult.hash = tx->GetHash();
    nameResult.nameOp.nHeight = nHeight;
    nameResult.nameOp.value = nti.value;
    nameResult.nameOp.txPos = pos;
    nameResult.nameOp.nOut = nti.nOut;
    nameResult.address = (nti.op != OP_NAME_DELETE) ? nti.strAddress : "";                 // we are not interested in address of deleted name
    nameResult.prev_address = (prev_nti.op != OP_NAME_DELETE) ? prev_nti.strAddress : "";  // same

    return true;

  reterr:
    string value(stringFromNameVal(nti.value));
    const int chomp_value_to_len = 80;
    if(value.length() > chomp_value_to_len)
        value = value.substr(0, chomp_value_to_len) + "...";
    return error("%s: %s; name=[%s] value=[%s] tx=%s, block=%d",
            __func__, errtxt, stringFromNameVal(name).c_str(), value.c_str(), tx->GetHash().GetHex().c_str(), nHeight);
}

// Checks name tx and save names data to vName if valid
// returns true if all names are valid
// false otherwise
bool CheckNameTx(const CTransactionRef& tx, const CBlockIndex* pindexBlock, vector<nameCheckResult> &vNameResult, const CDiskTxPos& pos, const CAmount& txFee)
{
    if (tx->nVersion != NAMECOIN_TX_VERSION)
        return false;

    //read names from tx
    std::vector<NameTxInfo> vnti = DecodeNameTx(IsV8Enabled(pindexBlock->pprev, Params().GetConsensus()), tx, true);
    if (vnti.empty()) {
        if (pindexBlock->nHeight > RELEASE_HEIGHT)
            LogPrintf("%s: could not decode name tx %s in block %d", __func__, tx->GetHash().GetHex(), pindexBlock->nHeight);
        return false;
    }

    if(!::IsNameFeeEnough(vnti, pindexBlock, txFee)) {
      // Not enough fee
      if (pindexBlock->nHeight > RELEASE_HEIGHT)
          return error("%s: rejected name_new because not enough fee for tx=%s block=%d", __func__, tx->GetHash().GetHex(), pindexBlock->nHeight);
      return false;
    }

    std::set<CNameVal> dup_names; // Name duplicate within transaction is not allowed
    for (const auto& nti : vnti) {
        if(dup_names.count(nti.name))
          return error("%s: rejected duplicate name=%s tx=%s block=%d", __func__, stringFromNameVal(nti.name), tx->GetHash().GetHex(), pindexBlock->nHeight);
        nameCheckResult nameResult;
        if (CheckName(nti, tx, pindexBlock->nHeight, nameResult, pos)) {
            vNameResult.push_back(nameResult);
            dup_names.insert(nti.name);
        } else
            return false;
    } // for vnti

    return true;
} // CheckNameTx


bool DisconnectNameTx(const CTransactionRef& tx, bool fMultiName)
{
    if (tx->nVersion != NAMECOIN_TX_VERSION)
        return false;

    std::vector<NameTxInfo> vnti = DecodeNameTx(fMultiName, tx, true);
    if (vnti.empty()) {
        LogPrintf("%s: could not decode name tx, skipping...", __func__);
        return false;
    }

    for (const auto& nti : vnti) {
        DisconnectNameOutput(tx, nti);
    }
    return true;
}

bool DisconnectNameOutput(const CTransactionRef& tx, const NameTxInfo& nti)
{
    CNameRecord nameRec;
    if (!pNameDB->ReadName(nti.name, nameRec)) {
        LogPrintf("%s: failed to read from name DB, skipping...", __func__);
        return false;
    }

    // vNameOp might be empty if we pruned expired transactions.  However, it should normally still not
    // be empty, since a reorg cannot go that far back.  Be safe anyway and do not try to pop if empty.
    if (nameRec.vNameOp.empty())
        return pNameDB->Erase(nti.name); // delete empty record

    CDiskTxPos postx;
    if (!g_txindex || !g_txindex->FindTxPosition(tx->GetHash(), postx))
        return error("%s: tx index not found", __func__);  // tx index not found

    // check if tx pos matches any known pos in name history (it should only match last tx)
    if (postx != nameRec.vNameOp.back().txPos) {
        bool found = false;
        if (nameRec.vNameOp.size() > 1) {
            for (int i = nameRec.vNameOp.size() - 2; i >= 0; i--) {
                if (found == true)
                    break;
                if (postx == nameRec.vNameOp[i].txPos)
                    found = true;
            }
        }
        assert(!found);
        LogPrintf("%s: did not find any name tx to disconnect, skipping...", __func__);
        return false;
    }

    // remove tx
    nameRec.vNameOp.pop_back();

    if (nameRec.vNameOp.size() == 0 && !pNameDB->Erase(nti.name)) // delete empty record
        return error("%s: failed to erase from name DB", __func__);
    else {
        // if we have deleted name_new - recalculate Last Active Chain Index
        if (nti.op == OP_NAME_NEW)
            for (int i = nameRec.vNameOp.size() - 1; i >= 0; i--)
                if (nameRec.vNameOp[i].op == OP_NAME_NEW) {
                    nameRec.nLastActiveChainIndex = i;
                    break;
                }

        if (!CalculateExpiresAt(nameRec))
            return error("%s: failed to calculate expiration time before writing to name DB", __func__);
        if (!pNameDB->Write(nti.name, nameRec))
            return error("%s: failed to write to name DB", __func__);
    }

    // update (address->name) index
    // delete name from old address and add it to new address
    if (fNameAddressIndex) {
        string oldAddress = (nti.op != OP_NAME_DELETE) ? nti.strAddress : "";
        string newAddress = "";
        if (!nameRec.vNameOp.empty() && !nameRec.deleted()) {
            CTransactionRef prevTx;
            if (!g_txindex || !g_txindex->FindTx(nameRec.vNameOp.back().txPos, prevTx))
                return error("%s: could not read tx from disk", __func__);
            NameTxInfo prev_nti;
            if (!DecodeNameOutput(prevTx, nameRec.vNameOp.back().nOut, prev_nti, true))
                return error("%s: failed to decode name tx", __func__);
            newAddress = prev_nti.strAddress;
        }
        if (!pNameAddressDB->MoveName(oldAddress, newAddress, nti.name))
            return error("%s: failed to move name in nameaddress.dat", __func__);
    }

    return true;
}

string stringFromOp(int op)
{
    switch (op)
    {
        case OP_NAME_UPDATE:
            return "name_update";
        case OP_NAME_NEW:
            return "name_new";
        case OP_NAME_DELETE:
            return "name_delete";
        default:
            return "<unknown name op>";
    }
}

bool CNamecoinHooks::ExtractAddress(const CScript& script, string& address)
{
    NameTxInfo nti;
    if (!DecodeNameScript(script, nti))
        return false;

    string strOp = stringFromOp(nti.op);
    address = strOp + ": " + stringFromNameVal(nti.name);
    return true;
}

// Executes name operations in vName and writes result to nameindexV3.
// NOTE: the block should already be written to blockchain by now - otherwise this may fail.
bool CNamecoinHooks::ConnectBlock(CBlockIndex* pindex, const vector<nameCheckResult> &vName)
{
    if (vName.empty())
        return true;

    // All of these name ops should succed. If there is an error - nameindexV3 is probably corrupt.
    set<CNameVal> sNameNew;

    for (const auto& i : vName) {
        {
            // remove from pending names list
            LOCK(cs_main);
            map<CNameVal, set<COutPoint> >::iterator mi = mapNamePending.find(i.name);
            if (mi != mapNamePending.end()) {
                mi->second.erase(COutPoint(i.hash, i.nameOp.nOut));
                if (mi->second.empty())
                    mapNamePending.erase(i.name);
            }
        }

        CNameRecord nameRec;
        if (pNameDB->Exists(i.name) && !pNameDB->ReadName(i.name, nameRec))
            return error("%s: failed to read from name DB", __func__);

        // only first name_new for same name in same block will get written
        if (i.op == OP_NAME_NEW && sNameNew.count(i.name))
            continue;

        nameRec.vNameOp.push_back(i.nameOp); // add

        // if starting new chain - save position of where it starts
        if (i.op == OP_NAME_NEW)
            nameRec.nLastActiveChainIndex = nameRec.vNameOp.size()-1;

        // limit to 1000 tx per name or a full single chain - whichever is larger
        static size_t maxSize = 0;
        if (maxSize == 0)
            maxSize = gArgs.GetArg("-nameindexchainsize", NAMEINDEX_CHAIN_SIZE);

        if (nameRec.vNameOp.size() > maxSize &&
            nameRec.vNameOp.size() - nameRec.nLastActiveChainIndex + 1 <= maxSize)
        {
            int d = nameRec.vNameOp.size() - maxSize; // number of elements to delete
            nameRec.vNameOp.erase(nameRec.vNameOp.begin(), nameRec.vNameOp.begin() + d);
            nameRec.nLastActiveChainIndex -= d; // move last index backwards by d elements
            assert(nameRec.nLastActiveChainIndex >= 0);
        }

        // save name op
        nameRec.vNameOp.back().op = i.op;

        if (!CalculateExpiresAt(nameRec))
            return error("%s: failed to calculate expiration time before writing to name DB for %s", __func__, i.hash.GetHex());
        if (!pNameDB->Write(i.name, nameRec))
            return error("%s: failed to write to name DB", __func__);
        if (i.op == OP_NAME_NEW)
            sNameNew.insert(i.name);
        LogPrintf("%s: writing %s %s in block %d to indexes/nameindexV3\n", __func__, stringFromOp(i.op), stringFromNameVal(i.name), pindex->nHeight);


        // update (address->name) index
        // delete name from old address and add it to new address
        // note: addresses are set inside hooks->CheckInputs()
        if (fNameAddressIndex)
            if (!pNameAddressDB->MoveName(i.prev_address, i.address, i.name))
                return error("%s: failed to move name in nameaddress.dat", __func__);
    }

    return true;
}

bool CNamecoinHooks::getNameValue(const string& sName, string& sValue)
{
    CNameVal name = nameValFromString(sName);
    if (!pNameDB->Exists(name))
        return false;

    CTransactionRef tx;
    CNameRecord nameRec;
    if (!GetLastTxOfName(name, tx, nameRec))
        return false;
    NameTxInfo nti;
    if (!DecodeNameOutput(tx, nameRec.vNameOp.back().nOut, nti, true))
        return false;

    if (!NameActive(name))
        return false;

    sValue = stringFromNameVal(nti.value);

    return true;
}

bool GetNameValue(const CNameVal& name, CNameVal& value)
{
    CNameRecord nameRec;

    if (!NameActive(name))
        return false;
    if (!pNameDB->ReadName(name, nameRec))
        return false;
    if (nameRec.vNameOp.empty())
        return false;

    value = nameRec.vNameOp.back().value;
    return true;
}

bool CNameDB::DumpToTextFile()
{
    ofstream myfile((GetDataDir() / "name_dump.txt").string().c_str());
    if (!myfile.is_open())
        return false;

    std::unique_ptr<CDBIterator> pcursor(NewIterator());
    pcursor->Seek(CNameVal());
    while (pcursor->Valid()) {
        CNameVal key;
        if (!pcursor->GetKey(key))
            return error("%s: failed to read key", __func__);

        CNameRecord value;
        if (!pcursor->GetValue(value))
            return error("%s: failed to read value", __func__);

        pcursor->Next();

        if (!value.vNameOp.empty())
            continue;

        myfile << "name =  " << stringFromNameVal(key) << "\n";
        myfile << "nExpiresAt " << value.nExpiresAt << "\n";
        myfile << "nLastActiveChainIndex " << value.nLastActiveChainIndex << "\n";
        myfile << "vNameOp:\n";
        for (unsigned int i = 0; i < value.vNameOp.size(); i++) {
            myfile << "    nHeight = " << value.vNameOp[i].nHeight << "\n";
            myfile << "    op = " << value.vNameOp[i].op << "\n";
            myfile << "    value = " << stringFromNameVal(value.vNameOp[i].value) << "\n";
        }
        myfile << "\n\n";
    }

    myfile.close();
    return true;
}

bool CNamecoinHooks::DumpToTextFile()
{
    return pNameDB->DumpToTextFile();
}

UniValue name_dump(const JSONRPCRequest& request)
{
    hooks->DumpToTextFile();
    UniValue oName(UniValue::VOBJ);
    return oName;
}

struct NameIndexStats
{
    int64_t nRecordsName;
    int64_t nSerializedSizeName;
    uint256 hashSerializedName;

    int64_t nRecordsAddress;
    int64_t nSerializedSizeAddress;
    uint256 hashSerializedAddress;

    NameIndexStats() : nRecordsName(0), nSerializedSizeName(0), nRecordsAddress(0), nSerializedSizeAddress(0) {}
};

//! Calculate statistics about name index
bool CNameDB::GetNameIndexStats(NameIndexStats &stats)
{
    std::unique_ptr<CDBIterator> pcursor(NewIterator());
    pcursor->Seek(CNameVal());
    CHashWriter ss(SER_GETHASH, PROTOCOL_VERSION);
    while (pcursor->Valid()) {
        CNameVal key;
        if (!pcursor->GetKey(key))
            return error("%s: failed to read key", __func__);

        CNameRecord value;
        if (!pcursor->GetValue(value))
            return error("%s: failed to read value", __func__);

        ss << key;
        ss << value.nExpiresAt;
        ss << value.nLastActiveChainIndex;
        for (unsigned int i = 0; i < value.vNameOp.size(); i++) {
            ss << value.vNameOp[i].nHeight;
            ss << value.vNameOp[i].op;
            ss << value.vNameOp[i].value;
        }
        stats.nRecordsName += 1;
        stats.nSerializedSizeName += ::GetSerializeSize(key, SER_NETWORK, PROTOCOL_VERSION);
        stats.nSerializedSizeName += ::GetSerializeSize(value, SER_NETWORK, PROTOCOL_VERSION);

        pcursor->Next();
    }

    stats.hashSerializedName = ss.GetHash();
    return true;
}

//! Calculate statistics about name index
bool CNameAddressDB::GetNameAddressIndexStats(NameIndexStats &stats)
{
    std::unique_ptr<CDBIterator> pcursor(NewIterator());
    pcursor->Seek("");
    CHashWriter ss(SER_GETHASH, PROTOCOL_VERSION);
    while (pcursor->Valid()) {
        std::string key;
        if (!pcursor->GetKey(key))
            return error("%s: failed to read key", __func__);

        std::set<CNameVal> value;
        if (!pcursor->GetValue(value))
            return error("%s: failed to read value", __func__);

        ss << key;
        ss << value;
        stats.nRecordsAddress += 1;
        stats.nSerializedSizeAddress += ::GetSerializeSize(key, SER_NETWORK, PROTOCOL_VERSION);
        stats.nSerializedSizeAddress += ::GetSerializeSize(value, SER_NETWORK, PROTOCOL_VERSION);

        pcursor->Next();
    }

    stats.hashSerializedAddress = ss.GetHash();
    return true;
}

UniValue name_indexinfo(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "name_indexinfo\n"
            "\nReturns statistics about name index.\n"
            "Note: this call may take some time.\n"
            "\nArguments:\n"
            "1. indextype   (numeric, optional) Index to show. 0 (default) - all indexes, 1 - main index, 2 - address index.\n"
            "\nResult:\n"
            "{\n"
            "  \"height\":n,     (numeric) The current block height (index)\n"
            "  \"bestblock\": \"hex\",   (string) the best block hash hex\n"
            "  \"records_name\": n,  (numeric) number of names in main index\n"
            "  \"bytes_name\": n,  (numeric) The serialized size of main index\n"
            "  \"hash_name\": \"hash\",   (string) The serialized hash of main index\n"
            "  \"records_address\": n,  (numeric) number of addresses in address index\n"
            "  \"bytes_address\": n,  (numeric) The serialized size of address index\n"
            "  \"hash_address\": \"hash\",   (string) The serialized hash of address index\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("name_indexinfo", "")
            + HelpExampleRpc("name_indexinfo", "")
        );

    int nIndexType = 0;
    if (request.params.size() > 0) {
        nIndexType = request.params[0].get_int();
        if (nIndexType < 0 || nIndexType > 2)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "indextype out of range");
    }
    bool fShowName = nIndexType == 0 || nIndexType == 1;
    bool fShowAddress = nIndexType == 0 || nIndexType == 2;

    LOCK(cs_main);

    UniValue ret(UniValue::VOBJ);
    ret.pushKV("height", ::ChainActive().Tip()->nHeight);
    ret.pushKV("bestblock", ::ChainActive().Tip()->GetBlockHash().ToString());

    NameIndexStats stats;
    if (fShowName) {
        if (pNameDB->GetNameIndexStats(stats)) {
            ret.pushKV("records_name", stats.nRecordsName);
            ret.pushKV("bytes_name", stats.nSerializedSizeName);
            ret.pushKV("hash_name", stats.hashSerializedName.GetHex());
        } else
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Unable to read main name index");
    }

    if (fNameAddressIndex) {
        if (fShowAddress) {
            if (pNameAddressDB->GetNameAddressIndexStats(stats)) {
                ret.pushKV("records_address", stats.nRecordsAddress);
                ret.pushKV("bytes_address", stats.nSerializedSizeAddress);
                ret.pushKV("hash_address", stats.hashSerializedAddress.GetHex());
            } else
                throw JSONRPCError(RPC_INTERNAL_ERROR, "Unable to read address index");
        }
    }

    if (!fNameAddressIndex && fShowAddress)
        ret.pushKV("note", "Name-address index is not available. Add nameaddress=1 to emercoin.conf to enable it.");

    return ret;
}

// Copyright (c) 2010-2011 Vincent Durham
// Distributed under the GPL3 software license, see the accompanying
// file license.txt or http://www.gnu.org/licenses/gpl.html.

#ifndef BITCOIN_HOOKS_H
#define BITCOIN_HOOKS_H

class CBlockIndex;
struct CDiskTxPos;
class CScript;
class CTransaction;
class CTxOut;

#include <stdlib.h>
#include <memory>

typedef int64_t CAmount;
typedef std::shared_ptr<const CTransaction> CTransactionRef;

struct nameCheckResult;

#include <map>
#include <vector>
#include <string>
using namespace std;

class CHooks
{
public:
    virtual bool IsNameFeeEnough(const CTransactionRef& tx, const CAmount& txFee) = 0;
    virtual bool ConnectBlock(CBlockIndex* pindex, const std::vector<nameCheckResult> &vName) = 0;
    virtual bool ExtractAddress(const CScript& script, std::string& address) = 0;
    virtual bool CheckPendingNames(const CTransactionRef& tx) = 0;
    virtual bool CheckNameTxForMempool(const CTransactionRef& tx) = 0;
    virtual void AddToPendingNames(const CTransactionRef& tx) = 0;
    virtual bool getNameValue(const string& sName, string& sValue) = 0;
    virtual bool DumpToTextFile() = 0;
};

extern CHooks* InitHook();
extern std::string GetDefaultDataDirSuffix();
extern CHooks* hooks;

#endif

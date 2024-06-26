// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <alert.h>

#include <clientversion.h>
#include <netmessagemaker.h>
#include <pubkey.h>
#include <timedata.h>
#include <ui_interface.h>
#include <validation.h>

#include <stdint.h>
#include <algorithm>
#include <map>

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/replace.hpp>
#include <boost/thread.hpp>

using namespace std;

map<uint256, CAlert> mapAlerts;
CCriticalSection cs_mapAlerts;

void CUnsignedAlert::SetNull()
{
    nVersion = 1;
    nRelayUntil = 0;
    nExpiration = 0;
    nID = 0;
    nCancel = 0;
    setCancel.clear();
    nMinVer = 0;
    nMaxVer = 0;
    setSubVer.clear();
    nPriority = 0;

    strComment.clear();
    strStatusBar.clear();
    strReserved.clear();
}

std::string CUnsignedAlert::ToString() const
{
    std::string strSetCancel;
    for (const auto& n : setCancel)
        strSetCancel += strprintf("%d ", n);
    std::string strSetSubVer;
    for (const auto& str : setSubVer)
        strSetSubVer += "\"" + str + "\" ";
    return strprintf(
        "CAlert(\n"
        "    nVersion     = %d\n"
        "    nRelayUntil  = %d\n"
        "    nExpiration  = %d\n"
        "    nID          = %d\n"
        "    nCancel      = %d\n"
        "    setCancel    = %s\n"
        "    nMinVer      = %d\n"
        "    nMaxVer      = %d\n"
        "    setSubVer    = %s\n"
        "    nPriority    = %d\n"
        "    strComment   = \"%s\"\n"
        "    strStatusBar = \"%s\"\n"
        ")\n",
        nVersion,
        nRelayUntil,
        nExpiration,
        nID,
        nCancel,
        strSetCancel,
        nMinVer,
        nMaxVer,
        strSetSubVer,
        nPriority,
        strComment,
        strStatusBar);
}

void CAlert::SetNull()
{
    CUnsignedAlert::SetNull();
    vchMsg.clear();
    vchSig.clear();
}

bool CAlert::IsNull() const
{
    return (nExpiration == 0);
}

uint256 CAlert::GetHash() const
{
    return Hash(this->vchMsg.begin(), this->vchMsg.end());
}

bool CAlert::IsInEffect() const
{
    return (GetAdjustedTime() < nExpiration);
}

bool CAlert::Cancels(const CAlert& alert) const
{
    if (!IsInEffect())
        return false; // this was a no-op before 31403
    return (alert.nID <= nCancel || setCancel.count(alert.nID));
}

bool CAlert::AppliesTo(int nVersion, const std::string& strSubVerIn) const
{
    // TODO: rework for client-version-embedded-in-strSubVer ?
    return (IsInEffect() &&
            nMinVer <= nVersion && nVersion <= nMaxVer);
    // oleg - ignored - &&  (setSubVer.empty() || setSubVer.count(strSubVerIn)));
}

bool CAlert::AppliesToMe() const
{
    return AppliesTo(EMERCOIN_VERSION, "");
    // oleg - commented unused
    // return AppliesTo(EMERCOIN_VERSION, FormatSubVersion(CLIENT_NAME, EMERCOIN_VERSION, std::vector<std::string>()));
}

bool CAlert::RelayTo(CNode* pnode) const
{
    if (!IsInEffect())
        return false;
    // don't relay to nodes which haven't sent their version message
    if (pnode->nVersion == 0)
        return false;
    // returns true if wasn't already contained in the set
    if (pnode->setKnown.insert(GetHash()).second)
    {
        if (GetAdjustedTime() < nRelayUntil) {
            if (g_connman)
                g_connman->PushMessage(pnode, CNetMsgMaker(pnode->GetSendVersion()).Make(NetMsgType::ALERT, *this));
            return true;
        }
    }
    return false;
}

bool CAlert::CheckSignature(const std::vector<unsigned char>& alertKey) const
{
    CPubKey key(alertKey);
    if (!key.Verify(Hash(vchMsg.begin(), vchMsg.end()), vchSig))
        return error("CAlert::CheckSignature(): verify signature failed");

    // Now unserialize the data
    CDataStream sMsg(vchMsg, SER_NETWORK, PROTOCOL_VERSION);
    sMsg >> *(CUnsignedAlert*)this;
    return true;
}

CAlert CAlert::getAlertByHash(const uint256 &hash)
{
    CAlert retval;
    {
        LOCK(cs_mapAlerts);
        map<uint256, CAlert>::iterator mi = mapAlerts.find(hash);
        if(mi != mapAlerts.end())
            retval = mi->second;
    }
    return retval;
}

bool CAlert::ProcessAlert(const std::vector<unsigned char>& alertKey)
{
    if (!CheckSignature(alertKey))
        return false;
    if (!IsInEffect())
        return false;

    // alert.nID=max is reserved for if the alert key is
    // compromised. It must have a pre-defined message,
    // must never expire, must apply to all versions,
    // and must cancel all previous
    // alerts or it will be ignored (so an attacker can't
    // send an "everything is OK, don't panic" version that
    // cannot be overridden):
    int maxInt = std::numeric_limits<int>::max();
    if (nID == maxInt)
    {
        if (!(
                nExpiration == maxInt &&
                nCancel == (maxInt-1) &&
                nMinVer == 0 &&
                nMaxVer == maxInt &&
                setSubVer.empty() &&
                nPriority == maxInt &&
                strStatusBar == "URGENT: Alert key compromised, upgrade required"
                ))
            return false;
    } else
    if(nPriority > maxInt - 100) {
        LogPrint(BCLog::ALERT, "malformed alert %d, priority too high %d\n", nID, nPriority);
        return false;
    }

    bool applied_to_me = false;
    {
        LOCK(cs_mapAlerts);
        // Cancel previous alerts
        for (map<uint256, CAlert>::iterator mi = mapAlerts.begin(); mi != mapAlerts.end();)
        {
            const CAlert& alert = (*mi).second;
            if (Cancels(alert))
            {
                LogPrint(BCLog::ALERT, "cancelling alert %d\n", alert.nID);
                uiInterface.NotifyAlertChanged((*mi).first, CT_DELETED);
                mapAlerts.erase(mi++);
            }
            else if (!alert.IsInEffect())
            {
                LogPrint(BCLog::ALERT, "expiring alert %d\n", alert.nID);
                uiInterface.NotifyAlertChanged((*mi).first, CT_DELETED);
                mapAlerts.erase(mi++);
            }
            else
                mi++;
        }

        // Check if this alert has been cancelled (alert comes too late)
        for (const auto& item : mapAlerts)
        {
            const CAlert& alert = item.second;
            if (alert.Cancels(*this))
            {
                LogPrint(BCLog::ALERT, "alert already cancelled by %d\n", alert.nID);
                return false;
            }
        } // for
        applied_to_me = AppliesToMe();
        if(nCancel < nID) {
            // MAX size is 64M
            if(mapAlerts.size() < 1000 || nID == maxInt)
                mapAlerts.insert(make_pair(GetHash(), *this)); // Add to mapAlerts
            else {
                // Alert map too load, reached 1000 entries!
                // Seems like alert key is compromised, and evil try to exhaust memory on peers
                // by generating lot of differrent alert messages.
                // In this case, we create synthetic alert for LOCAL USING ONLY.
                // We will add it into mapAlerts, but do not broadcast to a peers.
                // With such high priority, the wallet go to save mode.
                CAlert over1K;
                // There we using "maxInt - 1" to allow special forever alert "Key compromised"
                over1K.nID = over1K.nPriority = over1K.nExpiration = maxInt - 1;
                over1K.strStatusBar = "URGENT: Alert map overflow, upgrade required";
                mapAlerts.clear();
                mapAlerts.insert(make_pair(over1K.GetHash(), over1K)); // Add to mapAlerts
                uiInterface.NotifyAlertChanged(over1K.GetHash(), CT_NEW);
                AlertNotify(over1K.strStatusBar, false);
                return false;
            }
        }
        if(applied_to_me) {
            // Notify UI and -alertnotify if it applies to me
            uiInterface.NotifyAlertChanged(GetHash(), CT_NEW);
            AlertNotify(strStatusBar, false);
        }
    } // Lock

    LogPrint(BCLog::ALERT, "accepted alert %d, AppliesToMe()=%d\n", nID, applied_to_me);
    return true;
}

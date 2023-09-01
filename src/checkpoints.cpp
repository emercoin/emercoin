// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <checkpoints.h>

#include <chain.h>
#include <chainparams.h>
#include <txdb.h>
#include <validation.h>
#include <uint256.h>
#include <netmessagemaker.h>
#include <key.h>

#include <stdint.h>

#include <boost/foreach.hpp>


/** Synchronized checkpoint public key */
std::string strMasterPubKey = "";

namespace Checkpoints {
    bool ValidateBlockHeader(const CCheckpointData& data, int nHeight, const uint256& hash) {
        const MapCheckpoints& checkpoints = data.mapCheckpoints;
        MapCheckpoints::const_iterator cpit = checkpoints.upper_bound(nHeight - 1);
        return cpit == checkpoints.end() || cpit->first != nHeight || hash == cpit->second;
      // Old code from 0.7.x
      //   if (cpit == checkpoints.end())
      //      return true;
      //
      //  return (cpit->first == nHeight)?
      //      hash == cpit->second :
      //      LookupBlockIndex(cpit->second) == nullptr;
    }
} // namespace Checkpoints



namespace CheckpointsSync {

// ppcoin: synchronized checkpoint (centrally broadcasted)
uint256 hashSyncCheckpoint = uint256();
uint256 hashPendingCheckpoint = uint256();
CSyncCheckpoint checkpointMessage;
CSyncCheckpoint checkpointMessagePending;
uint256 hashInvalidCheckpoint = uint256();

// ppcoin: only descendant of current sync-checkpoint is allowed
bool ValidateSyncCheckpoint(uint256 hashCheckpoint)
{
    CBlockIndex* pindexSyncCheckpoint = LookupBlockIndex(hashSyncCheckpoint);
    CBlockIndex* pindexCheckpointRecv = LookupBlockIndex(hashCheckpoint);

    if (!pindexSyncCheckpoint)
        return error("ValidateSyncCheckpoint: block index missing for current sync-checkpoint %s", hashSyncCheckpoint.ToString());
    if (!pindexCheckpointRecv)
        return error("ValidateSyncCheckpoint: block index missing for received sync-checkpoint %s", hashCheckpoint.ToString());

    // emercoin: ignore checkpoint that are bellow last hard checkpoint
    static int nLastHardCheckpointHeight = 0;
    if (nLastHardCheckpointHeight == 0)
        nLastHardCheckpointHeight = Params().Checkpoints().mapCheckpoints.rbegin()->first;
    if (pindexCheckpointRecv->nHeight < nLastHardCheckpointHeight)
        return false;

    if (pindexCheckpointRecv->nHeight <= pindexSyncCheckpoint->nHeight)
    {
        // emercoin: debug only, because there is a potential to do a DoS attack with this check by spamming old checkpoints
        uint32_t log_categories = LogInstance().GetCategoryMask();
        if (log_categories != BCLog::NONE) {
            // Received an older checkpoint, trace back from current checkpoint
            // to the same height of the received checkpoint to verify
            // that current checkpoint should be a descendant block
            CBlockIndex* pindex = pindexSyncCheckpoint;
            while (pindex->nHeight > pindexCheckpointRecv->nHeight)
                if (!(pindex = pindex->pprev))
                    return error("ValidateSyncCheckpoint: pprev1 null - block index structure failure");
            if (pindex->GetBlockHash() != hashCheckpoint)
            {
                hashInvalidCheckpoint = hashCheckpoint;
                return error("ValidateSyncCheckpoint: new sync-checkpoint %s is conflicting with current sync-checkpoint %s", hashCheckpoint.ToString().c_str(), hashSyncCheckpoint.ToString().c_str());
            }
        }
        return false; // ignore older checkpoint
    }

    // Received checkpoint should be a descendant block of the current
    // checkpoint. Trace back to the same height of current checkpoint
    // to verify.
    CBlockIndex* pindex = pindexCheckpointRecv;
    while (pindex->nHeight > pindexSyncCheckpoint->nHeight)
        if (!(pindex = pindex->pprev))
            return error("ValidateSyncCheckpoint: pprev2 null - block index structure failure");
    if (pindex->GetBlockHash() != hashSyncCheckpoint)
    {
        hashInvalidCheckpoint = hashCheckpoint;
        return error("ValidateSyncCheckpoint: new sync-checkpoint %s is not a descendant of current sync-checkpoint %s", hashCheckpoint.ToString(), hashSyncCheckpoint.ToString());
    }
    return true;
}

bool WriteSyncCheckpoint(const uint256& hashCheckpoint)
{
    CBlockIndex* checkpointNew = LookupBlockIndex(hashCheckpoint);
    if (checkpointNew && checkpointNew->nStatus & BLOCK_HAVE_DATA) {
        if (!pblocktree->WriteSyncCheckpoint(hashCheckpoint))
            return error("WriteSyncCheckpoint(): failed to write to txdb sync checkpoint %s", hashCheckpoint.ToString());
        if (::ChainstateActive().CanFlushToDisk())
            ::ChainstateActive().ForceFlushStateToDisk();
    }
    hashSyncCheckpoint = hashCheckpoint;
    return true;
}

bool AcceptPendingSyncCheckpoint()
{
    if (strMasterPubKey == "") return false;  // no public key == no checkpoints

    LOCK(cs_main);
    CBlockIndex* pendingCheckpoint = LookupBlockIndex(hashPendingCheckpoint);
    if (!pendingCheckpoint)
        return false;

    // emercoin: checkpoint needs to be a block with 32 confirmation (rolled back to 3)
    if (pendingCheckpoint->nHeight > ::ChainActive().Height() - 3 && !::ChainstateActive().IsInitialBlockDownload())
        return false;

    if (!ValidateSyncCheckpoint(hashPendingCheckpoint)) {
        hashPendingCheckpoint = uint256();
        checkpointMessagePending.SetNull();
        return false;
    }

    //emcTODOne - redo this somehow [EM: not implemented in 0.7.x]
//    CBlockIndex* pindexCheckpoint = mapBlockIndex[hashPendingCheckpoint];
//    if (pindexCheckpoint->nStatus & BLOCK_HAVE_DATA && !::ChainActive().Contains(mapBlockIndex[hashPendingCheckpoint])) {
//        CValidationState state;
//        if (!SetBestChain(state, pindexCheckpoint))
//        {
//            hashInvalidCheckpoint = hashPendingCheckpoint;
//            return error("AcceptPendingSyncCheckpoint: SetBestChain failed for sync checkpoint %s", hashPendingCheckpoint.ToString().c_str());
//        }
//    }

    if (!WriteSyncCheckpoint(hashPendingCheckpoint))
        return error("AcceptPendingSyncCheckpoint(): failed to write sync checkpoint %s", hashPendingCheckpoint.ToString());
    hashPendingCheckpoint = uint256();
    checkpointMessage = checkpointMessagePending;
    checkpointMessagePending.SetNull();
    LogPrintf("AcceptPendingSyncCheckpoint : sync-checkpoint at %s\n", hashSyncCheckpoint.ToString());
    // relay the checkpoint
    if (g_connman && !checkpointMessage.IsNull())
        g_connman->ForEachNode([](CNode* pnode) {
            checkpointMessage.RelayTo(pnode);
        });
    return true;
}


// Automatically select a suitable sync-checkpoint
uint256 AutoSelectSyncCheckpoint()
{
    static int32_t  s_depth = -1;
    static uint32_t s_slots, s_node_no;
    if (s_depth < 0)
    {
        s_depth   = gArgs.GetArg("-checkpointdepth", 32); // default is 32 blocks
        s_slots   = gArgs.GetArg("-checkpointslots", 1); // quantity of check slots, def=1
        s_node_no = gArgs.GetArg("-checkpointnode", 0); // Number of current slot,  def=0
    }

    const CBlockIndex *pindex = ::ChainActive().Tip();

    // Get hash of current block stamp in specific depth
    for (int32_t i = 0; i < s_depth; i++)
        if((pindex = pindex->pprev) == NULL)
            return uint256();

    const CBlockIndex *rc = pindex;

    // Get H-selector from checkpointed stable area +32+6 deeper
    for (int i = 0; i < 38; i++)
        if((pindex = pindex->pprev) == NULL)
            return uint256();

    uint256 h = pindex->GetBlockHash();

    // Preserve analyze current printer node from public block hash
    uint256 hx = Hash(CSyncCheckpoint::strMasterPrivKey.begin(), CSyncCheckpoint::strMasterPrivKey.end(), h.GetDataPtr(), h.GetDataPtr() + 256 / 32);

    return (hx.GetDataPtr()[0] % s_slots == s_node_no) ? rc->GetBlockHash() : uint256();
}

// Check against synchronized checkpoint
bool CheckSync(CBlockIndex* pindexNew, std::set<CBlockIndex*>& setDirtyBlockIndex)
{
    if (strMasterPubKey.empty()) return true;     // no public key == no checkpoints
    LOCK(cs_main);
    assert(pindexNew != NULL);
    if (pindexNew->nHeight == 0) return true;                // genesis cannot be checked against previous block

    const CBlockIndex* pindexSync = LookupBlockIndex(hashSyncCheckpoint);
    // sync-checkpoint should always be accepted header
    assert(pindexSync != nullptr);

    if (pindexNew->nFlags & HEADER_CHECKPOINT_VALIDATED)
        return true;

    // lower height than sync-checkpoint
    if (pindexNew->nHeight < pindexSync->nHeight)
        return true;

    const CBlockIndex* pindex = pindexNew;
    while (pindex->nHeight > pindexSync->nHeight) {
        if (pindex->nFlags & HEADER_CHECKPOINT_VALIDATED) {
            break;
        }
        if (!(pindex = pindex->pprev))
            return error("CheckSync: pprev null - block index structure failure");
    }

    if (pindex->nHeight == pindexSync->nHeight) { // same height with sync-checkpoint
        if (pindex->GetBlockHash() != hashSyncCheckpoint)
            return false;
    }

    pindexNew->nFlags |= HEADER_CHECKPOINT_VALIDATED;
    if (pindexNew->nStatus & BLOCK_HAVE_DATA)
        setDirtyBlockIndex.insert(pindexNew);

    return true;
}

// ppcoin: reset synchronized checkpoint to last hardened checkpoint
bool ResetSyncCheckpoint()
{
    LOCK(cs_main);
    if (!WriteSyncCheckpoint(Params().GetConsensus().hashGenesisBlock))
        return error("ResetSyncCheckpoint: failed to write sync checkpoint %s", Params().GetConsensus().hashGenesisBlock.ToString());
    LogPrintf("ResetSyncCheckpoint: sync-checkpoint reset to %s\n", hashSyncCheckpoint.ToString());
    return true;
}

bool SetCheckpointPrivKey(std::string strPrivKey)
{
    // Test signing a sync-checkpoint with genesis block
    CSyncCheckpoint checkpoint;
    checkpoint.hashCheckpoint = Params().GetConsensus().hashGenesisBlock;
    CDataStream sMsg(SER_NETWORK, PROTOCOL_VERSION);
    sMsg << (CUnsignedSyncCheckpoint)checkpoint;
    checkpoint.vchMsg = std::vector<unsigned char>(sMsg.begin(), sMsg.end());

    std::vector<unsigned char> vchPrivKey = ParseHex(strPrivKey);
    CKey key;
    if(!key.SetPrivKey(CPrivKey(vchPrivKey.begin(), vchPrivKey.end()), false))
        LogPrintf("SetCheckpointPrivKey(): failed at key.SetPrivKey\n"); // if key is not correct openssl may crash
    if (!key.Sign(Hash(checkpoint.vchMsg.begin(), checkpoint.vchMsg.end()), checkpoint.vchSig))
        return false;

    // Test signing successful, proceed
    CSyncCheckpoint::strMasterPrivKey = strPrivKey;
    return true;
}

bool SendSyncCheckpoint(uint256 hashCheckpoint)
{
    if (!g_connman)
        return true;  // P2P disabled - nothing to do

    if (g_connman->GetNodeCount(CConnman::CONNECTIONS_ALL) == 0)
        return true; // no one to send to

    if (hashCheckpoint == uint256())
        return true; // don't send dummy checkpoint

    CSyncCheckpoint checkpoint;
    checkpoint.hashCheckpoint = hashCheckpoint;
    CDataStream sMsg(SER_NETWORK, PROTOCOL_VERSION);
    sMsg << (CUnsignedSyncCheckpoint)checkpoint;
    checkpoint.vchMsg = std::vector<unsigned char>(sMsg.begin(), sMsg.end());

    if (CSyncCheckpoint::strMasterPrivKey.empty())
        return error("SendSyncCheckpoint: Checkpoint master key unavailable.");
    std::vector<unsigned char> vchPrivKey = ParseHex(CSyncCheckpoint::strMasterPrivKey);
    CKey key;
    key.SetPrivKey(CPrivKey(vchPrivKey.begin(), vchPrivKey.end()), false); // if key is not correct openssl may crash
    if (!key.Sign(Hash(checkpoint.vchMsg.begin(), checkpoint.vchMsg.end()), checkpoint.vchSig))
        return error("SendSyncCheckpoint: Unable to sign checkpoint, check private key?");

    if(!checkpoint.ProcessSyncCheckpoint())
    {
        LogPrintf("WARNING: SendSyncCheckpoint: Failed to process checkpoint.\n");
        return false;
    }

    // Relay checkpoint
    g_connman->ForEachNode([&checkpoint](CNode* pnode) {
        checkpoint.RelayTo(pnode);
    });
    return true;
}

// Is the sync-checkpoint too old?
bool IsSyncCheckpointTooOld(unsigned int nSeconds)
{
    if (strMasterPubKey == "") return false;  // no public key == no checkpoints

    if (Params().NetworkIDString() == "test")  // requested by Olegh
        return false;

    LOCK(cs_main);
    const CBlockIndex* pindexSync = LookupBlockIndex(hashSyncCheckpoint);
    // sync-checkpoint should always be accepted block
    assert(pindexSync != nullptr);

    return (pindexSync->GetBlockTime() + nSeconds < GetAdjustedTime());
}

}  // namespace CheckpointsSync




// emercoin: sync-checkpoint master key
std::string CSyncCheckpoint::strMasterPrivKey = "";

// ppcoin: verify signature of sync-checkpoint message
bool CSyncCheckpoint::CheckSignature()
{
    CPubKey key(ParseHex(strMasterPubKey));
    if (!key.Verify(Hash(vchMsg.begin(), vchMsg.end()), vchSig))
        return error("CSyncCheckpoint::CheckSignature() : verify signature failed");

    // Now unserialize the data
    CDataStream sMsg(vchMsg, SER_NETWORK, PROTOCOL_VERSION);
    sMsg >> *(CUnsignedSyncCheckpoint*)this;
    return true;
}

// ppcoin: process synchronized checkpoint
bool CSyncCheckpoint::ProcessSyncCheckpoint()
{
    if (strMasterPubKey == "") return false;  // no public key == no checkpoints

    if (!CheckSignature())
        return false;

    LOCK(cs_main);
    CBlockIndex* pindexCheckpoint = LookupBlockIndex(hashCheckpoint);
    if (!pindexCheckpoint) {
        // We haven't received the checkpoint chain, keep the checkpoint as pending
        CheckpointsSync::hashPendingCheckpoint = hashCheckpoint;
        CheckpointsSync::checkpointMessagePending = *this;
        LogPrintf("ProcessSyncCheckpoint: pending for sync-checkpoint %s\n", hashCheckpoint.ToString());
        // Ask this guy to fill in what we're missing
//        if (pfrom) {
            //emcTODOne - redo this somehow [EM: not implemented in 0.7.x]
//            pfrom->PushGetBlocks(pindexBest, hashCheckpoint);
//            // ask directly as well in case rejected earlier by duplicate
//            // proof-of-stake because getblocks may not get it this time
//            pfrom->AskFor(CInv(MSG_BLOCK, mapOrphanBlocks.count(hashCheckpoint)? WantedByOrphan(mapOrphanBlocks[hashCheckpoint]) : hashCheckpoint));
//        }
        return false;
    }

    if (!CheckpointsSync::ValidateSyncCheckpoint(hashCheckpoint))
        return false;

    //emcTODOne - redo this somehow [EM: not implemented in 0.7.x]
//    if (pindexCheckpoint->nStatus & BLOCK_HAVE_DATA && !::ChainActive().Contains(pindexCheckpoint))
//    {
//        // checkpoint chain received but not yet main chain
//        CValidationState state;
//        if (!SetBestChain(state, pindexCheckpoint))
//        {
//            hashInvalidCheckpoint = hashCheckpoint;
//            return error("ProcessSyncCheckpoint: SetBestChain failed for sync checkpoint %s", hashCheckpoint.ToString());
//        }
//    }

    if (!CheckpointsSync::WriteSyncCheckpoint(hashCheckpoint))
        return error("ProcessSyncCheckpoint(): failed to write sync checkpoint %s", hashCheckpoint.ToString());
    CheckpointsSync::checkpointMessage = *this;
    CheckpointsSync::hashPendingCheckpoint = uint256();
    CheckpointsSync::checkpointMessagePending.SetNull();
    LogPrintf("ProcessSyncCheckpoint: sync-checkpoint at height=%d hash=%s\n", pindexCheckpoint->nHeight, hashCheckpoint.ToString());
    return true;
}

std::string CUnsignedSyncCheckpoint::ToString() const
{
    return strprintf(
                "CSyncCheckpoint(\n"
                "    nVersion       = %d\n"
                "    hashCheckpoint = %s\n"
                ")\n", nVersion, hashCheckpoint.ToString().c_str());
}

void CUnsignedSyncCheckpoint::print() const
{
    LogPrintf("%s", ToString());
}

uint256 CSyncCheckpoint::GetHash() const
{
    return SerializeHash(*this);
}

bool CSyncCheckpoint::RelayTo(CNode *pnode) const
{
    // returns true if wasn't already sent
    if (g_connman && pnode->hashCheckpointKnown != hashCheckpoint)
    {
        pnode->hashCheckpointKnown = hashCheckpoint;
        g_connman->PushMessage(pnode, CNetMsgMaker(pnode->GetSendVersion()).Make("checkpoint", *this));
        return true;
    }
    return false;
}

// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_BLOCK_H
#define BITCOIN_PRIMITIVES_BLOCK_H

#include <primitives/transaction.h>
#include <serialize.h>
#include <uint256.h>

class CAuxPow;
template<typename Stream> void SerReadWrite(Stream& s, const std::shared_ptr<const CAuxPow>& pobj, CSerActionSerialize ser_action);
template<typename Stream> void SerReadWrite(Stream& s, std::shared_ptr<CAuxPow>& pobj, CSerActionUnserialize ser_action);

// merged mining stuff
static const int AUXPOW_CHAIN_ID = 666;

enum
{
    // primary version
    BLOCK_VERSION_DEFAULT        = (1 << 0),

    // modifiers
    BLOCK_VERSION_AUXPOW         = (1 << 8),

    // bits allocated for chain ID
    BLOCK_VERSION_CHAIN_START    = (1 << 16),
    BLOCK_VERSION_CHAIN_END      = (1 << 30),
};

// ppcoin enum
enum
{
    BLOCK_PROOF_OF_STAKE = (1 << 0), // is proof-of-stake block
    BLOCK_STAKE_ENTROPY  = (1 << 1), // entropy bit for stake modifier
    BLOCK_STAKE_MODIFIER = (1 << 2), // regenerated stake modifier

    HEADER_CHECKPOINT_VALIDATED = (1 << 10), // this block passed sync checkpoint check
};

/** Nodes collect new transactions into a block, hash them into a hash tree,
 * and scan through nonce values to make the block's hash satisfy proof-of-work
 * requirements.  When they solve the proof-of-work, they broadcast the block
 * to everyone and the block is added to the block chain.  The first transaction
 * in the block is a special one that creates a new coin owned by the creator
 * of the block.
 */
class CBlockHeader
{
public:
    // header
    static const int32_t NORMAL_SERIALIZE_SIZE=80;
    static const int32_t CURRENT_VERSION=8;
    int32_t nVersion;     // emercoin: it might contain merged mining information in higher bits. Use GetBlockVersion() to ignore it.
    uint256 hashPrevBlock;
    uint256 hashMerkleRoot;
    uint256 hashMyself;
    uint32_t nTime;
    uint32_t nBits;
    uint32_t nNonce;
    std::shared_ptr<CAuxPow> auxpow;

    // emercoin: copy from CBlockIndex.nFlags from other clients. We need this information because we are using headers-first syncronization.
    int32_t nFlags;


    CBlockHeader()
    {
        SetNull();
    }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        READWRITE(this->nVersion);
        READWRITE(hashPrevBlock);
        READWRITE(hashMerkleRoot);
        READWRITE(nTime);
        READWRITE(nBits);
        READWRITE(nNonce);

        // emercoin: do not serialize these fields when computing hash
        if (!(s.GetType() & SER_GETHASH))
        {
            if (this->nVersion & BLOCK_VERSION_AUXPOW)
                SerReadWrite(s, auxpow, ser_action);
            else
                auxpow.reset();

            if (s.GetType() & SER_POSMARKER)
                READWRITE(nFlags);
        }
    }

    void SetNull()
    {
        SetBlockVersion(CBlockHeader::CURRENT_VERSION);
        hashPrevBlock.SetNull();
        hashMerkleRoot.SetNull();
        hashMyself.SetNull();
        nTime = 0;
        nBits = 0;
        nNonce = 0;
        nFlags = 0;
    }

    bool IsNull() const
    {
        return (nBits == 0);
    }

    uint256 GetHash() const;

    int64_t GetBlockTime() const
    {
        return (int64_t)nTime;
    }

    int GetChainID() const
    {
        return nVersion / BLOCK_VERSION_CHAIN_START;
    }

    void SetAuxPow(CAuxPow* pow);

    int32_t GetBlockVersion() const
    {
        return nVersion & 0xff;
    }
    void SetBlockVersion(int32_t nBlockVersion)
    {
        nVersion = nBlockVersion | (AUXPOW_CHAIN_ID * BLOCK_VERSION_CHAIN_START);
    }
};


class CBlock : public CBlockHeader
{
public:
    // network and disk
    std::vector<CTransactionRef> vtx;

    // ppcoin: block signature - signed by coin base txout[0]'s owner
    std::vector<unsigned char> vchBlockSig;

    // memory only
    mutable bool fChecked;

    CBlock()
    {
        SetNull();
    }

    CBlock(const CBlockHeader &header)
    {
        SetNull();
        *(static_cast<CBlockHeader*>(this)) = header;
    }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        READWRITEAS(CBlockHeader, *this);
        READWRITE(vtx);
        READWRITE(vchBlockSig);
    }

    void SetNull()
    {
        CBlockHeader::SetNull();
        vtx.clear();
        fChecked = false;
        vchBlockSig.clear();
    }

    CBlockHeader GetBlockHeader() const
    {
        CBlockHeader block;
        block.nVersion       = nVersion;
        block.hashPrevBlock  = hashPrevBlock;
        block.hashMerkleRoot = hashMerkleRoot;
        block.hashMyself     = hashMyself;
        block.nTime          = nTime;
        block.nBits          = nBits;
        block.nNonce         = nNonce;
        block.auxpow         = auxpow;
        block.nFlags         = nFlags;
        return block;
    }

    // ppcoin: entropy bit for stake modifier if chosen by modifier
    // if height is specified a special table with precomputed bits is used
    unsigned int GetStakeEntropyBit(int32_t height) const;

    // ppcoin: two types of block: proof-of-work or proof-of-stake
    bool IsProofOfStake() const
    {
        return (vtx.size() > 1 && vtx[1]->IsCoinStake());
    }

    bool IsProofOfWork() const
    {
        return !IsProofOfStake();
    }

    std::pair<COutPoint, unsigned int> GetProofOfStake() const
    {
        return IsProofOfStake()? std::make_pair(vtx[1]->vin[0].prevout, vtx[1]->nTime) : std::make_pair(COutPoint(), (unsigned int)0);
    }

    // ppcoin: get max transaction timestamp
    int64_t GetMaxTransactionTime() const
    {
        int64_t maxTransactionTime = 0;
        for (const auto& tx : vtx)
            maxTransactionTime = std::max(maxTransactionTime, (int64_t)tx->nTime);
        return maxTransactionTime;
    }


    std::string ToString() const;
};

/** Describes a place in the block chain to another node such that if the
 * other node doesn't have the same branch, it can find a recent common trunk.
 * The further back it is, the further before the fork it may be.
 */
struct CBlockLocator
{
    std::vector<uint256> vHave;

    CBlockLocator() {}

    explicit CBlockLocator(const std::vector<uint256>& vHaveIn) : vHave(vHaveIn) {}

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        int nVersion = s.GetVersion();
        if (!(s.GetType() & SER_GETHASH))
            READWRITE(nVersion);
        READWRITE(vHave);
    }

    void SetNull()
    {
        vHave.clear();
    }

    bool IsNull() const
    {
        return vHave.empty();
    }
};

// Whether the given coinstake is subject to specified protocol
bool IsProtocolV03(unsigned int nTimeCoinStake);
bool IsProtocolV04(unsigned int nTimeBlock);
bool IsProtocolV05(unsigned int nTimeTx);


#endif // BITCOIN_PRIMITIVES_BLOCK_H

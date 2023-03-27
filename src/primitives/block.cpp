// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <primitives/block.h>

#include <auxpow.h>

#include <hash.h>
#include <tinyformat.h>
#include <crypto/common.h>

#include <arith_uint256.h>
#include <checkpoints_eb.h>

uint256 CBlockHeader::GetHash() const
{
    if(hashMyself.IsNull())
        (uint256&)hashMyself = SerializeHash(*this);
    return hashMyself;
}

unsigned int CBlock::GetStakeEntropyBit(int32_t height) const
{
    unsigned int nEntropyBit = 0;
    if (IsProtocolV04(nTime))
        nEntropyBit = UintToArith256(GetHash()).GetLow64() & 1llu;// last bit of block hash
    else if (height > -1 && height <= vEntropyBits_number_of_blocks)
        // old protocol for entropy bit pre v0.4; exctracted from precomputed table.
        nEntropyBit = (vEntropyBits[height >> 5] >> (height & 0x1f)) & 1;

    return nEntropyBit;
}

std::string CBlock::ToString() const
{
    std::stringstream s;
    s << strprintf("CBlock(hash=%s, ver=0x%08x, hashPrevBlock=%s, hashMerkleRoot=%s, nTime=%u, nBits=%08x, nNonce=%u, vtx=%u)\n",
        GetHash().ToString(),
        nVersion,
        hashPrevBlock.ToString(),
        hashMerkleRoot.ToString(),
        nTime, nBits, nNonce,
        vtx.size());
    for (const auto& tx : vtx) {
        s << "  " << tx->ToString() << "\n";
    }
    return s.str();
}

// Whether the given coinstake is subject to new v0.3 protocol
bool IsProtocolV03(unsigned int nTimeCoinStake)
{
    return (nTimeCoinStake >= 1363800000);  // 03/20/2013 @ 5:20pm (UTC)
}

// Whether the given block is subject to new v0.4 protocol
bool IsProtocolV04(unsigned int nTimeBlock)
{
    return (nTimeBlock >= 1449100800);      // 12/03/2015 @ 12:00am (UTC)
}

// Whether the given transaction is subject to new v0.5 protocol
bool IsProtocolV05(unsigned int nTimeTx)
{
    return (nTimeTx >= 1560816000); // 06/18/2019
}

// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <policy/feerate.h>

#include <tinyformat.h>

const std::string CURRENCY_UNIT = "EMC";

CFeeRate::CFeeRate(const CAmount& nFeePaid, size_t nBytes_)
{
    assert(nBytes_ <= uint64_t(std::numeric_limits<int64_t>::max()));
    int64_t nSize = int64_t(nBytes_);

    if (nSize > 0)
        nSatoshisPerK = nFeePaid * 1000 / nSize;
    else
        nSatoshisPerK = 0;
}

CAmount GetMinFee(size_t nBytes)
{
    // Base fee is either MIN_TX_FEE or MIN_RELAY_TX_FEE
    CAmount nBaseFee = MIN_TX_FEE;
    CAmount nMinFee = (1 + nBytes / (10 * 1024)) * nBaseFee; // 1 subcent per 10 kb of data

    if (!MoneyRange(nMinFee))
        nMinFee = MAX_MONEY;
    return nMinFee;
}

CAmount CFeeRate::GetFee(size_t nBytes_) const
{
    // emercoin: return fixed fee
    return GetMinFee(nBytes_);
#if 0
    assert(nBytes_ <= uint64_t(std::numeric_limits<int64_t>::max()));
    int64_t nSize = int64_t(nBytes_);

    CAmount nFee = nSatoshisPerK * nSize / 1000;

    if (nFee == 0 && nSize != 0) {
        if (nSatoshisPerK > 0)
            nFee = CAmount(1);
        if (nSatoshisPerK < 0)
            nFee = CAmount(-1);
    }

    return std::max(nFee, GetMinFee(nSize));
#endif
}

std::string CFeeRate::ToString() const
{
    return strprintf("%d.%06d %s/kB", nSatoshisPerK / COIN, nSatoshisPerK % COIN, CURRENCY_UNIT);
}


// Copyright (c) 2014-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#if defined(HAVE_CONFIG_H)
#include <config/bitcoin-config.h>
#endif

#include <timedata.h>

#include <netaddress.h>
#include <sync.h>
#include <ui_interface.h>
#include <util/system.h>
#include <util/translation.h>
#include <warnings.h>

#include <atomic>
#include <limits>

static CCriticalSection cs_nTimeOffset;

// emercoin: read without cs_nTimeOffset (GetAdjustedTime runs on every minting attempt).
// Was a hand-made seqlock on volatile ints: a data race (UB), unsafe on ARM / 32-bit.
static std::atomic<int64_t> nTimeOffset{0};

/**
 * "Never go to sea with two chronometers; take one or three."
 * Our three time sources are:
 *  - System clock
 *  - Median of other nodes clocks
 *  - The user (asking the user to fix the system clock if the first two disagree)
 */
int64_t GetTimeOffset()
{
    return nTimeOffset;
}

int64_t GetAdjustedTime()
{
    return GetTime() + GetTimeOffset();
}

int64_t TimeOffsetSample(int64_t peer_time, int64_t now)
{
    // The limit is far beyond any -maxtimeadjustment, and saturation keeps the order of the
    // samples, so the median is the same; it also keeps the sum of two samples below from overflowing.
    static constexpr int64_t LIMIT = std::numeric_limits<int64_t>::max() / 4;
    const auto clamp = [](int64_t v) { return std::max(-LIMIT, std::min(LIMIT, v)); };
    return clamp(clamp(peer_time) - clamp(now));
}

#define BITCOIN_TIMEDATA_MAX_SAMPLES 200

void AddTimeData(const CNetAddr& ip, int64_t nOffsetSample)
{
    LOCK(cs_nTimeOffset);
    // Ignore duplicates
    static std::set<CNetAddr> setKnown;
    if (setKnown.size() == BITCOIN_TIMEDATA_MAX_SAMPLES)
        return;
    if (!setKnown.insert(ip).second)
        return;

    // Add data
    static CMedianFilter<int64_t> vTimeOffsets(BITCOIN_TIMEDATA_MAX_SAMPLES, 0);
    vTimeOffsets.input(nOffsetSample);
    LogPrint(BCLog::NET,"added time data, samples %d, offset %+d (%+d minutes)\n", vTimeOffsets.size(), nOffsetSample, nOffsetSample/60);

    // There is a known issue here (see issue #4521):
    //
    // - The structure vTimeOffsets contains up to 200 elements, after which
    // any new element added to it will not increase its size, replacing the
    // oldest element.
    //
    // - The condition to update nTimeOffset includes checking whether the
    // number of elements in vTimeOffsets is odd, which will never happen after
    // there are 200 elements.
    //
    // But in this case the 'bug' is protective against some attacks, and may
    // actually explain why we've never seen attacks which manipulate the
    // clock offset.
    //
    // So we should hold off on fixing this and clean it up as part of
    // a timing cleanup that strengthens it in a number of other ways.
    //
    // emercoin: there is no odd-size condition: the offset follows every sample from the 5th
    // (even sizes: the mean of the two middle values) until setKnown is full (200 peers).
    //
    size_t vlen = vTimeOffsets.size();
    if (vTimeOffsets.size() >= 5) {
        std::vector<int64_t> vSorted = vTimeOffsets.sorted();
        unsigned midpoint = vlen >> 1;
        // If vTimeOffsets.size is even, median=average(midpoint, midpoint-1)
        int64_t nMedian = (vSorted[midpoint] + vSorted[midpoint - (~vlen & 1)]) >> 1;

        // Only let other nodes change our time by so much
        const int64_t max_adjustment = std::max<int64_t>(0, gArgs.GetArg("-maxtimeadjustment", DEFAULT_MAX_TIME_ADJUSTMENT));
        if (nMedian < -max_adjustment || nMedian > max_adjustment) {
            nMedian = 0;

            static bool fDone;
            if (!fDone)
            {
                // If nobody has a time different than ours but within 5 minutes of ours, give a warning
                bool fMatch = false;
                for (const int64_t nOffset : vSorted)
                    if (nOffset != 0 && nOffset > -5 * 60 && nOffset < 5 * 60)
                        fMatch = true;

                if (!fMatch)
                {
                    fDone = true;
                    std::string strMessage = strprintf(_("Please check that your computer's date and time are correct! If your clock is wrong, %s will not work properly.").translated, PACKAGE_NAME);
                    SetMiscWarning(strMessage);
                    uiInterface.ThreadSafeMessageBox(strMessage, "", CClientUIInterface::MSG_WARNING);
                }
            }
        }

        nTimeOffset = nMedian;

        if (LogAcceptCategory(BCLog::NET)) {
            for (const int64_t n : vSorted) {
                LogPrint(BCLog::NET, "%+d  ", n); /* Continued */
            }
            LogPrint(BCLog::NET, "|  "); /* Continued */

            LogPrint(BCLog::NET, "nTimeOffset = %+d  (%+d minutes)\n", nMedian, nMedian/60);
        }
    }
}

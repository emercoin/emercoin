// Copyright (c) 2014 The Bitcoin developers
// Distributed under the GPL3 software license, see the accompanying
// file COPYING or http://www.gnu.org/licenses/gpl.html.

#include "timedata.h"

#include "netbase.h"
#include "sync.h"
#include "ui_interface.h"
#include "util.h"
#include "utilstrencodings.h"

#include <boost/foreach.hpp>

using namespace std;

static volatile int64_t nTimeOffset =  0;
static volatile int     nUpdCount   = ~0;


/**
 * "Never go to sea with two chronometers; take one or three."
 * Our three time sources are:
 *  - System clock
 *  - Median of other nodes clocks
 *  - The user (asking the user to fix the system clock if the first two disagree)
 */
int64_t GetTimeOffset()
{
    int64_t offset;
    int     cnt1;
    do {
	cnt1    = nUpdCount;
	offset  = nTimeOffset;
    } while(cnt1 != nUpdCount || cnt1 > 0);
    return offset;
}

int64_t GetAdjustedTime()
{
    return GetTime() + GetTimeOffset();
}

static int64_t abs64(int64_t n)
{
    return (n >= 0 ? n : -n);
}

#define BITCOIN_TIMEDATA_MAX_SAMPLES 200

void AddTimeData(const CNetAddr& ip, int64_t nTime)
{
    static CCriticalSection cs_nTimeOffset;
    LOCK(cs_nTimeOffset);

    // Ignore duplicates
    static set<CNetAddr> setKnown;
    if (setKnown.size() == BITCOIN_TIMEDATA_MAX_SAMPLES)
        return;
    if (!setKnown.insert(ip).second)
        return;

    int64_t nOffsetSample = nTime - GetTime();

    // Add data
    static CMedianFilter<int64_t> vTimeOffsets(BITCOIN_TIMEDATA_MAX_SAMPLES, 0);
    vTimeOffsets.input(nOffsetSample);
    LogPrintf("Added time data, samples %d, offset %+d (%+d minutes)\n", vTimeOffsets.size(), nOffsetSample, nOffsetSample/60);

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
    size_t vlen = vTimeOffsets.size();
    if (vlen >= 5)
    {
        std::vector<int64_t> vSorted = vTimeOffsets.sorted();
	unsigned midpoint = vlen >> 1;
	// If vTimeOffsets.size is even, median=average(midpoint, midpoint-1)
	int64_t nMedian = (vSorted[midpoint] + vSorted[midpoint - (~vlen & 1)]) >> 1;
        // Only let other nodes change our time by so much
        if (abs64(nMedian) >= 70 * 60)
        {
	    nMedian = 0; // clear untrusted median

            static bool fDone;
            if (!fDone)
            {
                // If nobody has a time different than ours but within 5 minutes of ours, give a warning
                bool fMatch = false;
                BOOST_FOREACH(int64_t nOffset, vSorted)
                    if (nOffset != 0 && abs64(nOffset) < 5 * 60)
                        fMatch = true;

                if (!fMatch)
                {
                    fDone = true;
                    string strMessage = _("Warning: Please check that your computer's date and time are correct! If your clock is wrong iTecoCoin Core will not work properly.");
                    strMiscWarning = strMessage;
                    LogPrintf("*** %s\n", strMessage);
                    uiInterface.ThreadSafeMessageBox(strMessage, "", CClientUIInterface::MSG_WARNING);
                }
            }
        }

	// Lock-free update nTimeOffset
	nUpdCount = -nUpdCount;
        nTimeOffset = nMedian;
	nUpdCount = ~nUpdCount | 0xe0000000;

        if (fDebug) {
            BOOST_FOREACH(int64_t n, vSorted)
                LogPrintf("%+d  ", n);
            LogPrintf("|  ");
        }
        LogPrintf("nTimeOffset = %+d  (%+d minutes)\n", nTimeOffset, nTimeOffset/60);
    }
} // void AddTimeData

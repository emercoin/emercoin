Emercoin Core integration/staging tree
=====================================

https://emercoin.com/

What is Emercoin?
----------------

**Emercoin** is an experimental new digital currency that enables instant payments to
anyone, anywhere in the world and enables of storing information as key/value pairs
in blockchain. **Emercoin** uses peer-to-peer technology to operate
with no central authority: managing transactions and issuing money are carried
out collectively by the network. For minting **Emercoin** uses Proof-of-Stake,
Proof-of-Work and Auxilary-Proof-of-Work mechanisms. **Emercoin** Core is the name of
open source software which enables the use of this currency.

For more information, as well as an immediately useable, binary version of
the **Emercoin Core** software, see [here](https://emercoin.com/).

License
-------

**Emercoin Core** is released under the terms of the GPL3 license. See [COPYING](COPYING) for more
information or the [GNU site](https://www.gnu.org/licenses/gpl.html).

Development process
-------------------

Developers work in their own trees, then submit pull requests when they think
their feature or bug fix is ready.

If it is a simple/trivial/non-controversial change, then one of the **Emercoin**
development team members simply pulls it.


The `master` branch is regularly built and tested, but is not guaranteed to be
completely stable. [Tags](https://github.com/emercoin/emercoin/releases) are created
regularly to indicate new official, stable release versions of **Emercoin**.

Testing
-------

Testing and code review is the bottleneck for development; we get more pull
requests than we can review and test on short notice. Please be patient and help out by testing
other people's pull requests, and remember this is a security-critical project where any mistake might cost people
lots of money.

### Automated Testing

Developers are strongly encouraged to write unit tests for new code, and to
submit new unit tests for old code. Unit tests can be compiled and run (assuming they weren't disabled in configure) with: `make check`

### Manual Quality Assurance (QA) Testing

Large changes should have a test plan, and should be tested by somebody other
than the developer who wrote the code.

See [here](https://github.com/bitcoin/QA/) for how to create a test plan.

Development tips and tricks
---------------------------

**compiling for debugging**

Run configure with the --enable-debug option, then make. Or run configure with
CXXFLAGS="-g -ggdb -O0" or whatever debug flags you need.

**debug.log**

If the code is behaving strangely, take a look in the debug.log file in the data directory;
error and debugging messages are written there.

The -debug=... command-line option controls debugging; running with just -debug will turn
on all categories (and give you a very large debug.log file).

The Qt code routes qDebug() output to debug.log under category "qt": run with -debug=qt
to see it.

**testnet and regtest modes**

Run with the -testnet option to run with "play emercoins" on the test network, if you
are testing multi-machine code that needs to operate across the internet.

If you are testing something that can run on one machine, run with the -regtest option.
In regression test mode, blocks can be created on-demand; see qa/rpc-tests/ for tests
that run in -regtest mode.

**DEBUG_LOCKORDER**

**Emercoin Core** is a multithreaded application, and deadlocks or other multithreading bugs
can be very difficult to track down. Compiling with -DDEBUG_LOCKORDER (configure
CXXFLAGS="-DDEBUG_LOCKORDER -g") inserts run-time checks to keep track of which locks
are held, and adds warnings to the debug.log file if inconsistencies are detected.

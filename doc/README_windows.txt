Emercoin 0.3.7 BETA

Copyright (c) 2013-2015 Emercoin Developers
Distributed under the MIT/X11 software license, see the accompanying
file license.txt or http://www.opensource.org/licenses/mit-license.php.
This product includes software developed by the OpenSSL Project for use in
the OpenSSL Toolkit (http://www.openssl.org/).  This product includes
cryptographic software written by Eric Young (eay@cryptsoft.com).


Intro
-----
Emercoin is a free open source project derived from Emercoin, with
the goal of providing a long-term energy-efficient crypto-currency.
Built on the foundation of Emercoin, innovations such as proof-of-stake
help further advance the field of crypto-currency.


Setup
-----
After completing windows setup then run emercoin-qt.
Alternatively you can run windows command line (cmd) in emercoin program dir.
  cd daemon
  emercoind
You would need to create a configuration file emercoin.conf in the default
wallet directory. Grant access to emercoind/emercoin-qt in anti-virus and firewall
applications if necessary.

The software automatically finds other nodes to connect to.  You can
enable Universal Plug and Play (UPnP) with your router/firewall
or forward port 6661 (TCP) to your computer so you can receive
incoming connections.  Emercoin works without incoming connections,
but allowing incoming connections helps the Emercoin network.

See the documentation/wiki at the emercoin website:
  http://www.emercoin.com/
for help and more information.

Upgrade
-------
All your existing coins/transactions should be intact with the upgrade.
To upgrade from 0.3.4 or bellow, first backup wallet
emercoind backupwallet <destination_backup_file>
Then shutdown emercoind by
emercoind stop
Uninstall v0.3.4 client, download and install v0.3.5+ client.
Start up the new emercoind (0.3.5+).
If upgrade is performed after upgrade deadline then blockchain re-download
is required.
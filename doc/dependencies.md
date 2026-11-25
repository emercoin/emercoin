Dependencies
============

These are the dependencies currently used by Bitcoin Core. You can find instructions for installing them in the `build-*.md` file for your platform.

| Dependency | Version used | Minimum required | CVEs | Shared | [Bundled Qt library](https://doc.qt.io/qt-5/configure-options.html#third-party-libraries) |
| --- | --- | --- | --- | --- | --- |
| Berkeley DB | [4.8.30](https://www.oracle.com/technetwork/database/database-technologies/berkeleydb/downloads/index.html) | 4.8.x | No |  |  |
| Boost | [1.70.0](https://www.boost.org/users/download/) | [1.47.0](https://github.com/bitcoin/bitcoin/pull/8920) | No |  |  |
| Clang |  | [3.3+](https://releases.llvm.org/download.html) (C++11 support) |  |  |  |
| Expat | [2.11.0](https://libexpat.github.io/) |  | No | Yes |  |
| fontconfig | [2.12.6](https://www.freedesktop.org/software/fontconfig/release/) |  | No | Yes |  |
| FreeType | [2.11.0](https://download.savannah.gnu.org/releases/freetype) |  | No |  |  |
| GCC |  | [4.8+](https://gcc.gnu.org/) (C++11 support) |  |  |  |
| HarfBuzz-NG |  |  |  |  |  |
| libevent | [2.1.13-stable](https://github.com/libevent/libevent/releases) | 2.0.22 | No |  |  |
| libpng |  |  |  |  | [Yes](https://github.com/bitcoin/bitcoin/blob/master/depends/packages/qt.mk) |
| librsvg | |  |  |  |  |
| MiniUPnPc | [2.3.5](https://miniupnp.tuxfamily.org/files/) |  | No |  |  |
| OpenSSL | [3.5.9](https://openssl-library.org/source/) |  | No |  |  |
| PCRE |  |  |  |  | [Yes](https://github.com/bitcoin/bitcoin/blob/master/depends/packages/qt.mk) |
| protobuf | [2.6.1](https://github.com/google/protobuf/releases) |  | No |  |  |
| Python (tests) |  | [3.5](https://www.python.org/downloads) |  |  |  |
| qrencode | [4.1.1](https://fukuchi.org/works/qrencode) |  | No |  |  |
| Qt | [5.15.19](https://download.qt.io/archive/qt/5.15/) | [5.11.3](https://github.com/bitcoin/bitcoin/pull/24132) | No |  |  |
| XCB | [1.14](https://xcb.freedesktop.org/releases/) (Linux only) |  |  | Yes |  |
| xkbcommon | [0.8.4](https://xkbcommon.org/download/) (Linux only) |  |  | Yes |  |
| ZeroMQ | [4.3.5](https://github.com/zeromq/libzmq/releases) | 4.0.0 | No |  |  |
| zlib | [1.4](https://zlib.net/) |  |  |  | No |

Controlling dependencies
------------------------
Some dependencies are not needed in all configurations. The following are some factors that affect the dependency list.

#### Options passed to `./configure`
* MiniUPnPc is not needed with  `--with-miniupnpc=no`.
* Berkeley DB is not needed with `--disable-wallet`.
* protobuf is only needed with `--enable-bip70`.
* Qt is not needed with `--without-gui`.
* If the qrencode dependency is absent, QR support won't be added. To force an error when that happens, pass `--with-qrencode`.
* ZeroMQ is needed only with the `--with-zmq` option.

#### Other
* librsvg is only needed if you need to run `make deploy` on (cross-compilation to) macOS.

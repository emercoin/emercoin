package=openssl
$(package)_version=3.5.9
$(package)_download_path=https://github.com/openssl/openssl/releases/download/openssl-$($(package)_version)
$(package)_file_name=$(package)-$($(package)_version).tar.gz
$(package)_sha256_hash=603f5602e2eef00d77fbd429d34dcd5822bb301757a1bc9cdb24c670f1eb859a

define $(package)_set_vars
$(package)_config_env=AR="$($(package)_ar)" RANLIB="$($(package)_ranlib)" CC="$($(package)_cc)"
$(package)_build_env=SOURCE_DATE_EPOCH=0
$(package)_config_opts=--prefix=$(host_prefix) --openssldir=$(host_prefix)/etc/openssl --libdir=lib
$(package)_config_opts+=no-apps
$(package)_config_opts+=no-docs
$(package)_config_opts+=no-tests
$(package)_config_opts+=no-shared
$(package)_config_opts+=no-module
$(package)_config_opts+=no-dso
$(package)_config_opts+=no-engine
$(package)_config_opts+=no-ui-console
$(package)_config_opts+=no-comp
$(package)_config_opts+=no-zlib
$(package)_config_opts+=no-zlib-dynamic
$(package)_config_opts+=no-ssl3
$(package)_config_opts+=no-dtls
$(package)_config_opts+=no-weak-ssl-ciphers
$(package)_config_opts+=no-camellia
$(package)_config_opts+=no-cast
$(package)_config_opts+=no-gost
$(package)_config_opts+=no-idea
$(package)_config_opts+=no-md2
$(package)_config_opts+=no-mdc2
$(package)_config_opts+=no-rc4
$(package)_config_opts+=no-rc5
$(package)_config_opts+=no-rfc3779
$(package)_config_opts+=no-sctp
$(package)_config_opts+=no-seed
$(package)_config_opts+=no-srp
$(package)_config_opts+=no-ssl-trace
$(package)_config_opts+=no-whirlpool
# Emercoin uses only BIGNUM and RAND from libcrypto (libssl only has to exist for configure).
# Any libcrypto 3 function pulls in the default provider with every algorithm it has, so leave
# out what nothing here uses; no-asm also drops ~1 MB of AES/SHA/EC assembly per binary.
$(package)_config_opts+=no-asm
$(package)_config_opts+=no-argon2
$(package)_config_opts+=no-aria
$(package)_config_opts+=no-bf
$(package)_config_opts+=no-blake2
$(package)_config_opts+=no-chacha
$(package)_config_opts+=no-cmp
$(package)_config_opts+=no-cms
$(package)_config_opts+=no-ct
$(package)_config_opts+=no-des
$(package)_config_opts+=no-dh
$(package)_config_opts+=no-dsa
$(package)_config_opts+=no-ec
$(package)_config_opts+=no-http
$(package)_config_opts+=no-legacy
$(package)_config_opts+=no-md4
$(package)_config_opts+=no-ml-dsa
$(package)_config_opts+=no-ml-kem
$(package)_config_opts+=no-ocb
$(package)_config_opts+=no-ocsp
$(package)_config_opts+=no-poly1305
$(package)_config_opts+=no-quic
$(package)_config_opts+=no-rc2
$(package)_config_opts+=no-rmd160
$(package)_config_opts+=no-scrypt
$(package)_config_opts+=no-siphash
$(package)_config_opts+=no-siv
$(package)_config_opts+=no-slh-dsa
$(package)_config_opts+=no-sm2
$(package)_config_opts+=no-sm3
$(package)_config_opts+=no-sm4
$(package)_config_opts+=no-srtp
$(package)_config_opts+=no-ts
$(package)_config_opts+=$($(package)_cflags) $($(package)_cppflags)
$(package)_config_opts_linux=-fPIC -Wa,--noexecstack
$(package)_config_opts_x86_64_linux=linux-x86_64
$(package)_config_opts_i686_linux=linux-generic32
$(package)_config_opts_arm_linux=linux-generic32
$(package)_config_opts_armv7l_linux=linux-generic32
$(package)_config_opts_aarch64_linux=linux-generic64
$(package)_config_opts_mipsel_linux=linux-generic32
$(package)_config_opts_mips_linux=linux-generic32
$(package)_config_opts_powerpc_linux=linux-generic32
$(package)_config_opts_riscv32_linux=linux-generic32
$(package)_config_opts_riscv64_linux=linux-generic64
$(package)_config_opts_x86_64_darwin=darwin64-x86_64-cc
$(package)_config_opts_x86_64_mingw32=mingw64
$(package)_config_opts_i686_mingw32=mingw
endef

define $(package)_config_cmds
  ./Configure $($(package)_config_opts)
endef

define $(package)_build_cmds
  $(MAKE) build_libs
endef

define $(package)_stage_cmds
  $(MAKE) DESTDIR=$($(package)_staging_dir) install_dev
endef

define $(package)_postprocess_cmds
  rm -rf share bin etc lib/cmake
endef

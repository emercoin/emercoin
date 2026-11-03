package=libevent
$(package)_version=2.1.12-stable
$(package)_download_path=https://github.com/libevent/libevent/releases/download/release-$($(package)_version)/
$(package)_file_name=$(package)-$($(package)_version).tar.gz
$(package)_sha256_hash=92e6de1be9ec176428fd2367677e61ceffc2ee1cb119035037a27d346b0403bb

$(package)_dependencies=openssl

define $(package)_preprocess_cmds
  ./autogen.sh
endef

define $(package)_set_vars
  $(package)_config_opts=--disable-shared --disable-libevent-regress --disable-samples
  $(package)_config_opts_release=--disable-debug-mode
  $(package)_config_opts_linux=--with-pic
  # getrandom() needs glibc 2.25, above what contrib/devtools/symbol-check.py allows (2.17);
  # without it libevent seeds its RNG from /dev/urandom, as in the 0.8.5 release binaries
  $(package)_config_opts_linux+=ac_cv_func_getrandom=no
endef

define $(package)_config_cmds
  $($(package)_autoconf)
endef

define $(package)_build_cmds
  $(MAKE)
endef

define $(package)_stage_cmds
  $(MAKE) DESTDIR=$($(package)_staging_dir) install
endef

define $(package)_postprocess_cmds
  rm lib/*.la
endef

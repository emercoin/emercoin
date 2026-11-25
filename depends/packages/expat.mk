package=expat
$(package)_version=2.11.0
$(package)_download_path=https://github.com/libexpat/libexpat/releases/download/R_$(subst .,_,$($(package)_version))/
$(package)_file_name=$(package)-$($(package)_version).tar.bz2
$(package)_sha256_hash=e4fad0deffe151dbb4ba23226211a4c607765bebfbe02772db3644a928482777

define $(package)_set_vars
  $(package)_config_opts=--disable-shared --without-docbook --without-tests --without-examples --without-xmlwf
  $(package)_config_opts_linux=--with-pic
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
  rm -rf lib/*.la lib/cmake share
endef

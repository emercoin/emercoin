package=miniupnpc
$(package)_version=2.3.5
$(package)_download_path=https://miniupnp.tuxfamily.org/files/
$(package)_file_name=$(package)-$($(package)_version).tar.gz
$(package)_sha256_hash=b9a1e57233216c5f62572de6d628e73e910f50cdb71e9c0eb89b169ce154d256
$(package)_patches=dont_leak_info.patch

define $(package)_set_vars
$(package)_build_opts=CC="$($(package)_cc)"
$(package)_build_opts_darwin=LIBTOOL="$($(package)_libtool)"
$(package)_build_opts_mingw32=-f Makefile.mingw
$(package)_build_env+=CFLAGS="$($(package)_cflags) $($(package)_cppflags)" AR="$($(package)_ar)"
endef

define $(package)_preprocess_cmds
  patch -p1 < $($(package)_patch_dir)/dont_leak_info.patch
endef

# Makefile builds into build/, Makefile.mingw into the source root
$(package)_library=$(if $(findstring mingw32,$(host_os)),libminiupnpc.a,build/libminiupnpc.a)

define $(package)_build_cmds
	$(MAKE) $($(package)_library) $($(package)_build_opts)
endef

define $(package)_stage_cmds
	mkdir -p $($(package)_staging_prefix_dir)/include/miniupnpc $($(package)_staging_prefix_dir)/lib &&\
	install -m 644 include/*.h $($(package)_staging_prefix_dir)/include/miniupnpc &&\
	install -m 644 $($(package)_library) $($(package)_staging_prefix_dir)/lib
endef

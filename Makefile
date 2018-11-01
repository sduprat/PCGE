FRAMAC_SHARE := $(shell frama-c-config -print-share-path)
FRAMAC_LIBDIR := $(shell frama-c-config -print-libpath)
PLUGIN_NAME = Pcge
PLUGIN_CMO = plug
PLUGIN_TESTS_DIRS := pcge
include $(FRAMAC_SHARE)/Makefile.dynamic

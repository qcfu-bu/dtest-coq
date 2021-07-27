
lib:
	$(MAKE) -C autosubst/theories/ all

all: lib
	$(MAKE) -C theories/ all

cleanlib:
	$(MAKE) -C autosubst/theories/ clean

clean:
	$(MAKE) -C theories/ clean

cleanall: clean cleanlib

.PHONY: all lib

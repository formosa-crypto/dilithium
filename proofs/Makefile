# -*- Makefile -*-

# --------------------------------------------------------------------
TESTS      ?= utils security
BRANCH     ?= dilithium
ECRJOBS    ?= 1
DOCKERUID  ?= $(shell id -u)
DOCKEROPTS ?= 

# --------------------------------------------------------------------
DOCKERUID  := $(shell if [ $(DOCKERUID) -lt 1000 ] ; then echo 1000 ; else echo $(DOCKERUID) ; fi)

# --------------------------------------------------------------------
.PHONY: all docker tests clean __force__

# --------------------------------------------------------------------
all: tests

tests: docker $(TESTS:%=__test-%)

docker:
	docker build $(DOCKEROPTS) \
	  --build-arg SOURCE_BRANCH=$(BRANCH) \
	  --build-arg UID=$(DOCKERUID) \
	  -t easycrypt docker

shell: __force__
	docker run --rm -ti -v "$$(pwd):/home/charlie/dilithium:z" -w /home/charlie/dilithium \
	  easycrypt opam config exec -- /bin/bash

test-%: docker __test-%
	@true

__test-%: __force__
	docker run --rm -t -v "$$(pwd):/home/charlie/dilithium:z" -w /home/charlie/dilithium \
	  easycrypt env ECRJOBS="$(ECRJOBS)" opam config exec -- easycrypt runtest tests.config "$*"

clean:
	rm -f utils/*.eco security/*.eco

pack:
	tar --owner=0 --group=0 --transform 's,^,dilithium/,' -cvzf DilithiumEC.tar.gz \
	docker Makefile README.md security tests.config utils

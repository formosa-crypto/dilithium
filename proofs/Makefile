# -*- Makefile -*-

# --------------------------------------------------------------------
TESTS ?= utils security
UID   ?= ${UID}

# --------------------------------------------------------------------
.PHONY: all docker tests clean __force__

# --------------------------------------------------------------------
all: tests

tests: docker $(TESTS:%=__test-%)

docker:
	docker build \
	  --build-arg SOURCE_BRANCH=deploy-expected-cost \
	  --build-arg UID=1000 \
	  -t easycrypt docker

shell: __force__
	docker run --rm -ti -v "$$(pwd):/home/charlie/dilithium:z" -w /home/charlie/dilithium \
	  easycrypt opam config exec -- /bin/bash

test-%: docker __test-%
	@true

__test-%: __force__
	docker run --rm -t -v "$$(pwd):/home/charlie/dilithium:z" -w /home/charlie/dilithium \
	  easycrypt opam config exec -- easycrypt runtest tests.config "$*"

clean:
	rm -f utils/*.eco security/*.eco

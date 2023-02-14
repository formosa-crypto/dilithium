# -*- Makefile -*-

# --------------------------------------------------------------------
TESTS ?= utils security
UID   ?= ${UID}

# --------------------------------------------------------------------
.PHONY: all docker tests clean __force__

# --------------------------------------------------------------------
all: sign-ct.ec

keygen-ct.ec:
	jasminc -CT -ec keygen -oec keygen-ct.ec ../src/keygen.jazz

sign-ct.ec:
	jasminc -CT -ec sign -oec sign-ct.ec ../src/sign.jazz

tests: docker $(TESTS:%=__test-%)

docker:
	docker build \
	  --build-arg SOURCE_BRANCH=deploy-expected-cost \
	  --build-arg UID=1000 \
	  -t easycrypt docker

test-%: docker __test-%
	@true

__test-%: __force__
	docker run --rm -t -v "$$(pwd):/home/charlie/dilithium:z" -w /home/charlie/dilithium \
	  easycrypt opam config exec -- easycrypt runtest tests.config "$*"

clean:
	rm -f Array*.ec WArray*.ec sign-ct.ec keygen.ec *.ec~ *.eco

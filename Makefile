# -*- Makefile -*-

# ------------------------------------------------------------------------
.PHONY: default docker run-docker

default:
	@true

docker:
	docker build -t jasmin-xmss .

run-docker:
	docker run --rm -ti jasmin-xmss

run-docker-%:
	docker run --rm -ti jasmin-xmss make -C $*

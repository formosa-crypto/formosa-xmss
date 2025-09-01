# -*- Makefile -*-

# ------------------------------------------------------------------------
.PHONY: default docker run-docker

default:
	@true

docker:
	docker build -t xmss .

run-docker:
	docker run -ti xmss

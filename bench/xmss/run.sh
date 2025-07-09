#!/bin/bash

for f in bin/*; do [[ -x "$f" && ! -d "$f" ]] && "$f"; done

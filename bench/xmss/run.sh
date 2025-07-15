#!/bin/bash

for f in bin/*_ref ; do [[ -x "$f" && ! -d "$f" ]] && "$f"; done
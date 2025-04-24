#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
import os

dir = sys.argv[-1] if len(sys.argv) > 1 else "bin/"

debug = True if "-d" in sys.argv else False

if debug:
    print(f"Listing object files in directory: {dir}")

dir_path = os.path.abspath(dir)

if not os.path.isdir(dir_path):
    print(f"Error: {dir_path} is not a valid directory")
    sys.exit(1)

files = os.listdir(dir_path)

if debug:
    print(f"Found {len(files)} files in directory: {dir} => {files}")

for file in files:
    if file.endswith(".o"):
        full_path = os.path.join(dir, file)

        assert os.path.isfile(full_path)

        size = os.path.getsize(full_path)
        print(f"{file}: {size} bytes")

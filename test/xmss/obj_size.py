#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import subprocess

try:
    subprocess.run(
        ["make", "jasmin_obj"], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
    )

    result = subprocess.run(
        ["size", "bin/test_xmssmt-sha2_20_2_256.o"], check=True, capture_output=True, text=True
    )

    jasmin_size = result.stdout.splitlines()[-1].split()[0]

    subprocess.run(
        ["make", "ref_obj"], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
    )

    result = subprocess.run(
        [
            "size",
            "fips202.o",
            "hash_address.o",
            "hash.o",
            "params.o",
            "utils.o",
            "wots.o",
            "xmss_commons.o",
            "xmss_core.o",
            "xmss.o",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    ref_size = sum(int(line.split()[0]) for line in result.stdout.splitlines()[1:])

    print(f"Jasmin size: {jasmin_size} bytes")
    print(f"C Reference size: {ref_size} bytes")
finally:
    subprocess.run(
        ["make", "clean"], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
    )

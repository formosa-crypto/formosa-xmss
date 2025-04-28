#!/bin/bash
# -*- coding: utf-8 -*-

mkdir -p csv/

nohup ./bench_xmss &
nohup ./bench_xmss_loop_u64 &
nohup ./bench_xmss_unrolled_u64 &

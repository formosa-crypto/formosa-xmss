#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os 
import sys 
import logging
import paramiko

def bench_everything(host: str):
    """
    Run all benchmarks on a hosts
    """
    dirs = [
        "hash",
        "wots",
        # "ltree",
        # Treehash
        "xmss"
    ]

    for d in dir:
        # clone the repo
        clone_command = "git clone https://github.com/formosa-crypto/formosa-xmss.git"
        submodule_command = "cd formosa-xmss && git submodule update --init"

        command = f"make -C bench/{d}/ run"
        # TODO: open an ssh connection, run the command, close the connection

hosts = [
    "bench-mpi-6700K",
    "bench-mpi-8700K",
    "bench-mpi-11700K",
    "bench-mpi-12700K",
    "bench-mpi-13700K",
    "bench-mpi-13900K",
]

# for host in hosts:
#     pass 
ssh_config_path = os.path.expanduser("~/.ssh/config")

if not os.path.exists(ssh_config_path):
    sys.stderr.write(f"SSH config file not found: {ssh_config_path}\n")
    sys.exit(1)

# Read the SSH config file
config = paramiko.config.SSHConfig()
with open(ssh_config_path, "r") as f:
        config.parse(f)
host_config = config.lookup("bench-mpi-6700K")
if 'hostname' in host_config:
    hostname = host_config['hostname']
    print(f"Hostname: {hostname}")
if 'user' in host_config:
    username = host_config['user']
    print(f"Username: {username}")
if 'port' in host_config:
    port = int(host_config['port'])
    print(f"Port: {port}")
if 'identityfile' in host_config:
    private_key_path = os.path.expanduser(host_config['identityfile'][0])
    print(f"Private key path: {private_key_path}")

# TODO: finish this 
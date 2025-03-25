#!/bin/bash  

# Based on https://stackoverflow.com/questions/61286774/how-to-set-specific-cpu-frequency-when-using-intel-pstate

echo passive | sudo tee /sys/devices/system/cpu/intel_pstate/status
sudo cpupower frequency-set -g userspace
sudo cpupower frequency-set -f 3.6GHz


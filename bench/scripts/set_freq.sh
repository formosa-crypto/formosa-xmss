#!/bin/bash  

# Based on https://stackoverflow.com/questions/61286774/how-to-set-specific-cpu-frequency-when-using-intel-pstate

UPPER=4200MHz
LOWER=4200MHz

echo passive | sudo tee /sys/devices/system/cpu/intel_pstate/status

sudo cpupower idle-set -E

sudo cpupower frequency-set -g userspace

sudo cpupower frequency-set -u $UPPER
sudo cpupower frequency-set -d $UPPER
sudo cpupower frequency-set -f $UPPER

sudo cpupower frequency-info

echo
sudo turbostat --num_iterations 1  --interval 2  2>/dev/shm/turbostat.stderr 
echo 
grep  -i "cpufreq" /dev/shm/turbostat.stderr
echo 
grep -i "frequency" /dev/shm/turbostat.stderr
echo
grep -i "max turbo" /dev/shm/turbostat.stderr
echo
inxi -C|cat
echo
grep "cpu MHz" /proc/cpuinfo 
sleep 3
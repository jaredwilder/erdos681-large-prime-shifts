#!/bin/bash
# top-down decade scan [1e11,1e12] in 1e10 chunks; one RANGE receipt line per chunk
cd "$(dirname "$0")"
for i in $(seq 99 -1 10); do
  lo=$((i*10000000000)); hi=$(((i+1)*10000000000))
  ./bad681 $lo $hi > chunk_$lo.log 2>&1
  tail -1 chunk_$lo.log >> topdown.log
  grep BAD chunk_$lo.log | sort -k2 -n | tail -1 >> topdown.log
done

#!/bin/bash
# build.sh <tag> [target...] : lake build, log to logs/<tag>.log, exit code on the last line
export PATH=$HOME/.elan/bin:$PATH
cd ~/lean/residue_apn
tag=$1; shift
lake build "$@" > logs/$tag.log 2>&1
echo "EXIT=$?" >> logs/$tag.log

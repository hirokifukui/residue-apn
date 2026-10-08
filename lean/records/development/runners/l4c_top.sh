#!/bin/bash
# l4c_top.sh <tag> <module> : hash the math sources, then lean4checker --fresh on ONE module (the top one;
# --fresh replays its whole environment, so every imported ResidueAPN module is re-checked with it).
export PATH=$HOME/.elan/bin:$PATH
cd ~/lean/residue_apn || exit 2
tag=$1; mod=$2; L=logs/l4c_$tag; mkdir -p $L
find ResidueAPN -name "*.lean" | sort | xargs shasum -a 256 > $L/SOURCE_HASHES.txt
shasum -a 256 ResidueAPN.lean >> $L/SOURCE_HASHES.txt
cut -c1-64 $L/SOURCE_HASHES.txt | shasum -a 256 | cut -c1-64 > $L/SOURCE_DIGEST.txt
start=$(date +%s)
lake env ~/lean/lean4checker/.lake/build/bin/lean4checker --fresh $mod > $L/$mod.log 2>&1
ec=$?
printf "%s\texit=%s\tseconds=%s\n" $mod $ec $(( $(date +%s) - start )) >> $L/results.tsv
echo DONE >> $L/results.tsv

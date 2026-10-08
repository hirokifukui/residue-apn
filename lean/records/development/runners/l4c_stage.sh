#!/bin/bash
# l4c_stage.sh <tag> : freeze hashes of the math sources, then lean4checker --fresh one module per run.
export PATH=$HOME/.elan/bin:$PATH
cd ~/lean/residue_apn || exit 2
tag=$1; L=logs/l4c_$tag; mkdir -p $L
find ResidueAPN -name '*.lean' | sort | xargs shasum -a 256 > $L/SOURCE_HASHES.txt
shasum -a 256 ResidueAPN.lean >> $L/SOURCE_HASHES.txt
cut -c1-64 $L/SOURCE_HASHES.txt | shasum -a 256 | cut -c1-64 > $L/SOURCE_DIGEST.txt
: > $L/results.tsv
for mod in $(grep '^import' ResidueAPN.lean | awk '{print $2}'); do
  lake env ~/lean/lean4checker/.lake/build/bin/lean4checker --fresh $mod > $L/$mod.log 2>&1
  printf '%s\texit=%s\n' $mod $? >> $L/results.tsv
done
echo DONE >> $L/results.tsv

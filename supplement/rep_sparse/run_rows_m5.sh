#!/bin/sh
# m=5: full exceptional rows at k=3 for the certified lift of every admissible c; natural lifts; k=4 samples; one full k=4.
cd /home/claude/w/research/sparse_r06
O=out/rows
for line in $(python3 -c "
import json
for l in open('out/lifts_5.jsonl'):
    if l.startswith('SUMMARY'): continue
    r=json.loads(l); print('%d,%d,%d'%(r['c'],r['rho'],r['A_nat_zeros']))
"); do
  c=$(echo $line|cut -d, -f1); rho=$(echo $line|cut -d, -f2); z=$(echo $line|cut -d, -f3)
  ./gr rows 5 37 3 terms/m5_c${c}_flat.txt $rho > $O/m5_c${c}_flat_k3_all.txt 2>/dev/null
  ./gr rows 5 37 3 terms/m5_c${c}_nat.txt $rho > $O/m5_c${c}_nat_k3_all.txt 2>/dev/null
  ./gr ord 5 37 3 terms/m5_c${c}_flat.txt $rho 300 $c > $O/m5_c${c}_flat_k3_ord300.txt 2>/dev/null
  ./gr rows 5 37 4 terms/m5_c${c}_flat.txt $rho 256 $c > $O/m5_c${c}_flat_k4_s256.txt 2>/dev/null
done
./gr rows 5 37 4 terms/m5_c3_flat.txt 15 > $O/m5_c3_flat_k4_all.txt 2>/dev/null
echo done > $O/m5.done

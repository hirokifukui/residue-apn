#!/usr/bin/env python3
"""compare_expected.py <run dir> -- compare a run of run_quick.sh with expected/: STATUS byte for byte and the 8 JSON
outputs as parsed JSON. Exit 0 and EXPECTED_CHECK=PASS iff all equal."""
import json, sys
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
EXP = HERE / 'expected'
JSONS = ['claims_result.json', 'controls_R6.json', 'main_C1.json', 'main_C2.json', 'main_C3.json',
         'r3_S1.json', 'r3_S2.json', 'r3_S3.json']

def main():
    run = Path(sys.argv[1]).resolve()
    bad = []
    if (run / 'STATUS').read_bytes() != (EXP / 'STATUS').read_bytes(): bad.append('STATUS')
    for j in JSONS:
        try:
            if json.loads((run / j).read_text()) != json.loads((EXP / j).read_text()): bad.append(j)
        except FileNotFoundError:
            bad.append(j + ' missing')
    print('compared STATUS +', len(JSONS), 'JSON')
    print('EXPECTED_CHECK=' + ('PASS' if not bad else 'FAIL ' + ' '.join(bad)))
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()

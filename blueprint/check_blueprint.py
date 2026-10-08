#!/usr/bin/env python3
"""Gate for the residue-APN blueprint (rewritten in session R11, GPT R7-04). Run after build_blueprint.sh.
G1 every generated file (src/content.tex, src/bib.tex, src/paperlabels.aux, nodes.json, dep_graph.dot,
   lean_imports.dot) is byte-identical to what gen_blueprint.py produces now from the paper and leanmap.json.
G2 every labelled theorem-like environment of the paper is a node, and nothing else is.
G3 every node other than Def/Rem has a proof body.
G4 every use resolves and the reference graph has no cycle.
G5 every Lean theorem name exists as a `theorem` and every Lean definition name as a `def` in the Lean sources
   (a NAME check, not a type check: types are checked by Lean through the audit files of lean/run_release.sh).
G6 src/print.log: no undefined reference or citation, no overfull box.
G7 BUILD_RECORD.json: starting from the required sets of build_record_spec.py (11 inputs of the PDF build: generated
   files, print.tex, the two graph PDFs, the paper source, leanmap.json; 2 built PDFs), every required entry is present
   with a 64-hex SHA-256 equal to the current file, and no entry is missing, extra or empty (R13, GPT R8-F02).
Exit 0 and BLUEPRINT_CHECK=PASS iff all pass. Does not check that a prose proof is correct."""
import sys, re, json, hashlib
sys.dont_write_bytecode = True
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_blueprint as g
import build_record_spec as spec

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    fails = []
    out, nodes, chapters = g.outputs()
    if 'src/paperlabels.aux' not in out: fails.append('G1-aux-missing')
    for p, t in sorted(out.items()):
        f = HERE / p
        if not f.is_file() or f.read_text(encoding='utf-8') != t: fails.append('G1:' + p)
    text = g.MS.read_text(encoding='utf-8')
    labelled = set()
    for it in g.items(text):
        if it[0] == 'env' and it[1] != 'proof':
            m = re.search(r'\\label\{([^}]*)\}', it[3])
            if m: labelled.add(m.group(1))
    if labelled != {n['label'] for n in nodes}: fails.append('G2')
    if [n['label'] for n in nodes if not n['proofs'] and n['trust'] not in ('Def', 'Rem')]: fails.append('G3')
    lab = {n['label']: n for n in nodes}
    if any(u not in lab for n in nodes for u in n['uses']): fails.append('G4-resolve')
    state = {}
    def dfs(v):
        state[v] = 1
        for u in lab[v]['uses']:
            if state.get(u) == 1 or (state.get(u) is None and dfs(u)): return True
        state[v] = 2; return False
    if any(state.get(v) is None and dfs(v) for v in lab): fails.append('G4-cycle')
    src = ''.join(p.read_text(encoding='utf-8') for p in sorted(g.LEANDIR.glob('ResidueAPN/**/*.lean')))
    missing = [d for n in nodes for d in n['lean'] if not re.search(r'\btheorem\s+' + re.escape(d.split('.')[-1]) + r'\b', src)]
    missing += [d for n in nodes for d in n['lean_defs'] if not re.search(r'\bdef\s+' + re.escape(d.split('.')[-1]) + r'\b', src)]
    if missing: fails.append('G5:' + ','.join(missing))
    log = HERE / 'src/print.log'
    if not log.is_file(): fails.append('G6-nolog')
    else:
        lt = log.read_text(encoding='utf-8', errors='replace')
        if re.search(r'undefined', lt): fails.append('G6-undefined')
        if re.search(r'Overfull \\[hv]box', lt): fails.append('G6-overfull')
    rec = HERE / 'BUILD_RECORD.json'
    if not rec.is_file(): fails.append('G7-norecord')
    else:
        try:
            r = json.loads(rec.read_text(encoding='utf-8'), object_pairs_hook=spec.no_duplicates)
        except ValueError as e:
            r = None; fails.append('G7-malformed:' + ('duplicate-key' if 'duplicate key' in str(e) else 'json'))
        if r is not None: fails += spec.problems(r, HERE, g, sha)
    print('nodes', len(nodes), 'lean theorem names', sum(len(n['lean']) for n in nodes),
          'lean definition names', sum(len(n['lean_defs']) for n in nodes), '(G5 is a name check, not a type check)')
    print('BLUEPRINT_CHECK=' + ('PASS' if not fails else 'FAIL ' + ' '.join(fails)))
    sys.exit(1 if fails else 0)

if __name__ == '__main__':
    main()

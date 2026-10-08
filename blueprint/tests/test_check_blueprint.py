#!/usr/bin/env python3
"""test_check_blueprint.py -- positive and negative tests of ../check_blueprint.py (session R11, GPT R7-04; record-set
cases added in R13 for GPT R8-F02).
Each case copies the inputs the gate reads into its own folder (same relative layout), changes one thing, and runs
the gate there. Nothing in the real tree is touched; nothing is deleted.
  python3 test_check_blueprint.py <work dir (new or empty)>
Last line: BLUEPRINT_GATE_TESTS=PASS n/n (exit 0) or FAIL (exit 1)."""
import json, shutil, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode = True
BP = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BP))
import gen_blueprint as g

def layout(dst):
    """Copy what the gate reads, keeping relative paths: papers/{blueprint,formalization,lean/residue_apn_portable}
    and the paper (paper/ in the release layout; the development folder otherwise: dev-layout fallback)."""
    papers = BP.parent
    shutil.copytree(BP, dst / 'papers/blueprint', ignore=shutil.ignore_patterns('tests', '__pycache__', '*.bak_pre_*'))
    (dst / 'papers/formalization').mkdir(parents=True)
    shutil.copy2(papers / 'formalization/leanmap.json', dst / 'papers/formalization/leanmap.json')
    shutil.copytree(papers / 'lean/residue_apn_portable/ResidueAPN', dst / 'papers/lean/residue_apn_portable/ResidueAPN')
    rel = g.MS.parent.relative_to(papers.parent) if g.MS.parent.parent == papers.parent else Path('papers') / g.MS.parent.name
    (dst / rel).mkdir(parents=True, exist_ok=True)
    for f in (g.MS, g.AUX): shutil.copy2(f, dst / rel / f.name)
    return dst / 'papers/blueprint'

def edit(p, fn):
    p.write_text(fn(p.read_text(encoding='utf-8')), encoding='utf-8')

def rec_edit(b, fn):
    """Change the copied BUILD_RECORD.json (parsed, changed by fn, written back)."""
    p = b / 'BUILD_RECORD.json'; r = json.loads(p.read_text(encoding='utf-8')); r = fn(r) or r
    p.write_text(json.dumps(r, indent=1) + '\n', encoding='utf-8')

def _pop(d, part, key): d[part].pop(key); return d

CASES = [
    ('pos_unchanged', None, 0, None),
    ('neg_nodes_json_empty', lambda b: (b / 'nodes.json').write_text('[]\n'), 1, 'G1:nodes.json'),
    ('neg_dep_dot_unrelated', lambda b: (b / 'dep_graph.dot').write_text('digraph x { a -> b; }\n'), 1, 'G1:dep_graph.dot'),
    ('neg_lean_dot_changed', lambda b: edit(b / 'lean_imports.dot', lambda t: t.replace('->', '<-', 1)), 1, 'G1:lean_imports.dot'),
    ('neg_paperlabels_changed', lambda b: edit(b / 'src/paperlabels.aux', lambda t: t + '\\newlabel{x}{{9}{9}}\n'), 1, 'G1:src/paperlabels.aux'),
    ('neg_content_changed', lambda b: edit(b / 'src/content.tex', lambda t: t + '% extra\n'), 1, 'G1:src/content.tex'),
    ('neg_bib_changed', lambda b: edit(b / 'src/bib.tex', lambda t: t.replace('Bartoli', 'Bartolo', 1)), 1, 'G1:src/bib.tex'),
    ('neg_pdf_changed', lambda b: open(b / 'blueprint_residue_apn.pdf', 'ab').write(b'%x\n'), 1, 'G7:blueprint_residue_apn.pdf'),
    ('neg_print_tex_changed', lambda b: edit(b / 'src/print.tex', lambda t: t.replace('How to read', 'How to read it', 1)), 1, 'G7:src/print.tex'),
    ('neg_graph_pdf_changed', lambda b: open(b / 'src/dep_graph.pdf', 'ab').write(b'%x\n'), 1, 'G7:src/dep_graph.pdf'),
    ('neg_build_record_missing', lambda b: (b / 'BUILD_RECORD.json').rename(b / 'BUILD_RECORD.json.moved_by_test'), 1, 'G7-norecord'),
    ('neg_log_overfull', lambda b: edit(b / 'src/print.log', lambda t: t + '\nOverfull \\hbox (3.0pt too wide) in paragraph\n'), 1, 'G6-overfull'),
    ('neg_log_undefined', lambda b: edit(b / 'src/print.log', lambda t: t + "\nLaTeX Warning: Reference `x' on page 1 undefined\n"), 1, 'G6-undefined'),
    ('neg_leanmap_unknown_name', lambda b: edit(b.parent / 'formalization/leanmap.json',
        lambda t: t.replace('"ResidueAPN.propW"', '"ResidueAPN.propW_missing"', 1)), 1, 'G5:'),
    ('neg_paper_changed', lambda b: edit(Path(str(b.parents[1] / (g.MS.relative_to(BP.parents[1]) if g.MS.parent.parent == BP.parents[1] else 'papers/paper/manuscript.tex'))),
        lambda t: t.replace('derivative-optimal', 'derivative optimal', 1)), 1, 'G1:src/content.tex'),
    # R13 (GPT R8-F02): the gate starts from the required sets of build_record_spec.py
    ('neg_record_empty', lambda b: (b / 'BUILD_RECORD.json').write_text('{"inputs": {}, "outputs": {}}\n'), 1, 'G7-empty:inputs'),
    ('neg_record_empty_pdf_changed', lambda b: ((b / 'BUILD_RECORD.json').write_text('{"inputs": {}, "outputs": {}}\n'),
        (b / 'blueprint_residue_apn.pdf').write_bytes(b'%PDF-1.4\nTEST-ONLY CHANGED COPY\n')), 1, 'G7-missing:outputs:blueprint_residue_apn.pdf'),
    ('neg_record_output_dropped', lambda b: rec_edit(b, lambda r: _pop(r, 'outputs', 'blueprint_residue_apn.pdf')), 1, 'G7-missing:outputs:blueprint_residue_apn.pdf'),
    ('neg_record_input_dropped', lambda b: rec_edit(b, lambda r: _pop(r, 'inputs', '@paper')), 1, 'G7-missing:inputs:@paper'),
    ('neg_record_extra_entry', lambda b: rec_edit(b, lambda r: r['inputs'].update({'src/extra.tex': '0' * 64})), 1, 'G7-extra:inputs:src/extra.tex'),
    ('neg_record_extra_top_key', lambda b: rec_edit(b, lambda r: r.update(signature='x')), 1, 'G7-extra-top:signature'),
    ('neg_record_short_hash', lambda b: rec_edit(b, lambda r: r['inputs'].update({'nodes.json': r['inputs']['nodes.json'][:63]})), 1, 'G7-badhash:nodes.json'),
    ('neg_record_inputs_not_object', lambda b: rec_edit(b, lambda r: r.update(inputs=[])), 1, 'G7-malformed:inputs'),
    ('neg_record_not_json', lambda b: (b / 'BUILD_RECORD.json').write_text('{"inputs": \n'), 1, 'G7-malformed:json'),
    ('neg_record_duplicate_key', lambda b: (b / 'BUILD_RECORD.json').write_text('{"outputs": {}, ' + (b / 'BUILD_RECORD.json').read_text(encoding='utf-8').lstrip()[1:]), 1, 'G7-malformed:duplicate-key'),
    ('neg_record_file_moved', lambda b: (b / 'src/lean_imports.pdf').rename(b / 'src/lean_imports.pdf.moved_by_test'), 1, 'G7-nofile:src/lean_imports.pdf'),
]

def main():
    work = Path(sys.argv[1]).resolve()
    if work.exists() and any(work.iterdir()): print('work dir not empty'); sys.exit(2)
    work.mkdir(parents=True, exist_ok=True)
    rows, ok = [], 0
    for name, mutate, exp, token in CASES:
        b = layout(work / name)
        if mutate: mutate(b)
        p = subprocess.run([sys.executable, '-I', str(b / 'check_blueprint.py')], cwd=b, capture_output=True, text=True)
        last = (p.stdout.strip().splitlines() or [''])[-1]
        good = p.returncode == exp and ((token is None and last == 'BLUEPRINT_CHECK=PASS') or (token is not None and token in last))
        ok += good
        rows.append({'case': name, 'exit': p.returncode, 'expected_exit': exp, 'gate_line': last, 'expected_token': token,
                     'result': 'ok' if good else 'WRONG'})
    (work / 'RESULTS.json').write_text(json.dumps(rows, indent=1) + '\n')
    for r in rows: print('%-28s exit=%s %s  %s' % (r['case'], r['exit'], r['result'], r['gate_line']))
    print('BLUEPRINT_GATE_TESTS=%s %d/%d' % ('PASS' if ok == len(CASES) else 'FAIL', ok, len(CASES)))
    sys.exit(0 if ok == len(CASES) else 1)

if __name__ == '__main__':
    main()

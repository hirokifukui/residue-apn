#!/usr/bin/env python3
"""build_record_spec.py -- the required content of BUILD_RECORD.json (session R13, GPT R8-F02 / R9-02), shared by
build_blueprint.sh (writer) and check_blueprint.py (gate G7). The gate starts from these sets, not from the keys of
the record: a record with a missing, extra, empty or malformed entry fails.
INPUTS: the 11 inputs of the PDF build -- 9 files of this folder, '@paper' (the paper source read by gen_blueprint.py)
and '@leanmap' (formalization/leanmap.json). OUTPUTS: the 2 built PDFs. Values: lowercase hex SHA-256 (64 characters).
Allowed top-level keys: _comment, inputs, outputs."""
import re
INPUTS = ('src/content.tex', 'src/bib.tex', 'src/paperlabels.aux', 'src/print.tex', 'src/dep_graph.pdf',
          'src/lean_imports.pdf', 'nodes.json', 'dep_graph.dot', 'lean_imports.dot', '@paper', '@leanmap')
OUTPUTS = ('src/print.pdf', 'blueprint_residue_apn.pdf')
TOP = ('_comment', 'inputs', 'outputs')
HEX64 = re.compile(r'^[0-9a-f]{64}$')

def no_duplicates(pairs):
    """object_pairs_hook for json.loads: a repeated key makes the record malformed (the last one would win silently)."""
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)): raise ValueError('duplicate key in BUILD_RECORD.json')
    return dict(pairs)

def path_of(key, here, g):
    """File behind a record key: '@paper' -> the paper source, '@leanmap' -> leanmap.json, else here/key."""
    return {'@paper': g.MS, '@leanmap': g.LEANMAP}.get(key, here / key)

def problems(rec, here, g, sha):
    """List of G7 failures for the parsed record `rec` (empty list = pass)."""
    out = []
    if not isinstance(rec, dict): return ['G7-malformed:not-an-object']
    out += ['G7-extra-top:' + k for k in sorted(set(rec) - set(TOP))]
    for part, want in (('inputs', INPUTS), ('outputs', OUTPUTS)):
        d = rec.get(part)
        if not isinstance(d, dict): out.append('G7-malformed:%s' % part); continue
        if not d: out.append('G7-empty:%s' % part)
        out += ['G7-missing:%s:%s' % (part, k) for k in want if k not in d]
        out += ['G7-extra:%s:%s' % (part, k) for k in sorted(set(d) - set(want))]
        for k in want:
            if k not in d: continue
            v = d[k]
            if not isinstance(v, str) or not HEX64.match(v): out.append('G7-badhash:' + k); continue
            f = path_of(k, here, g)
            if not f.is_file(): out.append('G7-nofile:' + k)
            elif sha(f) != v: out.append('G7:' + k)
    return out

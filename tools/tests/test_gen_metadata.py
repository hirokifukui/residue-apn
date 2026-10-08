#!/usr/bin/env python3
"""test_gen_metadata.py -- offline tests of ../gen_metadata.py (session R13, GPT R8-F01 / R9-01).
Case pos_shipped_regenerates copies the package's own files and checks that regeneration reproduces them byte for byte,
whatever the state of the package (candidate or release). Every other case starts from a baseline copy: the source reset
to state candidate with no identifier, and the two paper sources replaced by a short fixture that carries only the
Data-availability placeholder; it then changes the source, runs the generator twice (the two outputs must be
byte-identical), then `--check`, and asserts on the generated files. Identifiers used here are of the offline-test form 10.99999/... and https://example.invalid/...: they are not real,
no server is contacted, and they never leave the work folder. Nothing in the real tree is touched; nothing is deleted.
  python3 test_gen_metadata.py <work dir (new or empty)>
R14 cases (GPT R9-F01..F04) parse the descriptions with their own small HTMLParser subclass (independent of the
generator's), inject the R9 payload and an OR licence array into the generated files, and exercise --readback with
saved server copies made offline (no server exists or is contacted).
Last line: METADATA_TESTS=PASS n/n (exit 0) or FAIL (exit 1)."""
import html, json, shutil, subprocess, sys
from html.parser import HTMLParser
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
FILES = ['tools/gen_metadata.py', 'release/metadata_source.json', 'README.md', 'CHANGELOG.md', 'CITATION.cff',
         'release/metadata/zenodo_software.json', 'release/metadata/zenodo_paper.json',
         'paper/manuscript.tex', 'paper/elsarticle/manuscript_els.tex']
GEN = ['CITATION.cff', 'release/metadata/zenodo_software.json', 'release/metadata/zenodo_paper.json', 'README.md', 'CHANGELOG.md']
PENDING = r'\pending{repository identifier to be added at deposit}'
T = {'software_version': '10.99999/r13-test-software-v1', 'software_concept': '10.99999/r13-test-software-concept',
     'paper_version': '10.99999/r13-test-paper-v1', 'paper_concept': '10.99999/r13-test-paper-concept'}

DA_HEAD = 'The code and records, '
DA_CANDIDATE = ('will be deposited in a public repository and cited here ' + PENDING + '. '
                'Until then they accompany the submission as supplementary material.')
DA_RELEASE = 'are deposited at Zenodo, doi:%s (version %s); they also accompany the submission as supplementary material.'
def fixture(tail): return ('% test fixture standing in for the paper source (Data-availability section only)\n'
                           '\\section*{Data availability}\n' + DA_HEAD + tail + '\n\n\\begin{thebibliography}{9}\n\\end{thebibliography}\n')
FIXTURE = fixture(DA_CANDIDATE)

def layout(d, baseline=True):
    for f in FILES:
        (d / f).parent.mkdir(parents=True, exist_ok=True); shutil.copy2(ROOT / f, d / f)
    if baseline:
        def reset(m):
            m.update(state='candidate', release_date=None)
            m['software'].update(repository_code=None, git_tag=None, zenodo_version_doi=None, zenodo_concept_doi=None)
            m['paper'].update(zenodo_version_doi=None, zenodo_concept_doi=None)
        src_edit(d, reset)
        for f in ('paper/manuscript.tex', 'paper/elsarticle/manuscript_els.tex'): (d / f).write_text(FIXTURE, encoding='utf-8')
        r = run(d)
        if r.returncode: raise SystemExit('baseline generation failed: ' + r.stdout)

def src_edit(d, fn):
    p = d / 'release/metadata_source.json'; m = json.loads(p.read_text(encoding='utf-8')); fn(m)
    p.write_text(json.dumps(m, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')

def fill(m, keys=('software_version', 'software_concept', 'paper_version', 'paper_concept'), extra=True):
    for k in keys:
        kind, which = k.split('_'); m[kind]['zenodo_%s_doi' % which] = T[k]
    if extra:
        m['release_date'] = '2026-10-08'; m['software']['repository_code'] = 'https://example.invalid/residue-apn'
        m['software']['git_tag'] = 'v' + m['version']

def paper_doi(d):
    for f in ('paper/manuscript.tex', 'paper/elsarticle/manuscript_els.tex'):
        p = d / f; t = p.read_text(encoding='utf-8')
        p.write_text(t.replace(DA_CANDIDATE, DA_RELEASE % (T['software_version'], '1.0.0')), encoding='utf-8')

def run(d, *args):
    return subprocess.run([sys.executable, '-I', str(d / 'tools/gen_metadata.py')] + list(args), cwd=d, capture_output=True, text=True)

def snapshot(d): return {f: (d / f).read_bytes() for f in GEN}

def meta(d, kind): return json.loads((d / ('release/metadata/zenodo_%s.json' % kind)).read_text(encoding='utf-8'))

def rels(d, kind, relation): return [r['identifier'] for r in meta(d, kind)['metadata']['related_identifiers'] if r['relation'] == relation]

def cff_doi(d):
    lines = (d / 'CITATION.cff').read_text(encoding='utf-8').splitlines()
    top = [l for l in lines if l.startswith('doi: ')]
    pref = [l for l in lines if l.startswith('  doi: ')]
    return (top[0][5:].strip('"') if top else None), (pref[0][7:].strip('"') if pref else None)

def gen_twice(d, flag):
    a = run(d, *flag); s1 = snapshot(d) if a.returncode == 0 else None
    b = run(d, *flag); s2 = snapshot(d) if b.returncode == 0 else None
    return a, b, s1, s2

def case_null(d, shipped):
    a, b, s1, s2 = gen_twice(d, [])
    c = run(d, '--check')
    assert a.returncode == 0 and b.returncode == 0 and c.returncode == 0, (a.stdout, c.stdout)
    assert s1 == s2, 'two generations differ'
    assert cff_doi(d) == (None, None)
    assert rels(d, 'software', 'isSupplementTo') == [] and rels(d, 'paper', 'isSupplementedBy') == []
    for k in ('software', 'paper'):
        md = meta(d, k)['metadata']; assert 'publication_date' not in md and 'Candidate 1.0.0, not published' in md['description']
    assert 'MIT' in meta(d, 'software')['metadata']['description'] and 'CC BY 4.0' in meta(d, 'software')['metadata']['description']
    return 'null identifiers: no DOI, no pair relation, no date; two generations byte-identical'

def case_four_candidate(d, _):
    src_edit(d, lambda m: (fill(m, extra=False), m['software'].update(repository_code='https://example.invalid/residue-apn')))
    a, b, s1, s2 = gen_twice(d, ['--allow-test-ids'])
    c = run(d, '--check', '--allow-test-ids')
    assert a.returncode == 0 and c.returncode == 0 and s1 == s2, (a.stdout, c.stdout)
    assert rels(d, 'software', 'isSupplementTo') == [T['paper_version']]   # no tag in a candidate, so no tree link
    assert rels(d, 'paper', 'isSupplementedBy') == [T['software_version']]
    assert cff_doi(d) == (T['software_version'], T['paper_version'])
    cff = (d / 'CITATION.cff').read_text(encoding='utf-8')
    assert T['software_concept'] in cff and T['paper_concept'] in cff and 'concept DOI (all versions)' in cff
    assert meta(d, 'software')['_private']['own_version_doi'] == T['software_version']
    assert 'not yet published' in meta(d, 'paper')['metadata']['description']
    assert rels(d, 'software', 'cites') == rels(d, 'paper', 'cites') and '10.5281/zenodo.23074611' in rels(d, 'paper', 'cites')
    return 'four test DOIs and a repository, state candidate (no date, no tag): pair relations to the version DOIs, CFF doi = version DOIs, concepts under identifiers, regeneration byte-identical, old TIT paper stays cites'

def case_release(d, _):
    src_edit(d, lambda m: (fill(m), m.update(state='release'))); paper_doi(d)
    a, b, s1, s2 = gen_twice(d, ['--allow-test-ids'])
    c = run(d, '--check', '--allow-test-ids')
    assert a.returncode == 0 and c.returncode == 0 and s1 == s2, (a.stdout, c.stdout)
    for k in ('software', 'paper'):
        md = meta(d, k)['metadata']; assert md['publication_date'] == '2026-10-08' and 'not published' not in md['description']
    assert rels(d, 'software', 'isSupplementTo') == [T['paper_version'], 'https://example.invalid/residue-apn/tree/v1.0.0']
    readme = (d / 'README.md').read_text(encoding='utf-8')
    assert 'doi:' + T['software_version'] in readme and 'released 2026-10-08' in (d / 'CHANGELOG.md').read_text(encoding='utf-8')
    return 'state release with all identifiers and the paper sentence updated: PASS, dates and README/CHANGELOG blocks from the same source'

def case_manual_pair_rejected(d, _):
    src_edit(d, lambda m: fill(m, extra=False)); assert run(d, '--allow-test-ids').returncode == 0
    p = d / 'release/metadata/zenodo_software.json'; o = json.loads(p.read_text(encoding='utf-8'))
    o['metadata']['related_identifiers'].append({'identifier': '10.99999/other', 'relation': 'isSupplementTo', 'scheme': 'doi'})
    p.write_text(json.dumps(o, indent=1) + '\n', encoding='utf-8')
    c = run(d, '--check', '--allow-test-ids'); assert c.returncode == 1 and 'differs' in c.stdout
    assert run(d, '--allow-test-ids').returncode == 0 and run(d, '--check', '--allow-test-ids').returncode == 0
    assert rels(d, 'software', 'isSupplementTo')[0] == T['paper_version']
    return 'a hand-added relation fails --check; regeneration restores the generated relations'

def case_partial(d, _):
    src_edit(d, lambda m: fill(m, keys=('software_version',), extra=False))
    a = run(d, '--allow-test-ids'); c = run(d, '--check', '--allow-test-ids')
    assert a.returncode == 0 and c.returncode == 0, (a.stdout, c.stdout)
    assert rels(d, 'software', 'isSupplementTo') == [] and rels(d, 'paper', 'isSupplementedBy') == []
    assert cff_doi(d) == (T['software_version'], None)
    return 'only the software version DOI: no pair relation, no paper DOI, no date'

def neg(d, edit, token, flag=True, paper=False):
    src_edit(d, edit)
    if paper: paper_doi(d)
    a = run(d, *(['--allow-test-ids'] if flag else []))
    assert a.returncode == 1 and token in a.stdout, a.stdout
    return 'rejected: ' + token

def case_shipped(d, shipped):
    src = (d / 'release/metadata_source.json').read_text(encoding='utf-8')
    flag = ['--allow-test-ids'] if TEST_IN_SOURCE(src) else []
    a, b, s1, s2 = gen_twice(d, flag)
    c = run(d, '--check', *flag)
    assert a.returncode == 0 and c.returncode == 0, (a.stdout, c.stdout)
    assert s1 == s2 == shipped, 'regeneration from the shipped source changes shipped files'
    return 'the shipped source regenerates the shipped files byte for byte (state %s)' % json.loads(src)['state']

def TEST_IN_SOURCE(s): return '10.99999/' in s or '.invalid' in s

CASES = [
    ('pos_shipped_regenerates', case_shipped),
    ('pos_null_unchanged', case_null),
    ('pos_four_test_ids_candidate', case_four_candidate),
    ('pos_release_all_ids', case_release),
    ('pos_partial_software_only', case_partial),
    ('neg_manual_pair_relation', case_manual_pair_rejected),
    ('neg_test_ids_without_flag', lambda d, _: neg(d, lambda m: fill(m, extra=False), 'test-only identifiers', flag=False)),
    ('neg_release_incomplete', lambda d, _: neg(d, lambda m: (fill(m, keys=('software_version', 'paper_version')), m.update(state='release')), 'state release needs', paper=True)),
    ('neg_release_paper_placeholder', lambda d, _: neg(d, lambda m: (fill(m), m.update(state='release')), 'Data availability')),
    ('neg_version_equals_concept', lambda d, _: neg(d, lambda m: (fill(m, extra=False), m['paper'].update(zenodo_concept_doi=T['paper_version'])), 'equals its concept')),
    ('neg_not_a_doi', lambda d, _: neg(d, lambda m: m['software'].update(zenodo_version_doi='https://doi.org/10.1/x'), 'is not a DOI')),
    ('neg_state_published', lambda d, _: neg(d, lambda m: m.update(state='published'), 'state must be one of')),
    ('neg_wrong_tag', lambda d, _: neg(d, lambda m: (fill(m), m.update(state='release'), m['software'].update(git_tag='1.0')), 'git_tag must be', paper=True)),
    # R13 second pass (adversarial review of the first version)
    ('neg_sandbox_prefix', lambda d, _: neg(d, lambda m: m['software'].update(zenodo_version_doi='10.5072/zenodo.123'), 'test-only identifiers', flag=False)),
    ('neg_uppercase_test_host', lambda d, _: neg(d, lambda m: m['software'].update(repository_code='https://EXAMPLE.INVALID/x'), 'test-only identifiers', flag=False)),
    ('neg_related_test_id', lambda d, _: neg(d, lambda m: m['related'].append({'identifier': '10.99999/fake', 'scheme': 'doi', 'relation': 'cites'}), 'test-only identifiers', flag=False)),
    ('neg_related_pair_by_hand', lambda d, _: neg(d, lambda m: (fill(m, extra=False), m['related'].append({'identifier': T['paper_concept'], 'scheme': 'DOI', 'relation': 'isSupplementTo'})), 'related entry not allowed')),
    ('neg_earlier_paper_relabelled', lambda d, _: neg(d, lambda m: m['related'][0].update(relation='isPreviousVersionOf'), 'must appear once, as cites', flag=False)),
    ('neg_candidate_with_date', lambda d, _: neg(d, lambda m: m.update(release_date='2026-10-08'), 'must not carry release_date', flag=False)),
    ('neg_published_wording', lambda d, _: neg(d, lambda m: m['paper'].update(journal_note='published in Des. Codes Cryptogr. 2026'), 'calls the work published', flag=False)),
    ('neg_doi_case_variant', lambda d, _: neg(d, lambda m: m['software'].update(zenodo_version_doi='10.5281/zenodo.1', zenodo_concept_doi='10.5281/ZENODO.1'), 'equals its concept', flag=False)),
    ('neg_doi_trailing_newline', lambda d, _: neg(d, lambda m: m['software'].update(zenodo_version_doi='10.5281/zenodo.1\n'), 'is not a DOI', flag=False)),
    ('neg_unicode_c1_control', lambda d, _: neg(d, lambda m: m.update(abstract=m['abstract'] + '\x85'), 'control character', flag=False)),
    ('neg_example_other_tld', lambda d, _: neg(d, lambda m: m['software'].update(repository_code='https://example.co.uk/x'), 'test-only identifiers', flag=False)),
    ('neg_licence_changed', lambda d, _: neg(d, lambda m: m['software'].update(licence='Apache-2.0'), 'the author fixed', flag=False)),
]

def case_crlf(d, _):
    p = d / 'CITATION.cff'; p.write_bytes(p.read_bytes().replace(b'\n', b'\r\n'))
    c = run(d, '--check'); assert c.returncode == 1 and 'differs: CITATION.cff' in c.stdout, c.stdout
    assert run(d).returncode == 0 and run(d, '--check').returncode == 0 and b'\r' not in p.read_bytes()
    return 'a CRLF hand edit fails --check (byte comparison); regeneration restores LF'

def case_placeholder_in_comment(d, _):
    for f in ('paper/manuscript.tex', 'paper/elsarticle/manuscript_els.tex'):
        (d / f).write_text(fixture('doi:10.5281/zenodo.777.\n% ' + DA_CANDIDATE), encoding='utf-8')
    a = run(d); assert a.returncode == 1 and 'with a comment' in a.stdout, a.stdout
    for f in ('paper/manuscript.tex', 'paper/elsarticle/manuscript_els.tex'):
        (d / f).write_text(fixture('doi:10.5281/zenodo.777. \\iffalse ' + DA_CANDIDATE + ' \\fi'), encoding='utf-8')
    a = run(d); assert a.returncode == 1 and 'iffalse' in a.stdout, a.stdout
    return 'rejected: placeholder only inside a TeX comment or \\iffalse'

def case_yaml_quoting(d, _):
    src_edit(d, lambda m: m['author'].update(family="O'Neil: Jr"))
    a = run(d); c = run(d, '--check'); assert a.returncode == 0 and c.returncode == 0, a.stdout
    assert '  - family-names: "O\'Neil: Jr"' in (d / 'CITATION.cff').read_text(encoding='utf-8')
    return 'names and licences are quoted in CITATION.cff'

CASES += [('neg_crlf_hand_edit', case_crlf), ('neg_placeholder_in_comment', case_placeholder_in_comment), ('pos_yaml_quoting', case_yaml_quoting)]

def case_marker(d, _):
    p = d / 'README.md'; p.write_text(p.read_text(encoding='utf-8').replace('<!-- END gen_metadata:cite -->', ''), encoding='utf-8')
    a = run(d); assert a.returncode == 1 and 'markers' in a.stdout, a.stdout
    return 'rejected: README block marker missing'
CASES.append(('neg_readme_marker_missing', case_marker))

# ---- R14 (GPT R9 review): HTML text, licence meaning, rights, readback of the same draft ----
def html_text_paras(s):
    """Independent reading of an HTML description: (texts of the <p> elements, sorted set of tag names seen)."""
    class P(HTMLParser):
        def __init__(self):
            super().__init__(convert_charrefs=True); self.p, self.cur, self.tags = [], None, set()
        def handle_starttag(self, tag, attrs):
            self.tags.add(tag)
            if tag == 'p': self.cur = []
        def handle_endtag(self, tag):
            self.tags.add(tag)
            if tag == 'p' and self.cur is not None: self.p.append(''.join(self.cur)); self.cur = None
        def handle_data(self, x):
            if self.cur is not None: self.cur.append(x)
    q = P(); q.feed(s); q.close(); return q.p, sorted(q.tags)

def source(d): return json.loads((d / 'release/metadata_source.json').read_text(encoding='utf-8'))
SPECIAL = 'Calibration: a < b, c > d, x & y, sum_{i<r} X^(2^i), a literal <p>tag</p>, &amp; and "quotes".'

def case_html_real(d, _):
    src = source(d)
    for k in ('software', 'paper'):
        p, tags = html_text_paras(meta(d, k)['metadata']['description'])
        assert tags == ['p'] and p[0] == src['abstract'], (k, tags, p[0][:200])
    p, _t = html_text_paras(meta(d, 'software')['metadata']['description']); assert p[1] == src['formal_scope']
    assert '3r - 2 terms' in p[0] and '2^(m-r) finite ramification points' in p[0] and 'identity in Z[X]' in p[0]
    return 'the real abstract (with sum_{i<r}) is the exact text of the first paragraph of both records; formal scope too'

def case_html_special(d, _):
    src_edit(d, lambda m: m.update(abstract=m['abstract'] + ' ' + SPECIAL, formal_scope=m['formal_scope'] + ' (i<j & k>l)'))
    a, b, s1, s2 = gen_twice(d, []); c = run(d, '--check')
    assert a.returncode == 0 and c.returncode == 0 and s1 == s2, (a.stdout, c.stdout)
    src = source(d)
    for k in ('software', 'paper'):
        p, tags = html_text_paras(meta(d, k)['metadata']['description'])
        assert tags == ['p'] and p[0] == src['abstract'], (k, tags)
    assert html_text_paras(meta(d, 'software')['metadata']['description'])[0][1] == src['formal_scope']
    return 'calibration text with <, >, &, a literal <p> and &amp; survives: paragraph texts equal the source; regeneration byte-identical'

def case_r9_payload(d, _):
    src = source(d); p = d / 'release/metadata/zenodo_paper.json'; o = json.loads(p.read_text(encoding='utf-8'))
    esc = html.escape(src['abstract'], quote=False); assert esc in o['metadata']['description']
    o['metadata']['description'] = o['metadata']['description'].replace(esc, src['abstract'], 1)   # the R9 form
    p.write_text(json.dumps(o, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')
    got, tags = html_text_paras(o['metadata']['description']); assert got[0] != src['abstract'] and 'r}' in tags
    c = run(d, '--check'); assert c.returncode == 1 and 'on disk: paper description' in c.stdout, c.stdout
    return 'the R9 payload (abstract not escaped; `<r}` read as a tag, text lost) fails --check with an HTML reason'

def case_readback_candidate(d, _):
    p = d / 'cand.json'; p.write_text(json.dumps({'metadata': meta(d, 'software')['metadata']}))
    r = run(d, '--allow-test-ids', '--readback', 'software', str(p)); assert r.returncode == 1 and 'no version DOI' in r.stdout, r.stdout
    q = d / 'release/metadata/zenodo_software.json'; o = json.loads(q.read_text(encoding='utf-8')); o['_private'] = []
    q.write_text(json.dumps(o), encoding='utf-8'); c = run(d, '--check')
    assert c.returncode == 1 and 'software record unreadable' in c.stdout and 'Traceback' not in c.stderr, (c.stdout, c.stderr)
    return 'readback refuses a record without a version DOI; a mistyped record on disk is reported, not a traceback'

def case_source_values(d, _):
    for edit, token in ((lambda m: m.update(release_date='2027-13-45'), 'release_date format'),
                        (lambda m: m.update(release_date=20271013), 'release_date format'),
                        (lambda m: m.update(abstract='   '), 'abstract must be'),
                        (lambda m: m['paper'].update(title=''), 'paper title must be')):
        e = d / ('e%d' % len(token)); layout(e) if not e.exists() else None
        src_edit(e, edit); a = run(e); assert a.returncode == 1 and token in a.stdout and 'Traceback' not in a.stderr, (token, a.stdout, a.stderr)
    (d / 'release/metadata_source.json').write_text('{broken', encoding='utf-8'); a = run(d)
    assert a.returncode == 1 and 'source unreadable' in a.stdout and 'Traceback' not in a.stderr, (a.stdout, a.stderr)
    return 'impossible or mistyped dates, empty abstract or title, and a broken source fail with a message'

def case_cff_variants(d, _):
    base = (d / 'CITATION.cff').read_text(encoding='utf-8')
    for inj in ('"license": [MIT, CC-BY-4.0]\n', "'license': MIT\n", 'license: MIT\n', 'license: [MIT]\n'):
        (d / 'CITATION.cff').write_text(base.replace('keywords:\n', inj + 'keywords:\n', 1), encoding='utf-8')
        c = run(d, '--check'); assert c.returncode == 1 and 'top-level license' in c.stdout, (inj, c.stdout)
    (d / 'CITATION.cff').write_text(base, encoding='utf-8')
    src_edit(d, lambda m: m['keywords'].append('MIT')); a = run(d); c = run(d, '--check')
    assert a.returncode == 0 and c.returncode == 0, (a.stdout, c.stdout)
    return 'quoted, inline and flow forms of a top-level CFF license fail --check; a keyword "MIT" is not a false FAIL'

def case_cff_or(d, _):
    p = d / 'CITATION.cff'; t = p.read_text(encoding='utf-8'); assert '\nlicense:' not in t
    p.write_text(t.replace('keywords:\n', 'license:\n  - "MIT"\n  - "CC-BY-4.0"\nkeywords:\n', 1), encoding='utf-8')
    c = run(d, '--check'); assert c.returncode == 1 and 'top-level license' in c.stdout, c.stdout
    return 'the R9 CFF licence array (read as MIT OR CC-BY-4.0) fails --check with a meaning reason'

def case_single_mit(d, _):
    p = d / 'release/metadata/zenodo_software.json'; o = json.loads(p.read_text(encoding='utf-8'))
    o['_private']['final_rights'] = o['_private']['final_rights'][:1]
    p.write_text(json.dumps(o, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')
    c = run(d, '--check'); assert c.returncode == 1 and 'software final rights' in c.stdout, c.stdout
    q = d / 'release/metadata/zenodo_paper.json'; o = json.loads(q.read_text(encoding='utf-8')); o['metadata']['license'] = 'mit'
    q.write_text(json.dumps(o, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')
    c = run(d, '--check'); assert c.returncode == 1 and 'paper metadata.license' in c.stdout, c.stdout
    return 'a software record finished with MIT alone, or a paper record under MIT, fails --check'

def case_rights(d, _):
    sw, pa = meta(d, 'software'), meta(d, 'paper'); src = source(d)
    assert [r['id'] for r in sw['_private']['final_rights']] == ['mit', 'cc-by-4.0']
    assert [r['scope'] for r in sw['_private']['final_rights']] == [src['licence_scope']['MIT'], src['licence_scope']['CC-BY-4.0']]
    assert [r['id'] for r in pa['_private']['final_rights']] == ['cc-by-4.0']
    assert sw['metadata']['license'] == 'mit' and pa['metadata']['license'] == 'cc-by-4.0'
    assert 'web form' in sw['_private']['rights_procedure'] and 'final_rights' not in sw['metadata']
    cff = (d / 'CITATION.cff').read_text(encoding='utf-8').splitlines()
    assert not [l for l in cff if l.startswith('license')] and [l for l in cff if 'license:' in l] == ['  license: "CC-BY-4.0"']
    lic = html_text_paras(sw['metadata']['description'])[0][2]
    assert 'not alternatives' in lic and 'distributed under two licences' in lic and 'MIT: ' + src['licence_scope']['MIT'] in lic and 'CC BY 4.0: ' + src['licence_scope']['CC-BY-4.0'] in lic
    assert 'The licence field of this record (MIT)' not in sw['metadata']['description']
    return 'rights expected: software MIT + CC BY 4.0 with scopes, paper CC BY 4.0; CFF only preferred-citation CC-BY-4.0'

def server_copy(d, kind, md, name):
    md = json.loads(json.dumps(md))
    md['description'] = md['description'].replace('</p><p>', '</p>\n<p>').replace('&gt;', '>')   # server-side formatting
    own = meta(d, kind)['_private']['own_version_doi'] or '10.99999/server-field'   # the DOI reserved for this draft
    md.update(doi=own, prereserve_doi={'doi': own, 'recid': 1})
    for r in md['related_identifiers']: r['relation'] = r['relation'].lower()
    cdoi = meta(d, kind)['_private']['own_concept_doi'] or '10.99999/zenodo.0'
    p = d / name; p.write_text(json.dumps({'id': 1, 'conceptrecid': cdoi.rsplit('.', 1)[-1], 'state': 'unsubmitted', 'metadata': md}), encoding='utf-8'); return p

def case_readback(d, _):
    initial = {k: meta(d, k)['metadata'] for k in ('software', 'paper')}           # draft created from the candidate
    src_edit(d, lambda m: (fill(m), m.update(state='release'))); paper_doi(d)
    assert run(d, '--allow-test-ids').returncode == 0
    for k in ('software', 'paper'):
        good = run(d, '--allow-test-ids', '--readback', k, str(server_copy(d, k, meta(d, k)['metadata'], 'final_%s.json' % k)))
        assert good.returncode == 0 and ('READBACK_%s=PASS' % k.upper()) in good.stdout, good.stdout
        stale = run(d, '--allow-test-ids', '--readback', k, str(server_copy(d, k, initial[k], 'stale_%s.json' % k)))
        assert stale.returncode == 1 and all(x in stale.stdout for x in ('publication_date', 'description', 'related_identifiers')), stale.stdout
    src = source(d); bad = meta(d, 'paper')['metadata']
    bad['description'] = bad['description'].replace(html.escape(src['abstract'], quote=False), src['abstract'], 1)
    r = run(d, '--allow-test-ids', '--readback', 'paper', str(server_copy(d, 'paper', bad, 'unescaped_paper.json')))
    assert r.returncode == 1 and 'description' in r.stdout, r.stdout
    fin = meta(d, 'software')['metadata']
    def neg(tweak, token, after=False):
        md = json.loads(json.dumps(fin)); tweak(md); p = server_copy(d, 'software', md, 'neg_%s.json' % token.replace(' ', '_'))
        if token == 'reserved DOI': raw = json.loads(p.read_text()); raw['metadata']['prereserve_doi']['doi'] = '10.99999/other'; raw['metadata']['doi'] = '10.99999/other'; p.write_text(json.dumps(raw))
        r = run(d, '--allow-test-ids', '--readback', 'software', str(p), *(['--after-web-form'] if after else []))
        assert r.returncode == 1 and token in r.stdout, (token, r.stdout)
    neg(lambda md: None, 'reserved DOI')
    neg(lambda md: md.update(license='cc-by-4.0'), 'license')
    neg(lambda md: md.update(access_right='closed'), 'access_right')
    neg(lambda md: md['creators'][0].pop('orcid'), 'creators')
    neg(lambda md: md.update(description=md['description'] + '<h1>junk</h1>tail'), 'description')
    neg(lambda md: md['related_identifiers'][0].update(scheme='url'), 'related_identifiers')
    neg(lambda md: md['creators'][0].update(affiliation='Elsewhere'), 'creators')
    neg(lambda md: md.update(license='cc-by-4.0'), 'license', after=True)          # MIT replaced, not supplemented
    neg(lambda md: md.update(license=['mit', 'apache-2.0']), 'license', after=True)
    for lic in (None, {}, 7, [{'id': 'mit'}, {'title': 'GPL-3.0'}]):
        md = json.loads(json.dumps(fin)); md['license'] = lic
        if lic is None: md.pop('license')
        r = run(d, '--allow-test-ids', '--readback', 'software', str(server_copy(d, 'software', md, 'und.json')), '--after-web-form')
        assert r.returncode == 3 and 'READBACK_SOFTWARE=UNDECIDED' in r.stdout, (lic, r.stdout)
    md = json.loads(json.dumps(fin)); p = server_copy(d, 'software', md, 'top.json'); raw = json.loads(p.read_text())
    for k, v in (('doi', '10.5281/zenodo.11111'), ('conceptdoi', '10.5281/zenodo.22222'), ('links', {'doi': 'https://doi.org/10.5281/zenodo.11111'})):
        r2 = dict(raw); r2[k] = v; p.write_text(json.dumps(r2))
        r = run(d, '--allow-test-ids', '--readback', 'software', str(p)); assert r.returncode == 1 and 'DOI' in r.stdout, (k, r.stdout)
    r2 = dict(raw); r2['metadata'] = dict(raw['metadata'], related_identifiers=[dict(x, identifier=x['identifier'].upper()) if x['scheme'] == 'url' else x for x in raw['metadata']['related_identifiers']])
    p.write_text(json.dumps(r2)); r = run(d, '--allow-test-ids', '--readback', 'software', str(p))
    assert r.returncode == 1 and 'related_identifiers' in r.stdout, r.stdout
    p.write_text('[' * 200000); r = run(d, '--allow-test-ids', '--readback', 'software', str(p))
    assert r.returncode == 1 and 'READBACK_SOFTWARE=FAIL' in r.stdout and 'Traceback' not in r.stderr, (r.stdout, r.stderr[-300:])
    md = json.loads(json.dumps(fin)); p = server_copy(d, 'software', md, 'contra.json'); raw = json.loads(p.read_text())
    raw['metadata']['doi'] = '10.99999/other'; p.write_text(json.dumps(raw))
    r = run(d, '--allow-test-ids', '--readback', 'software', str(p)); assert r.returncode == 1 and 'reserved DOI' in r.stdout, r.stdout
    raw['metadata']['doi'] = raw['metadata']['prereserve_doi']['doi']; raw['metadata']['notes'] = 'server'
    raw['metadata']['doi'] = 'https://doi.org/' + raw['metadata']['doi'].upper(); p.write_text(json.dumps(raw))
    r = run(d, '--allow-test-ids', '--readback', 'software', str(p)); assert r.returncode == 0 and 'not compared' in r.stdout and 'notes' in r.stdout, r.stdout
    src_edit(d, lambda m: m['software'].update(zenodo_concept_doi='10.5281/zenodo.424242')); assert run(d, '--allow-test-ids').returncode == 0
    p = server_copy(d, 'software', meta(d, 'software')['metadata'], 'concept.json')
    r = run(d, '--allow-test-ids', '--readback', 'software', str(p)); assert r.returncode == 0, r.stdout
    raw = json.loads(p.read_text()); raw['conceptrecid'] = '999999'; p.write_text(json.dumps(raw))
    r = run(d, '--allow-test-ids', '--readback', 'software', str(p)); assert r.returncode == 1 and 'concept DOI' in r.stdout, r.stdout
    for args in (['--after-web-form', str(d / 'missing.json')], [str(d)]):
        r = run(d, '--allow-test-ids', '--readback', 'software', *args)
        assert r.returncode == 1 and 'READBACK_SOFTWARE=FAIL' in r.stdout and 'Traceback' not in r.stderr, (args, r.stdout, r.stderr)
    for bogus in ({'metadata': None}, {'metadata': dict(fin, creators=['x'])}, {'metadata': dict(fin, related_identifiers={'a': 1})}):
        p = d / 'bogus.json'; p.write_text(json.dumps(bogus)); r = run(d, '--allow-test-ids', '--readback', 'software', str(p))
        assert r.returncode == 1 and 'READBACK_SOFTWARE=FAIL' in r.stdout and 'Traceback' not in r.stderr, (r.stdout, r.stderr)
    after = server_copy(d, 'software', dict(fin, license=[{'id': 'mit'}, {'id': 'cc-by-4.0'}]), 'after_web_form.json')
    r = run(d, '--allow-test-ids', '--readback', 'software', str(after), '--after-web-form')
    assert r.returncode == 0 and 'licence field reported by the server' in r.stdout, r.stdout
    cff = (d / 'CITATION.cff').read_text(encoding='utf-8'); assert '  year: 2026' in cff
    return ('readback: the final draft (server formatting, extra server fields) PASS; the draft left with the initial '
            'metadata FAIL (publication_date, description, related_identifiers); unescaped description, other reserved '
            'DOI, licence, access right, missing ORCID, extra HTML, relation scheme FAIL; malformed copies FAIL without '
            'a traceback; --after-web-form reports the licence instead of comparing it')

CASES += [('pos_html_real_abstract', case_html_real), ('pos_html_special_characters', case_html_special),
          ('neg_r9_unescaped_payload', case_r9_payload), ('neg_cff_or_licence_array', case_cff_or), ('neg_cff_licence_variants', case_cff_variants), ('neg_readback_candidate_and_mistyped', case_readback_candidate), ('neg_source_values', case_source_values),
          ('neg_single_licence_records', case_single_mit), ('pos_rights_expected', case_rights),
          ('pos_neg_readback_same_draft', case_readback)]

def main():
    work = Path(sys.argv[1]).resolve()
    if work.exists() and any(work.iterdir()): print('work dir not empty'); sys.exit(2)
    work.mkdir(parents=True, exist_ok=True)
    shipped = {f: (ROOT / f).read_bytes() for f in GEN}
    rows, ok = [], 0
    for name, fn in CASES:
        d = work / name; layout(d, baseline=(name != 'pos_shipped_regenerates'))
        try:
            note = fn(d, shipped); res = 'ok'; ok += 1
        except AssertionError as e:
            note, res = 'assertion failed: %s' % (e,), 'WRONG'
        rows.append({'case': name, 'result': res, 'note': note})
    (work / 'RESULTS.json').write_text(json.dumps(rows, indent=1) + '\n')
    for r in rows: print('%-32s %s  %s' % (r['case'], r['result'], r['note']))
    print('METADATA_TESTS=%s %d/%d' % ('PASS' if ok == len(CASES) else 'FAIL', ok, len(CASES)))
    sys.exit(0 if ok == len(CASES) else 1)

if __name__ == '__main__':
    main()

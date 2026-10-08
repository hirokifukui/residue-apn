#!/usr/bin/env python3
"""gen_metadata.py -- every identifier-bearing text of this package from ONE source, release/metadata_source.json
(rewritten in session R13 for GPT R8-F01 / R9-01).
  python3 tools/gen_metadata.py [--check] [--allow-test-ids]       (paths are taken from this file's location)

Generated (whole files): CITATION.cff, release/metadata/zenodo_software.json, release/metadata/zenodo_paper.json.
Generated (marked blocks only, between `<!-- BEGIN gen_metadata:NAME -->` and `<!-- END gen_metadata:NAME -->`):
  README.md (status, cite), CHANGELOG.md (heading). The rest of those files is hand-written.
Checked, not written: the Data-availability sentence of paper/manuscript.tex and paper/elsarticle/manuscript_els.tex
  (candidate: the `\\pending{repository identifier to be added at deposit}` placeholder; release: the software
  version DOI and no placeholder). The paper is rebuilt by the author's publication procedure, not by this script.

Source fields (release/metadata_source.json):
  state            "candidate" (default; nothing published) or "release" (the version deposited under the identifiers
                   below). "release" needs all four DOIs, release_date (YYYY-MM-DD), repository_code (https://...) and
                   git_tag = "v" + version. This script never writes "published": deposit and publication are actions
                   outside this package and are recorded by the author.
  paper/software   zenodo_version_doi (this version) and zenodo_concept_doi (all versions); null until reserved.
  related          cites / references to other works (never a pair relation, never isIdenticalTo).
  licence_scope    which files carry which licence; printed in every description.

Identifier rules (what is generated from what):
  - CFF `doi` and `preferred-citation.doi` carry VERSION DOIs (the exact version of this package / of the paper);
    concept DOIs appear only under `identifiers` with the description "concept DOI (all versions)". A field whose
    DOI is null is omitted; no link, DOI or date is invented.
  - Pair relations are generated, never added by hand: when BOTH version DOIs exist, the software record gets
    {paper version DOI, isSupplementTo} and the paper record gets {software version DOI, isSupplementedBy}.
    With one or none of them, no pair relation is written.
  - When repository_code and git_tag exist, the software record gets {repository_code/tree/git_tag, isSupplementTo,
    url}. isIdenticalTo is never generated (it would need a byte comparison of the GitHub archive and the deposit).
  - The earlier paper of the author (IT-26-1499) stays a `cites` relation.
  - Zenodo files: only the object under "metadata" is the payload sent to Zenodo; "_private" is a local record
    (generator, state, the record's own DOIs for cross-checking) and is never sent.
Further rules (R13 second pass, after an adversarial review of the first version):
  - state candidate: release_date and git_tag must be null (no date or tag before the release); state release: the
    Data-availability sentence must give doi:<software version DOI> outside TeX comments; candidate: the placeholder
    must stand outside TeX comments.
  - `related`: only `cites` / `references`, scheme `doi`; never one of this package's own four DOIs; the author's
    earlier paper 10.5281/zenodo.23074611 must stay `cites`. DOIs are compared case-insensitively.
  - licences fixed by the author: software MIT, prose and paper CC-BY-4.0 (a change is refused, not silently printed).
  - no generated text may call the work published (word "published", any case; "not published", "not yet published"
    and "unpublished" excepted); no control or other Unicode category-C character in any source string.
  - the paper check reads only the section `\\section*{Data availability}` (up to the next section or the bibliography):
    it must appear once and contain no `%` and no `\\iffalse`; candidate: it contains the placeholder sentence DA_CANDIDATE;
    release: it contains DA_RELEASE with the software version DOI and version (R13 third pass).
R14 (GPT R9 review, findings R9-F01..F04):
  - every plain text placed in an HTML description (abstract, formal scope, licence and status sentences) is escaped
    with html.escape; the tags stay. The check parses each description with Python's HTMLParser: only <p> may occur and
    the text of each paragraph must equal the source text exactly (so `sum_{i<r}` can never be read as a tag again).
  - CITATION.cff has no top-level `license`: CFF 1.2.0 reads a list of licences as alternatives (OR), which is not the
    per-file split of this package (code MIT, prose CC BY 4.0). The split is stated in `message`, the comments, the
    README and release/DISTRIBUTION_FILES.tsv; the preferred citation (the paper alone) carries CC-BY-4.0.
  - Zenodo rights: `_private.final_rights` of each record is the rights state the published record must show (software:
    MIT and CC BY 4.0 with their scopes; paper: CC BY 4.0). The legacy deposit API has one licence field
    (`metadata.license`), so the second licence of the software record is added in the web form after the last
    metadata update (release/PUBLICATION_RUNBOOK.md, step 3); `_private.rights_procedure` states this.
  - `--readback KIND FILE [--after-web-form]`: compare a saved server copy of a draft (the JSON of a GET of the
    deposition) with the record generated now. The record must carry its own version DOI (state release or reserved
    identifiers); every DOI field present in the copy (`doi`, `prereserve_doi.doi`) must equal it; the concept DOI must
    equal 10.5281/zenodo.<conceptrecid> of the copy (Zenodo numbering, assumed, see the runbook); then title, version,
    publication_date, upload and publication type, access right, creators (all fields), keywords, the paragraph texts
    of the description (HTML parsed, whitespace normalised; anything outside the paragraphs fails), the related
    identifiers (identifier, relation, scheme; case-insensitive; `https://doi.org/` and `doi:` prefixes removed) and
    the legacy licence field (= first entry of final_rights). With --after-web-form the licence field, as a string or a
    list of strings/objects, must contain the first licence of final_rights and nothing outside final_rights; a field
    that is absent or in an unknown format gives READBACK_<KIND>=UNDECIDED, exit 3 (never PASS): the preview decides.
    Version-DOI fields checked: metadata.doi, metadata.prereserve_doi.doi, top-level doi, doi_url, links.doi (empty
    strings count as absent); concept-DOI fields: top-level / metadata conceptdoi, links.conceptdoi. URL identifiers
    are compared case-sensitively (Git tags are). Metadata keys the generator does not write are listed, not
    failed (servers add fields). The source must pass the structural rules first. An unreadable or malformed copy is a
    FAIL with a READBACK line, not a traceback. Prints READBACK_<KIND>=PASS|FAIL; exit 0 / 1. No network.
--check: exit 1 if any generated file or block differs BYTE FOR BYTE from what is on disk (line endings included), or a
  structural rule fails, or the files on disk fail the meaning checks above (reported with the prefix "on disk:").
--allow-test-ids: accept identifiers of the offline-test form (10.99999/..., *.invalid, example.*). Without the flag
  such identifiers are an error, so a test identifier cannot reach a candidate that passes the gate."""
import datetime, html, json, re, sys, unicodedata
from html.parser import HTMLParser
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'release/metadata_source.json'
PAPERS = ('paper/manuscript.tex', 'paper/elsarticle/manuscript_els.tex')
PENDING = r'\pending{repository identifier to be added at deposit}'
DOI_RE = re.compile(r'10\.\d{4,9}/[^\s"<>]+\Z')
TEST_RE = re.compile(r'\b10\.(9999\d*|5072)/|sandbox\.zenodo|\.(invalid|test|example|localhost)\b|\bexample\.[a-z]|\blocalhost\b', re.I)
DA_CANDIDATE = ('will be deposited in a public repository and cited here \\pending{repository identifier to be added at deposit}. '
                'Until then they accompany the submission as supplementary material.')
DA_RELEASE = 'are deposited at Zenodo, doi:%s (version %s); they also accompany the submission as supplementary material.'

def da_section(tex):
    """The Data-availability section (heading excluded) or None if the heading is not there exactly once."""
    h = '\\section*{Data availability}'
    if tex.count(h) != 1: return None
    rest = tex.split(h, 1)[1]
    end = min([rest.find(x) for x in ('\\section', '\\begin{thebibliography}', '\\bibliography', '\\end{document}') if rest.find(x) >= 0] or [len(rest)])
    return rest[:end]
PUBLISHED_RE = re.compile(r'(?<!not )(?<!not yet )\bpublished\b', re.I)
LICENCES = {'software.licence': 'MIT', 'software.licence_prose': 'CC-BY-4.0', 'paper.licence': 'CC-BY-4.0'}
EARLIER = '10.5281/zenodo.23074611'
def no_comments(tex): return re.sub(r'(?<!\\)%.*', '', tex)
STATES = ('candidate', 'release')

def q(s): return '"' + str(s).replace('\\', '\\\\').replace('"', '\\"') + '"'

def esc(s): return html.escape(str(s), quote=False)

def para(*texts):
    """HTML description from plain paragraphs: each text escaped, each in its own <p>."""
    return ''.join('<p>' + esc(x) + '</p>' for x in texts)

class _Paras(HTMLParser):
    """Text of each top-level <p>; every other tag, comment, declaration or text outside <p> goes to `other`."""
    def __init__(self):
        super().__init__(convert_charrefs=True); self.paras, self.other, self.cur = [], [], None
    def handle_starttag(self, tag, attrs):
        if tag == 'p' and self.cur is None and not attrs: self.cur = []
        else: self.other.append('<%s>' % tag)
    def handle_endtag(self, tag):
        if tag == 'p' and self.cur is not None: self.paras.append(''.join(self.cur)); self.cur = None
        else: self.other.append('</%s>' % tag)
    def handle_data(self, data):
        if self.cur is None: self.other.append('whitespace outside <p>' if not data.strip() else 'text outside <p>: %r' % data[:20])
        else: self.cur.append(data)
    def handle_comment(self, data): self.other.append('comment')
    def handle_decl(self, decl): self.other.append('declaration')
    def handle_pi(self, data): self.other.append('processing instruction')
    def unknown_decl(self, data): self.other.append('declaration')

def html_paragraphs(s):
    """(paragraph texts, other items) of an HTML description, as a browser-like parser reads it."""
    p = _Paras(); p.feed(str(s)); p.close()
    return p.paras, p.other + (['unclosed <p>'] if p.cur is not None else [])

def strings(o):
    if isinstance(o, str): yield o
    elif isinstance(o, dict):
        for v in o.values(): yield from strings(v)
    elif isinstance(o, list):
        for v in o: yield from strings(v)

def ids(m):
    p, s = m['paper'], m['software']
    return {'paper_version': p['zenodo_version_doi'], 'paper_concept': p['zenodo_concept_doi'],
            'software_version': s['zenodo_version_doi'], 'software_concept': s['zenodo_concept_doi']}

NAME = {'CC-BY-4.0': 'CC BY 4.0'}
ZENODO_ID = {'MIT': 'mit', 'CC-BY-4.0': 'cc-by-4.0'}

def licence_text(m):
    sc, s = m['licence_scope'], m['software']
    return ('Licences: the files of this record are distributed under two licences, each for a part of the files; '
            'they are not alternatives for the same file. %s: %s. %s: %s. The licence of every file is listed in '
            'release/DISTRIBUTION_FILES.tsv.' % (
                NAME.get(s['licence'], s['licence']), sc.get(s['licence'], '?'),
                NAME.get(s['licence_prose'], s['licence_prose']), sc.get(s['licence_prose'], '?')))

def desc_paragraphs(m, kind):
    """The plain-text paragraphs of the Zenodo description of record `kind` (before HTML escaping)."""
    st = 'Status: ' + state_text(m)
    if kind == 'paper':
        return [m['abstract'], 'Licence of this record: %s (the paper text and PDFs).' % NAME.get(m['paper']['licence'], m['paper']['licence']), st]
    return [m['abstract'], m['formal_scope'], licence_text(m), st]

def final_rights(m, kind):
    """The rights the published Zenodo record must show (R9-F03): licence id (Zenodo vocabulary) and scope."""
    if kind == 'paper':
        return [{'id': ZENODO_ID.get(m['paper']['licence'], m['paper']['licence'].lower()), 'scope': 'the whole record (the paper text and PDFs)'}]
    s, sc = m['software'], m['licence_scope']
    return [{'id': ZENODO_ID.get(x, x.lower()), 'scope': sc.get(x, '?')} for x in (s['licence'], s['licence_prose'])]

RIGHTS_PROCEDURE = {
    'software': ('The legacy deposit API carries one licence (metadata.license = mit). After the LAST metadata update of '
                 'this draft (PUT), add CC BY 4.0 next to MIT in the Zenodo web form (Licenses; mixed licence uploads) '
                 'and save; no metadata PUT follows (it would send the single licence field again). Then GET and '
                 '--readback --after-web-form again, and the preview must show exactly the licences of final_rights: '
                 'a hard stop before publish.'),
    'paper': 'metadata.license (cc-by-4.0) is the whole of final_rights; nothing is added in the web form.'}
READBACK_FIELDS = ('reserved version DOI (every DOI field present), concept DOI (10.5281/zenodo.<conceptrecid>), title, '
                   'version, publication_date, upload and publication type, access right, creators (all fields), keywords, '
                   'description paragraph texts, related identifiers (identifier, relation, scheme), licence field')
READBACK = ('python3 tools/gen_metadata.py --readback KIND SAVED.json [--after-web-form] compares a saved GET of the draft '
            'with this record: ' + READBACK_FIELDS + '. After the web-form step the licence field must include the first '
            'licence of final_rights and no licence outside final_rights; the preview must show exactly final_rights. '
            'File SHA-256 are compared in the file list.')

def state_text(m):
    i = ids(m)
    if m['state'] == 'release':
        return ('Version %s, deposited under the identifiers given in this record (software version DOI %s; paper version DOI %s).'
                % (m['version'], i['software_version'], i['paper_version']))
    return 'Candidate %s, not published; %s' % (m['version'], 'no identifier has been issued.' if not any(i.values())
                                              else 'identifiers reserved, not yet published.')

def cff_identifiers(version_doi, concept_doi, what, indent):
    out = []
    for d, desc in ((version_doi, 'version DOI of this %s (exactly this version)' % what),
                    (concept_doi, 'concept DOI (all versions) of this %s' % what)):
        if d: out += [indent + '- type: doi', indent + '  value: ' + q(d), indent + '  description: ' + q(desc)]
    return ([indent[:-2] + 'identifiers:'] + out) if out else []

def gen_files(m):
    a, p, s = m['author'], m['paper'], m['software']
    i = ids(m)
    cff = ['# CITATION.cff -- generated by tools/gen_metadata.py from release/metadata_source.json; do not edit by hand.',
           '# `doi` fields are VERSION DOIs; concept DOIs (all versions) are listed under `identifiers`.',
           '# Licences: code and machine-readable files MIT; paper sources and PDFs, blueprint and prose CC-BY-4.0.',
           '# No top-level `license` key: CFF 1.2.0 reads a list of licences as alternatives (OR), not as a per-file split;',
           '# the licence of every file is in release/DISTRIBUTION_FILES.tsv. The preferred citation (the paper) is CC-BY-4.0.',
           'cff-version: 1.2.0',
           'message: ' + q('If you use this package, please cite the paper (preferred citation) and this software. '
                           'Licences apply per file: code and machine-readable files MIT, prose by the author CC BY 4.0 '
                           '(release/DISTRIBUTION_FILES.tsv). '
                           + ('No identifier has been issued yet.' if not any(i.values()) else
                              'Cite the version DOIs given below.')),
           'type: software', 'title: ' + q(s['title']),
           'authors:', '  - family-names: ' + q(a['family']), '    given-names: ' + q(a['given']),
           '    orcid: ' + q('https://orcid.org/' + a['orcid']), '    affiliation: ' + q(a['affiliation']),
           'version: ' + q(m['version'])]
    if m['release_date']: cff.append('date-released: ' + q(m['release_date']))
    if s['repository_code']: cff.append('repository-code: ' + q(s['repository_code']))
    if i['software_version']: cff.append('doi: ' + q(i['software_version']))
    cff += cff_identifiers(i['software_version'], i['software_concept'], 'software', '  ')
    cff.append('keywords:'); cff += ['  - ' + q(k) for k in m['keywords']]
    cff.append('abstract: ' + q(m['abstract'] + ' ' + m['formal_scope']))
    cff += ['preferred-citation:', '  type: article', '  title: ' + q(p['title']), '  authors:',
            '    - family-names: ' + q(a['family']), '      given-names: ' + q(a['given']),
            '      orcid: ' + q('https://orcid.org/' + a['orcid']), '  year: %s' % (str(m['release_date'])[:4] if m['release_date'] else '2026'), '  status: preprint', '  license: ' + q(p['licence'])]
    if i['paper_version']: cff.append('  doi: ' + q(i['paper_version']))
    cff += cff_identifiers(i['paper_version'], i['paper_concept'], 'paper', '    ')
    cff.append('  notes: ' + q('paper/manuscript.pdf in this package; ' + p['journal_note']))
    creators = [{'name': a['family'] + ', ' + a['given'], 'orcid': a['orcid'], 'affiliation': a['affiliation']}]
    rel = [{'identifier': r['identifier'], 'relation': r['relation'], 'scheme': r['scheme']} for r in m['related']]
    rel_sw, rel_pa = list(rel), list(rel)
    if i['paper_version'] and i['software_version']:
        rel_sw.append({'identifier': i['paper_version'], 'relation': 'isSupplementTo', 'scheme': 'doi'})
        rel_pa.append({'identifier': i['software_version'], 'relation': 'isSupplementedBy', 'scheme': 'doi'})
    if s['repository_code'] and s['git_tag']:
        rel_sw.append({'identifier': s['repository_code'].rstrip('/') + '/tree/' + s['git_tag'], 'relation': 'isSupplementTo', 'scheme': 'url'})
    sw_md = {'upload_type': 'software', 'title': s['title'], 'creators': creators,
             'description': para(*desc_paragraphs(m, 'software')),
             'version': m['version'], 'license': s['licence'].lower(), 'keywords': m['keywords'],
             'related_identifiers': rel_sw, 'access_right': 'open'}
    pa_md = {'upload_type': 'publication', 'publication_type': p['resource_type'], 'title': p['title'], 'creators': creators,
             'description': para(*desc_paragraphs(m, 'paper')),
             'version': m['version'], 'license': p['licence'].lower(), 'keywords': m['keywords'],
             'related_identifiers': rel_pa, 'access_right': 'open'}
    for md in (sw_md, pa_md):
        if m['release_date']: md['publication_date'] = m['release_date']
    def priv(kind):
        return {'generated_by': 'tools/gen_metadata.py from release/metadata_source.json',
                'note': 'only the object "metadata" is the payload sent to Zenodo; "_private" is never sent',
                'state': m['state'], 'own_version_doi': i[kind + '_version'], 'own_concept_doi': i[kind + '_concept'],
                'final_rights': final_rights(m, kind), 'rights_procedure': RIGHTS_PROCEDURE[kind], 'readback': READBACK}
    dump = lambda o: json.dumps(o, indent=1, ensure_ascii=False) + '\n'
    return {'CITATION.cff': '\n'.join(cff) + '\n',
            'release/metadata/zenodo_software.json': dump({'_private': priv('software'), 'metadata': sw_md}),
            'release/metadata/zenodo_paper.json': dump({'_private': priv('paper'), 'metadata': pa_md})}

def gen_blocks(m):
    i, s = ids(m), m['software']
    if m['state'] == 'release':
        status = ('**Status: version %s, released %s.** Software (this version): doi:%s; all versions: doi:%s. '
                  'Paper (preprint, this version): doi:%s; all versions: doi:%s. Source repository: %s (tag `%s`). '
                  'Journal: %s.' % (m['version'], m['release_date'], i['software_version'], i['software_concept'],
                                     i['paper_version'], i['paper_concept'], s['repository_code'], s['git_tag'], m['paper']['journal_note']))
        cite = ('4. **Cite**: `CITATION.cff` (software, version DOI doi:%s; the paper is the preferred citation, '
                'version DOI doi:%s).' % (i['software_version'], i['paper_version']))
        head = '## %s — released %s' % (m['version'], m['release_date'])
    else:
        status = ('**Status: private release candidate. Not published, not submitted, no DOI issued.** Identifiers are added only when\n'
                  'the author publishes this package (GitHub and Zenodo together); until then every identifier field below is empty.')
        if any(i.values()):
            status = ('**Status: release candidate %s with reserved identifiers; not yet published.** Identifiers: %s.'
                      % (m['version'], ', '.join('%s doi:%s' % (k.replace('_', ' '), v) for k, v in i.items() if v)))
        cite = '4. **Cite**: `CITATION.cff` (software; the paper is the preferred citation). No identifier exists yet.' \
            if not any(i.values()) else '4. **Cite**: `CITATION.cff` (software; the paper is the preferred citation).'
        head = '## %s — not yet released (candidate prepared 2026-10-07)' % m['version']
    return {'README.md': {'status': status, 'cite': cite}, 'CHANGELOG.md': {'heading': head}}

def apply_blocks(text, blocks, path, bad):
    for name, body in blocks.items():
        b, e = '<!-- BEGIN gen_metadata:%s -->' % name, '<!-- END gen_metadata:%s -->' % name
        if text.count(b) != 1 or text.count(e) != 1 or text.index(b) > text.index(e):
            bad.append('%s: markers for block %s missing or repeated' % (path, name)); continue
        text = text[:text.index(b) + len(b)] + '\n' + body + '\n' + text[text.index(e):]
    return text

def structural(m, files, allow_test):
    bad = []
    if m.get('state') not in STATES: bad.append('state must be one of %s' % (STATES,)); return bad
    i = ids(m)
    for k, v in i.items():
        if v is not None and not (isinstance(v, str) and DOI_RE.match(v)): bad.append('%s is not a DOI: %r' % (k, v))
    for kind in ('paper', 'software'):
        if i[kind + '_version'] and str(i[kind + '_version']).lower() == str(i[kind + '_concept']).lower(): bad.append(kind + ' version DOI equals its concept DOI')
    vals = [v for v in i.values() if v]
    if len({str(v).lower() for v in vals}) != len(vals): bad.append('the four DOIs are not distinct')
    if any(unicodedata.category(ch)[0] == 'C' for x in strings(m) if x is not m.get('_comment') for ch in x): bad.append('control character in the source')
    for path, want in LICENCES.items():
        kind, key = path.split('.')
        if m[kind][key] != want: bad.append('licence %s is %r; the author fixed %s' % (path, m[kind][key], want))
    if set(m['licence_scope']) != {'MIT', 'CC-BY-4.0'}: bad.append('licence_scope must describe MIT and CC-BY-4.0')
    own = {str(v).lower() for v in vals}
    for r in m['related']:
        if r.get('relation') not in ('cites', 'references') or r.get('scheme') != 'doi' or not DOI_RE.match(str(r.get('identifier'))):
            bad.append('related entry not allowed (only cites/references with scheme doi): %r' % r.get('identifier'))
        if str(r.get('identifier')).lower() in own: bad.append('related entry is one of this package\'s own DOIs: %r' % r.get('identifier'))
    if [r.get('relation') for r in m['related'] if str(r.get('identifier')).lower() == EARLIER] != ['cites']:
        bad.append('the earlier paper %s must appear once, as cites' % EARLIER)
    s = m['software']
    if m['state'] == 'candidate' and (m['release_date'] or s['git_tag']): bad.append('state candidate must not carry release_date or git_tag')
    if m['release_date'] is not None:
        try:
            if not re.match(r'^\d{4}-\d{2}-\d{2}$', m['release_date']): raise ValueError
            datetime.date.fromisoformat(m['release_date'])
        except (TypeError, ValueError): bad.append('release_date format')
    for k in ('abstract', 'formal_scope', 'version'):
        if not isinstance(m.get(k), str) or not m[k].strip(): bad.append('%s must be a non-empty string' % k)
    for kind in ('paper', 'software'):
        if not isinstance(m[kind].get('title'), str) or not m[kind]['title'].strip(): bad.append(kind + ' title must be a non-empty string')
    if s['repository_code'] is not None and not s['repository_code'].startswith('https://'): bad.append('repository_code must be https://')
    if s['git_tag'] is not None and s['git_tag'] != 'v' + m['version']: bad.append('git_tag must be v' + m['version'])
    if m['state'] == 'release':
        miss = [k for k, v in i.items() if not v] + [k for k in ('release_date',) if not m[k]] + \
               [k for k in ('repository_code', 'git_tag') if not s[k]]
        if miss: bad.append('state release needs ' + ', '.join(miss))
    test_hits = [v for v in vals + [s['repository_code'] or '', str(m['release_date'] or '')] + [str(r.get('identifier')) for r in m['related']] if v and TEST_RE.search(v)]
    if test_hits and not allow_test: bad.append('test-only identifiers present (use --allow-test-ids only in offline tests): ' + ', '.join(test_hits))
    sw = json.loads(files['release/metadata/zenodo_software.json'])['metadata']
    pa = json.loads(files['release/metadata/zenodo_paper.json'])['metadata']
    pair_sw = [r for r in sw['related_identifiers'] if r['relation'].lower() == 'issupplementto' and r['scheme'].lower() == 'doi']
    pair_pa = [r for r in pa['related_identifiers'] if r['relation'].lower() in ('issupplementedby', 'issupplementto')]
    want = bool(i['paper_version'] and i['software_version'])
    if want and ([r['identifier'] for r in pair_sw] != [i['paper_version']] or [r['identifier'] for r in pair_pa] != [i['software_version']]):
        bad.append('pair relations do not point at the two version DOIs')
    if not want and (pair_sw or pair_pa): bad.append('pair relation without both version DOIs')
    if any(r['relation'] == 'isIdenticalTo' for r in sw['related_identifiers'] + pa['related_identifiers']): bad.append('isIdenticalTo used')
    gen_text = files['CITATION.cff'] + sw['description'] + pa['description'] + ''.join(
        files[f] for f in ('README.md', 'CHANGELOG.md') if f in files)
    if PUBLISHED_RE.search(gen_text) or any(PUBLISHED_RE.search(x) for x in strings(m) if x is not m.get('_comment')):
        bad.append('a generated text or source field calls the work published')
    c = files['CITATION.cff']
    for k in ('cff-version: 1.2.0', 'message: ', 'title: ', 'authors:', 'version: ', 'preferred-citation:'):
        if k not in c: bad.append('cff missing ' + k)
    if (i['software_version'] is None) == ('\ndoi: ' in c): bad.append('cff top-level doi does not match the software version DOI')
    if 'zenodo.org/records' in c or 'doi.org/' in c: bad.append('cff prints a link')
    if sw['creators'] != pa['creators'] or sw['keywords'] != pa['keywords'] or sw['version'] != pa['version']: bad.append('zenodo records differ')
    if m['author']['orcid'] not in c or m['version'] not in c or pa['title'] not in c or sw['title'] not in c: bad.append('cff author/version/titles')
    for rel in PAPERS:
        f = ROOT / rel
        if not f.is_file(): bad.append('missing ' + rel); continue
        raw = f.read_bytes().decode('utf-8'); t = no_comments(raw)
        if TEST_RE.search(raw) and not allow_test: bad.append(rel + ' contains a test-only identifier')
        sec = da_section(raw)
        if sec is None or '%' in sec or '\\iffalse' in sec:
            bad.append(rel + ': Data-availability section missing, repeated, or with a comment or \\iffalse'); continue
        if m['state'] == 'release':
            if PENDING in t or (DA_RELEASE % (i['software_version'], m['version'])) not in sec:
                bad.append(rel + ': Data availability does not give the software version DOI')
        elif DA_CANDIDATE not in sec:
            bad.append(rel + ': state candidate, but the Data-availability placeholder is not in the text')
    return bad + semantic(m, files)

def semantic(m, files):
    """Meaning checks (R14, GPT R9-F01..F03) on generated texts, or on the files on disk in --check."""
    bad = []
    for kind in ('software', 'paper'):
        try:
            o = json.loads(files['release/metadata/zenodo_%s.json' % kind]); md, pv = o['metadata'], o['_private']
            if not isinstance(md, dict) or not isinstance(pv, dict): raise TypeError('not an object')
        except (KeyError, ValueError, TypeError):
            bad.append('%s record unreadable' % kind); continue
        paras, other = html_paragraphs(md.get('description', ''))
        if other: bad.append('%s description: HTML other than plain <p> paragraphs: %s' % (kind, ', '.join(other[:4])))
        if paras != desc_paragraphs(m, kind):
            bad.append('%s description: the HTML paragraph texts differ from the source texts (escaping)' % kind)
        want = final_rights(m, kind)
        if pv.get('final_rights') != want: bad.append('%s final rights differ from the licence scope of the source' % kind)
        if md.get('license') != want[0]['id']: bad.append('%s metadata.license must be %s (legacy single field)' % (kind, want[0]['id']))
        if '_private' in md or 'final_rights' in md: bad.append('%s: a local field is inside the payload object' % kind)
    c = files.get('CITATION.cff', '')
    key = re.compile(r'(?m)^(?P<ind>[ \t]*)(?:-[ \t]*)?[{"\x27]*license["\x27]?[ \t]*:(?P<val>.*)$')
    hits = [(h.group('ind'), h.group('val').strip()) for h in key.finditer(c)]
    if any(i == '' for i, _ in hits) or re.search(r'(?m)^\{.*["\x27]?license["\x27]?[ \t]*:', c):
        bad.append('CITATION.cff has a top-level license (CFF reads a list as alternatives, OR)')
    if hits != [('  ', q(m['paper']['licence']))]:
        bad.append('CITATION.cff: the only license key must be the paper licence of the preferred citation')
    return bad

def bare_doi(s):
    s = str(s).strip()
    for p in ('https://doi.org/', 'http://doi.org/', 'https://dx.doi.org/', 'doi:'):
        if s.lower().startswith(p): s = s[len(p):]
    return s.lower()

def readback(m, kind, path, after_web_form=False):
    """Compare a saved server copy of a draft with the record generated now (R9-F04). No network."""
    o = json.loads(gen_files(m)['release/metadata/zenodo_%s.json' % kind]); want, own = o['metadata'], o['_private']
    norm = lambda s: ' '.join(str(s).split()) if s is not None else None
    low = lambda s: str(s).strip().lower() if s is not None else None
    bad, info, undecided = [], [], []
    try:
        raw = json.loads(Path(path).read_text(encoding='utf-8'))
        got = raw.get('metadata') if isinstance(raw, dict) else None
        if not isinstance(got, dict): raise TypeError('no metadata object')
        links = raw.get('links') if isinstance(raw.get('links'), dict) else {}
        pre = got.get('prereserve_doi') if isinstance(got.get('prereserve_doi'), dict) else {}
        if not own['own_version_doi']:
            bad.append('the record has no version DOI (readback is for drafts with reserved identifiers)')
        else:   # every version-DOI field the copy carries (empty strings count as absent: drafts may report "")
            seen = [x for x in (got.get('doi'), pre.get('doi'), raw.get('doi'), raw.get('doi_url'), links.get('doi')) if x not in (None, '')]
            if not seen or any(bare_doi(x) != bare_doi(own['own_version_doi']) for x in seen): bad.append('reserved DOI')
        cds = [x for x in (raw.get('conceptdoi'), got.get('conceptdoi'), links.get('conceptdoi')) if x not in (None, '')]
        if cds and (not own['own_concept_doi'] or any(bare_doi(x) != bare_doi(own['own_concept_doi']) for x in cds)): bad.append('concept DOI')
        cd = bare_doi(own['own_concept_doi']) if own['own_concept_doi'] else None
        if cd and cd.startswith('10.5281/zenodo.'):
            cr = raw.get('conceptrecid')
            if cr is None or 'zenodo.' + str(cr).strip() != cd.split('/', 1)[1]: bad.append('concept DOI')
        elif cd:
            info.append('concept DOI %s is not of the form 10.5281/zenodo.N: not compared with conceptrecid' % cd)
        for k in ('title', 'version', 'publication_date', 'upload_type', 'publication_type', 'access_right'):
            if norm(got.get(k)) != norm(want.get(k)): bad.append(k)
        paras, other = html_paragraphs(got.get('description') or '')
        other = [x for x in other if x != 'whitespace outside <p>']
        if [norm(x) for x in paras] != [norm(x) for x in desc_paragraphs(m, kind)] or other: bad.append('description')
        crs = got.get('creators')
        if not isinstance(crs, list) or not all(isinstance(c, dict) for c in crs) or \
                [{k: norm(v) for k, v in c.items()} for c in crs] != [{k: norm(v) for k, v in c.items()} for c in want['creators']]:
            bad.append('creators')
        if not isinstance(got.get('keywords'), list) or sorted(map(str, got['keywords'])) != sorted(want['keywords']): bad.append('keywords')
        gr = got.get('related_identifiers', [])
        key = lambda r: (bare_doi(r.get('identifier')) if low(r.get('scheme')) == 'doi' else str(r.get('identifier')).strip(), low(r.get('relation')), low(r.get('scheme')))
        if not isinstance(gr, list) or not all(isinstance(r, dict) for r in gr) or sorted(map(key, gr)) != sorted(map(key, want['related_identifiers'])):
            bad.append('related_identifiers')
        lic = got.get('license')
        ids = [lic] if isinstance(lic, (str, dict)) else lic if isinstance(lic, list) else None
        ids = None if ids is None else [x.get('id') if isinstance(x, dict) else x for x in ids]
        allowed = [r['id'] for r in own['final_rights']]
        if not after_web_form:
            if ids is None or [low(x) for x in ids] != [allowed[0]]: bad.append('license')
        elif ids is None or not ids or not all(isinstance(x, str) for x in ids):
            undecided.append('licence field absent or in an unknown format: %r' % (lic,))
        elif allowed[0] not in [low(x) for x in ids] or any(low(x) not in allowed for x in ids):
            bad.append('license')
        else:
            info.append('licence field reported by the server: %r' % (lic,))
        extra = sorted(set(got) - set(want) - {'doi', 'prereserve_doi', 'license'})
        if extra: info.append('server fields not written by the generator (not compared): ' + ', '.join(map(str, extra)))
    except (OSError, ValueError, TypeError, AttributeError, KeyError, RecursionError) as e:
        bad.append('unreadable or malformed server copy (%s)' % type(e).__name__)
    if bad: print('READBACK_%s=FAIL %s' % (kind.upper(), ', '.join(bad)))
    elif undecided: print('READBACK_%s=UNDECIDED %s -- every other field PASS; the preview must show exactly the licences '
                          'below, or stop' % (kind.upper(), '; '.join(undecided)))
    else: print('READBACK_%s=PASS' % kind.upper())
    for x in info: print(x)
    print('confirm in the record preview: licences exactly ' + '; '.join(
        '%s (%s)' % (r['id'], r['scope']) for r in final_rights(m, kind)) + '; file SHA-256 in the file list')
    return 1 if bad else 3 if undecided else 0

def main():
    allow = '--allow-test-ids' in sys.argv
    try:
        m = json.loads(SRC.read_text(encoding='utf-8'))
        if not isinstance(m, dict): raise ValueError('not an object')
    except (OSError, ValueError) as e:
        print('METADATA=FAIL source unreadable: %s' % e); sys.exit(1)
    bad = []
    if m.get('state') not in STATES:
        print('METADATA%s=FAIL state must be one of %s' % ('_CHECK' if '--check' in sys.argv else '', STATES)); sys.exit(1)
    files = gen_files(m)
    for path, blocks in gen_blocks(m).items():
        files[path] = apply_blocks((ROOT / path).read_bytes().decode('utf-8'), blocks, path, bad)
    bad += structural(m, files, allow)
    if '--readback' in sys.argv:
        pos = [a for a in sys.argv[sys.argv.index('--readback') + 1:] if not a.startswith('--')]
        if len(pos) < 2 or pos[0] not in ('software', 'paper'):
            print('READBACK=FAIL usage: --readback software|paper SAVED.json [--after-web-form]'); sys.exit(2)
        if bad: print('READBACK_%s=FAIL the source fails the structural rules: %s' % (pos[0].upper(), '; '.join(bad))); sys.exit(1)
        sys.exit(readback(m, pos[0], pos[1], '--after-web-form' in sys.argv))
    if '--check' in sys.argv:
        disk = {p: (ROOT / p).read_bytes().decode('utf-8', 'replace') for p in files if (ROOT / p).is_file()}
        bad += ['on disk: ' + x for x in semantic(m, disk)]
        bad += ['differs: ' + p for p, t in files.items() if not (ROOT / p).is_file() or (ROOT / p).read_bytes() != t.encode('utf-8')]
        print('METADATA_CHECK=' + ('PASS' if not bad else 'FAIL ' + '; '.join(bad))); sys.exit(1 if bad else 0)
    if bad: print('METADATA=FAIL ' + '; '.join(bad)); sys.exit(1)
    for p, t in files.items():
        if not (ROOT / p).is_file() or (ROOT / p).read_bytes() != t.encode('utf-8'):
            (ROOT / p).parent.mkdir(parents=True, exist_ok=True); (ROOT / p).write_bytes(t.encode('utf-8'))
    print('METADATA=OK state=%s written-or-unchanged %s' % (m['state'], sorted(files)))

if __name__ == '__main__':
    main()

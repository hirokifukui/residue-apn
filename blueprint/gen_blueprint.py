#!/usr/bin/env python3
"""Blueprint generator for the residue-APN paper (FFTA candidate). Adapted from apnlift blueprint/R48 (2026-10-07);
rewritten in session R11 (GPT R7-03/04/07): context from the paper, bibliography, two separately labelled graphs,
escaping of notes and Lean names, all outputs checkable byte for byte.

Run from anywhere:   python3 gen_blueprint.py
Inputs  the paper source and its .aux (paper/manuscript.tex in the release layout; the author's development folder otherwise), the
        statement map ../formalization/leanmap.json, the Lean sources ../lean/residue_apn_portable/ResidueAPN*.
Outputs src/content.tex, src/bib.tex, src/paperlabels.aux, nodes.json, dep_graph.dot, lean_imports.dot.
Every statement, proof and context paragraph is copied byte for byte from the manuscript (labels removed; equation
labels become tags with the paper's number). check_blueprint.py regenerates everything in memory and compares."""
import json, re, hashlib, sys
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent

def _first(*cands):
    for c in cands:
        if c.is_file(): return c
    return cands[-1]

MS = _first(HERE.parent / 'paper' / 'manuscript.tex', HERE.parents[1] / 'paper_R5' / 'manuscript.tex')  # dev-layout fallback
AUX = MS.with_suffix('.aux')
LEANMAP = HERE.parent / 'formalization' / 'leanmap.json'
LEANDIR = HERE.parent / 'lean' / 'residue_apn_portable'
ENVS = ['theorem', 'lemma', 'proposition', 'corollary', 'definition', 'remark']
NAMES = {'theorem': 'Theorem', 'lemma': 'Lemma', 'proposition': 'Proposition', 'corollary': 'Corollary',
         'definition': 'Definition', 'remark': 'Remark'}

def opt_arg(s, i):
    depth = 0; j = i
    while j < len(s):
        c = s[j]
        if c in '[{': depth += 1
        elif c in ']}':
            depth -= 1
            if depth == 0: return s[i + 1:j], j + 1
        j += 1
    raise ValueError('unbalanced optional argument')

def items(text):
    """Yield ('section', title, label, starred, start), ('env', env, opt, body, start), ('prose', text, start)
    for the document body (between \\maketitle or \\begin{document} and \\begin{thebibliography})."""
    b0 = text.find('\\maketitle'); b0 = b0 + len('\\maketitle') if b0 >= 0 else text.find('\\begin{document}')
    b1 = text.find('\\begin{thebibliography}'); b1 = b1 if b1 >= 0 else len(text)
    pat = re.compile(r'\\begin\{(' + '|'.join(ENVS + ['proof']) + r')\}|\\section(\*?)\{')
    pos = b0
    while True:
        m = pat.search(text, pos, b1)
        if m and m.start() > pos: yield ('prose', text[pos:m.start()], pos)
        if not m:
            if b1 > pos: yield ('prose', text[pos:b1], pos)
            return
        if m.group(1) is None:
            depth = 1; j = m.end()
            while depth:
                depth += {'{': 1, '}': -1}.get(text[j], 0); j += 1
            title = text[m.end():j - 1]
            lab = re.match(r'\s*\\label\{([^}]*)\}', text[j:])
            if lab: j += lab.end()
            yield ('section', title, lab.group(1) if lab else None, m.group(2) == '*', m.start()); pos = j; continue
        env = m.group(1); i = m.end(); opt = ''
        if i < len(text) and text[i] == '[': opt, i = opt_arg(text, i)
        end = text.index('\\end{%s}' % env, i)
        yield ('env', env, opt, text[i:end], m.start()); pos = end + len('\\end{%s}' % env)

def refs(s):
    out = []
    for grp in re.findall(r'\\(?:ref|eqref)\{([^}]*)\}', s): out += [g.strip() for g in grp.split(',')]
    return out

def strip_labels(s): return re.sub(r'\\label\{[^}]*\}', '', s)

def context_tex(s):
    s = re.sub(r'\\begin\{equation\}\\label\{([^}]*)\}', r'\\begin{equation}\\tag{\\ref*{\1}}', s)
    return strip_labels(s).strip()

def build():
    text = MS.read_text(encoding='utf-8')
    lm = json.loads(LEANMAP.read_text(encoding='utf-8'))['nodes']
    nodes, chapters = [], []
    sec = None; queue = []; last = None
    def close_section():
        if sec is not None and sec['nodes'] and queue and last is not None:
            last['after'] += list(queue)
    for it in items(text):
        if it[0] == 'section':
            close_section(); queue = []; last = None
            nsec = locals().get('nsec', 0) + (0 if it[3] else 1)
            sec = {'title': it[1], 'label': it[2], 'starred': it[3], 'nodes': [], 'number': nsec}
            if not it[3]: chapters.append(sec)
            continue
        if sec is None or sec['starred']: continue
        if it[0] == 'prose':
            t = it[1].strip()
            if t: queue.append(t)
            continue
        _, env, opt, body, start = it
        if env == 'proof':
            if last is not None and not queue: last['proofs'].append({'opt': opt, 'body': body, 'pos': start})
            elif last is not None: last['proofs'].append({'opt': opt, 'body': body, 'pos': start, 'pre': list(queue)}); queue = []
            continue
        lab = re.search(r'\\label\{([^}]*)\}', body)
        if lab is None:
            queue.append('\\begin{%s}%s%s\\end{%s}' % (env, '[' + opt + ']' if opt else '', body, env)); continue
        node = {'label': lab.group(1), 'env': env, 'opt': opt, 'body': body, 'proofs': [], 'pos': start,
                'context': list(queue), 'after': [], 'chapter': len(chapters) - 1}
        queue = []
        nodes.append(node); sec['nodes'].append(node['label']); last = node
    close_section()
    labels = {n['label'] for n in nodes}; pos = {n['label']: n['pos'] for n in nodes}
    for n in nodes:
        parts = [(n['opt'] + n['body'], n['pos'])] + [(p['opt'] + p['body'], p['pos']) for p in n['proofs']]
        u = set()
        for txt, where in parts:
            u |= {r for r in refs(txt) if r in labels and r != n['label'] and pos[r] < where}
        n['uses'] = sorted(u)
        n['forward'] = sorted({r for txt, _ in parts for r in refs(txt) if r in labels and r != n['label']} - u)
        e = lm.get(n['label'], {})
        n['trust'] = e.get('trust', 'Def' if n['env'] == 'definition' else 'M')
        n['lean'] = e.get('lean', []); n['lean_defs'] = e.get('lean_defs', []); n['trust_note'] = e.get('note', '')
    return nodes, [c for c in chapters if c['nodes']]

ESC = [('\\', '\\textbackslash{}'), ('{', '\\{'), ('}', '\\}'), ('_', '\\_'), ('^', '\\textasciicircum{}'),
       ('#', '\\#'), ('&', '\\&'), ('%', '\\%'), ('~', '\\textasciitilde{}'), ('>=', '$\\ge$'), ('<=', '$\\le$'),
       ('->', '$\\to$')]

def esc(s):
    out = []
    i = 0
    while i < len(s):
        for a, b in ESC:
            if s.startswith(a, i):
                out.append(b); i += len(a); break
        else:
            out.append(s[i]); i += 1
    return ''.join(out)

def lean_tt(d):
    return '\\texttt{' + esc(d).replace('.', '.\\allowbreak{}').replace('\\_', '\\_\\allowbreak{}') + '}'

def tex(nodes, chapters):
    L = ['% content.tex -- GENERATED by gen_blueprint.py; do not edit by hand.',
         '% Statements, proofs and context paragraphs are copied verbatim from the paper source (labels removed).']
    env_of = {m['label']: m['env'] for m in nodes}
    by_ch = {}
    for n in nodes: by_ch.setdefault(n['chapter'], []).append(n)
    for ci, c in enumerate(chapters):
        L.append('\\setcounter{chapter}{%d}\\chapter{%s}' % (c['number'] - 1, c['title']))
        if c['label']: L.append('\\noindent Paper: Section~\\ref{%s}.' % c['label'])
        for n in [x for x in nodes if x['label'] in c['nodes']]:
            for ctx in n['context']:
                L.append('\\begin{bpcontext}' + context_tex(ctx) + '\\end{bpcontext}')
            head = NAMES[n['env']] + '~\\ref{%s}' % n['label']
            title = (' (' + n['opt'] + ')') if n['opt'] else ''
            L.append('\\section*{%s%s}\\label{bp:%s}' % (head, title, n['label']))
            L.append('\\addcontentsline{toc}{section}{%s \\quad[%s]}' % (head.replace('~', ' '), esc(n['trust'])))
            L.append('\\bpmeta{Trust}{[%s]}' % esc(n['trust']))
            if n['uses']:
                L.append('\\bpmeta{Cites (earlier labelled statements)}{' + ', '.join(
                    '\\hyperref[bp:%s]{%s~\\ref*{%s}}' % (u, NAMES[env_of[u]], u) for u in n['uses']) + '}')
            if n['lean']:
                L.append('\\bpmeta{Lean theorems}{' + ', '.join(lean_tt(d) for d in n['lean']) + '}')
            if n['lean_defs']:
                L.append('\\bpmeta{Lean definitions}{' + ', '.join(lean_tt(d) for d in n['lean_defs']) + '}')
            if n['trust_note']:
                L.append('\\bpmeta{Label note}{' + esc(n['trust_note']) + '}')
            L.append('\\begin{bpstatement}' + strip_labels(n['body']) + '\\end{bpstatement}')
            for p in n['proofs']:
                for ctx in p.get('pre', []):
                    L.append('\\begin{bpcontext}' + context_tex(ctx) + '\\end{bpcontext}')
                L.append('\\begin{proof}' + ('[' + p['opt'] + ']' if p['opt'] else '') + strip_labels(p['body']) + '\\end{proof}')
            for ctx in n['after']:
                L.append('\\begin{bpcontext}' + context_tex(ctx) + '\\end{bpcontext}')
    return '\n'.join(L) + '\n'

def bib_tex():
    text = MS.read_text(encoding='utf-8')
    a = text.find('\\begin{thebibliography}'); b = text.find('\\end{thebibliography}')
    if a < 0 or b < 0: return '% no bibliography in the paper\n'
    return ('% bib.tex -- GENERATED by gen_blueprint.py: the paper\'s bibliography, copied verbatim.\n'
            + text[a:b + len('\\end{thebibliography}')] + '\n')

def paper_labels_text():
    if not AUX.is_file(): return None
    aux = AUX.read_text(encoding='utf-8')
    bib = set(re.findall(r'\\bibcite\{([^}]*)\}', aux))
    keep = [l for l in aux.splitlines() if l.startswith('\\newlabel{') and re.match(r'\\newlabel\{([^}]*)\}', l).group(1) not in bib]
    return '\n'.join(keep) + '\n'

def nodes_json(nodes):
    js = [{'label': n['label'], 'env': n['env'], 'trust': n['trust'], 'uses': n['uses'], 'forward_refs': n['forward'],
           'trust_note': n['trust_note'], 'lean': n['lean'], 'lean_defs': n['lean_defs'],
           'statement_sha256': hashlib.sha256(n['body'].encode()).hexdigest(),
           'proofs': [hashlib.sha256(p['body'].encode()).hexdigest() for p in n['proofs']],
           'context_sha256': [hashlib.sha256(c.encode()).hexdigest() for c in n['context'] + n['after']]} for n in nodes]
    return json.dumps(js, indent=1, ensure_ascii=False) + '\n'

def dep_dot(nodes):
    def col(t):
        if t == 'F': return 'palegreen'
        if t.startswith('F'): return 'lightcyan'
        return {'L + M': 'lightblue', 'M': 'lightyellow', 'Def': 'white', 'Rem': 'white'}.get(t, 'white')
    dot = ['digraph blueprint {',
           '  graph [rankdir=LR, ranksep=0.5, nodesep=0.15, fontsize=10, labelloc=t,',
           '         label="Reference graph of the paper: an arrow A -> B means that the statement or a proof of B cites the earlier statement A by \\\\ref.\\nIt is extracted from the source; it is not a complete proof-dependency graph and not the Lean import graph."];',
           '  node [shape=box, style=filled, fontsize=10];']
    for n in nodes:
        dot.append('  "%s" [fillcolor=%s, label="%s\\n[%s]"];' % (n['label'], col(n['trust']), n['label'], n['trust']))
    for n in nodes:
        for u in n['uses']: dot.append('  "%s" -> "%s";' % (u, n['label']))
    dot.append('}')
    return '\n'.join(dot) + '\n'

def lean_dot():
    mods = {}
    files = sorted(LEANDIR.glob('ResidueAPN/**/*.lean'))
    for f in files:
        mod = 'ResidueAPN.' + '.'.join(f.relative_to(LEANDIR / 'ResidueAPN').with_suffix('').parts)
        mods[mod] = sorted(re.findall(r'^import\s+(ResidueAPN\.[\w.]+)', f.read_text(encoding='utf-8'), re.M))
    dot = ['digraph lean_imports {',
           '  graph [rankdir=TB, ranksep=0.3, nodesep=0.2, fontsize=10, labelloc=t,',
           '         label="Lean module import graph of ResidueAPN: an arrow A -> B means that module B imports module A.\\nRead from the import lines of the sources; it is not the paper\'s reference graph."];',
           '  node [shape=box, fontsize=9];']
    for m in sorted(mods): dot.append('  "%s";' % m)
    for m in sorted(mods):
        for i in mods[m]: dot.append('  "%s" -> "%s";' % (i, m))
    dot.append('}')
    return '\n'.join(dot) + '\n'

def outputs():
    nodes, chapters = build()
    out = {'src/content.tex': tex(nodes, chapters), 'src/bib.tex': bib_tex(), 'nodes.json': nodes_json(nodes),
           'dep_graph.dot': dep_dot(nodes), 'lean_imports.dot': lean_dot()}
    pl = paper_labels_text()
    if pl is not None: out['src/paperlabels.aux'] = pl
    return out, nodes, chapters

def main():
    out, nodes, chapters = outputs()
    (HERE / 'src').mkdir(exist_ok=True)
    for p, t in out.items(): (HERE / p).write_text(t, encoding='utf-8')
    from collections import Counter
    print('paper', MS)
    print('paper labels', out.get('src/paperlabels.aux', '').count('\\newlabel') if 'src/paperlabels.aux' in out else 'aux missing: build the paper first')
    print('chapters', len(chapters), 'nodes', len(nodes), dict(Counter(n['trust'] for n in nodes)))
    print('context paragraphs', sum(len(n['context']) + len(n['after']) for n in nodes))
    print('theorem-like nodes without proof (not Def/Rem):', [n['label'] for n in nodes if not n['proofs'] and n['trust'] not in ('Def', 'Rem')])

if __name__ == '__main__': main()

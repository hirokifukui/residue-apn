#!/usr/bin/env python3
"""make_elsarticle.py (2026-10-07, after Dr. Fukui installed elsarticle on agora with tlmgr):
build an elsarticle (preprint) version of the amsart source manuscript.tex WITHOUT touching it.
The body (from \\maketitle to \\end{document}) is copied byte-for-byte; only the preamble and front matter change.
Run from this folder:  python3 make_elsarticle.py && pdflatex manuscript_els.tex (twice)."""
import re, sys, hashlib
sys.dont_write_bytecode = True
import os
SRC = '../paper_R5/manuscript.tex' if os.path.isfile('../paper_R5/manuscript.tex') else '../manuscript.tex'   # dev-layout fallback (R11l); release: ../manuscript.tex
s = open(SRC, encoding='utf-8').read()
title = re.search(r'\\title\[[^\]]*\]\{(.*)\}\n', s).group(1)
abstract = s[s.index('\\begin{abstract}') + len('\\begin{abstract}'):s.index('\\end{abstract}')].strip()
kw = re.search(r'\\keywords\{([^}]*)\}', s).group(1).split(', ')
msc = re.search(r'\\subjclass\[2020\]\{([^}]*)\}', s).group(1).split(', ')
body = s[s.index('\\maketitle') + len('\\maketitle'):]
macros = s[s.index('\\newtheorem{theorem}'):s.index('\\begin{document}')]
pre = r"""\documentclass[preprint,12pt]{elsarticle}
\usepackage{lmodern}
\usepackage{amssymb,amsmath,mathtools,booktabs,amsthm}
\usepackage[hidelinks]{hyperref}
""" + macros + r"""\journal{Finite Fields and Their Applications}
\begin{document}
\begin{frontmatter}
\title{""" + title + r"""}
\author[a,b]{Hiroki Fukui\corref{cor1}}
\ead{fukui@somec.org}
\cortext[cor1]{Corresponding author. ORCID: 0009-0008-7122-522X.}
\affiliation[a]{organization={Research Institute of Criminal Psychiatry / Sex Offender Medical Center},
  addressline={4F Akasaka K-Tower, 1-2-7 Moto-Akasaka}, city={Minato-ku, Tokyo}, country={Japan}}
\affiliation[b]{organization={Department of Neuropsychiatry, Kyoto University}, city={Kyoto}, country={Japan}}
\begin{abstract}
""" + abstract + r"""
\end{abstract}
\begin{keyword}
""" + ' \\sep '.join(kw) + r"""
\MSC[2020] """ + ' \\sep '.join(msc) + r"""
\end{keyword}
\end{frontmatter}
"""
out = pre + body
open('manuscript_els.tex', 'w', encoding='utf-8').write(out)
print('source sha256', hashlib.sha256(s.encode()).hexdigest())
print('body copied byte-for-byte:', out.endswith(body), 'keywords', len(kw), 'msc', len(msc))

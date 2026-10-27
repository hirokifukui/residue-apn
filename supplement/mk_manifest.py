# mk_manifest.py (R04, R05, R05c, R06, R07, R08): generates MANIFEST.txt (artifact <- command <- inputs, with SHA256).
# SHA256SUMS.txt is written by the packing script over every file of the tree.
import hashlib, os
def h(p): return hashlib.sha256(open(p,'rb').read()).hexdigest()
M5='F1_c0A1_plus2X2.txt P53nat.txt P53nat_split.txt P53sp.txt c0_A1.txt c0_A1_split.txt c1_A1.txt c1nat.txt m124_A1.txt m40_A1.txt m57_A1.txt m75_A1.txt'.split()
M=[
 ('cert/identities_cert.out','replay_core stage 1: cd cert && python3 identities_cert.py',['cert/identities_cert.py']),
 ('e_tests.json','replay_core stage 2: python3 e_tests.py',['e_tests.py','inv.py','c0_A1.txt','F1_c0A1_plus2X2.txt','P53nat.txt','P53sp.txt','c1nat.txt']),
 ('negative_controls.json','replay_core stage 3: python3 run_negative.py',['run_negative.py','validate_v3.py','neg/mk.sh','grddt3.c','c0_A1.txt','c1_o3.txt']),
 ('validate_v3.json','replay_core stage 4: VEXPECT_MATCH=23 VEXPECT_BOUND=1 python3 validate_v3.py <12 m=5 inputs>',['validate_v3.py','grddt3.c','inv.py']+M5),
 ('validate_v3_Azero.json','replay_core stage 5: VEXPECT_MATCH=2 VEXPECT_BOUND=2 python3 validate_v3.py c0_o3.txt c1_o3.txt',['c0_o3.txt','c1_o3.txt']),
 ('rep/m7_search.log','replay_core stage 6: rep/rsearch 7 20261025 2000000',['rep/rsearch.c']),
 ('rep/representative_certificate.json','replay_core stage 7: cd rep && python3 build_rep.py (+ SHA check of the 4 tables)',['rep/build_rep.py','rep/rep5_seed.json','inv.py','rep/m7_search.log']),
 ('validate_v3_rep5.json','replay_core stage 8: VEXPECT_MATCH=2 VEXPECT_BOUND=2 python3 validate_v3.py rep5_nat.txt rep5_A1.txt',['rep5_nat.txt','rep5_A1.txt']),
 ('tests/cross_level_regression.json','replay_core stage 9: python3 tests/test_cross_level.py',['tests/test_cross_level.py','c1_o3.txt','F1_c0A1_plus2X2.txt','rep5_A1.txt']),
 ('tests/crypto_c3_test.json','replay_core stage 9: python3 tests/test_crypto_c3.py',['tests/test_crypto_c3.py','P53sp.txt']),
 ('tests/markov_two_words.json','replay_core stage 9 (R05): python3 tests/test_markov_two_words.py',['tests/test_markov_two_words.py','P53sp.txt','inv.py']),
 ('tests/natural_k3.json','replay_core stage 9 (R05): python3 tests/test_natural_k3.py (P95/P97 samples)',['tests/test_natural_k3.py','natural/P95nat.txt','natural/P97nat.txt','natural/P95nat_k3.out','natural/P97nat_k3.out']),
 ('tests/natural_k3_full.json','replay_full F3b (R05): NATURAL_REQUIRE_P75=1 python3 tests/test_natural_k3.py',['tests/test_natural_k3.py','validate_v3_P75.json']),
 ('natural/P97nat_k3.out','R05 (Mac Studio): ./grddt3 9 3 529 natural/P97nat.txt 2 1',['grddt3.c','natural/P97nat.txt']),
 ('natural/P95nat_k3.out','R05 (Mac Studio): ./grddt3 9 3 529 natural/P95nat.txt 2 1',['grddt3.c','natural/P95nat.txt']),
 ('tests/replay_scope_negatives_r05.log','R05: sh tests/replay_scope_negatives.sh',['tests/replay_scope_negatives.sh','replay_core.sh','rep/m11check.py']),
 ('rep/m11_check_r05.out','R05: python3 rep/m11check.py (patched: non-zero exit on 0 witnesses or mismatch)',['rep/m11check.py','inv.py','rep/m11_search.log']),
 ('tests/rep_family.json','replay_core stage 9 (R05b): python3 tests/test_rep_family.py',['tests/test_rep_family.py','rep_family/symcheck.py','rep_family/sym.py','rep_family/brute.c']),
 ('tests/m3_no_H_check.out','replay_core stage 9 (R05b): python3 tests/m3_no_H_check.py',['tests/m3_no_H_check.py']),
 ('rep_family/independent_m13/inv_p13_d6.json','R05b: python3 rep_family/independent_m13/gen.py 13; python3 -I inv.py 13 p13_d6.txt',['rep_family/independent_m13/gen.py','rep_family/independent_m13/p13_d6.txt','inv.py']),
 ('layers/summary.json','R05b (layers research): redspec2.c / rowspec.c rows graded by predict.py (m=5, 691 rows)',['layers/predict.py','layers/redspec2.c','layers/rowspec.c']),
 ('natural/P75sp_k4.out','R05b (Mac Studio): ./grddt3 7 4 131 P75sp.txt 2 7',['grddt3.c','P75sp.txt']),
 ('natural/P75nat_k4.out','R05b (Mac Studio): ./grddt3 7 4 131 P75nat.txt 2 7',['grddt3.c','P75nat.txt']),
 ('validate_v3_rep7.json','replay_full F1: VM=7 VK=3,4 VEXPECT_MATCH=2 python3 validate_v3.py rep7_nat.txt',['rep7_nat.txt']),
 ('validate_v3_P73_full.json','replay_full F2: VM=7 VK=3 VEXPECT_MATCH=2 python3 validate_v3.py P73sp.txt P73nat.txt',['P73sp.txt','P73nat.txt']),
 ('validate_v3_P75.json','replay_full F3: VM=7 VK=3 VEXPECT_MATCH=1 VEXPECT_BOUND=1 python3 validate_v3.py P75sp.txt P75nat.txt',['P75sp.txt','P75nat.txt']),
 ('rep/m9_search.log','replay_full F4: rep/rsearch 9 20261025 3000000',['rep/rsearch.c']),
 ('inv_P113sp.json','replay_full F5: python3 inv.py 11 P113sp.txt',['P113sp.txt']),('inv_P113nat.json','replay_full F5: python3 inv.py 11 P113nat.txt',['P113nat.txt']),
 ('inv_P133sp.json','replay_full F5: python3 inv.py 13 P133sp.txt',['P133sp.txt']),('inv_P133nat.json','replay_full F5: python3 inv.py 13 P133nat.txt',['P133nat.txt']),
 ('rep/m11_search.log','R04b: rep/rsearch 11 20261025 1000000',['rep/rsearch.c']),
 ('rep/m11_check.json','R04b: python3 rep/m11check.py (independent check of every mu=0, z=0 hit with inv.py)',['rep/m11check.py','inv.py','rep/m11_search.log']),
 ('lit/bs_trace_validate_k3.json','VK=3 python3 validate_v3.py lit/bs_trace_m5_nat.txt lit/bs_trace_m5_A0.txt',['lit/bs_trace_m5_nat.txt','lit/bs_trace_m5_A0.txt']),
 ('lit/bs_trace_validate_k4.json','VK=4 python3 validate_v3.py lit/bs_trace_m5_nat.txt lit/bs_trace_m5_A0.txt',['lit/bs_trace_m5_nat.txt','lit/bs_trace_m5_A0.txt']),
 ('tests/sparse_family.out','replay_core stage 9 (R05c): python3 tests/test_sparse_family.py',['tests/test_sparse_family.py','rep_family/sym.py']),
 ('tests/hull_toy.out','replay_core stage 9 (R05c): python3 tests/test_hull_toy.py',['tests/test_hull_toy.py']),
 ('tests/hull_layer.out','replay_core stage 9 (R06): python3 tests/test_hull_layer.py',['tests/test_hull_layer.py']),
 ('cert/sparse_cert_r06.out','replay_core stage 9 (R06): python3 cert/sparse_cert_r06.py (certificate of Thm sparse, written from scratch)',['cert/sparse_cert_r06.py']),
 ('layers/r05c/ver3_replay.jsonl','replay_full F6 (R05c): cd layers/r05c && python3 verify_batch.py gen3.jsonl ver3_replay.jsonl',['layers/r05c/verify_batch.py','layers/r05c/verify.py','layers/r05c/gr.py','layers/r05c/closed.py','layers/r05c/clsspec2.c','layers/r05c/gen3.jsonl']),
 ('rep_sparse/replay_counts.out','replay_full F7 (R05c): rep_sparse/independent_param_count.c (m=5..13) and independent_curve_count.c (m=17)',['rep_sparse/independent_param_count.c','rep_sparse/independent_curve_count.c']),
 ('layers/r05c/ver1.jsonl','R05c research (container): python3 verify_batch.py gen1u.jsonl ver1.jsonl',['layers/r05c/gen1u.jsonl','layers/r05c/verify_batch.py']),
 ('layers/r05c/ver2.jsonl','R05c research (container): python3 verify_batch.py gen2u.jsonl ver2.jsonl',['layers/r05c/gen2u.jsonl','layers/r05c/verify_batch.py']),
 ('layers/r05c/ver3.jsonl','R05c research (container): python3 verify_batch.py gen3.jsonl ver3.jsonl',['layers/r05c/gen3.jsonl','layers/r05c/verify_batch.py']),
 ('layers/r05c/ver3b.jsonl','R05c research (container): python3 verify_batch.py gen3b.jsonl ver3b.jsonl',['layers/r05c/gen3b.jsonl','layers/r05c/verify_batch.py']),
 ('layers/r05c/recheck_old.jsonl','R05c research (container): python3 recheck_old.py (691 R05b rows)',['layers/r05c/recheck_old.py']),
 ('tex/apn2_full.pdf','cd tex && pdflatex apn2_full.tex (3 runs)',['tex/apn2_full.tex']),
 ('checker_magma_v2.m','python3 mkmagma_v2.py (R03)',['mkmagma_v2.py']),
]
with open('MANIFEST.txt','w') as f:
    f.write('# MANIFEST R08 (artifact <- command <- inputs). Tools: gcc 13.3.0, Python 3.13.17, sympy 1.14.0, numpy 2.x, pdfTeX (TeX Live), Magma V2.29-7 (A9, R03), Lean 4.31.0-rc1 (Studio).\n')
    f.write('# Replays (core and full) were run in fresh scratch copies with all generated files removed (cloud container, 2 cores): replay_core_r04.log, replay_full_r04.log;\n')
    f.write('# R05: replay_core_r05.log and replay_full_r05.log (fresh scratch copies of r07). The shipped JSON/.out are kept from R04b (Studio) except the new R05 tests.\n')
    f.write('# R05c: replay_full_r05c.log (fresh scratch copy, container); the new R05c outputs (stage 9 tests, F6, F7) are taken from that run.\n')
    f.write('# R06: replay_core_r06.log and replay_full_r06.log (fresh scratch copies of r08); new stage 9 outputs tests/hull_layer.out and cert/sparse_cert_r06.out.\n')
    f.write('# R07: no code or Lean change; replay_core_r07.log (fresh scratch copy of r09, container). replay_full_r06.log remains the latest full replay.\n')
    f.write('# R08: no code or Lean change.\n')
    f.write('# The JSON/.out/.log outputs shipped here were regenerated on Mac Studio (Apple clang 21, Python 3.9.6, numpy 2.0.2) from a scratch copy\n')
    f.write('# (stages 0,2-9 and F1-F5, lit/ scripts); cert/identities_cert.out comes from the container run (stage 1 needs sympy). Log: regen_studio_r04.log.\n')
    f.write('# Sampled k>=4 directions come from the C library rand(), so their lists differ between the container (glibc) and macOS; all statuses and counts agree.\n')
    for a,c,ins in M:
        f.write(f"\n{a}  {h(a) if os.path.exists(a) else 'MISSING'}\n  cmd: {c}\n")
        for i in ins: f.write(f"  in : {i}  {h(i) if os.path.exists(i) else 'MISSING'}\n")
print(open('MANIFEST.txt').read().count('MISSING'),'missing')

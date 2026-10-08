#!/usr/bin/env python3
"""test_run_release.py -- negative and positive tests of ../run_release.sh with a mock `lake` and a mock checker,
each in its own copy of the lean/ folder with an isolated HOME and a minimal PATH (no real Lean is run).

  python3 test_run_release.py <work dir (new or empty)>

Writes <work>/RESULTS.tsv and <work>/RESULTS.json; last line RUN_RELEASE_TESTS=PASS n/n (exit 0) or FAIL (exit 1).
Nothing is deleted; every case keeps its copy and logs under <work>/<case>/."""
import json, os, shutil, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode = True
LEAN = Path(__file__).resolve().parents[1]

MOCK_LAKE = r'''#!/bin/bash
# mock lake for tests: behaviour from MOCK_* variables
case "$1" in
  --version) echo "Lake version MOCK"; exit 0;;
  build)
    [ -n "${MOCK_TOUCH:-}" ] && printf '\n-- touched\n' >> "$MOCK_TOUCH"
    [ "${MOCK_BUILD_SORRY:-0}" = "1" ] && echo "warning: ResidueAPN/X.lean:1:0: declaration uses 'sorry'"
    echo "Build completed successfully (mock)."; exit "${MOCK_BUILD_EXIT:-0}";;
  exe) echo "mock cache get"; exit "${MOCK_FETCH_EXIT:-0}";;
  env)
    shift
    if [ "$1" = "lean" ]; then
      f="$2"; mode="${MOCK_AUDIT_MODE:-good}"
      case "$f" in *AuditAxiomsAll.lean)
        grep -v '^#' "$MOCK_FINALS" | while IFS= read -r d; do
          [ -z "$d" ] && continue
          if [ "$mode" = "missingname" ] && [ "$d" = "ResidueAPN.propW" ]; then continue; fi
          if [ "$mode" = "subset" ]; then echo "'$d' depends on axioms: [propext]";
          elif [ "$mode" = "noaxiom" ]; then echo "'$d' does not depend on any axioms";
          elif [ "$mode" = "badaxiom" ] && [ "$d" = "ResidueAPN.theorem_3_1" ]; then echo "'$d' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]";
          elif [ "$mode" = "sorry" ] && [ "$d" = "ResidueAPN.theorem_3_1" ]; then echo "'$d' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]";
          else echo "'$d' depends on axioms: [propext, Classical.choice, Quot.sound]"; fi
        done;;
      *) echo "'x_restated' depends on axioms: [propext, Classical.choice, Quot.sound]";;
      esac
      exit "${MOCK_AUDIT_EXIT:-0}"
    fi
    exec "$@";;
esac
echo "mock lake: unexpected $*" >&2; exit 99
'''
MOCK_CHECKER = '#!/bin/bash\necho "mock lean4checker $*"\nexit "${MOCK_CHECKER_EXIT:-0}"\n'

# name, env, setup, expected exit (None = any nonzero), expected failing stage (None for PASS)
CASES = [
    ('pos_all_pass', {}, None, 0, None),
    ('pos_axiom_subset', {'MOCK_AUDIT_MODE': 'subset'}, None, 0, None),
    ('pos_no_axioms', {'MOCK_AUDIT_MODE': 'noaxiom'}, None, 0, None),
    ('neg_build_exit23', {'MOCK_BUILD_EXIT': '23'}, None, 23, 'build'),
    ('neg_build_sorry', {'MOCK_BUILD_SORRY': '1'}, None, 6, 'build'),
    ('neg_audit_exit7', {'MOCK_AUDIT_EXIT': '7'}, None, 7, 'audit_AuditStage1'),
    ('neg_audit_sorryAx', {'MOCK_AUDIT_MODE': 'sorry'}, None, 6, 'axioms'),
    ('neg_axiom_not_allowed', {'MOCK_AUDIT_MODE': 'badaxiom'}, None, 6, 'axioms'),
    ('neg_final_name_missing', {'MOCK_AUDIT_MODE': 'missingname'}, None, 6, 'axioms'),
    ('neg_checker_exit1', {'MOCK_CHECKER_EXIT': '1'}, None, 1, 'checker'),
    ('neg_cache_get_exit5', {'MOCK_FETCH_EXIT': '5', '_ARGS': '--cache-get'}, None, 5, 'fetch'),
    ('neg_no_lake', {'_NOLAKE': '1'}, None, 127, 'inputs'),
    ('neg_no_checker', {'_NOCHECKER': '1'}, None, 127, 'inputs'),
    ('neg_source_modified', {}, 'modify_source', 5, 'src_before'),
    ('neg_source_changed_during_run', {'MOCK_TOUCH': 'ResidueAPN/Basic.lean'}, None, 5, 'src_after'),
    ('neg_toolchain_changed', {}, 'change_toolchain', 5, 'config'),
    ('neg_path_dependency', {}, 'path_dep', 5, 'config'),
    ('neg_mathlib_rev_changed', {}, 'mathlib_rev', 5, 'config'),
    ('neg_audit_file_missing', {}, 'missing_audit', 3, 'inputs'),
    ('neg_checker_rev_unpinned', {'_ARGS': '--checker-rev-check'}, None, 5, 'config'),
    ('neg_logs_not_empty', {}, 'logs_not_empty', 2, None),
]

def setup(case_dir, kind):
    proj = case_dir / 'lean/residue_apn_portable'
    if kind == 'modify_source':
        with open(proj / 'ResidueAPN/Ring.lean', 'a', encoding='utf-8') as f: f.write('\n-- modified\n')
    elif kind == 'change_toolchain':
        (proj / 'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    elif kind == 'path_dep':
        t = (proj / 'lake-manifest.json').read_text()
        (proj / 'lake-manifest.json').write_text(t.replace('"type": "git"', '"type": "path"', 1))
    elif kind == 'mathlib_rev':
        for n in ('lakefile.toml', 'lake-manifest.json'):
            t = (proj / n).read_text(); (proj / n).write_text(t.replace('d568c8c09630de097a046763c17b9ea99f95f950', 'e' * 40))
    elif kind == 'missing_audit':
        (proj / 'audit/AuditStage2.lean').rename(proj / 'audit/AuditStage2.lean.moved_by_test')
    elif kind == 'logs_not_empty':
        (case_dir / 'logs').mkdir(); (case_dir / 'logs/PASS.json').write_text('{"result": "PASS", "stale": true}\n')

def main():
    work = Path(sys.argv[1]).resolve()
    if work.exists() and any(work.iterdir()): print('work dir not empty'); sys.exit(2)
    work.mkdir(parents=True, exist_ok=True)
    rows, ok = [], 0
    for name, env_add, kind, exp_exit, exp_stage in CASES:
        cd = work / name
        (cd / 'lean').mkdir(parents=True)
        for f in ('run_release.sh', 'PINS.json', 'FINAL_DECLARATIONS.txt'): shutil.copy2(LEAN / f, cd / 'lean' / f)
        shutil.copytree(LEAN / 'residue_apn_portable', cd / 'lean/residue_apn_portable',
                        ignore=shutil.ignore_patterns('.lake', '*.bak_pre_*'))
        home = cd / 'home'; mb = home / 'mockbin'; mb.mkdir(parents=True)
        if not env_add.get('_NOLAKE'):
            (mb / 'lake').write_text(MOCK_LAKE); (mb / 'lake').chmod(0o755)
        ck = home / 'checker/lean4checker'; ck.parent.mkdir()
        if not env_add.get('_NOCHECKER'):
            ck.write_text(MOCK_CHECKER); ck.chmod(0o755)
        setup(cd, kind)
        env = {'HOME': str(home), 'PATH': '%s:/usr/bin:/bin' % mb, 'LC_ALL': 'C',
               'MOCK_FINALS': str(cd / 'lean/FINAL_DECLARATIONS.txt')}
        env.update({k: v for k, v in env_add.items() if not k.startswith('_')})
        if 'MOCK_TOUCH' in env: env['MOCK_TOUCH'] = str(cd / 'lean/residue_apn_portable' / env['MOCK_TOUCH'])
        cmd = ['/bin/bash', str(cd / 'lean/run_release.sh'), '--checker', str(ck), '--logs', str(cd / 'logs')]
        cmd += env_add.get('_ARGS', '').split()
        p = subprocess.run(cmd, cwd=cd, env=env, capture_output=True, text=True)
        logs = cd / 'logs'
        has_pass = (logs / 'PASS.json').is_file() and '"stale"' not in (logs / 'PASS.json').read_text()
        stale_kept = kind != 'logs_not_empty' or '"stale"' in (logs / 'PASS.json').read_text()
        stage = None
        if (logs / 'FAIL.json').is_file(): stage = json.loads((logs / 'FAIL.json').read_text())['stage']
        if exp_exit == 0:
            good = p.returncode == 0 and has_pass and stage is None
        else:
            good = p.returncode == exp_exit and not has_pass and (exp_stage is None or stage == exp_stage) and stale_kept
        ok += good
        rows.append({'case': name, 'exit': p.returncode, 'expected_exit': exp_exit, 'fail_stage': stage,
                     'expected_stage': exp_stage, 'PASS.json': has_pass, 'result': 'ok' if good else 'WRONG',
                     'stderr_tail': p.stderr.strip().splitlines()[-1:] })
    (work / 'RESULTS.json').write_text(json.dumps(rows, indent=1) + '\n')
    with open(work / 'RESULTS.tsv', 'w') as f:
        f.write('case\texit\texpected_exit\tfail_stage\texpected_stage\tPASS.json\tresult\n')
        for r in rows:
            f.write('%s\t%s\t%s\t%s\t%s\t%s\t%s\n' % (r['case'], r['exit'], r['expected_exit'], r['fail_stage'],
                                                      r['expected_stage'], r['PASS.json'], r['result']))
    print(open(work / 'RESULTS.tsv').read())
    print('RUN_RELEASE_TESTS=%s %d/%d' % ('PASS' if ok == len(CASES) else 'FAIL', ok, len(CASES)))
    sys.exit(0 if ok == len(CASES) else 1)

if __name__ == '__main__':
    main()

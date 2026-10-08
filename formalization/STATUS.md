# STATUS — Lean formalization of paper_R5 (ResidueAPN), 2026-10-07 16:0x

Machine: studio `~/lean/residue_apn` (toolchain v4.31.0-rc1; Mathlib d568c8c0 via path `../mathlib-latest`). Authoring copy: `papers/lean/residue_apn/` (`sync_to_studio.sh`).
Statuses are counted separately: **closed in the working tree** (lake build 0 errors, 0 sorry) · **audited** (restated types + axioms, `lake env lean audit/*.lean`) · **lean4checker --fresh** (one module per run) · **fresh/portable build elsewhere** · **in the vault**.

| part (handoff §3) | paper | modules | closed | audited | lean4checker | portable | vault |
|---|---|---|---|---|---|---|---|
| 1 definitions | §2, Def. 2.1 | Shared/*, Basic | yes (b19) | yes (stage 1) | yes (stage 2) | no | no |
| 2 Lemma 2.2 | lem:O | — | not started (needs a normal basis; not used by the formal Thm 3.1) | | | | |
| 3 Theorem 3.1 | thm:A | Family, ThmA, Support, ThmAImage, TheoremA | yes | yes (`theorem_3_1_restated`) | yes (stage 2) | no | no |
| 4 Prop. 5.1 identity | prop:C | Family, TheoremA | yes | yes (`proposition_5_1_restated`) | yes (stage 2) | no | no |
| 5 Lemma 3.2, Cor. 3.3 | lem:LW, cor:P | — | not started | | | | |
| 6 Prop. 7.1 | prop:W | PropW | yes | yes | yes (stage 2) | no | no |
| 7 Thm 4.1 core | thm:B | ThmB | yes | yes (`thmB_core_restated`, `thmB_roots_restated`) | yes (stage 2) | no | no |
| 8 Prop. 6.1, Thm 6.2 | prop:lift, thm:R | Ring, TheoremR | yes (abstract finite local ring) | yes | yes (stage 2) | no | no |

Records (studio `logs/`): builds b00–b19 (b19 = final: EXIT=0, 0 errors, 0 `declaration uses 'sorry'`); `audit_stage1.log`, `audit_stage1_rerun.log`, `audit_stage2.log` (every final statement: [propext, Classical.choice, Quot.sound]); `l4c_stage1b/` (TheoremA, aborted by Claude after ~13 min CPU, superseded); `l4c_stage2_failed_prefix_match/` (`--fresh ResidueAPN` matched 14 modules — tool refuses; not a check failure); `l4c_stage2/` (`--fresh ResidueAPN.All`, source digest dad9c6b2…1891): **exit 0, 799 s** (studio, 2026-10-07 16:1x); copy in `papers/lean/residue_apn/logs_copy/`.

Notes
- `ResidueAPN/All.lean` exists only so that one leaf module imports everything (lean4checker `--fresh` needs a single module).
- `lake env lean` was used only for audits and scratch compiles; sorry detection is from the `lake build` log.
- The trust labels and the statement ↔ declaration map: `leanmap.json` → `STATEMENT_MAP.md`, blueprint.

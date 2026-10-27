# LEAN_SCOPE — 紙の主張 → Lean → 紙のみの部分 → 独立実行（R06 正本、2026-10-26）

**この節の表だけが現行の範囲を示す。** R03〜R05c の記述は末尾の「履歴」に移した（上書き規則を読む必要はない）。

- 対象：`lean/`（57 ファイル＝55 モジュール＋ルート `Apn2R03.lean`＋`Audit.lean`、11,599 行。Lean 4.31.0-rc1、Mathlib d568c8c）。
- Studio でクリーンビルド 8549 ジョブ（BUILD_EXIT 0、警告 0）。`Audit.lean` の **150 宣言**すべてが標準 3 公理（propext、Classical.choice、Quot.sound）のみ、sorryAx 0。ルートと全 55 モジュールの `leanchecker` 再検査 EXIT 0。
- ログ：`r06_lean/build_clean_r06.log`、`audit_r06.log`、`SOURCES_SHA256_r06.txt`（57 ファイル）。
- **これは著者側の kernel 実行である。** 第三者のマシンでの独立再ビルドとは区別する。
- 機械可読版は `LEAN_SCOPE.csv`（R06 の行を追加済み）。

| 本文の主張 | Lean 宣言（標準 3 公理のみ） | 紙のみの部分 | 独立実行・計算機照合 |
|---|---|---|---|
| Thm A（一項補正 F♯、P_{m,r}） | `fam3_units'`、`fam5_units'`、`thmA3_GR(_units)`、`thmA5_GR(_units)`、`fam3_lower_all`、`fam5_lower_all`、`fam3_spectrum`、`fam5_spectrum`、`natDegree_Fsh3`、`natDegree_Fsh5`、`fam3_natural_exact`、`fam5_natural_q2`、`fam5_nat_k3`、`fam5_nat_k3_spectrum` | 演算量（項別評価モデル）、どの単項式が現れるか | validate_v3（m=5 全行、m=7 の P73・P75 全 16384 行）、Magma 64 方向 |
| Thm B（minimax） | `minimax_k3_attain`、`minimax_k4_attain`、`minimax_k4_lower`、`lower_q2`、`lower_2q_k4` | — | validate_v3（m=5、32 記録＝27 MATCH＋5 BOUND） |
| Thm C（全 minimizer） | `minimizers_k3`、`minimizers_k4` | — | 同上 |
| Thm D（スペクトル、mod 8） | `spectrum_mu0`、`spectrum_mu`、`spectrum_k3`、`delta_stable_mod8`、`delta_stable_mod8_GR` | — | validate_v3、e_tests |
| Cor E・Thm CL・Cor CL2（level 間） | `cross_level_stay`、`cross_level_exists`、`*_GR`、`coherent_family`、`coherent_family_GR`、`towerGR` | — | tests/test_cross_level.py |
| Thm F（penultimate、k=3 中間層、両立不能） | `penultimate`、`middle_k3`、`O3_iff`、`tradeoff` | — | layers/ |
| Thm inter (i)–(iii)、Cor interfamily | `inter_dvd`、`inter_upper`、`inter_row`、`inter_count`、`inter_mult`、`inter_flat_iff`、`inter_layer_iff`、`fam5_interfamily`、`fam5_nat_inter` | Prop. GR（桁再帰）と残りの配置の分類 | layers/r05c（133 配置、75 全行、旧 691 行） |
| Prop. valuation | `unit_diff`、`nonunit_diff` | — | — |
| Prop. markov、Cor G (a) | `trail_card`、`trail_prob`、`round_diff`、`char_prob_le`、`char_prob_le_fam3'`、`char_prob_le_fam5'` | — | tests/test_markov_two_words.py、test_crypto_c3.py |
| Prop. layerchar、Cor G (b) | `char_prob_le_digit`、`char_prob_le_layer`、`top_layer_le`、`char_prob_le_fam5_layer`、`char_prob_le_top` | — | — |
| Prop. hull、Cor G (c) 前半 | `hull2_le`、`card_out2`、`diff2_prob_le`、`branch_lift`、`fam5_dp_le`、`fam5_bij`、`fam5_diff2` | N ≥ 2 ラウンドへの拡張、一般の lift で η = 2/q | tests/test_hull_toy.py |
| **Prop. hullunit（R06：層 s ごと、2^n なし）**、Cor G (c) 後半 | **`hull2_digit`、`diff2_digit`、`diff2_layer`、`fam5_diff2_unit_sharp`（s=0、D_0=2q）、`fam5_diff2_mid`（1 ≤ s ≤ k−2、D_s=q^{s+1}）、`diff2_top`（頂層、p′ が 2 対 1 の任意の lift）**。旧版（2^n 付き）の `hull_core`、`hull2_unit`、`diff2_unit_le`、`fam5_diff2_unit` も残す | N ≥ 2 ラウンドへの拡張 | **tests/test_hull_layer.py（GR(4,2)、2 語、B=3、32 置換、全入力×全出力、整数計算）**；GPT の independent_layer_hull.py |
| Prop. fixedkey、Cor G (d) | `fixed_key_markov`、`fixed_key_le`、`fam5_fixed_key`、`fam5_fixed_key_unit`、**`fixed_key_layer`** | — | — |
| Prop. congpart | `poly_cong`、`round_cong`、`iter_cong` | ランダム置換との確率比較 | — |
| Prop. resAPN、剰余の置換性 | `resAPN3`、`resAPN5`、`resPerm3`、`resPerm5`、`cube_inj` | — | — |
| Cor natural | `fam5_nat_k3`、`fam5_nat_k3_spectrum`、`A5n_zero`、`fam5_nat_E0`、`cc_A0_mu0_k3` | — | P75 全行、P95・P97 標本 |
| 補題 A・E、制御、(H) ⇒ Hyp | `A_spec`、`E_spec`、`E_transl`、`A_prescribe`、`E_prescribe`、`hyp_of_H` | — | — |
| GR の実在 | `grs`、`grs_card`、`exists_GR_poly` | — | — |
| Thm repfamily | `Ad_inj`、`Ad_rho`、`cubeAd_inj`、`Kd_zero_iff`、`eps_not_im`、`Lam_ne_zero` | p_d の係数公式、Kloosterman による個数 | tests/test_rep_family.py、rep_family/ |
| Thm sparse | `sq_add_add_one_ne`、`sparse_Lam_ne`（Λ の非零） | p_c の係数公式、存在証明（Bézout と Aubry–Perret） | **cert/sparse_cert_r06.py（R06、他のコードを使わずに新規作成：t^17+t^3+1 の既約性、F_{2^17} 上 125769 点、m ≤ 13 の個数を 2 方法で）**、rep_sparse/（replay_full F7）、GPT の independent_new_fields.py |
| Prop. lowcost | P_{m,r} の場合 `fam5'_A`、`fam5'_A_eq_sharp`、`fam5'_upper` | 一般の p、係数変更 lift の層の最適性、演算量 | rep_sparse/ |
| 有限計算 | なし | — | replay_core（stage 0–9）、replay_full（F1–F7）、Magma ログ |

---

## 履歴（R03〜R05c。参照用で、現行の範囲は上の表）

### R05〜R05c の記述（当時の正本）

**R05（2026-10-25）での状態（この節が正本。以下の R04・R04b の記述は経緯）**：40 ファイル（38 モジュール＋ルート＋Audit）、7647 行。Studio でクリーンビルド 8532 ジョブ（BUILD_EXIT 0）、監査 92 宣言すべて標準 3 公理のみ（sorryAx 0）、ルートと全 38 モジュールの `leanchecker` 再検査 EXIT 0。ビルドログの警告は 7 件（未使用変数など、エラーではない）。ログは `r06_lean/build_clean_r05.log`・`audit_r05.log`・`SOURCES_SHA256_r05.txt`、詳細は LEAN_REPORT_R05.md。
- 主定理の番号：Theorem A（一項補正）、B（minimax）、C（全 minimizer）、D（スペクトルと mod 8）、**Corollary E（level 間）**、**Theorem F（層）**、**Corollary G（遷移確率と characteristic）**。R04 の表の「Theorem E（層）」は Theorem F に改めた。
- **形式化した文と紙の系を区別する**：`cross_level_exists`（`_GR`）は固定した 1 組の level (k, 3) の文。紙の系 CL2（全 level で同時に最適な互換族）は、抽象的な塔の上の `coherent_family` で形式化した。GR の具体的な塔への instantiation は未形式化。
- 自然 lift：r = 3 は全 level で = 4q（`fam3_natural_exact`）。r ≥ 5 は全 level で全例外行に ≥ q²（`fam5_natural_q2`）、k = 3 で最大値 q²（r ≡ 1 mod 4）・2q²（r ≡ 3 mod 4）（`fam5_nat_k3`）。Cor. natural の個数は紙のみ。
- Markov 積公式は**有限可換加法群**上の文（任意の有限群ではない）。
- 剰余分割（Prop. congpart）の構造部分を形式化（`iter_cong`）。ランダム置換との確率比較は紙。
- 未形式化：演算量（乗算 1 回）、台の記帳、有限計算、Prop. congpart の確率比較、GR の具体的な塔。

- **R05b 追記**：43 ファイル、8535 ジョブ、監査 104 宣言（標準 3 公理のみ）、leanchecker EXIT 0、**警告 0**。Cor. 7.5 は個数まで形式化（`fam5_nat_k3_spectrum`）。系 CL2 は GR の具体的な塔の上で全 level まで形式化（`towerGR`、`coherent_family_GR`）し、R05 の「未 instantiation」は解消した。§10 の新定理 repfamily（μ = 0・Z = ∅ の代表の全奇数 m での存在）は、体レベルの核（A_d の単射性、ρ = d⁻⁴、ker K、ε ∉ Im K、Λ ≠ 0）を RepFamily で Lean 化した。p_d の係数公式と個数の評価は紙と計算機照合。

- **R05c 追記（2026-10-26）**：56 ファイル（54 モジュール＋ルート＋Audit）、クリーンビルド 8548 ジョブ（BUILD_EXIT 0、警告 0）、監査 143 宣言（標準 3 公理のみ、sorryAx 0）。新規 13 モジュールで、Theorem inter の (i)–(iii)（多重度を含む）と Cor. interfamily（F♯ と自然 lift）、全層の characteristic（Prop. layerchar）、2 ラウンド差分（Prop. hull・hullunit）、固定鍵（Prop. fixedkey）、P_{m,r} の係数変更 lift（Prop. lowcost の特別な場合）、疎な族の Λ ≠ 0 を形式化した。紙のまま：Prop. GR と中間層 3 小場合の分類、N ≥ 2 ラウンドへの拡張、一般の lift での η = 2/q、Thm sparse の係数公式と存在証明、Prop. lowcost の一般形。詳細は LEAN_REPORT_R05c.md と CLAIM_MAP_R05c.md。

---


2026-10-25、Claude。機械可読版は `LEAN_SCOPE.csv`。対象は `lean/`（R04、30 モジュール＋ルート＋Audit、6231 行）。
Studio でクリーンビルド成功（`lake build Apn2R03`、8524 ジョブ、約 95 秒）。`lake env lean Audit.lean` で監査した 59 宣言は、すべて標準 3 公理（propext、Classical.choice、Quot.sound）だけに依存する。コメントを除いた静的走査で、sorry、admit、追加 axiom、native_decide、unsafe、implemented_by は 0 件。ログは `r06_lean/build_clean_r04.log`、`r06_lean/audit_r04.log`、署名対象のハッシュは `r06_lean/SOURCES_SHA256_r04.txt`（35 ファイル。lakefile、manifest、toolchain を含む）。
**R04b 追記**：返却後に StabilityLit・Markov・Degree・CryptoCor・ResPerm を追加し、クリーンビルド（8529 ジョブ）、監査 82 宣言（標準 3 公理のみ）、全 36 モジュールの `leanchecker` 再検査（EXIT 0）を行った。詳細は LEAN_REPORT_R04b.md。下表の該当行は R04b の状態に更新した。
**この報告は著者側の kernel 実行である。** 独立した再ビルド（第三者のマシンでの kernel 再実行）とは区別して数える。

## 0. 読み方
- 「抽象」：公理系 `GRS R K`（π : R → K 全射、ker π = 2R、2^k = 0、2-torsion = 2^{k−1}R）の上の定理。`grs` により、GR(2^k, m) = (ℤ/2^k)[X]/(f) がこの公理系を満たすことも証明済み（`grs`、`grs_card`、`exists_GR_poly`）。
- 「GR」：具体的な環 AdjoinRoot f の上で述べた定理。
- `delta f α β` は有限解集合の実際の濃度である。結論を仮定に置いた形式化ではない。
- **MainGR / MainGR2 の定理を「Theorem A 全文の形式化」とは呼ばない。** §2 の対応表のとおり、Theorem A の主張のうち上界、下界、スペクトル、全単元、自然 lift の非最適性は Lean 化した。次数は R04b で Lean 化した（`natDegree_Fsh3`、`natDegree_Fsh5`）。台と評価コストは Lean 化していない。

## 1. R04 での変更
| 項目 | R03 | R04 |
|---|---|---|
| 剰余 P_{m,r} の APN 性 | 仮定 `hAPN : ResAPN …`（方向 c ∉ {0,1}） | **証明**（`resAPN3`、`resAPN5`、ResAPN.lean）。全単元の Theorem A は仮定なし（`fam3_units'`、`fam5_units'`、GR 上の `thmA3_GR_units`、`thmA5_GR_units`） |
| APN 性の出典記述 | 「x^{2^r+1} との線形同値」（誤り） | P_{m,r} = σ^{m−2} ∘ X³ ∘ T_r（旧第 2 弾 Thm 3.1）。内側の冪は cube で、r は T_r の添字である。Ordinary.lean 冒頭と EXPLICIT_IDENTITIES_PROOF を訂正 |
| level 間の最適性 | なし（紙の誤文 B1 は未認証） | **証明**：`cross_level_stay`、`cross_level_exists`（抽象、Compat 付き）、GR(2^k,m) → GR(8,m) で `cross_level_stay_GR`、`cross_level_exists_GR` |
| lakefile / manifest | URL（`.git` の有無）とルート名（apnlift / apn2r03）が不一致で out-of-date 警告 | rev d568c8c は動かさず、URL とルート名を同期。ビルドログに警告なし |

ResAPN の証明の筋：Y(x) = Σ_{i<r−2} x^{2^i} + x^{2^{m−2}} + x^{2^{m−1}}（F_q 上で T_r(x)^{2^{m−2}} に等しい）とおき、次を示した。
1. 評価等式 P_{m,r}(x) = Y(x)³（`p3_cube`、`p5_cube`）。
2. Y は加法的（`Y3_add`、`Y5_add`）。
3. Y⁴ = T_r と T_r + T_r² = x + x^{2^r}、さらに gcd(r, m) = 1 と r 奇数から、Y の核は自明（`S_inj`、`Y3_inj`、`Y5_inj`）。
4. 加法的で単射な Y について Y³ はすべての非零方向で APN（`resAPN_of_cube`）。
これは旧稿の経路（cube の APN 性、T_r の可逆性、出力の Frobenius）を、σ^{m−2} を Y の側へ吸収した形で実装したものである。

## 2. 対応表（要約。全行は CSV）

| 紙 | Lean 宣言 | 結論の形 | 追加仮定（GRS 公理と有限性以外） | 範囲外 |
|---|---|---|---|---|
| 補題 F2（A_F の well-definedness） | `A_spec` | 代表によらない | Hyp.hper | — |
| 補題 E2（E_F の well-definedness） | `E_spec` | 代表によらない | Λ(a) = 0 | — |
| E3 平行移動恒等式 | `E_transl` | 等式 | — | — |
| F3/E6（A・E の制御） | `A_prescribe`、`E_prescribe` | 存在 | — | — |
| (H) ⇒ Hyp | `hyp_of_H` | Hyp と導関数の 2 対 1 | 二次台、ker、ρ 方向 APN | — |
| 定理 M1/B 下界（k ≥ 4） | `minimax_k4_lower`、`lower_q2`、`lower_2q_k4` | ∃β で ≥ vmin、≥ q²、≥ 2q | Hyp | — |
| 定理 B（k = 3、k ≥ 4）達成 | `minimax_k3_attain`、`minimax_k4_attain` | 同じ剰余の lift が存在 | Hyp | — |
| 定理 C（全 minimizer） | `minimizers_k3`、`minimizers_k4` | ⟺ | Hyp、q > 2 | — |
| **系 E = CL・CL2（1 組の level、R04）** | `cross_level_stay`、`cross_level_exists`、`*_GR` | ⟺ | Hyp、Compat（GR では構成済み） | 固定した k ≥ 4 と level 3 の組だけ |
| **系 CL2（全 level の互換族、R05）** | `coherent_family`（`Tower`） | ∃F ∀level 最適 ⟺ μ = 0 ∨ Z ≠ ∅ | 塔のデータ（φ_j、level 3 との可換性、φ_0 全射） | GR の具体的な塔は未 instantiation |
| 定理 D(1) スペクトル | `spectrum_mu0`、`spectrum_mu` | 個数式 | Hyp、A 非消失 | — |
| 定理 D(2)（k = 3、A 任意） | `spectrum_k3` | 個数式 | Hyp、μ ≠ 0、k = 3 | — |
| S3 の字義形（異なる環の間の DDT 等式 δ_{F} = δ_{F mod 8}） | `delta_stable_mod8`、`delta_stable_mod8_GR`（R04b） | 等式 | Hyp、A 非消失、Compat（GR では構成済み） | μ 任意、互換な任意の 2 level |
| 定理 F（penultimate、中間層、両立不能） | `penultimate`、`middle_k3`、`O3_iff`、`tradeoff` | 等式・⟺ | Hyp、導関数の 2 対 1 | — |
| Theorem A 上界（例外方向 2q） | `fam3_upper`、`fam5_upper`、`thmA3_GR`、`thmA5_GR` | ≤ 2q | 族の条件 | — |
| Theorem A 全単元（R04） | `fam3_units'`、`fam5_units'`、`thmA3_GR_units`、`thmA5_GR_units` | ≤ 2q、通常方向 ≤ 2 | 族の条件のみ | — |
| Theorem A 全 lift の下界 | `fam3_lower_all`、`fam5_lower_all` | ∃β で ≥ 2q | 族の条件 | — |
| Theorem A スペクトル | `fam3_spectrum`、`fam5_spectrum` | 個数式 | 族の条件 | — |
| 自然 lift の比較値（R05） | `fam3_natural_exact`（全 level、全例外行の最大 = 4q）、`fam5_natural_q2`（全 level、全例外行に ≥ q²） | 等号・不等式 | 族の条件 | R04b の弱い形（≥ 4q、> 2q）を解消 |
| Cor. natural（k = 3、r ≥ 5、R05） | `fam5_nat_k3`、`A5n_zero`、`fam5_nat_E0`、`cc_A0_mu0_k3` | 最大値 = q²（r ≡ 1 mod 4）、= 2q²（r ≡ 3 mod 4） | 族の条件、k = 3 | 個数 n_{2q}・n_{q²}・n_{2q²} は紙（P75 全行、P95・P97 標本で照合） |
| 次数 3q/4 不変 | `natDegree_Fnat3`、`natDegree_Fsh3`、`natDegree_F5`、`natDegree_Fsh5`（R04b） | = 2^{m−2}+2^{m−1} | m ≥ 5（r ≥ 5 は 5 ≤ r < m）、R 自明でない | — |
| 乗算 +1、台の記帳 | なし | — | — | **未形式化**（紙の初等計算） |
| C1（遷移確率） | Theorem A の系（割り算のみ） | — | — | 割り算は紙 |
| C2 付値保存 | `unit_diff`、`nonunit_diff` | 単数→単数、α·単数 | 剰余置換、p′ 非消失 | — |
| C3'（Markov 積公式） | `trail_card`、`trail_prob`、`round_diff`（R04b） | 個数・確率の等式 | **有限可換加法群** G、任意の S、加法自己同型 M | 非可換群では述べていない |
| Prop. congpart（剰余分割、R05） | `poly_cong`、`round_cong`、`iter_cong` | 法 2 の合同を全ラウンドで保つ | 任意の可換環、多項式 S-box、加法的な層、任意の鍵、初期 whitening | ランダム置換との確率比較は紙 |
| C3''（branch number 上界、系全体） | `char_prob_le`（R04b）、F♯ 版 `char_prob_le_fam3'`・`char_prob_le_fam5'`（D = 2q、追加仮定なし） | 確率 ≤ (D/|R|)^{B⌊N/2⌋} | 単数行 ≤ D、剰余置換、π∘M = M̄∘π、M̄ の branch number B、入力差分に単数成分 | 部品：`dd_pi`、`sum_active_ge`、`prod_le_pow_of_active`、`unit_diff` |
| 剰余 P_{m,r} の置換性 | `resPerm3`、`resPerm5`、`cube_inj`（R04b） | 単射 | m 奇数、gcd 条件 | — |
| 有限計算（行の全数計数、代表の探索、Magma） | なし | — | — | 計算機検証（replay、Magma ログ） |

## 3. 仮定の地位
- GRS の 4 公理と |R| = q^k は GR(2^k, m) で証明済みで、GR 上の定理では仮定ではない。
- `Hyp f ρ μ`（ρ ≠ 0、p′ の ρ-周期性、Hasse 第 2 導関数の差 = μ、p(a+ρ) − p(a) の 2 対 1）は (H) から `hyp_of_H` で導ける。明示族では `fam3_hyp`、`fam5_hyp` で証明済み。
- 族の条件：m ≥ 5、gcd(3, m) = 1（r = 3）、または 5 ≤ r < m、r 奇数、m 奇数、gcd(r, m) = 1。
- `Compat`：同じ剰余体をもつ level k と level 3 の構造を、剰余写像と可換な環準同型 ψ でつなぐもの。GR では係数還元 ψ : GR(2^k, m) → GR(8, m) と、剰余体の同一視（`AdjoinRoot.algEquivOfEq`）で構成済み（`compatGR`）。

## 4. 紙の誤文（B1）と Lean の関係
R03 の紙の文「法 8 で値を達成する lift は全 level で達成する」は Lean で証明されておらず、偽である（CROSS_LEVEL.md §5 の反例）。R04 で正しい形（定理 CL、系 CL2）を Lean で証明した。紙の本文もこの形に置き換えた。

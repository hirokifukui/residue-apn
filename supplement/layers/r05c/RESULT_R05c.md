# R05c (research note; named R06 during the work) — the three open sub-cases of the intermediate-layer classification

Setting and notation as in `apn2_full.tex` (§ "The lower layers", Theorem `thm:inter`) and `RESULT_R05b.md`
(Theorems A–E, Prop. 5). Everything below is new unless attributed to R05b.

---------------------------------------------------------------------------------------------------

## 0. Summary

| sub-case (R05b §7) | status | form of the answer |
|---|---|---|
| (1) merged DEG+DEG ($\mu=0\ne c_3$, $A_F(a)=0=w_\alpha(a)$), $d\ge3$ | **proved** | Theorem I: a closed level formula, iterated only along the *resonant chain* (at most $\lfloor (d-1)/2\rfloor$ levels); explicit multiset in terms of the chain data; exact maximum; universal bounds $m_{\rm deg}(d)\le\max\le 2m_{\rm deg}(d)$, both attained |
| (2) merged DEEP+DEEP ($\mu=0=c_3$, $A_F(a)=0=\pi(a)$), $d\ge2$ | **proved**, closed form in every configuration except two that need $\ge5$ independent $\mathbb F_q$-conditions on Taylor data (§9), where the answer is the output of the proved recursion GR | Theorem II: split/merged dichotomy by $\bar e_P$; merged case $=q\cdot$(pair of *halves* at depth $d-1$), classified by the types of the halves |
| (3) single DEEP class with $w'_\alpha(a)=c'(a)=0$, $d\ge2$ | **proved** for $d\le3$, for all $d$ when $\lambda_1\neq0$, and for $\lambda_1=0$ except when a further zero-residue node with non-Hensel half occurs (§9) | Theorem III: $N=q^2[g\in4R]\,N_\Psi(g/4)$ with $\Psi=\Phi/4$ of residue $L(y)=\lambda_1y+\lambda_2y^2+c_5y^4$; explicit formulas for $\lambda_1,\lambda_2$; sharp lower bound $\max\ge q^{2}$ with an exact equality criterion |

In **every** case (including the residual configurations of (2),(3)) the multiset is the output of the general
digit recursion GR (Lemma GR, §2.1), which is proved for arbitrary polynomials and terminates after at most
$\lceil d/2\rceil$ levels; it needs $O(q)$ evaluations of $T$ per critical node.

Verification (§7): 133 lift/row instances of the three sub-cases ($m=5$, $d=2,\dots,5$, $k\le8$; 40 / 37 / 56 for sub-cases 1 / 2 / 3), each open-type
pair or class brute-forced exhaustively, 75 of them also as full brute-force rows; plus the 691 R05b rows re-graded.
**133/133 MATCH** for the closed forms (no fallback needed) and for GR; **75/75** full rows MATCH; **691/691** old rows MATCH. No mismatch anywhere.

The multisets are **not** functions of $(p,A_F,j,\bar u)$: different lifts with the same $p$, the same $A_F$ and the same row give different
multisets (many examples in §7). The invariants that enter are level data read off from $T$ (one block of data per two units of $d$ along the degenerate
chain). I do not prove that no fixed finite set of invariants could suffice uniformly in $d$; what is proved is the closed level formula and the exact
dependence on the level data that occur.

---------------------------------------------------------------------------------------------------

## 1. Setting and conventions

$R=R_k$, $\alpha=2^ju$ ($u$ a unit), $1\le j\le k-3$, $n=k-j$, $d=n-2\ge1$. $T=\sum_{i\ge1}\alpha^{i-1}F^{[i]}$, and for $\bar x=a$
$$\Phi_x(z)=\frac{T(x+2z)-T(x)}4=\sum_{r\ge1}2^{r-2}\,T^{[r]}(x)\,z^r\qquad(\text{coefficient of }z\text{ is }W(x)=T'(x)/2).$$
**Taylor data.** Put $f_s=F^{[s]}(x)$. Directly from the definition of $T$ and $(F^{[i]})^{[r]}=\binom{i+r}{r}F^{[i+r]}$:
$$T^{[r]}(x)=\sum_{s>r}\binom sr\alpha^{\,s-r-1}f_s .\tag{1.1}$$
$f_s\equiv p^{[s]}(a)\pmod 2$; for quadratic $p$, $p^{[s]}=0$ unless $s$ has binary weight $\le2$, $p^{[2^i]}$ is affine and
$p^{[2^i+2^l]}=c_{2^i+2^l}$ is constant (Lucas). In particular $p^{[3]}=c_3$, $p^{[5]}=c_5$, and $p^{[4]}$ is affine.
Conversely, the lift $F+\sum_s 2^t b_s(X-x)^s$ has the same residue and Taylor data $f_s+2^tb_s$ at $x$; so the data
$(f_s)_{s\ge1}$ at one point are arbitrary subject to $f_s\equiv p^{[s]}(a)$ (this is how the test lifts of §7 are built).

**Counting.** For $\Phi\in R[z]$ and $D\ge0$: $N^D_\Phi(g)=\#\{z\in R/2^D:\Phi(z)\equiv g\ (2^D)\}$, $g\in R/2^D$, and
$M^D(\Phi)$ is the multiset of these $q^D$ numbers (zeros included). By Theorem A (R05b) a class contributes the entries
$q^{j+1}N^d_{\Phi_{x_a}}(g)$; a merged pair ($B_\alpha(a)=0$, $x_b:=x_a+\tau$, $\bar\tau=\rho$) contributes
$q^{j+1}\big(N_a(g)+N_b(g+e)\big)$ with $e=e_P=(T(x_a)-T(x_b))/4$.

**Configurations.** More generally a *configuration* is a finite family of nodes $(\Phi_i,\varepsilon_i,\omega_i)$ (polynomial,
offset in $R$, weight in $\mathbb Z_{>0}$) and $N_{\mathcal C}(g)=\sum_i\omega_iN^D_{\Phi_i}(g+\varepsilon_i)$.

**Witt digits.** $[y]$ is the Teichmüller lift. Every $r\in R/4$ is uniquely $[r_0]+2[r_1]$; in $R/4$:
$[a][b]=[ab]$, $2[a]+2[b]=2[a+b]$, and $[a]+[b]=[a+b]+2[\sqrt{ab}]$ (square $[a]+[b]=[a+b]+2[t]$ and compare with
$[a^2]+[b^2]+2[ab]$).

**Universal multisets** (R05b): $S_{\rm nd}(c,D)=\{2^{(q^D/2)},0^{(q^D/2)}\}$ if $c\ne0$, $\{1^{(q^D)}\}$ if $c=0$; $S_{\rm deg}(D)$
(Prop. 5(c)); depth $0$: $\{1\}$. $m_{\rm deg}(D):=\max S_{\rm deg}(D)$: $m_{\rm deg}(0)=m_{\rm deg}(1)=1$, $m_{\rm deg}(D)=q^{D/2}$ ($D\ge2$ even),
$2q^{(D-1)/2}$ ($D\ge3$ odd). For a multiset $M$ and integers $\lambda,\beta$: $\lambda M+\beta=\{\lambda v+\beta:v\in M\}$; $k\otimes M$ is $k$ copies.

---------------------------------------------------------------------------------------------------

## 2. General tools

### 2.1 Lemma GR (digit recursion; arbitrary polynomials)

Let $\Phi\in R[z]$, $D\ge1$, $y\in\mathbb F_q$, $\hat y=[y]$.

(i) If $\Phi'(\hat y)\in R^\times$ ($y$ is a *Hensel point*), then for each $g$ with $\bar g=\bar\Phi(y)$ exactly one $z\equiv\hat y\ (2)$, $z\bmod 2^D$,
has $\Phi(z)\equiv g$.

(ii) If $\Phi'(\hat y)\in2R$ ($y$ is *critical*), then $\Phi(\hat y+2z)-\Phi(\hat y)\in4R[z]$ coefficientwise; with the *child*
$\Phi_y(z):=(\Phi(\hat y+2z)-\Phi(\hat y))/4$, for $D\ge2$
$$\#\{z\equiv\hat y\,(2):\Phi(z)\equiv g\}=q\,[g\equiv\Phi(\hat y)\ (4)]\;N^{D-2}_{\Phi_y}\!\big((g-\Phi(\hat y))/4\big),$$
and for $D=1$ the count is $[\bar g=\bar\Phi(y)]$. The class of $\Phi(\hat y)$ mod 4 does not depend on the lift $\hat y$.
The child has $z^r$-coefficient $\Phi'(\hat y)/2$ ($r=1$) and $2^{r-2}\Phi^{[r]}(\hat y)$ ($r\ge2$).

*Proof.* (i) For $z,z'\equiv\hat y$ (2): $\Phi(z)-\Phi(z')=(z-z')U$ with $U=\sum_{r\ge1}\Phi^{[r]}(z')(z-z')^{r-1}\equiv\Phi'(z')\equiv\Phi'(\hat y)$ (mod 2), a unit; so
$z\mapsto\Phi(z)$ is injective from $\hat y+2R/2^D$ ($q^{D-1}$ elements) into $\Phi(\hat y)+2R/2^D$ ($q^{D-1}$ elements), hence bijective.
(ii) $\Phi(\hat y+2z)-\Phi(\hat y)=\sum_{r\ge1}2^r\Phi^{[r]}(\hat y)z^r$; the $r=1$ term is $2\Phi'(\hat y)z\in4R$ and all others lie in $4R$.
$\Phi(\hat y+2z)\equiv g$ (mod $2^D$) iff $g\equiv\Phi(\hat y)$ (4) and $\Phi_y(z)\equiv(g-\Phi(\hat y))/4$ (mod $2^{D-2}$); the latter depends on $z$ mod $2^{D-2}$,
and $z$ runs mod $2^{D-1}$ ($q$ lifts). Lift independence: $\Phi(\hat y+2w)-\Phi(\hat y)\in4R$. $\square$

**Corollary GR (configurations).** For a configuration $\mathcal C$ at depth $D\ge2$ let $H(t)=\sum\omega_i$ over the Hensel points $(i,y)$
with $\bar\Phi_i(y)-\bar\varepsilon_i=t$, and group the critical points $(i,y)$ by the class $\kappa=\Phi_i(\hat y)-\varepsilon_i$ mod 4; the group of $\kappa$ is the
configuration $\mathcal C_\kappa=\{(\Phi_{i,y},\ (\Phi_i(\hat y)-\varepsilon_i-\tilde\kappa)/4,\ q\omega_i)\}$ ($\tilde\kappa$ a fixed representative). Then
$$M^D(\mathcal C)=\biguplus_{t\in\mathbb F_q}\Big(\{H(t)^{(q^{D-1}-n_tq^{D-2})}\}\uplus\biguplus_{\kappa\ \text{over}\ t}\big(M^{D-2}(\mathcal C_\kappa)+H(t)\big)\Big),$$
$n_t$ = number of groups over $t$; for $D=1$, $M^1(\mathcal C)=\{\sum_{(i,y):\bar\Phi_i(y)-\bar\varepsilon_i=t}\omega_i\}_t$; $M^0=\{\sum\omega_i\}$.
*Proof.* Sum Lemma GR over all $(i,y)$; targets over $t$ outside every group only receive Hensel contributions. $\square$

This recursion is exact for **every** lift and every row; it is implemented in `gr.py` and evaluates $T$ only at the points
$c+p+2^E[y]$ of critical nodes (§7).

### 2.2 Node classes and their children

For $\Phi=\sum_{r\ge1}\varphi_rz^r$ define the classes
* $\mathcal C$: $\varphi_r\in2^{r-2}R$ for $r\ge3$;
* $\mathcal A$ (admissible, R05b): $\varphi_r\in2R$ ($r\ge3$), $\varphi_r\in4R$ ($r\ge3$ odd);
* $\mathcal{SA}$ (strongly admissible): $\varphi_3\in8R$, $\varphi_r\in4R$ ($r\ge4$), $\varphi_r\in8R$ ($r\ge5$ odd).

**Lemma N.** (a) For $\Phi\in\mathcal C\cup\mathcal A$: $\bar\Phi(y)=\bar\varphi_1y+\bar\varphi_2y^2$ and $\Phi'\equiv\bar\varphi_1$ (mod 2) identically. So
$\Phi$ is Hensel everywhere iff $w:=\bar\varphi_1\ne0$, and critical everywhere iff $w=0$.
(b) Every child (Lemma GR(ii)) of every polynomial lies in $\mathcal C$, with residue $\mu_yz+c_yz^2$, $\mu_y=\overline{\Phi'(\hat y)/2}$, $c_y=\overline{\Phi^{[2]}(\hat y)}$.
(c) If $\Phi\in\mathcal A$ and $w=0$, every child is in $\mathcal{SA}$, $c_y=\bar\varphi_2=:c$ and $\mu_y=\lambda+cy$ with $\lambda=\overline{\varphi_1/2}$.
(d) If $\Phi\in\mathcal{SA}$ then $\Phi(z)\equiv\varphi_1z+\varphi_2z^2$ (mod 4); if moreover $w=0$, writing $\varphi_1\equiv2[\lambda]$, $\varphi_2\equiv[c]+2[\nu]$ (mod 4),
$$\Phi([y])\equiv[cy^2]+2[\sigma(y)]\pmod 4,\qquad \sigma(y)=\lambda y+\nu y^2 .$$
(e) (Lemma Z) If $\Phi\in\mathcal C$ has residue $\equiv0$ then $\Phi\in2R[z]$ and $N^D_\Phi(g)=q\,[\bar g=0]\,N^{D-1}_{\Phi/2}(g/2)$ ($D\ge1$).

*Proof.* (a) In $\mathcal C\cup\mathcal A$, $\varphi_r\equiv0$ for $r\ge3$ and $r\varphi_r\equiv0$ for $r\ge3$ (odd $r$: $\varphi_r\in2R$; even $r$). (b) Lemma GR(ii):
the $z^r$-coefficient $2^{r-2}\Phi^{[r]}(\hat y)$, $r\ge3$. (c) $\Phi^{[3]}(\hat y)=\sum_{r\ge3}\binom r3\varphi_r\hat y^{r-3}\in4R$ ($\binom r3$ odd forces $r$ odd, so $\varphi_r\in4R$; otherwise
$\binom r3\varphi_r\in4R$), so the $z^3$-coefficient $2\Phi^{[3]}$ is in $8R$; $z^r$, $r\ge4$: $2^{r-2}\in4R$, and $\in8R$ for odd $r\ge5$. $\Phi'(\hat y)/2=\varphi_1/2+\varphi_2\hat y+\sum_{r\ge3}\frac{r\varphi_r}2\hat y^{r-1}$ and
$r\varphi_r/2\in2R$ ($r\ge3$). $\Phi^{[2]}(\hat y)\equiv\varphi_2$. (d) $\varphi_r\in4R$ for $r\ge3$; then the Witt rules of §1. (e) the residue $\bar\varphi_1y+\bar\varphi_2y^2$ is
the zero function iff $\bar\varphi_1=\bar\varphi_2=0$ (degree $<q$), and $\varphi_r\in2R$ for $r\ge3$; then as Prop. 5(d). $\square$

The class nodes satisfy: $\Phi_x\in\mathcal{SA}$ for every class ($\varphi_3=2T^{[3]}\in8R$ since $T^{[3]}\in4R[X]$; $\varphi_r=2^{r-2}T^{[r]}$) — R05b Lemma 4.

### 2.3 Hensel configurations and one degenerate node

**Lemma T1.** If every node of $\mathcal C$ is Hensel everywhere, $N_{\mathcal C}(g)=\sum_i\omega_i\,n_i(\bar g+\bar\varepsilon_i)$ with $n_i(t)=\#\{y:\bar\Phi_i(y)=t\}$,
so $M^D(\mathcal C)=\{(\sum_i\omega_in_i(t+\bar\varepsilon_i))^{(q^{D-1})}\}_{t}$. For two nodes with residues $w_xy+c_xy^2$ ($w_x\ne0$), $\varepsilon=\varepsilon_b-\varepsilon_a$:
* $c_a=c_b=0$: $\{2^{(q^D)}\}$; exactly one $c_x=0$: $\{3^{(q^D/2)},1^{(q^D/2)}\}$;
* $c_ac_b\ne0$, $c_a/w_a^2\ne c_b/w_b^2$: $\{4^{(q^D/4)},2^{(q^D/2)},0^{(q^D/4)}\}$;
* $c_a/w_a^2=c_b/w_b^2$: $\{4^{(q^D/2)},0^{(q^D/2)}\}$ if $\mathrm{Tr}(c_b\bar\varepsilon/w_b^2)=0$, else $\{2^{(q^D)}\}$.

*Proof.* Lemma GR(i) at every point. $n_x=2\cdot1_{H_x}$ with $H_x=\{w_xy+c_xy^2\}=(w_x^2/c_x)\ker\mathrm{Tr}=\{t:\mathrm{Tr}(c_xt/w_x^2)=0\}$ when $c_x\ne0$,
and $n_x\equiv1$ when $c_x=0$. Two hyperplanes are equal iff $c_a/w_a^2=c_b/w_b^2$; distinct affine hyperplanes meet in $q/4$ points. $\square$

**Lemma T2 (one degenerate node over a Hensel background).** Let $\Phi\in\mathcal A$ with residue $cy^2$, $c\ne0$, and $N(g)=N^D_\Phi(g)+H(\bar g)$ for a
function $H:\mathbb F_q\to\mathbb Z_{\ge0}$. Put $t^*=\lambda^2/c$ ($\lambda=\overline{\varphi_1/2}$). Then $M=\{(H(t)+1)\}_t$ for $D=1$, and for $D\ge2$
$$M=\biguplus_{t}\Big(\{H(t)^{(q^{D-1}-q^{D-2})}\}\uplus\big(q\,X_t+H(t)\big)\Big),\qquad X_t=\begin{cases}S_{\rm deg}(D-2)&t=t^*,\ D\ge3\\ S_{\rm nd}(c\neq0,D-2)&\text{otherwise.}\end{cases}$$
*Proof.* Corollary GR with the single critical node; over $t$ the unique critical point is $y_t=\sqrt{t/c}$, the child is in $\mathcal{SA}$ with residue
$(\lambda+cy_t)z+cz^2$ (Lemma N(c)), degenerate iff $t=t^*$; then Prop. 5(a),(c). $\square$

For $H=2\cdot1_{A}$ with $A$ an affine hyperplane this is R05b Theorem C(iv), with $\kappa=[t^*\in A]$; for $H\equiv1$ it is $S_{\rm deg}(D)+1$ (C(2)).
$m_{T2}(D,\kappa):=\max M$ for $H=2\cdot1_A$: $3$ ($D=1$), $q+2$ ($D=2$), $2q+2$ ($D=3$), $q\,m_{\rm deg}(D-2)+2\kappa$ ($D\ge4$).

### 2.4 Theorem P (two degenerate nodes)

Let $\Phi_a,\Phi_b\in\mathcal A$ with residues $c_ay^2$, $c_by^2$ ($c_ac_b\ne0$), with $\Phi_x([y])\equiv[c_xy^2]+2[\sigma_x(y)]$ (mod 4) and $\sigma_x$ additive
($\mathbb F_2$-linear); let $e\in R$, $e\equiv[\bar e]+2[e_1]$ (mod 4), and $P^D=M^D$ of the configuration $N(g)=N_a(g)+N_b(g+e)$.
For $t\in\mathbb F_q$ put $y_a(t)=\sqrt{t/c_a}$, $y_b(t)=\sqrt{(t+\bar e)/c_b}$ and define the **level data**
* $C=\{t:\ \sigma_a(y_a(t))+\sigma_b(y_b(t))+\sqrt{t\bar e}+e_1=0\}$, $s=|C|$ (coincidence set);
* $W_a(t)=\lambda_a+c_ay_a(t)$, $W_b(t)=\lambda_b+c_by_b(t)$ (linear residues of the children; $\lambda_x=\overline{\varphi_{x,1}/2}$);
* $\delta'=\lambda_a/\sqrt{c_a}+\lambda_b/\sqrt{c_b}+\sqrt{\bar e}$; $t^*_a=\lambda_a^2/c_a$, $t^*_b=\lambda_b^2/c_b+\bar e$;
* for $t\in C$: the child offset $e'(t)=(\Phi_a([y_a])+e-\Phi_b([y_b]))/4$, its residue $\bar e'(t)$.

**Theorem P.** (a) $D=1$: $P^1=\{2^{(q)}\}$. $D=2$: $P^2=\{(2q)^{(s)},q^{(2(q-s))}\}$ + zeros.

(b) (*resonance*) $W_a(t)/\sqrt{c_a}+W_b(t)/\sqrt{c_b}=\delta'$ for all $t$. Hence the following are equivalent: $\delta'=0$; $t^*_a=t^*_b$; for some (equivalently every)
$t$ the two children with $W_a,W_b\neq0$ have the same image hyperplane $H_a(t)=H_b(t)$.

(c) ($C$) $C$ is empty or a coset of an $\mathbb F_2$-subspace; with $u=\sqrt t$ the defining function is affine-additive in $u$, with linear part
$\delta'u+(\nu_a/c_a+\nu_b/c_b)u^2$ when both nodes are in $\mathcal{SA}$ (so $s\in\{0,1,2,q\}$, and $s\in\{0,1,q\}$ if $\delta'=0$).

(d) (*level formula*, $D\ge3$, $D'=D-2$; nonzero parts, completed by zeros to $q^D$):
* **non-resonant** ($\delta'\ne0$): with $i_x=[t^*_x\in C]$, $s'=s-i_a-i_b$,
$$P^D=q\Big[s'\otimes\{4^{(q^{D'}/4)},2^{(q^{D'}/2)}\}\ \uplus\ (q-2-s')\otimes\{2^{(q^{D'})}\}\ \uplus X_a\uplus X_b\Big],$$
$X_a=$ Lemma T2 at depth $D'$ for the degenerate child $\Phi_{a,y_a(t^*_a)}$ over the background $H=n_{b}(\cdot+\bar e'(t^*_a))$ of the ND child $\Phi_{b,y_b(t^*_a)}$ if $i_a=1$
(this is C(iv) with $\kappa_a=[\mathrm{Tr}(c_b(t^{**}_a+\bar e'(t^*_a))/W_b(t^*_a)^2)=0]$, $t^{**}_a$ the degenerate residue of that child), and
$X_a=S_{\rm deg}(D')\uplus S_{\rm nd}(1,D')$ if $i_a=0$; $X_b$ symmetrically.
* **resonant** ($\delta'=0$, $t^*:=t^*_a=t^*_b$): with $i=[t^*\in C]$ and $r=\#\{t\in C\setminus\{t^*\}:\chi(t)=0\}$, $\chi(t)=\mathrm{Tr}\big(c_a\bar e'(t)/W_a(t)^2\big)$,
$$P^D=q\Big[r\otimes\{4^{(q^{D'}/2)}\}\ \uplus\ (q-1-r)\otimes\{2^{(q^{D'})}\}\ \uplus\ X\Big],\qquad X=\begin{cases}P^{D'}(\Phi_{a,y_a(t^*)},\Phi_{b,y_b(t^*)},e'(t^*))& i=1\\ S_{\rm deg}(D')\uplus S_{\rm deg}(D')&i=0.\end{cases}$$
The pair in the case $i=1$ consists of two $\mathcal{SA}$ nodes with the same $c_a,c_b$, so (a)–(d) apply again (*resonant chain*).

*Proof.* Corollary GR; all points are critical (Lemma N(a)). Over a target residue $t$ the class-$a$ critical point is $y_a(t)$ and the class-$b$
point is $y_b(t)$ (residue of $\Phi_b([y'])-e$ is $c_by'^2+\bar e$). Their classes mod 4 coincide iff $\Phi_a([y_a])+e\equiv\Phi_b([y_b])$ (mod 4); by the Witt rules
$\Phi_a([y_a])+e\equiv[t+\bar e]+2[\sigma_a(y_a)+e_1+\sqrt{t\bar e}]$ and $\Phi_b([y_b])\equiv[t+\bar e]+2[\sigma_b(y_b)]$, which gives $C$. So over $t\notin C$ there are two groups of
one child each (weight $q$), over $t\in C$ one group with both children and offset $e'(t)$, and $H\equiv0$; (a) follows ($D'\le0$). The children are in $\mathcal{SA}$
with residues $W_x(t)z+c_xz^2$ (Lemma N(c), with $y_a(t)$ resp. $y_b(t)$). (b): $W_a/\sqrt{c_a}=\lambda_a/\sqrt{c_a}+\sqrt t$ and $W_b/\sqrt{c_b}=\lambda_b/\sqrt{c_b}+\sqrt{t}+\sqrt{\bar e}$;
equality of hyperplanes $\iff W_a^2/c_a=W_b^2/c_b$ (Lemma T1); $W_a(t^*_a)=0$ gives $W_b(t^*_a)/\sqrt{c_b}=\delta'$. (c): $y_a,y_b,\sqrt{t\bar e}$ are affine in $u$, $\sigma_x$ additive;
with $\sigma_x=\lambda_xy+\nu_xy^2$ the linear part is as stated, and its kernel has dimension $\le1$ unless it vanishes. (d): child multisets by Lemma T1
(ND+ND; distinct hyperplanes when $\delta'\ne0$, equal when $\delta'=0$, by (b)), Lemma T2 (DEG+ND: when $\delta'\ne0$ the special residues $t^*_a\ne t^*_b$ are distinct, so a
merged group is never DEG+DEG), Prop. 5 (single children), and induction for the DEG+DEG group (only possible when $\delta'=0$ at $t^*$). Counting:
non-resonant — $s'$ residues of type ND+ND merged, $q-2-s'$ residues with two separate ND children ($2\otimes\{2^{(q^{D'}/2)}\}=\{2^{(q^{D'})}\}$), and the two special
residues; resonant — $r$ merged ND+ND with $\chi=0$, and $q-1-r$ residues giving $\{2^{(q^{D'})}\}$ (merged with $\chi=1$, or separate), plus $t^*$. $\square$

**Closed form along the chain.** Let $\ell=0,1,\dots,L-1$ be the resonant levels with $i_\ell=1$ (depths $D_\ell=D-2\ell$), and level $L$ the terminal one (depth
$D_L\le2$, or non-resonant, or resonant with $i_L=0$). Then
$$P^D=\biguplus_{\ell<L}q^{\ell+1}\Big[r_\ell\otimes\{4^{(q^{D_\ell-2}/2)}\}\uplus(q-1-r_\ell)\otimes\{2^{(q^{D_\ell-2})}\}\Big]\ \uplus\ q^{L}\,P_{\rm term},\tag{2.1}$$
$P_{\rm term}$ given by (a) or (d) at depth $D_L$. $L\le\lfloor(D-1)/2\rfloor$.

**Maximum.** $\max P^D$ is computed by the same recursion: $\max P^1=2$; $\max P^2=2q$ if $s>0$, else $q$; for $D\ge3$
non-resonant: $q\max\big(2,\ 4[s'>0],\ \max X_a,\ \max X_b\big)$ with $\max X_x=m_{T2}(D',\kappa_x)$ if $i_x=1$, else $\max(m_{\rm deg}(D'),2)$;
resonant: $q\max\big(2,\ 4[r>0],\ \max X\big)$ with $\max X=\max P^{D'}(\text{child pair})$ if $i=1$, else $m_{\rm deg}(D')$.
Always $m_{\rm deg}(D)\le\max P^D\le2m_{\rm deg}(D)$ (each class alone has maximum $m_{\rm deg}(D)$, Prop. 5(c)).

---------------------------------------------------------------------------------------------------

## 3. Sub-case (1): merged DEG+DEG

**Theorem I.** Let $\mu=0$, $c_3\ne0$, $d\ge3$, and let $a$ satisfy $w_\alpha(a)=0$ and $A_F(a)=0$ (so $b=a+\rho$ has $w_\alpha(b)=w_\alpha(a)+\mu=0$ and the
pair is merged, $B_\alpha=A_F$). Then the pair contributes $q^{j+1}\cdot P^d(\Phi_{x_a},\Phi_{x_b},e_P)$, given by Theorem P with $c_a=c_b=c_3$:
1. $\Phi_{x_a},\Phi_{x_b}\in\mathcal{SA}$, $\sigma_x(y)=\lambda_xy+\nu_xy^2$ with $\sigma_x(y)$ the second Witt digit of $(T(x+2[y])-T(x))/4$; the level data are
   $\delta'=(\lambda_a+\lambda_b)/\sqrt{c_3}+\sqrt{\bar e_P}$ and $C=\{u^2:\ \delta'u+\nu'u^2=\sigma_b(\sqrt{\bar e_P/c_3})+e_1\}$, $\nu'=(\nu_a+\nu_b)/c_3$.
   **$c_3$ and $\nu_a,\nu_b$ are inherited** by every pair of the resonant chain (Lemma P' below), so $\nu'$ is one invariant for the whole chain, and at every level:
   resonant & $\nu'\ne0$ $\Rightarrow s=1$; resonant & $\nu'=0\Rightarrow s\in\{0,q\}$; non-resonant & $\nu'=0\Rightarrow s=1$; non-resonant & $\nu'\ne0\Rightarrow s\in\{0,2\}$.
2. The multiset is (2.1); in particular it is determined by the chain data
   $\big((\delta'_\ell=0?),s_\ell,i_\ell\ \text{or}\ (i_{a,\ell},i_{b,\ell},\kappa_{a,\ell},\kappa_{b,\ell}),r_\ell\big)_{\ell\le L}$, at most $\lfloor(d-1)/2\rfloor+1$ levels, each computable from $O(q)$
   values of $T$ (level $\ell$ uses $T$ modulo $2^{2\ell+6}$ on the points $x+2[y_0]+\dots+2^{\ell}[y_{\ell-1}]+2^{\ell+1}[y]$).
3. $m_{\rm deg}(d)\le\max\le2m_{\rm deg}(d)$, the exact maximum given by §2.4. Explicitly:
   $d=3$: $\max=4q$ if ($\delta'\ne0,s'>0$) or ($\delta'=0,r>0$); else $3q$ if $\delta'\ne0$ and $i_a+i_b>0$; else $2q$.
   $d=4$: non-resonant: $q^2+2q$ if $i_a+i_b>0$, else $q^2$; resonant: $2q^2$ if $i=1$ and the child pair (depth 2) has $s_1>0$, else $q^2$.
   $d=5$: non-resonant: $2q^2+2q$ if $i_a+i_b>0$, else $2q^2$; resonant: $q\cdot\max(P^3_{\rm child})\in\{2q^2,3q^2,4q^2\}$ if $i=1$, else $2q^2$.

**Lemma P'.** If $\Phi\in\mathcal{SA}$ then every child satisfies $\varphi_{2}(\Phi_y)\equiv\varphi_2(\Phi)\pmod 4$; hence $c$ and $\nu$ are the same for a node and all its descendants.
*Proof.* $\varphi_2(\Phi_y)=\Phi^{[2]}(\hat y)=\sum_{r\ge2}\binom r2\varphi_r\hat y^{r-2}$; $\varphi_3,\varphi_5,\varphi_7,\ldots\in8R$, $\binom42\varphi_4\in 8R$ and $\binom r2\varphi_r\in4R$ for even $r\ge6$. $\square$

*Proof of Theorem I.* Lemma 4 of R05b ($\Phi_x\in\mathcal{SA}$, residue $w_\alpha(a)y+c_3y^2=c_3y^2$), Lemma N(d) for $\sigma_x$, then Theorem P; the statements on $s$ are Theorem P(c) with Lemma P'. In sub-case (1) all nodes of the chain have quadratic
residue $c_3$ (Lemma N(c)), and all children of $\mathcal{SA}$ nodes are $\mathcal{SA}$, so Theorem P applies at every level. $\square$

*Remarks.* (i) The resonance condition says that the two degenerate paths of the two Hensel trees pass through the *same* target residue; the coincidence set
$C$ says which residues carry a merged group. Generic lifts are non-resonant ($\delta'$ is one $\mathbb F_q$-condition), and then the answer is the closed
non-resonant formula with $s\in\{0,1,2\}$ — no recursion at all.
(ii) Example (R05b §7, $r1010\_A0$, $k=7$, $j=2$): non-resonant, $s=s'=1$, $i_a=i_b=0$: $P^3=q[\{4^{(8)},2^{(16)}\}\uplus29\{2^{(32)}\}\uplus2(S_{\rm deg}(1)\uplus S_{\rm nd}(1))]=\{4q^{(8)},2q^{(976)},q^{(64)}\}$, the observed row.

---------------------------------------------------------------------------------------------------

## 4. Sub-case (2): merged DEEP+DEEP

Let $\mu=0=c_3$, $\pi(a)=0$, $A_F(a)=0$; then $\pi(b)=0$, both classes are DEEP and merged. Halves $h_x=\Phi_x/2\in\mathcal A$ (R05b Lemma 4) have residue
$w'_xy+c'_xy^2$ (R05b Thm B(4)); their mod-4 reduction is $h_x(z)\equiv h_{x,1}z+h_{x,2}z^2+2t_{4}z^4$ with $t_4=T^{[4]}(x)\equiv c_5$, so for $w'_x=0$:
$h_x([y])\equiv[c'_xy^2]+2[\sigma_x(y)]$, $\sigma_x=\lambda'_xy+\nu'_xy^2+c_5y^4$ (additive). Types of a half: ND ($w'\neq0$), DEG ($w'=0\ne c'$), DEEP2 ($w'=c'=0$, sub-case (3) inside).

**Theorem II.** Let $e=e_P$, $d\ge2$.
1. If $\bar e\ne0$ the two classes reach disjoint targets and the pair multiset is $M_a\uplus M_b$ with $M_x=q\,M^{d-1}(h_x)$ (R05b Thm B(4): $q S_{\rm nd}(c'_x,d-1)$
   or $qS_{\rm deg}(d-1)$), or Theorem III if $h_x$ is DEEP2.
2. If $\bar e=0$ the pair multiset is $q\cdot P^{d-1}(h_a,h_b,e/2)$ (completed by zeros), where with $\varepsilon=e/2$:
   * ND+ND: Lemma T1 (the table there, with $D=d-1$; e.g. both $c'\ne0$, distinct hyperplanes: $\{4q^{(q^{d-1}/4)},2q^{(q^{d-1}/2)}\}$).
   * ND+DEG: Lemma T2 with $H=n_{\rm ND}(\cdot+\bar\varepsilon)$; i.e. $S_{\rm deg}(d-1)+1$ if $c'_{\rm ND}=0$, C(iv) with $\kappa=[t^*+\bar\varepsilon\in H_{\rm ND}]$ if $c'_{\rm ND}\ne0$.
   * DEG+DEG: Theorem P at depth $d-1$ with $c_a=c'_a$, $c_b=c'_b$ (in general $c'_a\ne c'_b$) and $\sigma_x$ as above; here $s\in\{0,1,2,4,q\}$ (the linear part of the
     coincidence function has a $u^4$ term $c_5(c_a'^{-2}+c_b'^{-2})u^4$); the children are $\mathcal{SA}$, so the chain continues within Theorem P.
   * DEEP2+ND (say $h_a$ DEEP2 with quarter $\Psi_a=h_a/2$): $\{H(t)^{(q^{d-2})}:t\ne0\}\uplus\big(q\,M^{d-2}(\Psi_a)+H(0)\big)$ with $H(t)=n_b(t+\bar\varepsilon)$; $M(\Psi_a)$ from Theorem III.
   * DEEP2+DEG with $\Psi_a$ Hensel ($\lambda_1(\Psi_a)\ne0$) or $d=3$: over $\bar g\ne0$ the DEG half's tree alone; over $\bar g=0$ (targets $g=2g'$): value $q\,n_L(\bar g')$ on
     all $g'$ except the coset $\bar g'=t_0$ hit by the DEG half, where it is $q\,n_L(t_0)+q\,X$, $X=S_{\rm deg}(d-3)$ or $S_{\rm nd}(1,d-3)$ (as in Lemma T2). Here $t_0$ is the
     second Witt digit of $h_b([y_0])-\varepsilon$, $y_0=\sqrt{\bar\varepsilon/c'_b}$.
   * DEEP2+DEEP2: if $\bar\varepsilon\ne0$: $q\,M(\Psi_a)\uplus q\,M(\Psi_b)$; if $\bar\varepsilon=0$ and both quarters Hensel (or $d=3$): $q\cdot$Lemma T1 for $(\Psi_a,\Psi_b,\varepsilon/2)$ at depth $d-2$.
3. Maximum (exact value read off from 1–2). If $\bar e\ne0$: $\max\ge q$, with equality iff each half is ND with $c'=0$, or $d=2$ and each half has bijective residue
   (ND with $c'=0$, or DEG). If $\bar e=0$: $\max\ge2q$, with equality iff both halves are ND and either $c'_a=c'_b=0$ or ($c'_ac'_b\ne0$, equal hyperplanes, $\mathrm{Tr}(c'_b\bar\varepsilon/w_b'^2)=1$),
   or $d=2$ and both halves have bijective residue.

*Proof.* Prop. 5(d): $N_x(g)=q[\bar g=0]N^{d-1}_{h_x}(g/2)$ and $N_b(g+e)=q[\bar g+\bar e=0]N^{d-1}_{h_b}((g+e)/2)$. If $\bar e\ne0$ the supports are disjoint. If $\bar e=0$,
$e\in2R$ and on $\bar g=0$, $g=2g'$: $N_a+N_b=q\big(N_{h_a}(g')+N_{h_b}(g'+\varepsilon)\big)$, a configuration of the two halves at depth $d-1$. Its types: ND halves are Hensel
everywhere (Lemma N(a), $h\in\mathcal A$), so Lemma T1/T2 apply; a DEG half is in $\mathcal A$ with additive $\sigma$ (computed above from $h_{x,3}=T^{[3]}\in4R$, $h_{x,4}=2T^{[4]}$,
$h_{x,r}\in4R$ for $r\ge5$), so Theorem P applies; a DEEP2 half is $\equiv0$, hence $h=2\Psi$ (Lemma N(e) / §5) with $N_h(g')=q[\bar g'=0]N_{\Psi}(g'/2)$:
with an ND partner the partner is residue-level (Lemma T1), giving the formula; with a DEG partner and $\Psi$ Hensel, $N_\Psi(g'/2)$ depends only on the residue of $g'/2$, i.e. on the
second Witt digit of $g'$, while the DEG half's tree over the residue $\bar g'=0$ consists of exactly one coset of $4R$ (Lemma GR(ii)) — this is the formula; DEEP2+DEEP2 as in (1),(2)
one level down. Max: on $\bar g=0$ the total mass is $2q^{d}$ over $q^{d-1}$ targets ($\bar e=0$), resp. $q^d$ per class; equality requires the half configuration to
take the constant value $2$ (resp. $1$) on all $q^{d-1}$ targets. For $d\ge3$ (half depth $D\ge2$) a DEG half has some value $\ge q>2$ ($S_{\rm deg}(D)$, $D\ge2$) and a DEEP2
half has some value $\ge q$ (Lemma N(e)); so both halves are Hensel, and Lemma T1 lists when the sum is constant $2$ (resp. $1$). For $d=2$ ($D=1$) everything is
residue level: $N_h(t)=\#\bar h^{-1}(t)$, constant $1$ iff the residue is bijective. $\square$

*Remark.* The only previously observed row of this type ($r1111\_A0$, $k=5$, $j=1$, $d=2$) has $\bar e\ne0$ (split): $\{q^{(32)}\}$ per class, i.e. the row
$\{2048^{(15360)},65536^{(32)}\}$ — now predicted (§7).

---------------------------------------------------------------------------------------------------

## 5. Sub-case (3): DEEP class with $w'_\alpha(a)=c'(a)=0$

**Theorem III.** Let $c_3=0=\pi(a)$, $\bar x=a$, $f_s=F^{[s]}(x)$, and $w'_\alpha(a)=c'(a)=0$, $d\ge2$.
1. $f_2,f_3\in4R$, $\Phi_x\in4R[z]$, and $\Psi:=\Phi_x/4\in R[z]$ has residue
   $$L(y)=\lambda_1y+\lambda_2y^2+c_5y^4,\quad \lambda_1=\overline{f_2/4}+[j=1]\big(\bar u\,\overline{f_3/4}+\bar u^3c_5\big),\quad \lambda_2=\overline{f_3/4}+[j=1]\,\bar u\,p^{[4]}(a).$$
   $L$ is independent of the choice of $x$ (intrinsically $L(y)=\overline{(T(x+2[y])-T(x))/16}$). $\Psi'\equiv\lambda_1$ (mod 2).
2. $N_a(g)=q^2\,[g\in4R]\,N^{d-2}_\Psi(g/4)$. Every nonzero entry of the class is a multiple of $q^2$, i.e. of $q^{j+3}$ in the row.
3. $d=2$: $\{q^{2\,(1)}\}$. $d=3$: $\{(2^\kappa q^2)^{(q/2^\kappa)}\}$ with $2^\kappa=|\ker L|$ (so $\{q^{3\,(1)}\}$ if $L\equiv0$).
4. $d\ge4$, $\lambda_1\ne0$: $\{(2^\kappa q^2)^{(q^{d-2}/2^\kappa)}\}$, $\kappa=\dim\ker L\in\{0,1,2\}$.
5. $d\ge4$, $\lambda_1=0$, $L\not\equiv0$: every point is critical for $\Psi$; the child at $y$ is admissible with residue $\mu(y)z+\lambda_2z^2$,
   $\mu(y)=\mu_0+\lambda_2y+\theta y^2$, $\mu_0=\overline{\psi_1/2}$, $\theta=\overline{\psi_3/2}=p^{[4]}(a)+[j=1]\bar uc_5$, and its mod-4 reduction is $\varphi_1z+\varphi_2z^2$. The fibres
   of $L=M^2$ ($M=\sqrt{\lambda_2}y+\sqrt{c_5}y^2$) have size $|\ker L|\in\{1,2\}$. Hence
   $$M^{d}(\text{class})=q^3\biguplus_{t\in{\rm Im}L}\ \biguplus_{\text{groups }G\subseteq L^{-1}(t)}M^{d-4}(G)\ \ (+\text{zeros}),$$
   groups = points of the fibre with equal $\Psi([y])$ mod 4 (size 1 or 2), and $M^{d-4}(G)$ is given by: single ND child: $S_{\rm nd}(\lambda_2,d-4)$; single DEG child
   ($\mu(y)=0\ne\lambda_2$): $S_{\rm deg}(d-4)$; two children: Lemma T1, T2, or Theorem P according to their types; a single child of residue $0$ ($\mu(y)=0=\lambda_2$): Lemma Z,
   closed when its half is Hensel. In particular:
   * $\lambda_2\ne0$, $c_5=0$: $\{(2q^3)^{((q-z_\mu)q^{d-4}/2)}\}\uplus z_\mu\otimes q^3S_{\rm deg}(d-4)$, $z_\mu=\#\mu^{-1}(0)\in\{0,1,2\}$;
   * $\lambda_2=0$ (so $c_5\ne0$, $L$ bijective) and $\mu$ zero-free: $\{q^{3\,(q^{d-3})}\}$;
   * $\lambda_2c_5\ne0$: fibres $\{y,y+\eta\}$, $\eta=\sqrt{\lambda_2/c_5}$, and $\mu(y+\eta)-\mu(y)=\lambda_2\eta+\theta\eta^2$ is constant. The two children of a fibre have the
     same hyperplane iff $\theta^2=\lambda_2c_5$ ("resonance"); then the coincidence of $y$ and $y+\eta$ mod 4 is the same for **all** fibres, and a fibre with $\mu(y)=0$ gives a
     DEG+DEG group (Theorem P). Otherwise the coincident fibres are the zero set of an affine-additive function of $y$ with linear part
     $(\theta+\sqrt{\lambda_2c_5})(\eta y^2+\eta^2y)$; since $y\mapsto\eta y^2+\eta^2y$ is 2-to-1 with fibres $\{y,y+\eta\}$, **at most one** fibre is coincident.
6. Maximum: $\max\ge q^2$, with equality iff ($d=2$) or ($L$ bijective and ($d=3$ or $\lambda_1\ne0$)). In cases 3–4 $\max=2^\kappa q^2$. In case 5 $\max=q^3\max_G\max M^{d-4}(G)\ge q^3$.
   So a class of sub-case (3) always has row entries $\ge q^{j+3}$, while a DEEP class with $w'\ne0=c'$ has all entries $q^{j+2}$ (R05b Thm B(4)): sub-case (3) is never
   optimal.

*Proof.* (1) By (1.1), $\Phi_x=\sum_{t\ge1}\varphi_tz^t$ with $\varphi_t=2^{t-2}\sum_{s>t}\binom st\alpha^{s-t-1}f_s$ ($t\ge2$) and $\varphi_1=\sum_{s\ge2}\frac s2\alpha^{s-2}f_s$. $w'=c'=0$
means $\varphi_1,\varphi_2\in4R$ (R05b proof of Thm B); for $j\ge1$ this is $f_2,f_3\in4R$ (induct on the formulas below). Mod 8:
$\varphi_1=f_2+3\cdot2^{j-1}uf_3+2^{2j+1}u^2f_4+5\cdot2^{3j-1}u^3f_5+(\in8R)$, so $\overline{\varphi_1/4}=\overline{f_2/4}+[j=1](\bar u\overline{f_3/4}+\bar u^3c_5)$ ($f_5\equiv c_5$);
$\varphi_2=3f_3+6\cdot2^juf_4+(\in8R)$, so $\overline{\varphi_2/4}=\overline{f_3/4}+[j=1]\bar u\,p^{[4]}(a)$; $\varphi_3=2(4f_4+10\alpha f_5+\dots)\in8R$; $\varphi_4=4(5f_5+\dots)$ with
$\overline{\varphi_4/4}=c_5$; $\varphi_t/4=2^{t-4}T^{[t]}(x)\in2R$ for $t\ge5$. So $\Psi$ has $\psi_3\in2R$, $\psi_4\equiv c_5$, $\psi_t\in2R$ ($t\ge5$), residue $L$, and
$\Psi'=\sum t\psi_tz^{t-1}\equiv\psi_1$. Changing $x$ to $x+2z_0$ replaces $\Psi$ by $\Psi(z+z_0)-\Psi(z_0)$, whose residue is $L(y+\bar z_0)-L(\bar z_0)=L(y)$.
(2) $\Phi_x=4\Psi$ coefficientwise; $\Phi_x(z)\equiv g$ (mod $2^d$) iff $g\in4R$ and $\Psi(z)\equiv g/4$ (mod $2^{d-2}$), which depends on $z$ mod $2^{d-2}$ ($q^2$ lifts mod $2^d$).
(3),(4) Depth $d-2\le1$ is residue-level; for $\lambda_1\ne0$, $\Psi$ is Hensel everywhere and Lemma T1 applies: $n_L(t)=|\ker L|\cdot[t\in{\rm Im}L]$.
(5) Lemma GR for $\Psi$ ($\Psi'\equiv0$). $\Psi'(z)/2=\psi_1/2+\psi_2z+\frac32\psi_3z^2+2\psi_4z^3+\frac52\psi_5z^4+\dots$; $\psi_5=2T^{[5]}(x)$ and $T^{[5]}\equiv6f_6\equiv0$ give
$\psi_5\in4R$; the terms $t\ge6$ lie in $2R$; so $\mu(y)=\mu_0+\lambda_2y+\theta y^2$ with $\theta=\overline{\psi_3/2}=\overline{T^{[3]}(x)/4}=\overline{f_4+\frac52\alpha f_5+\dots}$, which is
$p^{[4]}(a)+[j=1]\bar uc_5$. $\Psi^{[2]}(\hat y)\equiv\psi_2\equiv\lambda_2$. The child coefficients $2\Psi^{[3]}(\hat y)$ ($\Psi^{[3]}=\psi_3+4\psi_4z+\dots\in2R$, so $\in4R$),
$4\Psi^{[4]}$, $2^{r-2}\Psi^{[r]}$ show that the child is admissible and $\equiv\varphi_1z+\varphi_2z^2$ mod 4. Then Corollary GR with the type lemmas. The two bullet points:
if $\lambda_2\ne0=c_5$, $L=\lambda_2y^2$ is bijective, every group is one child of residue $\mu(y)z+\lambda_2z^2$, ND or DEG; if $\lambda_2=0$, the children have residue $\mu(y)z$ and are
Hensel with $n\equiv1$ when $\mu(y)\ne0$. For $\lambda_2c_5\ne0$: $\mu(y+\eta)-\mu(y)=\lambda_2\eta+\theta\eta^2$ is constant, zero iff $\theta\eta=\lambda_2$ iff $\theta^2=\lambda_2c_5$; the mod-4
digit of $\Psi([y])$ is $\sigma_\Psi(y)=\mu_0y+\nu_2y^2+(\theta+\sqrt{\lambda_2c_5})y^3+\nu_4y^4$ (Witt rule for $[\lambda_2y^2]+[c_5y^4]$), and
$\sigma_\Psi(y+\eta)-\sigma_\Psi(y)$ is affine in $y$ with linear part $(\theta+\sqrt{\lambda_2c_5})(\eta y^2+\eta^2y)$.
(6) $\sum_gN_\Psi(g)=q^{d-2}$ over $q^{d-2}$ targets, so $\max N_\Psi\ge1$, with equality iff $\Psi$ is a bijection of $R/2^{d-2}$; for $d-2\ge1$ this needs $L$ bijective, and for
$d-2\ge2$ it needs no critical point (a critical point maps $q^{d-3}$ points into a coset of $4R$ of size $q^{d-4}$), i.e. $\lambda_1\ne0$; conversely these conditions give a
bijection (Lemma GR(i)). $\square$

---------------------------------------------------------------------------------------------------

## 6. Consequences for the row maxima (Corollary M)

Let $1\le j\le k-3$ and $d=k-j-2$.
1. (sub-case 1) A merged DEG+DEG pair contributes a maximum between $q^{j+1}m_{\rm deg}(d)$ and $2q^{j+1}m_{\rm deg}(d)$, both attained (§7). So Corollary D(4) of R05b
   ($\ge q^{j+1+\lfloor d/2\rfloor}$) is the right order, and merging can at most double the top value.
2. (sub-case 2) A merged DEEP+DEEP pair contributes a maximum $\ge q^{j+2}$, and $\ge2q^{j+2}$ when $\bar e_P=0$.
3. (sub-case 3) The class contributes a maximum $\ge q^{j+3}$, with equality iff $d=2$ or ($L$ bijective and ($d=3$ or $\lambda_1\ne0$)).
In none of the three sub-cases can the layer be flat (R05b Cor. D(2) already excludes them); the new information is the exact size of the excess.

---------------------------------------------------------------------------------------------------

## 7. Verification

**Method.** Three independent predictors and two brute forces.
* *Closed forms* (`closed.py`, `theory.py`): the formulas of Theorems P/I, II, III and Lemmas T1, T2, Z, with every invariant read off from $O(q)$ values of $T$
  per level; R05b Theorems A–C (`predict.py`, unchanged) for all other pairs of the row. `Fallback` would be raised outside the closed cases — it never was.
* *GR* (`gr.py`): Corollary GR as an exact recursion for every pair of the row (independent of the closed forms; it uses no type theory at all).
* *Brute force*: `clsspec2` enumerates every $y$ in the pair/class (mod $2^n$) and histograms $T(y)$; full rows for $n=k-j\le5$, and for selected $n=6$ rows,
  as the union over all $q/2$ pairs (both classes, values indexed mod $2^n$ relative to $T(x_a)$, which only uses $\bar T=p'$). `clsspec2` was cross-checked against
  `clsspec` (Taylor data of $F$) on 84 pairs and both against R05b's `redspec2` (direct evaluation of $F$) on full $k=5$ rows; the Taylor evaluation of $T$ in Python was
  checked against direct evaluation at 240 random points.
* The theorems' internal claims are asserted during prediction (Prop. 5(b) child residues, resonance $\Leftrightarrow$ equal hyperplanes, additivity of $\sigma$,
  criticality of all points in Thm III(5), $L$-formula for every constructed sub-case-3 lift).

**Lifts.** All $m=5$ ($q=32$, $t^5=t^2+1$), built from R05b representatives by Taylor perturbations $F+2^tb(X-x)^s$ at the class centres
(§1), searched/solved so as to hit prescribed level data: sub-case 1 from $r1010\_A0$, $r1011\_A0$ (40 lifts, `gen1u.jsonl`);
sub-case 2 from $r1111\_A0$ (37 lifts, `gen2u.jsonl`); sub-case 3 from $r0110\_A0$, $r0111\_A0$, $r1111\_A0$ (44 lifts with $w'=c'=0$ and prescribed
$(\lambda_1,\lambda_2)$, `gen3.jsonl`, plus 12 lifts with $\lambda_1=0$, $\lambda_2c_5\ne0$, resonant/non-resonant, coincident/not, $\mu$ with/without zeros, `gen3b.jsonl`).
Sub-case (3) had never been observed before; it is now realised 56 times.

**Results** (per open-type pair or class; "rows" = full rows brute-forced; every count is MATCH unless stated):

| sub-case | d | targets | closed_MATCH | closed_MISMATCH | closed_FALLBACK | gr_MATCH | gr_MISMATCH | rows | row_closed_MATCH | row_closed_MISMATCH | row_closed_FALLBACK | row_gr_MATCH | row_gr_MISMATCH | closed!=gr | CHECKFAIL |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 3 | 10 | 10 | 0 | 0 | 10 | 0 | 10 | 10 | 0 | 0 | 10 | 0 | 0 | 0 |
| 1 | 4 | 20 | 20 | 0 | 0 | 20 | 0 | 10 | 10 | 0 | 0 | 10 | 0 | 0 | 0 |
| 1 | 5 | 10 | 10 | 0 | 0 | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 2 | 2 | 4 | 4 | 0 | 0 | 4 | 0 | 4 | 4 | 0 | 0 | 4 | 0 | 0 | 0 |
| 2 | 3 | 12 | 12 | 0 | 0 | 12 | 0 | 12 | 12 | 0 | 0 | 12 | 0 | 0 | 0 |
| 2 | 4 | 16 | 16 | 0 | 0 | 16 | 0 | 9 | 9 | 0 | 0 | 9 | 0 | 0 | 0 |
| 2 | 5 | 5 | 5 | 0 | 0 | 5 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 3 | 2 | 10 | 10 | 0 | 0 | 10 | 0 | 10 | 10 | 0 | 0 | 10 | 0 | 0 | 0 |
| 3 | 3 | 14 | 14 | 0 | 0 | 14 | 0 | 14 | 14 | 0 | 0 | 14 | 0 | 0 | 0 |
| 3 | 4 | 17 | 17 | 0 | 0 | 17 | 0 | 6 | 6 | 0 | 0 | 6 | 0 | 0 | 0 |
| 3 | 5 | 15 | 15 | 0 | 0 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| all | | 133 | 133 | 0 | 0 | 133 | 0 | 75 | 75 | 0 | 0 | 75 | 0 | 0 | 0 |
distinct (lift,row) records: 133

Columns: `targets` = open-type pairs/classes brute-forced exhaustively; `closed_*` / `gr_*` = closed formula / GR recursion vs brute force for that pair/class;
`rows` = full rows brute-forced (all $q/2$ pairs); `row_closed_*`, `row_gr_*` = whole predicted row vs brute row; `closed!=gr` = rows where the two predictors differ;
`CHECKFAIL` = failed internal assertions of R05b's Lemma checks. Sub-case 3 counts include the classes merged with an ND partner (Thm C(2) + Theorem III).


*Covered configurations.* Sub-case 1: $d=3$: non-resonant $s\in\{1,2\}$ (with $i_a$ or $i_b$), resonant $s=1$ with $i=0$ and $i=1$; $d=4$: non-resonant
($s=2$, $i_a=1$), resonant $i=0$, resonant chains $\to$ depth-2 child with $s_1\in\{0,1,2\}$, including $\nu'=0$ chains with $s=q$ ($r=31$, $r=15$);
$d=5$: non-resonant with $\kappa$, resonant $\to$ non-resonant child, resonant $\to$ resonant $\to$ depth 1 (chain of length 2).
Sub-case 2 ($d=2..5$): split ($\bar e\ne0$) with ND/DEG/DEEP2 halves; merged halves ND+ND (distinct hyperplanes, equal hyperplanes with $\chi=0$ and $\chi=1$,
$c'=0$), ND+DEG, DEG+DEG (with $c'_a\ne c'_b$), DEEP2+ND, DEEP2+DEG (Hensel quarter), DEEP2+DEEP2.
Sub-case 3 ($d=2..5$; split and merged with an ND partner): $\lambda_1\ne0$ with $|\ker L|=1,2,4$; $\lambda_1=0$ with $\lambda_2\ne0$ (fibres of size 2:
resonant all-coincident with a DEG+DEG group, resonant non-coincident, non-resonant with 0 or 1 coincident fibre, $\mu$ with and without zeros) and $\lambda_1=\lambda_2=0$
(zero-residue child, closed by Lemma Z).

**Further checks.**
* All **691 rows of R05b** re-graded with the new row predictor and with GR: 691/691 MATCH for both, including the two rows that R05b had to leave
  UNPREDICTED ($r1111\_A0$ $k=5$: sub-case 2, split; $r1010\_A0$ $k=7$: sub-case 1, non-resonant $s=1$). (`recheck_old.jsonl`)
* `check1.py`: on all 40 sub-case-1 lifts, along the whole resonant chain: $c,\nu$ inherited (Lemma P'), and $s$ obeys Theorem I(1). 40/40.
* `check3.py`: on the 22 sub-case-3 lifts with $\lambda_1=0$: all points critical, $\mu(y)=\mu_0+\lambda_2y+\theta y^2$ with the stated $\theta$, cubic coefficient of
  $\sigma_\Psi$ equal to $\theta+\sqrt{\lambda_2c_5}$, and the fibre-coincidence dichotomy (resonant: 0 or all 16 fibres; non-resonant: $\le1$ fibre). 22/22
  (observed: resonant 16 fibres ×4, 0 ×2; non-resonant 1 fibre ×8, 0 ×3).
* `maxcheck.py`: the maximum computed from the level data alone (§2.4 recursion) equals the brute-force maximum for all 40 sub-case-1 pairs, and
  $m_{\rm deg}(d)\le\max\le2m_{\rm deg}(d)$ with **both bounds attained** for $d=3,4,5$; sub-case 2 bounds hold (41/41; equality $2q$ attained for merged halves);
  sub-case 3: $\max\ge q^2$ and the equality criterion of Theorem III(6) agree with brute force in every case.
* GR and the closed forms agree on every row where both apply (closed$\neq$GR: 0).

## 8. Reproduction

All in `/home/claude/w/research/layers_r06/` (python3, numpy not needed; gcc). Files copied unchanged from `r07/layers`: `grlib.py`, `predict.py`,
`pinv.py`, `closedforms.py`, `lifts.py`, `lifts/`, `redspec2.c`, `rowspec.c`, `reps_m5.json`.

```
gcc -O2 -o redspec2 redspec2.c                 # R05b brute force (direct F evaluation), used for cross-checks
gcc -O2 -march=native -o clsspec clsspec.c     # exhaustive pair/class spectrum from Taylor data of F
gcc -O3 -march=native -o clsspec2 clsspec2.c   # same from Taylor data of T (2x faster; cross-checked against clsspec on 84 pairs)
# lifts (deterministic seeds; outputs in lifts_r06/ and gen*.jsonl)
python3 gen3.py  "$(cat jobs3.json)"  gen3.jsonl     # sub-case 3, prescribed lambda1, lambda2 (asserts the lambda formulas)
python3 gen3b.py "$(cat jobs3b.json)" gen3b.jsonl    # sub-case 3, lambda1=0, lambda2*c5!=0, resonant / coincident / mu-zero variants
python3 gen1b.py "$(cat jobs1.json)"  gen1.jsonl     # sub-case 1 (coordinate scan on Taylor data; specs in gen1b.SPECS)
python3 gen2.py  "$(cat jobs2.json)"  gen2.jsonl     # sub-case 2
# verification (closed forms vs GR vs exhaustive brute force)
python3 verify_batch.py gen1u.jsonl ver1.jsonl ; python3 verify_batch.py gen2u.jsonl ver2.jsonl
python3 verify_batch.py gen3.jsonl ver3.jsonl ; python3 verify_batch.py gen3b.jsonl ver3b.jsonl
python3 verify_full6.py                        # extra full-row brute force for n=6 rows (ver_full6.jsonl)
python3 recheck_old.py                         # re-grades the 691 R05b rows (recheck_old.jsonl)
python3 summarize.py ver1.jsonl ver2.jsonl ver3.jsonl ver3b.jsonl ver_full6.jsonl   # table of section 7
python3 maxcheck.py ; python3 check1.py ; python3 check3.py                       # max-entry and structural checks
```
`gen1u.jsonl`/`gen2u.jsonl` are `gen1.jsonl`/`gen2.jsonl` with duplicate records removed (restarted generators re-wrote identical lifts).
Main modules: `gr.py` (ring, Taylor data, Lemma GR engine `GR.config`, `gr_row`), `closed.py` (Theorems P, I, II, III, Lemmas T1, T2, Z),
`theory.py` (row predictor = R05b Thms A–C + Theorems I–III), `brute.py`, `verify.py`.

## 9. What remains open (precisely)

1. **Residual configurations without a closed formula** (the multiset is still given exactly by Corollary GR, which is proved; only the type-calculus
   shortcut is missing). Each requires at least five independent $\mathbb F_q$-conditions on residues of Taylor data, none was met by the test lifts:
   * sub-case (2), $\bar e=0$: a DEEP2 half whose quarter is not Hensel ($\lambda_1=0$), $d\ge4$, paired with a DEG half, or two DEEP2 halves with
     $\bar\varepsilon=0$ and a non-Hensel quarter;
   * sub-case (3), $\lambda_1=0=\lambda_2$: the zero-residue child (it exists iff $\theta y^2=\mu_0$ is solvable) whose own half is not Hensel, $d\ge6$;
   * sub-case (3), $L\equiv0$ (needs $c_5=0$; for every $p$ used here $c_5\ne0$): $d\ge5$; here $\Psi/2$ has residue $\nu_1y+\nu_2y^2+\theta y^3+\nu_4y^4$, not
     additive, and the type calculus of §2 does not apply (for $d=4$ the answer is the residue-level fibre count of that quartic, by Lemma N(e)).
2. **Invariants are intrinsic, not coefficient formulas.** $\lambda_x,\nu_x,\bar e,e_1$ (hence $\delta'$, $C$, $s$), $r_\ell$, $\kappa$ are defined from $T$ (Witt digits
   of $T$ at $O(q)$ points), like $\kappa,s_P,\chi$ in R05b. Only Theorem III(1) ($\lambda_1,\lambda_2,\theta$) is expressed through the Taylor coefficients of $F$.
   The count $r_\ell=\#\{t\in C\setminus\{t^*\}:\chi(t)=0\}$ is a character-sum-type quantity for which I have no formula; it is an invariant of the row.
3. **Realisability** of arbitrary chain data (e.g. resonant chains of every length, every $r_\ell$) is not proved; only the examples of §7 are exhibited.
   Consequently the attainment of the upper bound $2m_{\rm deg}(d)$ is shown for $d=3,4,5$ only.
4. **Coverage limits of the computation**: $m=5$ only; $d\le5$; resonant chains of length $\le2$; Theorem P inside Theorem III only at child depth 1; full-row brute force
   for $n\le6$ (pairs/classes only for $n=7$).
5. Not addressed: the R05b open item on $\pi^{-1}(0)$ for $P_{m,3}$; the paper text (`apn2_full.tex`) was not edited — its open-problem paragraph can now be replaced by
   references to Theorems I–III.

# Intermediate layers $v_j$, $1\le j\le k-3$ — difference spectra of lifts of (H)-permutations

Status line (details in §6): **proved** (on paper, below) for every row except three sub-cases that are
stated as open in §7; **every computed row agrees** with the prediction or falls in the declared open
sub-cases (no mismatch). Computations: $m=5$, $k=4,5,6,7$, see §6 for exact coverage.

Notation follows `apn2_full.tex`: $R_k=\mathrm{GR}(2^k,m)$, $q=2^m$, $m$ odd, $p$ satisfies (H) with
$p'=\varepsilon+K$, $\ker K=\{0,\rho\}$; $F$ is any lift; $F^{[i]}$ are Hasse derivatives; $A_F,\mu$ as in
the paper. $[y]$ is the Teichmüller lift of $y\in\mathbb F_q$; $\bar x$ is reduction mod 2.

---------------------------------------------------------------------------------------------------

## 1. The new invariants

**Of $p$ alone** (they are not changed by any lift):

* $c_3:=[X^3]p\in\mathbb F_q$;
* $\pi:=p^{[2]}=c_2+c_3X+\sum_{i\ge2}c_{2+2^i}X^{2^i}$, an *affine* map $\mathbb F_q\to\mathbb F_q$ with
  $\pi(a+\rho)=\pi(a)+\mu$ (paper, Lemma F0(i)). Its linear part $\ell_1=\pi-\pi(0)$ is a nonzero map when
  $c_3\neq0$ (nonzero polynomial of degree $<q$).

**Of the row** $\alpha=2^ju\in v_j$, $u$ a unit, $\bar u\in\mathbb F_q^*$; put $n=k-j\ (\ge3)$, $d=n-2=k-j-2\ (\ge1)$:

* $w_\alpha(a):=\pi(a)+[j=1]\,\bar u\,c_3$ (so $w_\alpha(a+\rho)=w_\alpha(a)+\mu$);
* $B_\alpha(a):=A_F(a)+[j=1]\,\bar u\,\mu$ ($\rho$-periodic), $s_\alpha:=\#B_\alpha^{-1}(0)$ (even).

A residue $a$ is of type **ND** if $w_\alpha(a)\ne0$, **DEG** if $w_\alpha(a)=0\ne c_3$, **DEEP** if
$w_\alpha(a)=0=c_3$ (then $\pi(a)=0$). A pair $\{a,a+\rho\}$ is **merged** if $B_\alpha(a)=0$, otherwise **split**.
Note: for $j\ge2$ the row data $(w_\alpha,B_\alpha)=(\pi,A_F)$ do not depend on $u$; for $\mu=0$, $B_\alpha=A_F$ for all $j$.

Second-level data, only where needed (all are well defined, Lemma 4/Prop. 6):

* (DEEP, $c_3=0=\pi(a)$) $c'(a):=\overline{F^{[3]}(x)/2}$, $w'_\alpha(a):=\overline{F^{[2]}(x)/2}+[j=1]\bar u\,c'(a)$, $\bar x=a$;
* (merged, both ND, $\mu=0$, $c_3\ne0$) $\chi_\alpha(a):=\mathrm{Tr}\big(c_3\,e/w_\alpha(a)^2\big)$ with
  $e=\overline{(T(x+\tau)-T(x))/4}$, $T=T_\alpha$ below; equivalently
  $e=\overline{\big(F(x+\tau+\alpha)-F(x+\tau)-F(x+\alpha)+F(x)\big)/(4\alpha)}$;
* (merged DEG+ND, $\mu\ne0$, $c_3\ne0$, $d\ge3$) a bit $\kappa_\alpha(a)$ (Theorem C(iv));
* (merged DEG+DEG, $\mu=0$, $d=2$) an integer $s_P\in\{0,1,2,q\}$ (Theorem C(vi)).

The exceptional-row invariants $\Lambda$, $Z$, $E_F$, $\chi_F$ play **no role** in the layers $v_j$, $j\ge1$.

---------------------------------------------------------------------------------------------------

## 2. Statements

Let $S_{\rm nd}(c,d)$ be the multiset $\{1^{(q^d)}\}$ if $c=0$ and $\{2^{(q^d/2)},0^{(q^d/2)}\}$ if $c\ne0$
(and $\{1\}$ if $d=0$), and let the **universal degenerate multiset** be
$$
S_{\rm deg}(d)=\Big\{\,2q^{i}\ \text{with multiplicity}\ \tfrac{(q-1)q^{d-2i}}2\ \ (1\le i\le\lfloor\tfrac{d-1}2\rfloor),\quad q^{\lfloor d/2\rfloor}\ \text{with multiplicity}\ q\,\Big\}
$$
(nonzero part; completed by zeros to $q^d$ entries; total mass $q^d$). E.g. $S_{\rm deg}(1)=\{1^{(q)}\}$,
$S_{\rm deg}(2)=\{q^{(q)}\}$, $S_{\rm deg}(3)=\{2q^{((q-1)q/2)},q^{(q)}\}$,
$S_{\rm deg}(4)=\{2q^{((q-1)q^2/2)},q^{2\,(q)}\}$.

**Theorem A (reduction and decomposition).** Let $1\le j\le k-3$. $\delta_F(\alpha,\beta)=0$ unless
$\beta\in\alpha R_k$, and the nonzero entries of row $\alpha$ are exactly the numbers $q^{j+1}N$ where $N$ runs (with
multiplicity, zeros discarded) over the union over the $q/2$ pairs $P=\{a,b=a+\rho\}$ of the *pair multisets*
* split pair: $M_a\uplus M_b$, where $M_x=\{N_x(g):g\in R_d\}$ is the class multiset of Theorem B;
* merged pair: $\{N_a(g)+N_b(g+e_P):g\in R_d\}$, $e_P=(T(x_a)-T(x_a+\tau))/4\in R_d$, given by Theorem C.

**Theorem B (classes).** With $d=k-j-2\ge1$:
1. ND, $c_3=0$: $M_a=\{1^{(q^d)}\}$.
2. ND, $c_3\neq0$: $M_a=\{2^{(q^d/2)}\}$.
3. DEG: $M_a=S_{\rm deg}(d)$.
4. DEEP: $d=1$: $M_a=\{q^{(1)}\}$. $d\ge2$: if $w'_\alpha(a)\ne0$: $\{q^{(q^{d-1})}\}$ ($c'(a)=0$) or $\{2q^{(q^{d-1}/2)}\}$ ($c'(a)\ne0$);
   if $w'_\alpha(a)=0\ne c'(a)$: $q\cdot S_{\rm deg}(d-1)$ (values multiplied by $q$). [$w'=c'=0$: open, §7.]

**Theorem C (merged pairs).**
1. ($d=1$, all types) $N_x(g)$ depends on $\bar g$ only: ND: $\#\{y:w_\alpha(x)y+c_3y^2=\bar g\}$; DEG: $1$; DEEP: $q[\bar g=0]$;
   the pair multiset is $\{N_a(\bar g)+N_b(\bar g+\bar e_P)\}_{\bar g\in\mathbb F_q}$. Explicitly:
   ND+ND as in (ii)/(iii) below with $d=1$; DEG+ND ($\mu\ne0$): $\{3^{(q/2)},1^{(q/2)}\}$; DEEP+ND ($\mu\ne0$): $\{(q+1)^{(1)},1^{(q-1)}\}$;
   DEG+DEG ($\mu=0$): $\{2^{(q)}\}$; DEEP+DEEP ($\mu=0$): $\{2q^{(1)}\}$ if $\bar e_P=0$, else $\{q^{(2)}\}$.
2. (one class ND with $c_3=0$) $\{N_{\rm other}(g)+1:g\in R_d\}$; in particular ND+ND with $c_3=0$ gives $\{2^{(q^d)}\}$.
3. ND+ND, $c_3\ne0$: $\mu\ne0$: $\{4^{(q^d/4)},2^{(q^d/2)}\}$; $\mu=0$: $\{4^{(q^d/2)}\}$ if $\chi_\alpha(a)=0$, $\{2^{(q^d)}\}$ if $\chi_\alpha(a)=1$.
4. DEG+ND ($\mu\ne0$, $c_3\ne0$; the ND class $b$ has $w_\alpha(b)=\mu$), $d\ge2$:
   $d=2$: $\{2^{(q(q-1)/2)},(q+2)^{(q/2)},q^{(q/2)}\}$.
   $d\ge3$: with $S=S_{\rm deg}(d-2)$, $Z_S=q^{d-2}-|S|$ and $\kappa=\kappa_\alpha(a)\in\{0,1\}$:
   $2$ with multiplicity $\tfrac q2(q^{d-1}-q^{d-2})+(\tfrac q2-\kappa)\tfrac{q^{d-2}}2+\kappa Z_S$;
   $2q+2$ with multiplicity $(\tfrac q2-\kappa)\tfrac{q^{d-2}}2$; $2q$ with multiplicity $(\tfrac q2-1+\kappa)\tfrac{q^{d-2}}2$;
   and $qv+2\kappa$ for each $v\in S$.
   Here $\kappa=[\bar g^*+\bar e_P\in H_b]$, $H_b=\{\mu y+c_3y^2\}$, $\bar g^*=c_3y_*^2$ and $y_*$ is the unique residue
   whose child in the tree of class $a$ is again degenerate (Prop. 5(b)); intrinsically, $\kappa=1$ iff
   $T(x_a+2[y_*])\bmod 8$ is a value of $T$ on the class of $b$.
5. DEEP+ND with $c_3=0$ is case 2.
6. DEG+DEG ($\mu=0$), $d=2$: $\{2q^{(s_P)},q^{(2(q-s_P))}\}$ with
   $s_P=\#\{y\in\mathbb F_q:\sigma_a(y)+\sigma_b(y+y_e)+\sqrt{c_3\bar e_P}\,y+e_1=0\}\in\{0,1,2,q\}$, where
   $\sigma_x(y)=\overline{(\Phi_x([y])-[c_3y^2])/2}$ ($\Phi_x$ of Lemma 4, $x_b=x_a+\tau$), $y_e=\sqrt{\bar e_P/c_3}$, $e_P\equiv[\bar e_P]+2[e_1]\pmod4$.
7. Open: DEG+DEG ($\mu=0$) for $d\ge3$; DEEP+DEEP ($\mu=0=c_3$) for $d\ge2$.

**Consistency with the paper.** Put $d=0$ ($n=2$): every class gives one value $N=1$, a merged pair gives $2$;
for $j=k-2$ this is Theorem M4 ($q-s$ entries $q^{k-1}$, $s/2$ entries $2q^{k-1}$), and for $k=3$, $j=1$ it is
Theorem O3 ($B_\alpha(a)=0\iff \bar uA_F(a)+\bar u^2\mu=0$).

**Corollary D (flatness, lower bounds).** Let $1\le j\le k-3$.
1. Every nonzero entry of a row in $v_j$ is a multiple of $q^{j+1}$ and $\ge q^{j+1}$.
2. All nonzero entries of all rows of $v_j$ equal $q^{j+1}$ iff $c_3=0$, $\pi$ has no zero, and no pair is merged,
   i.e. $A_F$ zero-free (if $j\ge2$, or $j=1$ and $\mu=0$), resp. $A_F\equiv0$ (if $j=1$ and $\mu\ne0$).
   For $\mu\ne0$ and $k\ge5$ the layers $v_1$ and $v_2$ can therefore not both be flat (same incompatibility as
   O3 vs exceptional optimality).
3. If $c_3\ne0$ some class is ND, so some entry $\ge2q^{j+1}$.
4. If $w_\alpha$ has a zero and $c_3\ne0$, row $\alpha$ has an entry $\ge q^{\,j+1+\lfloor (k-j-2)/2\rfloor}$
   (regardless of merging). If $c_3\ne0$, such rows exist in $v_1$ for every lift ($\bar u=\pi(a)/c_3$ with $\pi(a)\ne0$),
   and in every $v_j$ if $\pi$ has a zero. So for $c_3\ne0$ the maximum over $v_1$ grows at least like $q^{(k+1)/2}$.
5. If a class is DEEP, the row has an entry $\ge q^{j+2}$.

**Corollary E ($P_{m,r}$).** (i) $r\ge5$: $c_3=0$, $\pi=1+X^w+X^u$ has no zero, $\mu=0$. Hence for $F^\sharp=F+2X^3$
(A zero-free) every row of every layer $v_j$, $1\le j\le k-2$, has all nonzero entries equal to $q^{j+1}$ (with M4 for
$j=k-2$). The natural lift ($A_F^{-1}(0)=\{0,1\}$) has $(q-2)q^{d}$ entries $q^{j+1}$ and $q^{d}$ entries $2q^{j+1}$.
(ii) $r=3$: $c_3=1$ and $\pi(1)=0$, so *every* lift has, in every $v_j$ ($1\le j\le k-3$), rows with entries
$\ge q^{j+1+\lfloor(k-j-2)/2\rfloor}$. For $F^\sharp$ and $j\ge2$ (unmerged, $\pi^{-1}(0)=\{1\}$ for $m=5,7$) the row is
$\{2q^{j+1}\ \text{with mult.}\ (q-1)q^d/2\}\uplus q^{j+1}S_{\rm deg}(d)$; e.g. $k=5,j=2$: $496\times 2q^3$, $32\times q^3$ (computed).

---------------------------------------------------------------------------------------------------

## 3. Proofs

Throughout $R=R_k$ and $\alpha=2^ju$, $1\le j\le k-3$, $n=k-j$, $d=n-2$.

### Lemma 1 (reduction)
$F(x+\alpha)-F(x)=\alpha T(x)$ with $T=T_\alpha:=\sum_{i\ge1}\alpha^{i-1}F^{[i]}\in R[X]$. Since $u$ is a unit,
$\alpha y=\alpha y'$ iff $y\equiv y'\pmod{2^n}$, so $\delta_F(\alpha,\beta)=0$ for $\beta\notin\alpha R$ and
$\delta_F(\alpha,\alpha\gamma)=\#\{x\in R:T(x)\equiv\gamma\ (2^n)\}=q^j\,\#\{y\in R/2^n:\ T(y)\equiv\gamma\ (2^n)\}$,
because $T(x)\bmod 2^n$ depends only on $x\bmod2^n$ and each class mod $2^n$ has $q^j$ elements. $\square$

### Lemma 2 (Hasse coefficients of $T$)
Use $(F^{[i]})^{[r]}=\binom{i+r}{r}F^{[i+r]}$ and $\overline{F^{[i]}}=p^{[i]}$. For quadratic reduced $p$:
$p^{[2]}=\pi$ (paper) and $p^{[3]}=c_3$: $\binom e3$ is odd iff $e\equiv3\pmod4$ (Lucas), and the only exponent
$2^a+2^b$ or $2^a$ with this property is $3$.
(i) $\bar T=p'$ (as functions), since $\alpha\in2R$.
(ii) $T'=\sum_{i\ge1}(i+1)\alpha^{i-1}F^{[i+1]}=2F^{[2]}+3\alpha F^{[3]}+\dots$ has all coefficients in $2R$; put
$W=T'/2=F^{[2]}+3\frac\alpha2F^{[3]}+\sum_{i\ge3}(i+1)\frac{\alpha^{i-1}}2F^{[i+1]}$. The last sum lies in $2R[X]$
($\alpha^{i-1}/2\in2^{2j-1}R$), and $\alpha/2=2^{j-1}u$. Hence $\overline{W(x)}=\pi(\bar x)+[j=1]\bar uc_3=w_\alpha(\bar x)$.
(iii) $T^{[2]}=3F^{[3]}+6\alpha F^{[4]}+\dots\equiv F^{[3]}\pmod2$, residue $c_3$.
(iv) $T^{[3]}=4F^{[4]}+10\alpha F^{[5]}+\sum_{i\ge3}\binom{i+3}3\alpha^{i-1}F^{[i+3]}\in4R[X]$. $\square$

### Lemma 3 (classes and pairs mod 4)
Let $\bar x=a$, $\bar\tau=\rho$. (i) $T(x+2z)\equiv T(x)\pmod 4$. (ii) $T(x+\tau)-T(x)\equiv2[B_\alpha(a)]\pmod4$.
Hence two residues give values in the same coset of $4R$ only if they are equal or form a pair, and a pair has its
two classes in the same coset of $4R$ iff $B_\alpha(a)=0$.

*Proof.* (i) $T(x+2z)-T(x)=2zT'(x)+4(\dots)$ and $T'\in2R[X]$. (ii) $T(x+\tau)-T(x)=[F'(x+\tau)-F'(x)]+\alpha[F^{[2]}(x+\tau)-F^{[2]}(x)]+\sum_{i\ge3}\alpha^{i-1}[\dots]$.
The first bracket is $\equiv2[A_F(a)]$ (definition of $A_F$, paper Lemma A). The second term is $\equiv0$ mod 4 if
$j\ge2$, and for $j=1$ it is $2u\cdot(\text{element with residue }\pi(a+\rho)-\pi(a)=\mu)\equiv2[\bar u\mu]$. The rest lies in $\alpha^2R\subseteq4R$.
By (i) the left side mod 4 does not depend on the lifts, so $B_\alpha$ is well defined. Since $\bar T=p'$ is exactly
two-to-one on pairs, different pairs never meet. $\square$

### Lemma 4 (local expansion; admissibility)
For $\bar x=a$: $T(x+2z)=T(x)+4\Phi_x(z)$ with
$\Phi_x(z)=W(x)z+T^{[2]}(x)z^2+\sum_{r\ge3}2^{r-2}T^{[r]}(x)z^r$. Its coefficients satisfy $\varphi_3=2T^{[3]}(x)\in8R$,
$\varphi_r\in4R$ ($r\ge4$), $\varphi_r\in8R$ (odd $r\ge5$). Its residue is $\bar\Phi_x(y)=w_\alpha(a)y+c_3y^2$ (Lemma 2).

Call a polynomial $\Phi=\sum\varphi_rz^r$ **admissible** if $\varphi_r\in2R$ for all $r\ge3$ and $\varphi_r\in4R$ for
odd $r\ge3$. Every $\Phi_x$ is admissible, and so is $\Phi_x/2$ when $\Phi_x\in2R[z]$ (DEEP case).

*Proof.* Taylor expansion $T(x+h)=\sum_r h^rT^{[r]}(x)$ with $h=2z$, Lemma 2. For the DEEP case, $\Phi_x/2$ has
coefficients $\varphi_r/2$: $\varphi_3/2\in4R$, $\varphi_r/2\in2R$ ($r\ge4$), $\varphi_r/2\in4R$ (odd $r\ge5$). $\square$

### Proof of Theorem A
By Lemma 1, $\delta_F(\alpha,\alpha\gamma)=q^j\#\{y\in R/2^n:T(y)=\gamma\}$. A solution has residue $a$ with
$p'(a)=\bar\gamma$, i.e. $a$ in one pair $P$. On the class of $a$, $y=x_a+2z$ with $z$ mod $2^{n-1}$, and
$T(x_a+2z)=\gamma$ iff $\gamma\equiv T(x_a)\pmod4$ and $\Phi_{x_a}(z)\equiv g\pmod{2^d}$, $g=(\gamma-T(x_a))/4\in R/2^d$.
The left side depends on $z$ mod $2^d$, and $z$ mod $2^{n-1}=2^{d+1}$ has $q$ lifts, so the class contributes
$q\,N_a(g)$, $N_a(g)=\#\{z\bmod2^d:\Phi_{x_a}(z)\equiv g\}$. For fixed $\bar\gamma$ there are $q\cdot q^d$ values of
$\gamma$ mod $2^n$; the class of $a$ is reached by the $q^d$ values with $\gamma\equiv T(x_a)$ (4), parametrized
bijectively by $g\in R/2^d$. By Lemma 3 the two classes of $P$ use disjoint sets of $\gamma$ if $B_\alpha(a)\ne0$,
and the same set if $B_\alpha(a)=0$, in which case $g_b=g+e_P$. $\square$

### Proposition 5 (Hensel tree of an admissible $\Phi$)
Let $\Phi$ be admissible over a Galois ring $R$ with residue $\psi(y)=wy+cy^2$, $d\ge1$, and
$N_\Phi(g)=\#\{z\bmod2^d:\Phi(z)\equiv g\ (2^d)\}$.

(a) If $w\ne0$: $N_\Phi(g)=\#\psi^{-1}(\bar g)$. Hence $\{1^{(q^d)}\}$ if $c=0$ and $\{2^{(q^d/2)},0^{(q^d/2)}\}$ if $c\ne0$.

(b) If $w=0\ne c$: for $d=1$, $N_\Phi\equiv1$. For $d\ge2$ let $y_g$ be the unique root of $cy^2=\bar g$ and $\hat y$ any lift.
Then $\Phi(\hat y+2z)=\Phi(\hat y)+4\Phi_1(z)$ with $\Phi_1$ admissible, residue $(\lambda+cy_g)y+cy^2$, $\lambda=\overline{\varphi_1/2}$, and
$N_\Phi(g)=q\,[\Phi(\hat y)\equiv g\ (4)]\,N_{\Phi_1}\big((g-\Phi(\hat y))/4\big)$ (depth $d-2$; depth 0 means $N=1$).

(c) If $w=0\ne c$ the multiset $\{N_\Phi(g):g\in R/2^d\}$ equals $S_{\rm deg}(d)$ (completed by zeros).

(d) If $w=c=0$ and $\Phi/2$ is admissible with residue $w'y+c'y^2$: $N_\Phi(g)=[\bar g=0]\,q\,N_{\Phi/2}(g/2)$ at depth $d-1$.

*Proof.* (a) $\Phi'(z)=\varphi_1+2\varphi_2z+\sum_{r\ge3}r\varphi_rz^{r-1}\equiv w\pmod2$ is a unit, so every residue root lifts
uniquely to a root mod $2^d$ (if $\Phi(z_0)\equiv g$ mod $2^e$, $e\ge1$, then $\Phi(z_0+2^eh)\equiv\Phi(z_0)+2^eh\Phi'(z_0)$
mod $2^{e+1}$, which fixes $\bar h$ uniquely). The image of $y\mapsto wy+cy^2$ ($c\ne0$) is
$(w^2/c)\{t+t^2\}=(w^2/c)\ker\mathrm{Tr}$, of size $q/2$, each value twice.

(b) $\Phi(\hat y+2z)=\Phi(\hat y)+2z\Phi'(\hat y)+4z^2\Phi^{[2]}(\hat y)+\sum_{s\ge3}2^sz^s\Phi^{[s]}(\hat y)$. Since $w=0$,
$\varphi_1\in2R$, and $\varphi_r\in2R$ ($r\ge3$), so $\Phi'(\hat y)\in2R$ and $\Phi_1(z)=\frac{\Phi'(\hat y)}2z+\Phi^{[2]}(\hat y)z^2+\sum_{s\ge3}2^{s-2}\Phi^{[s]}(\hat y)z^s$.
Admissibility: $\Phi^{[3]}(\hat y)=\sum_{r\ge3}\binom r3\varphi_r\hat y^{r-3}\in2R$, so the $z^3$ coefficient is in $4R$;
for $s\ge4$, $2^{s-2}\in4R$. Residues: $\Phi^{[2]}(\hat y)\equiv\varphi_2\equiv c$; $\Phi'(\hat y)/2=\varphi_1/2+\varphi_2\hat y+\sum_{r\ge3}\frac{r\varphi_r}2\hat y^{r-1}$
and $r\varphi_r/2\in2R$ for every $r\ge3$ (odd $r$: $\varphi_r\in4R$; even $r$: $(r/2)\varphi_r$), so the residue is $\lambda+cy_g$.
Counting: the residue of a solution must be $y_g$ ($cy^2$ is bijective); write $z=\hat y+2z'$, $z'$ mod $2^{d-1}$.
Then $\Phi(z)\equiv g$ (mod $2^d$) iff $\Phi(\hat y)\equiv g$ (mod 4) and $\Phi_1(z')\equiv(g-\Phi(\hat y))/4$ (mod $2^{d-2}$); the latter depends
on $z'$ mod $2^{d-2}$, which has $q$ lifts mod $2^{d-1}$. For $d=1$ only the residue condition remains.

(c) Induction on $d$; $d=1$: $\{1^{(q)}\}$. $d\ge2$: for each of the $q$ residues $\bar g$ exactly one of the $q$ values of
$g$ mod 4 above it satisfies $\Phi(\hat y)\equiv g$, and then $g'=(g-\Phi(\hat y))/4$ runs bijectively over $R/2^{d-2}$
($q^{d-2}$ targets); the other $q^{d-1}-q^{d-2}$ targets above $\bar g$ get $0$. The child's linear residue $\lambda+cy_g$
vanishes for exactly one $y_g$, i.e. one residue $\bar g$; that child has multiset $S_{\rm deg}(d-2)$ (induction), the other
$q-1$ children are of type (a) with $c\ne0$. So $S_{\rm deg}(d)=q\cdot S_{\rm deg}(d-2)\uplus(q-1)\,q\cdot S_{\rm nd}(c\neq0,d-2)$.
Unfolding $t=\lfloor d/2\rfloor$ times gives the closed form (for $d$ even the last unfolding produces $(q-1)$ copies of
$q^t\cdot\{1\}$ plus $q^t\cdot S_{\rm deg}(0)=\{q^t\}$, i.e. $q^t$ with multiplicity $q$; for $d$ odd the tail is $q^t\cdot S_{\rm deg}(1)$).
Checked mechanically against the recursion for $q\in\{8,32,128\}$, $d\le11$ (`closedforms.py`, `predict.py`).

(d) $\Phi(z)\equiv g\ (2^d)$ iff $g\in2R$ and $\Phi(z)/2\equiv g/2\ (2^{d-1})$; the latter depends on $z$ mod $2^{d-1}$, $q$ lifts. $\square$

### Proof of Theorem B
Apply Prop. 5 to $\Phi_{x_a}$ (Lemma 4): ND $\Rightarrow$ (a); DEG $\Rightarrow$ (c). DEEP: $\bar\Phi_{x_a}\equiv0$, so
$\Phi_{x_a}=2\tilde\Phi$ with $\tilde\Phi$ admissible (Lemma 4) and residue $w'y+c'y^2$, where
$c'=\overline{T^{[2]}(x)/2}=\overline{F^{[3]}(x)/2}$ (from $T^{[2]}=3F^{[3]}+6\alpha F^{[4]}+\dots$, $F^{[3]}(x)\in2R$ since $c_3=0$) and
$w'=\overline{W(x)/2}=\overline{F^{[2]}(x)/2}+[j=1]\bar u\,\overline{F^{[3]}(x)/2}$ (from the formula for $W$ in Lemma 2: the term
$3\frac\alpha4F^{[3]}$ is $3u\cdot F^{[3]}/2$ for $j=1$ and lies in $2R$ for $j\ge2$; the terms $i\ge3$ lie in $2R$).
Independence of the lift $x$: $T^{[2]}(x+2z)\equiv T^{[2]}(x)$ (mod 4) because $T^{[3]}\in4R$, and
$W(x+2z)\equiv W(x)+2zT^{[2]}(x)\equiv W(x)$ (mod 4) because $T^{[2]}(x)\in2R$ here. Then Prop. 5(d), followed by (a) or (c)
for $\tilde\Phi$ at depth $d-1$. For $d=1$: $N(g)=q[\bar g=0]$. $\square$

### Proof of Theorem C
By Theorem A the merged multiset is $\{N_a(g)+N_b(g+e_P)\}$.
(1) For $d=1$, Prop. 5 shows $N_x(g)$ depends on $\bar g$ only, with the stated values; the explicit lists follow:
DEG+ND needs $\mu\ne0$ ($w_b=w_a+\mu$), gives $1+2[\bar g+\bar e\in H_b]$, $|H_b|=q/2$; DEEP+ND gives $q[\bar g=0]+1$;
DEG+DEG gives $1+1$; DEEP+DEEP gives $q[\bar g=0]+q[\bar g=\bar e]$.
(2) An ND class with $c_3=0$ has $N\equiv1$ (Prop. 5(a)).
(3) $N_a(g)+N_b(g+e)=2[\bar g\in H_a]+2[\bar g+\bar e\in H_b]$ with $H_x=(w_x^2/c_3)\ker\mathrm{Tr}$. For $\mu\ne0$,
$w_b^2\ne w_a^2$ and $H_a\ne H_b$ are distinct hyperplanes: $\bar g$ lies in both for $q/4$ residues and in exactly one
for $q/2$ residues, each residue carrying $q^{d-1}$ targets. For $\mu=0$, $H_a=H_b=H$ and the two conditions coincide iff
$\bar e\in H$, i.e. $\mathrm{Tr}(c_3\bar e/w^2)=0$. (Well-definedness of $\chi_\alpha$: the two alternatives give different
multisets, so $\chi_\alpha$ is determined by the row; it does not depend on the choice of $x_a,\tau$.)
(4) $\mu\ne0$, $w_a=0$: class $b$ is ND with $w_b=\mu$, so $N_b(g+e)=2h(\bar g)$, $h(\bar g)=[\bar g+\bar e\in H_b]$ ($q/2$ residues
have $h=1$). Class $a$ by Prop. 5(b): above each residue $\bar g$, $q^{d-1}-q^{d-2}$ targets have $N_a=0$ and $q^{d-2}$ targets
carry $q\cdot$(child multiset at depth $d-2$). For $d=2$ every child gives $\{1\}$: values $2h$ ($(q-1)$ per residue),
$q+2h$ (one per residue). For $d\ge3$ the $q-1$ ND children give $\{2^{(q^{d-2}/2)},0^{(q^{d-2}/2)}\}$ and the DEG child
(residue $\bar g^*$) gives $S_{\rm deg}(d-2)$; adding $2h(\bar g)$ and counting residues with $h=1$ / $h=0$ (with $\bar g^*$ in
the class $h=\kappa$) gives the list. (Mechanical check of the closed form vs the per-residue construction: `closedforms.py`.)
The intrinsic description of $\kappa$: $\bar g^*$ corresponds to $T(x_a+2[y_*])$ mod 8, and $h(\bar g^*)=1$ iff that value is
attained (mod 8) by $T$ on the class of $b$, because $T$ on class $b$ mod 8 is $T(x_b)+4\psi_b$.
(6) $d=2$, both DEG ($\mu=0$). Mod 4, $\Phi_x([y])\equiv\varphi_1[y]+\varphi_2[y]^2$ ($\varphi_r\in4R$ for $r\ge3$).
Write $\varphi_1=2\varphi_1'$, $\varphi_2=[c_3]+2\varphi_2''$; then $\Phi_x([y])\equiv[c_3y^2]+2[\lambda_xy+\nu_xy^2]$ with
$\lambda_x=\bar\varphi_1'$, $\nu_x=\bar\varphi_2''$, i.e. $\sigma_x(y)=\lambda_xy+\nu_xy^2$. Write $g\equiv[\bar g]+2[g_1]$ mod 4. Class $a$ hits
$g$ (with $N_a=q$) iff $g_1=\sigma_a(y_g)$. Witt addition in $R/4$: $[s]+[t]\equiv[s+t]+2[\sqrt{st}]$, so
$g+e\equiv[\bar g+\bar e]+2[g_1+e_1+\sqrt{\bar g\bar e}]$ and class $b$ hits iff $g_1+e_1+y_g\sqrt{c_3\bar e}=\sigma_b(y_g+y_e)$.
Both hit the same $g$ iff $y=y_g$ solves the stated equation, which is $\mathbb F_2$-affine in $y$
($(\lambda_a+\lambda_b+\sqrt{c_3\bar e})y+(\nu_a+\nu_b)y^2+\sigma_b(y_e)+e_1=0$), so $s_P\in\{0,1,2,q\}$. Per residue: coincidence gives one
target with $N=2q$, otherwise two targets with $N=q$. $\square$

### Proof of Corollary D
(1) Theorem A. (2) $N=1$ throughout iff every pair is split and every class multiset is $\{1^{(\cdot)}\}$: by Theorem B this
excludes ND with $c_3\ne0$ (value 2), DEEP (value $\ge q$), and DEG unless $d=1$; but if $c_3\ne0$ then $w_\alpha$ is a
nonconstant affine map, so some class is ND with value 2. Hence $c_3=0$ and $\pi$ zero-free; merging gives values
$\ge2$ (Thm C(2)). The merging condition: $B_\alpha=A_F$ ($j\ge2$ or $\mu=0$); for $j=1$, $\mu\ne0$, $B_\alpha(a)=0$ for
$\bar u=A_F(a)/\mu$ whenever $A_F(a)\ne0$. (3) as just said. (4) Pigeonhole along the degenerate path: by Prop. 5(b)
there is a chain of $t=\lfloor d/2\rfloor$ degenerate nodes; fixing the $t$ corresponding $2$-adic digits of $z$ leaves
$q^{\,n-1-t}$ points of the class on which $T$ is constant mod $2^{2t+2}$ ($T=T(x)+4\Phi$, $\Phi$ constant mod $4^t$). A coset
of $2^{2t+2}R_n$ has $q^{n-2t-2}$ elements, so some $\gamma$ has $\ge q^{t+1}$ preimages, i.e. an entry $\ge q^{j+1+t}$; extra
solutions from the partner class only increase it. (5) DEEP: $T\equiv T(x)$ mod 8 on the class ($q^{n-1}$ points, cosets of
size $q^{n-3}$), so an entry $\ge q^j q^2$. $\square$

### Proof of Corollary E
(i) $p$ for $r\ge5$ has no monomial $X^3$ ($w,u\ge8$); $\pi=p^{[2]}=1+X^w+X^u$ (paper, Prop. I123(ii)) and
$\pi(a)=0$ would give $\mathrm{Tr}(a^w)+\mathrm{Tr}(a^u)=0\ne\mathrm{Tr}(1)$. $\mu=0$, $A_{F^\sharp}$ zero-free, and for the natural lift
$A_F^{-1}(0)=\{0,1\}$ (paper). Apply Theorem A, B(1), C(2). (ii) $r=3$: $c_3=1$, $\pi=1+X+X^u+X^v$, $\pi(1)=0$; Corollary D(4).
For $m=5,7$ the linear part of $\pi$ is bijective (computed, `pinv.py`), so $\pi^{-1}(0)=\{1\}$. $\square$

---------------------------------------------------------------------------------------------------

## 4. What the answer looks like (case split)

| $c_3$ | $\pi$ zeros | merging | row of $v_j$ (values $/q^{j+1}$) |
|---|---|---|---|
| $0$ | none | none | all $1$ (flat optimum $q^{j+1}$) |
| $0$ | none | $s_\alpha>0$ | $1$ and $2$: $(q-s_\alpha)q^d$ ones, $\frac{s_\alpha}2q^d$ twos (as M4, times $q^{d}$) |
| $\ne0$ | $w_\alpha$ zero-free | none | all $2$ |
| $\ne0$ | $w_\alpha$ zero-free | merged ND+ND | $2,4$ (Thm C(3)) |
| $\ne0$ | $w_\alpha$ has zeros | any | universal tree $S_{\rm deg}(d)$: values up to $\max(2q^{\lfloor(d-1)/2\rfloor},q^{\lfloor d/2\rfloor})$ |
| $0$ | zeros | any | DEEP: values $\ge q$ |

The *case split in $j$* is: $j=1$ ($\bar u$ enters $w_\alpha$ through $c_3$ and $B_\alpha$ through $\mu$) versus $j\ge2$ (row
data independent of $u$); and the depth $d=k-j-2$ (parity of $d$ decides the top value of $S_{\rm deg}$, $d=1$ makes all
merged pairs residue-level, $d\le2$ makes $\kappa$ irrelevant).

---------------------------------------------------------------------------------------------------

## 5. Computational method

* `redspec2.c` (C, single-threaded): exhaustive row spectrum using only Lemma 1 (enumerate $y\in R/2^n$, compute
  $(F(y+\alpha)-F(y))/2^j$ in $R_k$, histogram, multiply by $q^j$). `rowspec.c`: full-table brute force over all of
  $R_k$ (no reduction). They agree on every cross-checked row (`crosscheck.py`: 8 lifts x 8 rows at $k=4$, $j=1,2,3$,
  `crosscheck_k4.json`; plus 2 rows at $k=5$, 1 row at $k=6$ in the session log).
* `predict.py`: computes the row invariants ($w_\alpha$, $c_3$, $B_\alpha$, $e_P$, $\chi$, $\kappa$, $w',c'$, $s_P$) from
  $O(q)$ evaluations of $F$ and assembles the multiset of Theorems A–C. It also checks Lemma 2(ii)/(iii)
  ($w_\alpha=\pi+[j=1]\bar uc_3$, quadratic coefficient $=c_3$) and Lemma 3 ($B_\alpha=A_F+[j=1]\bar u\mu$, $A_F$ computed
  independently mod 8) on every row: **0 check failures** in the final data.
* `closedforms.py`: closed forms of $S_{\rm deg}$ and of Thm C(4) vs the recursions ($q=8,32,128$, $d\le11$ / $d\le8$).
* Lifts (`lifts/`, index `lifts/index.json`): 17 residue representatives over $\mathbb F_{32}$ ($t^5=t^2+1$): one random
  representative $L(A(x)^3)$ for each of the 14 realised combinations of ($\mu=0$?, $c_3=0$?, $\pi$ has zero?, $Z\ne\emptyset$?)
  (`search_reps.py`, `reps_m5.json`; all 16 combinations except two occur) plus $P_{5,3}$, `c1`, `rep5` of r07. For each: natural
  0/1 lift, $A_F\equiv1$, $A_F\equiv0$, $A_F$ with one zero pair (all via Prop. Acontrol), and two random $2(\cdot)+4(\cdot)$
  perturbations: 102 lifts. Plus $m=7$ term files of r07 (none completed in time, see §6).
* Note: $m=3$ is impossible: exhaustive search shows **no** quadratic APN permutation of $\mathbb F_8$ has zero-free $p'$
  (`m3exh.py`), so (H) never holds for $m=3$.

## 6. Verification coverage (`summary.json`, raw rows in `res_k4.jsonl`, `res_k5.jsonl`, `res_k6_targeted.jsonl`, `res_k7_targeted.jsonl`)

691 rows, 108 lifts (102 test lifts; all $m=5$), every row exhaustive:

| k | j | d | rows | MATCH | UNPREDICTED (declared open) | MISMATCH |
|---|---|---|---|---|---|---|
| 4 | 1 | 1 | 235 | 235 | 0 | 0 |
| 5 | 1 | 2 | 231 | 230 | 1 (DEEP+DEEP, $d=2$) | 0 |
| 5 | 2 | 1 | 216 | 216 | 0 | 0 |
| 6 | 1 | 3 | 1 | 1 | 0 | 0 |
| 6 | 3 | 1 | 1 | 1 | 0 | 0 |
| 7 | 2 | 3 | 7 | 6 | 1 (DEG+DEG, $\mu=0$, $d=3$) | 0 |

Rows at $j=1$ were chosen per lift to hit every realised combination of (w has zero, pair merged, merged pair degenerate) as
$\bar u$ varies. Four $k=5$ rows were first graded MISMATCH; the brute spectrum equalled the prediction except that the predictor
listed a value with multiplicity 0 (Thm C(6) with $s_P=0$); re-graded MATCH and the predictor fixed (noted in the JSON).

Coverage by local type (rows containing that type, $k\ge5$ rows; the $k=4$ rows were run before type labels were recorded but
all 235 match): split ND $c_3=0$: 113; split ND $c_3\ne0$: 167; split DEG: 90; split DEEP: 58 (DEEP with $w'\ne0$: 35 rows,
with $w'=0\ne c'$: 2 rows); merged ND+ND ($\mu\ne0$, $\mu=0$, $c_3=0$ variants, $d=1,2,\ge3$): 141; merged DEG+ND
($\mu\ne0$): $d=1$: 4, $d=2$: 9, $d=3$: 3 (with $\kappa=0$ once and $\kappa=1$ twice); merged DEEP+ND: 14; merged DEG+DEG
$\mu=0$: $d=1$: 4, $d=2$: 14 ($s_P\in\{0,1,2\}$ all seen; $s_P=q$ not seen); merged DEEP+DEEP $d=1$: 2.
Corollary E(ii) instance: $P_{5,3}$ with $A\equiv1$, $k=5,j=2$: $496\times2q^3$, $32\times q^3$; $k=7,j=2$: $507904\times2q^3,\ 496\times2q^4,\ 32\times q^4$ (matches $q^{3}S_{\rm deg}(3)$).
Corollary E(i) ($P_{7,5}$, $m=7$): **not run by me** (killed for time); the coordinator independently reports $k=4,j=1$: $F^\sharp$ flat
($16384\times q^2$) and natural lift $128\times2q^2$, $16128\times q^2$, which is exactly $(q-2)q^d$ and $q^d$ with $d=1$.

**Not covered computationally:** $d\ge4$ at all; $d=3$ only 9 rows; DEEP with $w'=0\ne c'$ at $d\ge3$; $m\ge7$ except the
coordinator's check; Thm C(6) with $s_P=q$.

## 7. Open sub-cases (no closed formula claimed)

1. **Merged DEG+DEG** ($\mu=0$, $c_3\ne0$, $A_F(a)=0=w_\alpha(a)$) for $d\ge3$. Explicit for $d=1,2$ (Thm C(1),(6)). Observed
   example ($r1010\_A0$, $k=7$, $j=2$): the row is $\{262144\times 2q^3,\ 114688\times4q^3,\ 64\times q^4,\ 976\times2q^4,\ 8\times4q^4\}$, i.e. the DEG+DEG pair produces values up to $4q^{j+2}$; the joint
   tree couples two degenerate Hensel trees through an $\mathbb F_2$-affine coincidence condition at every level, and I have not
   derived its general multiset. Avoided by any lift with $A_F$ zero-free (the optimal choice when $\mu=0$).
2. **Merged DEEP+DEEP** ($\mu=0=c_3$, $A_F(a)=0=\pi(a)$) for $d\ge2$. Explicit for $d=1$. One observed row ($k=5$).
3. **Single (split) DEEP class with $w'_\alpha(a)=c'(a)=0$**, $d\ge2$: open. Then $\Phi_x/2$ has zero residue and
   $\Phi_x/4$ need not be admissible (the $z^4$ coefficient $T^{[4]}$ is only known to be a unit-or-not), so the recursion
   of Prop. 5 does not apply as stated. Never observed in the data (all 37 DEEP sub-cases had $w'\ne0$ or $c'\ne0$). Lower bound
   of Cor. D(5) still holds. The same applies to such a class inside a merged pair (Thm C(2)).
4. Merged DEG+ND: proved for all $d$; $\kappa$ is defined via the degenerate child; I have no formula for $\kappa$ in terms of
   $A_F$, $E_F$ etc.; likewise $s_P$ and $\chi_\alpha$ are given intrinsically (from $T$ at $O(q)$ points), not in terms of
   coefficients of $F$.
5. Whether $\pi^{-1}(0)=\{1\}$ for $P_{m,3}$ at all odd $m$ (checked $m=5,7$) — only affects the exact form in Cor. E(ii), not the bound.

In all open cases the lower bounds of Corollary D hold, and every entry is a multiple of $q^{j+1}$.

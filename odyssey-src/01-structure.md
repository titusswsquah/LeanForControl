<!-- lem:structure — structure of Sigma+ under C3w: the uncontrollable block is antistable-only, so -->
<!-- Sigma+|22 = Sigma+|aa > 0 is nonsingular, its information is the steady A_a^{-1}-gramian, F_inf is Schur. -->
<!-- Plus uniform boundedness and antistable positivity along the recursion. No marginal block here. -->
<!-- lem:structure -->
### Lemma (lem:structure) — Structure of the strong solution, boundedness, antistable positivity

Let C1 and C3w hold. The strong solution $\Sigma_\infty$ of `eq:dare` exists and is unique (`fact:dare-strong`); in the frame `eq:three-block` the uncontrollable block is antistable-only ($e_2 = e_a$, $n_m = 0$):

<!-- lem:structure-1 -->
**1. (Uncontrollable block positive definite; the error map is Schur.)**

<!-- eq:Sinf-struct -->
$$ \Sigma_\infty\!\mid_{aa} \succ 0 \qquad\text{(the entire uncontrollable block)} \tag{eq:Sinf-struct} $$

and the antistable information is the steady $A_a^{-1}$-gramian

<!-- eq:Sinf-gram -->
$$ (\Sigma_\infty\!\mid_{aa})^{-1} = \sum_{j=0}^{\infty} \big(A_a^{-j}\big)'\, W_\infty\!\mid_{aa}\, A_a^{-j} \qquad W_\infty\!\mid_{aa} := (\Sigma_\infty\!\mid_{aa})^{-1} - A_a^{-1\prime}(\Sigma_\infty\!\mid_{aa})^{-1} A_a^{-1} \succeq 0 \tag{eq:Sinf-gram} $$

a finite sum, since $A_a^{-1}$ is Schur (`eq:A2-inv`). From this the strong error map $F_\infty = A(I - L_\infty C)$, $L_\infty := \Sigma_\infty C'(C\Sigma_\infty C' + R)^{-1}$, has the spectrum `eq:Finf-spec` (Fact 1),

$$ \operatorname{spec}(F_\infty) = \operatorname{spec}(A_c)\ \cup\ \{\,\lambda^{-1} : \lambda \in \operatorname{spec}(A_a)\,\} $$

— the stabilizable closed loop ($A_c$, Schur) and the antistable spectrum **reflected** inside the disk ($A_a \mapsto A_a^{-1}$). Both parts are strictly inside, so **$F_\infty$ is Schur**, $\rho(F_\infty) < 1$ — the stabilizing solution (`def:stab`, `eq:Finf-c3w`).

<!-- lem:structure-2 -->
**2. (Uniform boundedness.)** For every prior $\Sigma_0$ the iterates are bounded,

<!-- eq:bounded -->
$$ \sup_{T \ge 0}\, \Sigma_T(\Sigma_0) \preceq \bar\Pi(\Sigma_0) < \infty \tag{eq:bounded} $$

<!-- lem:structure-3 -->
**3. (Antistable positivity along the recursion.)** If $\Sigma_{0}\!\mid_{aa} \succ 0$, then $\Sigma_T\!\mid_{aa} \succ 0$ for all $T$, so the antistable information $J_T^{aa} := (\Sigma_T\!\mid_{aa})^{-1}$ is well defined.

*Proof.*

**Part 1.** $\Sigma_\infty\succeq0$ is the strong solution (`fact:dare-strong`). Under C3w the uncontrollable block carries only antistable modes, so $\Sigma_\infty\!\mid_{22} = \Sigma_\infty\!\mid_{aa}$, and no singular marginal sub-block appears. By Fact 1 (`eq:Finf-spec`, imported) the antistable spectrum of $F_\infty$ is the reflection $\{\lambda^{-1}:\lambda\in\operatorname{spec}(A_a)\}$, strictly inside the unit disk; the reflection is effected by the gain $L_\infty$ on the antistable block, so a direction $v\in\ker(\Sigma_\infty\!\mid_{aa})$ would be left uncorrected and contribute an eigenvalue $\lambda$, $|\lambda|>1$, forcing $\rho(F_\infty)>1$ and contradicting Fact 1's $\rho(F_\infty)\le1$. Hence $\Sigma_\infty\!\mid_{aa}\succ0$, and its information $J_\infty^{aa}:=(\Sigma_\infty\!\mid_{aa})^{-1}$ is well defined. Because $A_2=A_a$ here, the $e_2$-fixed-point identity (`app:machinery`-2, $GQG'\!\mid_{22}=0$) reads $\Sigma_\infty\!\mid_{aa}=A_a\,\mathcal U(\Sigma_\infty)\!\mid_{aa}\,A_a'$; inverting (both sides $\succ0$, $A_a$ nonsingular) gives $J_\infty^{aa}=A_a^{-1\prime}J_\infty^{aa}A_a^{-1}+W_\infty^{aa}$, where $W_\infty^{aa}:=J_\infty^{aa}-A_a^{-1\prime}J_\infty^{aa}A_a^{-1}$. This $W_\infty^{aa}\succeq0$ because the measurement update **contracts** the block, $\mathcal U(\Sigma_\infty)\!\mid_{aa}\preceq\Sigma_\infty\!\mid_{aa}$, so $(\mathcal U(\Sigma_\infty)\!\mid_{aa})^{-1}\succeq J_\infty^{aa}$ and therefore $J_\infty^{aa}\succeq A_a^{-1\prime}J_\infty^{aa}A_a^{-1}$. Since $A_a^{-1}$ is Schur (`eq:A2-inv`), the relation unrolls to the convergent steady gramian `eq:Sinf-gram` (a finite sum), and observability of the antistable mode (C1) keeps the injection — hence $J_\infty^{aa}$ — positive definite. The stabilizable diagonal block of $F_\infty$ is $A_c$, Schur by the strong-solution gain; with the antistable modes reflected inside and no marginal block, $\rho(F_\infty)<1$.

**Part 2.** Detectability (C1) is exactly the existence of a fixed gain $L$ with $A - LC$ Schur. The fixed-gain observer with that $L$, seeded at $\Sigma_0$, is one admissible estimator of $x(T)$ from $\{y_0,\dots,y_T\}$; its error covariance $\Pi_T$ obeys the linear Lyapunov recursion $\Pi_{T+1} = (A - LC)\Pi_T(A - LC)' + LRL' + GQG'$, $\Pi_0 = \Sigma_0$, which converges ($A - LC$ Schur, `fact:schur-decay`), so $\Pi_T \preceq \bar\Pi < \infty$. By `fact:filter-opt` the Kalman filter is the minimum-covariance estimator, so $\Sigma_T \preceq \Pi_T \preceq \bar\Pi$ for all $T$ — this is `eq:bounded`.

**Part 3.** The antistable block obeys $\Sigma_{T+1}\!\mid_{aa} = A_a\,\mathcal{U}(\Sigma_T)\!\mid_{aa}\,A_a'$ (the unconditional $(a,a)$-block identity of `app:machinery`-2, valid for every $\Sigma\succeq0$). By `fact:update-kernel`, $\Sigma_T\!\mid_{aa}\succ0 \Rightarrow \mathcal{U}(\Sigma_T)\!\mid_{aa}\succ0$ — the diagonal sub-block alone drives the conclusion, no full positive-definiteness of $\Sigma_T$ being required. With $A_a$ nonsingular, $\Sigma_{T+1}\!\mid_{aa}\succ0$. Since $\Sigma_0\!\mid_{aa}\succ0$, induction gives the claim. ∎

<!-- verify: under C3w Sigma+|22 = Sigma+|aa > 0 is NONSINGULAR (no marginal block), so the whole-block information J_inf = (Sigma+|22)^{-1} = J^aa is well-defined — the P3 conflation cannot arise here. Sigma+|aa>0 from the imported spectrum eq:Finf-spec (a kernel direction stays unreflected => rho(F_inf)>1, contra Fact 1); gramian eq:Sinf-gram with W_inf^aa>=0 from the U-contraction. F_inf Schur (spec A_c inside + reflected A_a^{-1} inside, no marginal). check_a03.py [A],[C] residual 3e-16; check_structure_p3.py min eig Saa=8.87>0, antistable eig 2 -> 0.5 reflected, rho(F_inf)=0.5<1. Boundedness = optimal <= fixed stabilizing observer (C1). -->
<!-- verify: LIVE consumers — lem:structure-1 (F_inf Schur, eq:Sinf-struct/eq:Sinf-gram) feeds thm:formula, lem:sysinterp, thm:sufficiency, thm:payoff; eq:bounded feeds thm:formula (finite-T denominator nonsingularity) and thm:sufficiency (sup||M_T^-1||<inf, early T). The retired anchors also read eq:bounded/eq:Sinf-gram/Part 3 — that path is dead. Necessity (Sigma+|aa>0 as its lever) is flagged open. Marginal case (Sigma+|mm=0) is lem:structure-marg below. -->

<!-- lem:structure-marg — MARGINAL structure of Sigma+ (Arc 2, n_m>=1): extinction Sigma+|_{.m}=0, so -->
<!-- Sigma+|22 = diag(Sigma+|aa, 0) with Sigma+|aa > 0; F_inf carries spec(A_m) on the unit circle (rho=1), -->
<!-- F_inf|_{e1+a} Schur. Separated from lem:structure (C3w) for confinement: C3w consumers cite lem:structure, -->
<!-- marginal consumers (03 C2w criterion, 05 squeeze limit, 06b-C necessity) cite this. -->
<!-- lem:structure-marg -->
### Lemma (lem:structure-marg) — Marginal structure of the strong solution

Let C1 hold and let a marginal block be present, $n_m \ge 1$, in the frame `eq:three-block` ($A_2 = A_a \oplus A_m$, $|\lambda(A_m)| = 1$). Then the strong solution **extinguishes on the marginal directions**,

<!-- eq:marg-extinct -->
$$ \Sigma_\infty\!\mid_{\cdot\, m} = 0, \qquad\text{hence}\qquad \Sigma_\infty\!\mid_{22} = \begin{bmatrix} \Sigma_\infty\!\mid_{aa} & 0 \\ 0 & 0 \end{bmatrix}, \quad \Sigma_\infty\!\mid_{aa} \succ 0, \tag{eq:marg-extinct} $$

and its error map carries the marginal spectrum on the unit circle, unreflected, Schur off it:
$$ \operatorname{spec}(F_\infty) = \Lambda_{\mathrm{in}}(A_1,G_1,C_1) \ \sqcup\ \{\lambda^{-1}:\lambda\in\operatorname{spec}(A_a)\}\ \sqcup\ \operatorname{spec}(A_m), \qquad \rho(F_\infty) = 1, \quad F_\infty\!\mid_{e_1\oplus a}\ \text{Schur} $$
(`eq:Finf-spec`, `eq:Finf-c3w`).

*Proof.* The antistable block is exactly as in `lem:structure`-1: a kernel direction in $\Sigma_\infty\!\mid_{aa}$ would leave an antistable mode unreflected, contributing $|\lambda|>1$ to $\operatorname{spec}(F_\infty)$ and forcing $\rho(F_\infty)>1$ against $\rho(F_\infty)\le1$ (`fact:dare-strong`); hence $\Sigma_\infty\!\mid_{aa}\succ0$. The spectrum and $F_\infty\!\mid_{e_1\oplus a}$ Schur are imported (`eq:Finf-spec`, `eq:Finf-c3w`). Everything else follows from extinction $\Sigma_\infty\!\mid_{\cdot\,m}=0$, which gives the block form of `eq:marg-extinct` directly. Let $\Delta := \Sigma_\infty C'(C\Sigma_\infty C'+R)^{-1}C\Sigma_\infty \succeq 0$ be the measurement correction, so $\mathcal U(\Sigma_\infty) = \Sigma_\infty - \Delta$, and write $P := \Sigma_\infty\!\mid_{mm}\succeq0$.

**The marginal correction vanishes.** The $(2,2)$-block fixed-point identity (`app:machinery`-2: $GQG'\!\mid_{22}=0$, $A$ has $e_2$-row $[\,0\ A_2\,]$, $A_2 = A_a\oplus A_m$) reads $\Sigma_\infty\!\mid_{22} = A_2\,\mathcal U(\Sigma_\infty)\!\mid_{22}\,A_2'$; its $(m,m)$ entry, $A_2$ being block-diagonal, is $P = A_m\,\mathcal U(\Sigma_\infty)\!\mid_{mm}\,A_m' = A_m(P - \Delta\!\mid_{mm})A_m'$. Since $A_m$ is nonsingular this rearranges to the Stein relation

<!-- eq:marg-stein -->
$$ P - A_m^{-1}\,P\,A_m^{-\prime} = \Delta\!\mid_{mm} \;\succeq\; 0. \tag{eq:marg-stein} $$

Unrolling `eq:marg-stein`, for every $N$,
$$ \sum_{k=0}^{N-1} A_m^{-k}\,\Delta\!\mid_{mm}\,A_m^{-k\prime} = P - A_m^{-N} P A_m^{-N\prime} \preceq P, $$
the omitted tail being PSD. The partial sums are nondecreasing and bounded above by $P$, so the series converges and its general term tends to $0$: $A_m^{-k}\,\Delta\!\mid_{mm}\,A_m^{-k\prime}\to0$. Factoring $\Delta\!\mid_{mm} = \sum_i \sigma_i u_iu_i'$ ($\sigma_i>0$, $u_i\ne0$), the trace of the $k$-th term is $\sum_i\sigma_i\|A_m^{-k}u_i\|^2\to0$, so $A_m^{-k}u_i\to0$ for each $i$. But $A_m^{-1}$ has every eigenvalue of modulus $1$, so $A_m^{-k}u_i\to0$ forces $u_i=0$ (`fact:no-decay`) — a contradiction unless there are no such $i$. Therefore $\Delta\!\mid_{mm}=0$.

**The marginal columns are unobservable, hence zero.** With $B := \Sigma_\infty C'$ and $S := C\Sigma_\infty C'+R\succ0$, the vanishing block $\Delta\!\mid_{mm} = B_m\,S^{-1}B_m' = 0$ forces $B_m = \Sigma_\infty\!\mid_{m\,\cdot}\,C' = 0$, i.e. $C\,\Sigma_\infty\!\mid_{\cdot\,m}=0$. Hence $\Delta\!\mid_{\cdot\,m} = \Sigma_\infty C'S^{-1}(C\,\Sigma_\infty\!\mid_{\cdot\,m}) = 0$, and the marginal-column fixed point $\Sigma_\infty\!\mid_{\cdot\,m} = [A\,\mathcal U(\Sigma_\infty)\,A']\!\mid_{\cdot\,m}$ collapses to $Z = A\,Z\,A_m'$ for $Z := \Sigma_\infty\!\mid_{\cdot\,m}$. Thus $A Z = Z A_m^{-\prime}$, so $A^k Z = Z A_m^{-k\prime}$ and $C A^k Z = (C\,Z)A_m^{-k\prime} = 0$ for all $k$: every column of $Z$ lies in the unobservable subspace $\mathcal{NO}(C,A) = \bigcap_{k\ge0}\ker(CA^k)$. Moreover $\operatorname{range}(Z)$ is $A$-invariant ($A\operatorname{range}(Z) = \operatorname{range}(ZA_m^{-\prime})\subseteq\operatorname{range}(Z)$), and there $A$ acts as $A_m^{-\prime}$, with spectrum in $\{|\lambda|=1\}$. Detectability (C1) confines $\mathcal{NO}(C,A)$ to the stable subspace ($|\lambda|<1$), which admits no $A$-invariant subspace carrying unit-circle spectrum. Hence $\operatorname{range}(Z)=\{0\}$, i.e. $\Sigma_\infty\!\mid_{\cdot\,m}=0$. ∎

<!-- verify: GATE-2 (check_extinction_proof.py). Extinction Sigma_inf|_{.m} -> 0 across semisimple rotation e^{+-0.7i} AND defective Jordan blocks at +1, -1 (size 2). eq:marg-stein identity (P - Am^-1 P Am^-') = Delta_mm holds ~1e-10; Delta_mm -> 0; C Z -> 0; Z -> 0; Sigma_inf|_aa = 4.19 > 0. Defective cases converge slower (polynomial w/ Jordan factor) but same limit. -->
<!-- verify: hypotheses/DAG. lem:structure-marg: C1 (detectability -> NO(C,A) stable), app:machinery-2 ((2,2) block identity, unconditional), fact:no-decay (|lambda(Am^-1)|=1), fact:dare-strong + eq:Finf-spec/eq:Finf-c3w (a00, spectrum imported). Antistable Sigma_inf|_aa>0 reused verbatim from lem:structure-1. CONSUMERS: 03 (C2w criterion), 05 (squeeze limit Sigma_inf|_mm=0), 06b-C (marginal necessity). No forward refs. -->
<!-- verify: CONFINEMENT — this lemma is the MARGINAL (GAS) branch; it does NOT read C3w and is not read by the C3w/exponential chain (04, 06). rho(F_inf)=1 here (marginal present) vs rho<1 in lem:structure. Extinction is the discrete dual of CW eq:ker-gap (riccaflow, critical block of the gap = 0). -->

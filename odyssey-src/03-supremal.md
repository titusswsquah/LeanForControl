<!-- 03-supremal — Charybdis, the upper anchor of the GAS squeeze. From any dominating prior the trajectory -->
<!-- dominates the run and converges to Sigma_inf, through the FIXED strong loop F_inf (the gap-Riccati -->
<!-- eq:gap-ric in a02-machinery). Antistable reaches Sigma_inf|aa>0 exponentially (A_a^-1 Schur), marginal -->
<!-- reaches 0 polynomially (lem:marginal). Discrete image of Callier-Winkin lem:supremal; the "smallest CW -->
<!-- deviation" (stablistep-handoff §1): CW's monotone ceiling R(Sigma-bar)<=Sigma-bar has NO discrete analog -->
<!-- (antistable amplification), so anchor at ANY Sigma-bar >= Sigma_inf and contract the gap through F_inf. -->
<!-- Ported from riccastep 01-marginal-v3 + 05-supremal-v3; the gap engine (eq:diff-id/eq:gap-ric) already -->
<!-- lives in a02-machinery, so this file is the two anchor lemmas built on it. -->
<!-- sec:supremal — main text -->
### The upper anchor: marginal extinction and the supremal bound

The from-above gap has a fixed contraction the from-below gap lacks: for $V\succeq0$, `eq:gap-ric` gives $\mathcal R(\Sigma_\infty + V) - \Sigma_\infty \preceq F_\infty V F_\infty'$, so above $\Sigma_\infty$ the gap rides the **fixed** strong loop $F_\infty$, Schur on $e_1\oplus a$ (`eq:Finf-spec`). The only unit-circle modes of $F_\infty$ are the marginal block, and there the upper trajectory's marginal covariance is driven to zero by observation — the one piece needing its own argument. We record it first.

<!-- lem:marginal -->
### Lemma (lem:marginal) — Extinction of the marginal block

Let C1 hold and let $\bar\Sigma_T := \mathcal R^T(\overline\Sigma_0)$ for a full-rank prior $\overline\Sigma_0 = \overline\Sigma_0' \succ 0$. The marginal block is driven to zero at a polynomial rate,

<!-- eq:marg-zero -->
$$ \bar\Sigma_T\!\mid_{mm} \;\longrightarrow\; 0 \qquad (T\to\infty), \tag{eq:marg-zero} $$

and hence, by comparison, $\Sigma_T\!\mid_{mm}\to0$ for **every** prior $\Sigma_0$ (consistent with $\Sigma_\infty\!\mid_{mm}=0$, `eq:marg-extinct`).

*Proof.* Since $\overline\Sigma_0\succ0$, $\bar\Sigma_T\succ0$ for all $T$ (the update and $GQG'$ preserve positive-definiteness), so $\bar\Sigma_T\!\mid_{22}\succ0$ and the $e_2$-information $J_T := (\bar\Sigma_T\!\mid_{22})^{-1}$ is defined. By `app:machinery`-2 it runs the backward $A_2^{-1}$-gramian (`eq:Jrec`/`eq:Jgram`, legal since $A_2 = A_a\oplus A_m$ is nonsingular, `eq:A2-inv`),

<!-- eq:Jrec-marg -->
$$ J_{T+1} = A_2^{-1\prime}\big(J_T + \widehat W_T\big)A_2^{-1}, \qquad \widehat W_T := (\mathcal U(\bar\Sigma_T)\!\mid_{22})^{-1} - (\bar\Sigma_T\!\mid_{22})^{-1} \succeq 0. \tag{eq:Jrec-marg} $$

The increment $\widehat W_T$ is the $e_2$-block information one measurement injects; being the $(2,2)$-block of the **full** update, it carries what reaches $e_2$ through the coupling to the observed $e_1$ block — not the isolated $(A_m,C_m)$ measurement.

**Marginal information diverges (uniform coercivity).** $A_2$ block-diagonal closes the $(m,m)$ recursion,
$$ J_{T+1}^{mm} = A_m^{-1\prime}(J_T^{mm} + \widehat W_T^{mm})A_m^{-1} \;\Longrightarrow\; J_T^{mm} \succeq \sum_{j=0}^{T-1}\big(A_m^{-(T-1-j)}\big)'\,\widehat W_j^{mm}\,\big(A_m^{-(T-1-j)}\big). $$
The marginal mode is $(A,C)$-**observable**: under C1 every $(A,C)$-unobservable mode is stable, but $|\lambda(A_m)|=1$, so PBH gives $\operatorname{rank}[\lambda I - A;\,C]=n$ at each $\lambda\in\operatorname{spec}(A_m)$. This makes the windowed injection **uniformly** coercive, iterate-independently:

<!-- eq:marg-coercive -->
$$ \exists\,\nu, c>0:\quad \sum_{j=0}^{\nu-1}\big(A_m^{-j}\big)'\,\widehat W_T^{mm}\,\big(A_m^{-j}\big) \;\succeq\; c\,I \qquad\text{for all }T. \tag{eq:marg-coercive} $$

The innovation is bounded above, $S_T := C\bar\Sigma_T C' + R \preceq C\bar\Pi C' + R =: \bar S$ (`eq:bounded`), so $\widehat W_T^{mm}$ is bounded **below** by the marginal observability weighted by $\bar S^{-1}\succ0$: over a window the $A_m^{-1}$ rotation fills the missing directions (a scalar output makes each $\widehat W_T^{mm}$ rank-one, but the window is full-rank). Were `eq:marg-coercive` false, some marginal unit $v$ would have $\widehat W_T^{mm}A_m^{-j}v = 0$ for all $j$ — the measurement never reduces covariance along the $A_m$-orbit of $v$, i.e. $v$ is $(A,C)$-unobservable, contradicting C1. The bound uses only C1 and `eq:bounded`; **no appeal to the upper anchor's convergence** (this removes the injection-settling detour). Running the coercive window through the unit-circle $A_m^{-1}$-gramian (`fact:gramian`, `fact:poly-growth`) gives
$$ \lambda_{\min}(J_T^{mm}) \longrightarrow \infty \quad\text{polynomially.} $$

**Marginal covariance vanishes.** By the Schur-complement for the inverse,
$$ \bar\Sigma_T\!\mid_{mm} = \big(J_T^{mm} - J_T^{ma}(J_T^{aa})^{-1}J_T^{am}\big)^{-1}. $$
The antistable information $J_T^{aa}$ and cross $J_T^{ma}$ are bounded — the $e_2$-information runs the $A_a^{-1}$-gramian (`eq:Jgram`), convergent since $A_a^{-1}$ is Schur (`eq:A2-inv`), only boundedness used — so the subtracted term stays bounded while $J_T^{mm}\to\infty$; the inverse tends to $0$, which is `eq:marg-zero`, at the polynomial rate. For a general prior $\Sigma_0\preceq\overline\Sigma_0=cI$, comparison (`eq:comparison`) gives $\Sigma_T\!\mid_{mm}\preceq\bar\Sigma_T\!\mid_{mm}\to0$, no inversion of a singular $\Sigma_0\!\mid_{mm}$ needed. ∎

<!-- verify: GATE-2. Uniform windowed coercivity eq:marg-coercive (BINDING C_m=0, marginal seen only via A_1m coupling): min over 80 trials x windows of lambda_min(sum_j (A_m^-j)' What_mm A_m^-j) = 8.8e-4 > 0 UNIFORMLY (check_marg_coercive_uniform.py) -- iterate-independent, from C1 + eq:bounded; riccastep's lem:supremal-2 injection-settling residual REMOVED. Sigma_T|mm -> 0 (mean 4.2e-2 @ T=400, decreasing). J_T^mm -> inf ~poly, J^aa/J^ma bounded, eq:marg-schur exact (riccastep check_marginv.py, 1e-14). Unobservable control (C_m=0 AND A1m=0): windowed gramian min eig 0.0 (NOT coercive), Sigma|mm stuck -- confirms eq:marg-coercive <=> observability. -->
<!-- verify: deps — app:machinery-2 (e2 (2,2)-identity eq:Jrec/eq:Jgram), eq:A2-inv, eq:comparison, fact:gramian, fact:poly-growth, eq:bounded (uniform innovation bound -> uniform injection floor), C1 (PBH marginal observability), fact:schur. eq:marg-extinct (fixed-point Sigma_inf|mm=0) cited for consistency, not needed in-proof. NO forward ref to lem:supremal (residual removed). CONSUMER: lem:supremal (marginal half), thm:sufficiency (Sigma_inf|mm=0), 06/07 (poly rate). Confinement: MARGINAL branch, no C3w. -->

<!-- lem:supremal -->
### Lemma (lem:supremal) — The supremal upper bound converges to $\Sigma_\infty$

Let C1 hold and fix any $\overline\Sigma_0 \succeq \Sigma_\infty$ (e.g. $\overline\Sigma_0 = cI$, $c$ large). The **supremal** trajectory $\bar\Sigma_T := \mathcal R^T(\overline\Sigma_0)$ dominates every trajectory below it and converges to the strong solution:

<!-- eq:above -->
$$ \mathcal R^T(\Sigma_0) \preceq \bar\Sigma_T \ \ (\Sigma_0\preceq\overline\Sigma_0) \qquad\text{and}\qquad \bar\Sigma_T \;\longrightarrow\; \Sigma_\infty, \tag{eq:above} $$

the antistable block reaching $\Sigma_\infty\!\mid_{aa}\succ0$ exponentially ($A_a^{-1}$ Schur, `eq:Sinf-gram`), the marginal block reaching $\Sigma_\infty\!\mid_{mm}=0$ polynomially (`lem:marginal`).

*Proof.* **Domination** is comparison (`eq:comparison`): $\Sigma_0\preceq\overline\Sigma_0 \Rightarrow \mathcal R^T(\Sigma_0)\preceq\mathcal R^T(\overline\Sigma_0)$.

**Convergence.** Let $\Delta_T := \bar\Sigma_T - \Sigma_\infty\succeq0$ ($\overline\Sigma_0\succeq\Sigma_\infty$, $\Sigma_\infty$ a fixed point, comparison). By `eq:gap-ric`, $\Delta_{T+1}\preceq F_\infty\Delta_T F_\infty'$. In the frame `eq:three-block` the only unit-circle modes of $F_\infty$ are the marginal block; $F_\infty$ is Schur on $e_1\oplus a$ (`eq:Finf-spec`: $A_c$ and the reflected $A_a^{-1}$), $\rho(F_\infty\!\mid_{e_1\oplus a})<1$.

*Marginal/cross.* $\Delta_T\!\mid_{mm} = \bar\Sigma_T\!\mid_{mm}\to0$ (`lem:marginal`, `eq:marg-zero`, the full-rank prior $\overline\Sigma_0$), and $\Delta_T\succeq0$ with `fact:schur` sends every marginal row/column to zero: $\|\Delta_T\!\mid_{m,\,e_1a}\|^2 \le \|\Delta_T\!\mid_{mm}\|\,\|\Delta_T\!\mid_{e_1a}\|\to0$ ($\Delta_T\!\mid_{e_1a}$ bounded, `eq:bounded`).

*Stabilizable–antistable.* Restricting `eq:gap-ric` to $e_1\oplus a$, $\Delta_{T+1}\!\mid_{e_1a}\preceq F_\infty\!\mid_{e_1\oplus a}\Delta_T\!\mid_{e_1a}F_\infty\!\mid_{e_1\oplus a}' + \Xi_T$, where $\Xi_T$ collects the marginal-routed terms (each carrying $\Delta_T\!\mid_{m,\,e_1a}$ or $\Delta_T\!\mid_{mm}$), so $\|\Xi_T\|\to0$. The Stein operator $\delta\mapsto F_\infty\!\mid_{e_1\oplus a}\delta F_\infty\!\mid_{e_1\oplus a}'$ has spectral radius $\rho(F_\infty\!\mid_{e_1\oplus a})^2<1$, so $\|F_\infty\!\mid_{e_1\oplus a}^{\,k}\|\le c\gamma^k$, $\gamma<1$ (`fact:schur-decay`); iterating the Löwner inequality and taking norms, $\|\Delta_T\!\mid_{e_1a}\| \le c^2\gamma^{2T}\|\Delta_0\!\mid_{e_1a}\| + \sum_{k<T}c^2\gamma^{2(T-1-k)}\|\Xi_k\|\to0$ (geometric kernel against a null sequence), closing the boundedness used above.

Both blocks vanish, so $\Delta_T\to0$, i.e. $\bar\Sigma_T\to\Sigma_\infty$: antistable exponentially (through the Schur $A_a^{-1}$, `eq:Sinf-gram`), marginal polynomially (`lem:marginal`). ∎

<!-- verify: GATE-2 (check_dsgg_upper.py, seed barSig0=Sig0+Sinf >= Sinf): domination barSig_T >= Sig_T held all T<=20000 (min eig >= -1e-9); barSig_T -> Sinf; marginal block (barSig-Sinf)_mm ~ 1/T polynomial (log-log slope -0.95), antistable exp -- the marginal paces. Gap eq:gap-ric Delta_{T+1} <= F_inf Delta_T F_inf' throughout (riccastep check_dom.py, min eig >= -2e-11). -->
<!-- verify: deps — eq:comparison (domination), eq:gap-ric (from-above fixed-F_inf gap, a02-machinery), eq:Finf-spec (F_inf Schur on e1+a), fact:schur-decay (Stein rho^2<1), fact:schur (marginal rows via PSD), eq:bounded (Delta|e1a bounded), lem:marginal (eq:marg-zero), eq:Sinf-gram (antistable rate). CONSUMER: thm:sufficiency (eq:above, upper half of the squeeze). Confinement: does not read C3w (rho(F_inf)=1 with marginal present). PORT of riccastep 05-supremal-v3 Part 3; Parts 1-2 (eq:diff-id/eq:gap-ric) already in a02-machinery. -->
<!-- verify: CW correspondence — this is CW lem:supremal discrete (stablistep-handoff §1 "smallest CW deviation"): drop the monotone ceiling (no discrete analog, antistable amplification R(cI) can grow), keep the gap-to-Sigma_inf through the FIXED F_inf. NOT DSGG 4.2 (which gives convergence but no rate and breaks CW lineage); DSGG stays a fact:dare-strong citation. -->

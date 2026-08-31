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

Let C1 hold, let the marginal block be **power-bounded in both directions** — $c_m := \sup_{k\ge0}\max\{\|A_m^k\|,\|A_m^{-k}\|\} < \infty$; equivalently, the unit-circle marginal eigenvalues are semisimple — and let $\bar\Sigma_T := \mathcal R^T(\overline\Sigma_0)$ for any prior with positive-definite uncontrollable block, $\overline\Sigma_0\!\mid_{22} \succ 0$. The marginal block is driven to zero,

<!-- eq:marg-zero -->
$$ \bar\Sigma_T\!\mid_{mm} \;\longrightarrow\; 0 \qquad (T\to\infty), \tag{eq:marg-zero} $$

and hence, by comparison, $\Sigma_T\!\mid_{mm}\to0$ for **every** prior $\Sigma_0\preceq\overline\Sigma_0$ (consistent with $\Sigma_\infty\!\mid_{mm}=0$, `eq:marg-extinct`). No rate is claimed. **The defective-marginal case is OPEN**: the numerics support the same conclusion with Jordan-degraded rates, but no proof is currently on the page, and every downstream use carries the semisimple qualification.

*Proof.* The uncontrollable corner stays positive definite, $\bar\Sigma_T\!\mid_{22}\succ0$ for all $T$ (the `lem:structure`-3 mechanism on the whole $e_2$ block; full positive-definiteness of $\bar\Sigma_T$ need **not** persist when $\ker A'\cap\ker G'\ne\{0\}$, and is not used). Track the **backward-transported uncontrollable columns**

<!-- eq:Ydef -->
$$ Y_T := \bar\Sigma_T\,E_2\,A_2^{-T\prime} \qquad (E_2 := \text{the } e_2\text{-inclusion}); \tag{eq:Ydef} $$

no information coordinates and no injected-information floor appear.

**(i) The output energy of $Y_T$ is summable.** For fixed $u$, the transported quadratic $\varphi_T(u) := (A_2^{-T\prime}u)'\,\bar\Sigma_T\!\mid_{22}\,(A_2^{-T\prime}u)$ steps by the $e_2$-block identity $\bar\Sigma_{T+1}\!\mid_{22} = A_2\,\mathcal U(\bar\Sigma_T)\!\mid_{22}\,A_2'$ (`app:machinery`-2) to $\varphi_{T+1}(u) = w'\,\mathcal U(\bar\Sigma_T)\!\mid_{22}\,w$ with $w := A_2^{-T\prime}u$. The variational form of the update — the Joseph square evaluated at the rank-one gain $K = \beta\,(E_2w)b'$ and minimized over $\beta$, cf. Part 2 of `lem:structure` — gives, for every output direction $b\ne0$,
$$ \varphi_{T+1}(u) \;\le\; \varphi_T(u) \;-\; \frac{\big(b'\,C\,Y_T\,u\big)^2}{b'S_Tb}, \qquad S_T := C\bar\Sigma_TC'+R \preceq \bar S \ \ (\text{`eq:bounded`}), $$
using $C\bar\Sigma_TE_2w = C\,Y_T\,u$. So $\varphi_T(u)$ is nonincreasing and, telescoping over $T$ and ranging $b,u$ over basis vectors,
$$ \sum_{T\ge0} \|C\,Y_T\|^2 \;<\; \infty. $$

**(ii) $Y_T$ rides the error map and dies.** The $e_2$-column identities ($A'E_2 = E_2A_2'$, $GQG'E_2 = 0$) give $\bar\Sigma_{T+1}E_2 = A\,\mathcal U(\bar\Sigma_T)E_2\,A_2'$, hence
$$ Y_{T+1} \;=\; A\,Y_T \;-\; AK_T\,(C\,Y_T), \qquad K_T := \bar\Sigma_TC'S_T^{-1}\ \text{bounded (`eq:bounded`, } S_T^{-1}\preceq R^{-1}). $$
Insert the stabilizing injection $L$ of C1 ($A-LC$ Schur, as in Part 2 of `lem:structure`): $Y_{T+1} = (A-LC)\,Y_T + E_T$ with $\|E_T\| \le c_E\,\|CY_T\|$ square-summable by (i). Unrolling against the geometric kernel of $A-LC$ (`fact:schur-decay`) and splitting each convolution at its midpoint (head: geometric decay against a bounded $\ell^2$-mass; tail: an $\ell^2$-tail against a summable kernel), $Y_T \to 0$.

**(iii) Power-boundedness closes.** Since $A_2 = A_a\oplus A_m$, the marginal columns of $Y_T$ are $\bar\Sigma_T E_m A_m^{-T\prime}$, so $\bar\Sigma_T\!\mid_{mm} = \big(E_m'\,\bar\Sigma_T E_m A_m^{-T\prime}\big)A_m^{T\prime}$ and
$$ \|\bar\Sigma_T\!\mid_{mm}\| \;\le\; \text{const}\cdot\|Y_T\|\cdot\|A_m^{T}\| \;\le\; \text{const}\cdot c_m\,\|Y_T\| \;\longrightarrow\; 0. $$
For a general prior $\Sigma_0\preceq\overline\Sigma_0$, comparison (`eq:comparison`) gives $\Sigma_T\!\mid_{mm}\preceq\bar\Sigma_T\!\mid_{mm}\to0$, no inversion of a singular $\Sigma_0\!\mid_{mm}$ needed. ∎

**Remark (what changed and why).** An earlier version argued through the injected information: the $(m,m)$ block of `eq:Jrec` with a uniform windowed coercivity of the increments $\widehat W_T^{mm}$. That display windowed a *single* $\widehat W_T$ where the unrolled sum needs windows of *consecutive* increments, and its uniformity argument negated a uniform-in-$T$ bound into a single exact-zero vector — a hole (Lean verification finding 5). The present proof needs no information coordinates, no $\widehat W$-floor, and no `fact:gramian`/`fact:poly-growth`; the price is the power-bounded (semisimple) qualification, whose removal is the flagged open problem.

<!-- verify: GATE-2 (scratch/check_marginal_route.py): phi_T(u) monotone nonincreasing EXACTLY (max violation 0.0); sum ||C Y_T||^2 converges (tail 1e-4/1e-6 at T=4000); ||Y_T|| -> 0; Sigma_T|mm -> 0 on both a semisimple rotation AND a defective Jordan block (numerics only for the latter — the proof covers power-bounded Am). Old-route checks (check_marg_coercive_uniform.py etc.) retired with the route. -->
<!-- verify: deps — app:machinery-2 (e2 (2,2)-identity and column identities), eq:A2-inv, eq:comparison, eq:bounded (uniform innovation bound + K_T bounded), C1 (via the stabilizing injection, as in lem:structure-2), fact:schur-decay, the Joseph variational square (lem:structure-2 mechanism), lem:structure-3 mechanism (corner positivity). fact:gramian / fact:poly-growth NO LONGER consumed here. eq:marg-extinct cited for consistency, not needed in-proof. CONSUMER: lem:supremal (marginal half), thm:sufficiency, 08 (all now carrying the semisimple qualification on the marginal branch). Confinement: MARGINAL branch, no C3w. -->

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

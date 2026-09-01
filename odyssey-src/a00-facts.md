
# Appendix

## Mathematical facts

<!-- fact:schur -->
### Fact (fact:schur) — Schur complement bound

If $\begin{bmatrix} A & B \\ B' & C \end{bmatrix} \succeq 0$ and $C \succ 0$, then $A - B C^{-1} B' \succeq 0$.

<!-- fact:no-decay -->
### Fact (fact:no-decay) — No decay for autonomous modes on or outside the unit circle

If every eigenvalue of $A$ satisfies $|\lambda| \geq 1$, then $A^k v \to 0$ implies $v = 0$.

<!-- fact:gramian -->
### Fact (fact:gramian) — Spectral mapping and divergence of the sampled state-energy Gramian

Let $A \in \mathbb{R}^{n \times n}$ have every eigenvalue with $|\lambda| \geq 1$. For every integer $m \geq 1$,

$$ \operatorname{spec}(A^m) = \{ \lambda^m : \lambda \in \operatorname{spec}(A) \} $$

so every eigenvalue of $A^m$ also satisfies $|\lambda| \geq 1$. Moreover,

$$ \lambda_{\min}\!\left( \sum_{j=0}^{\kappa-1} (A^{jm})' A^{jm} \right) \to \infty \quad \text{as } \kappa \to \infty $$

**Proof.** The spectral identity is the spectral mapping theorem. For the Gramian, set $G_\kappa := \sum_{j=0}^{\kappa-1} (A^{jm})' A^{jm}$, so $G_{\kappa+1} \succeq G_\kappa$ and $\lambda_{\min}(G_\kappa)$ is nondecreasing. Suppose for contradiction $\lambda_{\min}(G_\kappa) \not\to \infty$. Then there exist $M < \infty$ and unit vectors $v_\kappa$ with $v_\kappa' G_\kappa v_\kappa \leq M$. Pass to a subsequence with $v_\kappa \to v$, $\|v\| = 1$. For every $N$ and all $\kappa \geq N$,

$$ \sum_{j=0}^{N-1} \|A^{jm} v_\kappa\|^2 \leq v_\kappa' G_\kappa v_\kappa \leq M $$

Taking $\kappa \to \infty$ along the subsequence gives $\sum_{j=0}^{N-1} \|A^{jm} v\|^2 \leq M$ for every $N$, hence $\sum_{j=0}^\infty \|A^{jm} v\|^2 < \infty$ and $A^{jm} v \to 0$. Since every eigenvalue of $A^m$ has modulus at least one, `fact:no-decay` forces $v = 0$, contradicting $\|v\| = 1$. ∎

**Observable-injection form.** If, in addition, $H$ is a matrix with $(A, H)$ **observable**, then

$$ \lambda_{\min}\!\left( \sum_{j=0}^{\kappa-1} (A^{j})'\,H'H\,A^{j} \right) \to \infty \quad \text{as } \kappa \to \infty $$

(the per-step injection $H'H$ may be rank-deficient — the orbit fills the missing directions). **Proof.** Identical compactness argument with $\|HA^{j}v_\kappa\|^2$ in place of $\|A^{jm}v_\kappa\|^2$: a bounded limit forces $\sum_{j\ge0}\|HA^{j}v\|^2 < \infty$, hence $HA^{j}v \to 0$. For an eigenvector $w$ of $A$ at $\lambda$ ($|\lambda|\ge1$), $HA^{j}w = \lambda^{j}Hw$ with $\|HA^{j}w\| = |\lambda|^{j}\|Hw\|$, which tends to $0$ only if $Hw=0$; observability (PBH: no $A$-eigenvector lies in $\ker H$) rules this out, and the Jordan generalization adds only polynomial factors. So $v=0$, a contradiction. ∎

<!-- fact:psd-bounds -->
### Fact (fact:psd-bounds) — Spectral factorization and quadratic-form bounds for symmetric positive semidefinite matrices.

Every $P = P' \succeq 0$ admits an orthogonal factorization

$$
P = M \Lambda M'
\qquad M M' = I
\qquad \Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n)
\qquad \lambda_i \ge 0
$$

Consequently, for every $x$,

$$
\lambda_{\min}(P)\, \|x\|^2 \le x' P x \le \lambda_{\max}(P)\, \|x\|^2
$$

Equivalently,

$$
\lambda_{\min}(P)\, I \preceq P \preceq \lambda_{\max}(P)\, I
$$

If $P \succ 0$, then

$$
\|P^{-1}\| = \frac{1}{\lambda_{\min}(P)}
$$

<!-- fact:uniexp -->
### Fact (fact:uniexp) — Uniform exponential stability of a time-varying system (Zhou & Zhao 2017)

Given a linear time-varying system

$$ z(k+1) = F(k)\, z(k) \qquad k \geq 0 $$

in which the limit $\lim_{k \to \infty} F(k) = F$ exists, the time-varying system is uniformly exponentially stable if and only if $F$ is Schur stable.

<!-- fact:poly-growth -->
### Fact (fact:poly-growth) — Polynomial growth of powers for spectra in the closed unit disk

Let $A \in \mathbb{R}^{n \times n}$ have every eigenvalue satisfying $|\lambda| \leq 1$, and let $m$ with $1 \leq m \leq n$ be the size of the largest Jordan block associated with an eigenvalue on the unit circle ($m = 1$ if no eigenvalue lies on the unit circle). Then there exists $c > 0$ such that

$$ \|A^k\| \;\leq\; c\,(1 + k)^{m-1} \qquad k \geq 0. $$

<!-- fact:schur-decay -->
### Fact (fact:schur-decay) — Geometric decay of Schur matrix powers

Let $M\in\mathbb{R}^{n\times n}$ have $\rho(M) < 1$. Then for every $\gamma\in(\rho(M),1)$ there is $c\ge 1$ with

$$ \|M^k\| \;\le\; c\,\gamma^k \qquad k\ge 0. $$

**Proof.** In the Jordan form $M = S J S^{-1}$, each block of size $m$ at eigenvalue $\lambda$ has $\|(\lambda I+N)^k\| \le \sum_{i<m}\binom{k}{i}|\lambda|^{k-i}\|N\|^i \le p(k)\,|\lambda|^{k-(m-1)}$ for a polynomial $p$; since $|\lambda|\le\rho(M)<\gamma$, $p(k)|\lambda|^{k}/\gamma^k\to 0$, so the ratio is bounded. Taking the max over blocks and absorbing $\|S\|\|S^{-1}\|$ gives a finite $c$. (Equivalently, $\limsup_k\|M^k\|^{1/k}=\rho(M)<\gamma$ by Gelfand, so $\|M^k\|\gamma^{-k}$ is bounded.) ∎

The induced **Stein/Lyapunov operator** $\mathcal{L}_M(\delta) := M\delta M'$ on symmetric matrices has spectrum $\{\lambda_i\lambda_j : \lambda_i,\lambda_j\in\operatorname{spec}(M)\}$, hence $\rho(\mathcal{L}_M)=\rho(M)^2$; so $\rho(M)<1$ likewise gives $\|\mathcal{L}_M^{\,k}\| = \|\delta\mapsto M^k\delta M'^k\| \le c'\,\gamma^{2k}$.

<!-- fact:update-kernel -->
### Fact (fact:update-kernel) — The measurement update preserves the kernel

For $\Sigma = \Sigma' \succeq 0$ and $R \succ 0$, the measurement update $\mathcal{U}(\Sigma) := \Sigma - \Sigma C'(C\Sigma C'+R)^{-1}C\Sigma$ satisfies, with $D := C\Sigma^{1/2}$,

$$ \mathcal{U}(\Sigma) \;=\; \Sigma^{1/2}\,\big(I + D'R^{-1}D\big)^{-1}\,\Sigma^{1/2} $$

The middle factor $(I+D'R^{-1}D)^{-1} \succ 0$, so $\ker\mathcal{U}(\Sigma) = \ker\Sigma^{1/2} = \ker\Sigma$. Consequently, for any index set $J$,

$$ \Sigma\!\mid_{JJ} \succ 0 \quad\Longrightarrow\quad \mathcal{U}(\Sigma)\!\mid_{JJ} \succ 0 $$

**Proof.** The identity $I - D'(DD'+R)^{-1}D = (I+D'R^{-1}D)^{-1}$ (push-through) gives $\mathcal{U}(\Sigma) = \Sigma^{1/2}[I-D'(DD'+R)^{-1}D]\Sigma^{1/2} = \Sigma^{1/2}(I+D'R^{-1}D)^{-1}\Sigma^{1/2}$; the middle factor is $\succ 0$ since $D'R^{-1}D\succeq 0$. Hence $\ker\mathcal{U}(\Sigma)=\ker\Sigma^{1/2}=\ker\Sigma$. For the block: if $\mathcal{U}(\Sigma)\!\mid_{JJ}v_J = 0$ for $v_J\ne 0$, then the embedding $v=\iota_J v_J$ has $v'\mathcal{U}(\Sigma)v = v_J'\mathcal{U}(\Sigma)\!\mid_{JJ}v_J = 0$, so $v\in\ker\mathcal{U}(\Sigma)=\ker\Sigma$, whence $v_J'\Sigma\!\mid_{JJ}v_J = v'\Sigma v = 0$ — contradicting $\Sigma\!\mid_{JJ}\succ0$. ∎

<!-- fact:dare-strong -->
### Fact (fact:dare-strong) — Strong DARE solution: existence, uniqueness, spectrum, stabilization (Fact 1, foundational)

Let $(A,C)$ be detectable, $Q\succeq 0$, $R\succ 0$. Then the filtering DARE `eq:dare` has a **strong** solution $\Sigma_\infty = \Sigma_\infty'\succeq 0$ (`def:strong`): it is the **maximal** positive-semidefinite solution and the **unique** solution with $\rho(F_\infty)\le 1$, where $F_\infty := A(I-L_\infty C)$ and $L_\infty := \Sigma_\infty C'(C\Sigma_\infty C'+R)^{-1}$.

**(Spectrum.)** In the frame `eq:three-block`, the closed loop splits along the three blocks:

<!-- eq:Finf-spec -->
$$ \operatorname{spec}(F_\infty) \;=\; \Lambda_{\mathrm{in}}(A_1,G_1,C_1)\ \sqcup\ \{\,\lambda^{-1} : \lambda\in\operatorname{spec}(A_a)\,\}\ \sqcup\ \operatorname{spec}(A_m), \tag{eq:Finf-spec} $$

where $\Lambda_{\mathrm{in}}(A_1,G_1,C_1)$ is the open-unit-disk half of the $2n_1$ reciprocally paired ($\lambda\leftrightarrow 1/\bar\lambda$) generalized eigenvalues of the symplectic pencil of the stabilizable subsystem $(A_1,G_1,C_1)$ — equivalently, the $n_1$ eigenvalues of the stabilizing-solution closed loop of the $(A_1,G_1,C_1)$ filter, all of modulus $<1$. The **antistable** modes are *reflected* to their reciprocals (modulus $<1$); the **marginal** modes are *fixed* on the unit circle.

**(Corollary — stabilization under C3w.)** $\rho(F_\infty)\le 1$ always, and

<!-- eq:Finf-c3w -->
$$ \rho(F_\infty) < 1 \quad\Longleftrightarrow\quad \text{no uncontrollable unit-circle mode (C3w)} \quad\Longleftrightarrow\quad n_m = 0. \tag{eq:Finf-c3w} $$

Under C3w the strong solution is **stabilizing**. Without it, $\rho(F_\infty)=1$ exactly, carried by the marginal block $\operatorname{spec}(A_m)\subset\{|\lambda|=1\}$, which is never reflected inside; the stabilizable and antistable directions are Schur regardless, so $F_\infty\!\mid_{e_1\oplus a}$ — the closed loop restricted to the stabilizable-plus-antistable subspace — is **Schur in every case**.

**(Verified construction, phase D.)** Existence and uniqueness are now *proved* in the frame, by chart assembly: the reduced $(A_1,G_1,C_1)$ stabilizing solution $P_\infty$ (zero-seed monotone convergence, one-step PBH–Stein Schur loop), the loading $\Lambda_\infty$ (a discrete Sylvester fixed point with Schur factors $L_\infty$, $A_a^{-1}$), and the information gramian $J_\infty\succ0$ (PSD by its iterates; *definite* because a kernel eigenvector would lift through the loading identity to an undetectable antistable mode of $(A,C)$, against C1); the assembled $\Sigma_\infty = e_1P_\infty e_1' + V_\infty J_\infty^{-1}V_\infty'$ is a fixed point by the conditional-chart step read backwards, with $\rho(F_\infty)\le1$ by the strict one-step PBH–Stein kill. Existence needs **C1 alone**; uniqueness (among $\rho\le1$ solutions) follows from `lem:supremal` seeded at $\Sigma_\infty+\Sigma_\infty'$, under the power-bounded marginal. **Maximality is not consumed by this development and remains a classical citation.**

(Classical references: existence, uniqueness, and maximality under detectability alone — de Souza–Gevers–Goodwin 1986; see also Chan–Goodwin–Sin 1984. The reciprocal-pairing / reflection structure `eq:Finf-spec` is the symplectic-pencil theory of the discrete Hamiltonian, Lancaster–Rodman 1995. This is the discrete dual of Callier–Winkin 1995, Fact 1.) Formerly imported; the present development establishes the *structure* of $\Sigma_\infty$ (`lem:structure`), that the recursion is *attracted* to it, and — as of the phase-D verification — the load-bearing spectrum claims themselves (`lem:structure-marg`: the $(e_1\oplus a\,|\,m)$ split, $F_\infty\!\mid_{e_1\oplus a}$ Schur, the unit-modulus witness for $\rho(F_\infty)=1$), all from the bundle's $\rho(F_\infty)\le1$ alone. As of phase D4 existence and uniqueness are theorems as well (`exists_strong_solution` under C1 alone; `strong_solution_unique` / `existsUnique_strong_solution`); only maximality (not consumed) and the finer reciprocal pairing $\Lambda_{\mathrm{in}}\sqcup\{\lambda^{-1}\}$ (an Arc-1 consumer) remain imported.

<!-- verify: eq:Finf-spec confirmed numerically in scratch/check_fact1.py — spec(F_inf) of the maximal (from-above) solution matches Lambda_in(A1,G1,C1) ⊔ {1/lambda(A_a)} ⊔ spec(A_m) to 2e-2: antistable {1.5,2.0} -> {0.667,0.5} (reflected inside), marginal e^{±0.6i} on the circle, Lambda_in inside. rho(F_inf)=1.0 with the marginal present; dropping the marginal block gives rho=0.667<1 (eq:Finf-c3w), and the e1⊕a restriction is Schur in both runs. -->
<!-- verify: import side-conditions — detectability (C1) is the standing hypothesis; Q>=0, R>0; the strong/maximal solution exists under detectability ALONE (no stabilizability of the unstable modes), the regime here. Primary citation: de Souza-Gevers-Goodwin 1986. F_inf|e1+a Schur and the split are now proved (strong_Fs_schur/strong_spec_split, phase D), consumed by lem:structure-1/-marg and the main line; the reciprocal-pairing fine form of eq:Finf-spec is consumed by thm:formula and lem:sysinterp (Arc 1) (disjoint pencil spectra => complementary deflating subspaces V_+/V_-); confine C3w to the GES branch — eq:Finf-c3w must NOT enter the GAS/attraction argument. -->

<!-- fact:filter-opt -->
### Fact (fact:filter-opt) — Optimality and information-monotonicity of the Kalman filter (foundational)

For the model `eq:linsys` with $x(0)\sim N(x_0,\Sigma_0)$, $w\sim N(0,Q)$, $v\sim N(0,R)$ independent, the Kalman filter error covariance $\Sigma_T$ is the **minimum** error covariance among all estimators of $x(T)$ measurable with respect to $\{y_0,\dots,y_T\}$: for any such estimator $\hat x$, $\operatorname{cov}(x(T)-\hat x) \succeq \Sigma_T$. Moreover the optimal error covariance is **monotone non-increasing under enlargement of the conditioning data**: if an estimator is additionally given the exact values of a subset of the state coordinates over $\{0,\dots,T\}$, the resulting optimal error covariance is $\preceq \Sigma_T$ (restricted to the estimated coordinates). (Standard minimum-variance/MMSE optimality and the data-processing monotonicity of conditional covariance; foundational and imported, not proved here.)

<!-- verify: LEAN status (phase A) — fact:schur: mathlib (Matrix.PosDef.fromBlocks₂₂); thin wrapper lands with first consumer. fact:no-decay: VERIFIED = LinearSystems.no_decay (SpectralGrowth.lean); consumed twice in the repaired lem:structure-marg (correction kill, row kill). fact:gramian: VERIFIED for H = I = LinearSystems.gramian_growth (quantitative c*T floor); in-frame marginal instantiation marg_gramian_growth (phase F4) — the identified tool for the defective-marginal open problem; the observable-injection form has no remaining consumer (the marginal route was rewritten off fact:gramian — finding 5 / 03's remark). fact:psd-bounds: VERIFIED = LinearSystems/QuadForm.lean layer. fact:uniexp: VERIFIED in the consumed direction (F(k) -> F Schur => uniform exponential bound) = LinearSystems.transitionProd_norm_le_of_tendsto, now consumed on the reduced run (redProdF_geometric, phase D3) AND on the full three-block run (fullProd_geometric, phase F2 — transitionProd made index-generic); thm:payoff's ISS display consumes it (payoff_iss); the converse direction is not consumed and not formalized. fact:poly-growth: verified-weakened = LinearSystems.pow_mulVec_le_poly (exponent n-1, not the Jordan-sharp m-1; every consumer needs only some polynomial rate — deviation register D5). fact:schur-decay: VERIFIED = LinearSystems.IsSchurStable.exists_pow_norm_le. fact:update-kernel: VERIFIED = Dare.updM_mulVec_eq_zero_iff (+ block form Dare.updM_toBlocks₂₂_posDef, corner form Dare.updM_corner_posDef). fact:dare-strong: PROVED (phase D4): existence = DareSystem.exists_strong_solution (C1 alone; chart assembly with Sylvester fixed points + gramian_fixed_posDef, Estimation/Dare/Existence.lean), uniqueness = strong_solution_unique / existsUnique_strong_solution (power-bounded marginal, via lem:supremal; the semisimple qualification is a verified implication — MargSemisimple => both power bounds, marg_powers_bounded, phase F4); the IsStrongSolution bundle (PSD + fixed + rho<=1) is now instantiated, not hypothesized; maximality not consumed, still classical; on the REDUCED (A1,G1,C1) system it is fully PROVED (phase D2/D3: exists_stabilizing_solution — monotone-from-zero + one-step PBH-Stein fixed_point_schur + uniqueness; redP_tendsto_infP identifies the limit; Estimation/Dare/Reduced.lean, ReducedFacts.lean); the eq:Finf-spec/eq:Finf-c3w load-bearing content is VERIFIED (phase D) from the bundle alone — strong_spec_split, strong_Fs_schur, strong_exists_unit_eigenvalue (Estimation/Dare/Spectrum.lean); the reciprocal-pairing fine form remains imported (Arc-1 consumers only). fact:filter-opt: IMPORTED; after the finding-1 adoption, consumed only by 09-payoff's FIE=TVKF identification. -->

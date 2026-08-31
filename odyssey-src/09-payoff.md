<!-- 09-payoff — the estimator payoff (headline). The covariance dichotomy thm:main transfers to the two -->
<!-- estimators that share the filtering Riccati: the Full-Information Estimator (FIE) and the Time-Varying -->
<!-- Kalman Filter (TVKF), which coincide for the linear-Gaussian model. RGES iff C1+C2+C3w, RGAS iff C1+C2w; -->
<!-- robustness (ISS to bounded disturbances) folds in here via the error-map difference identity eq:diff-unroll -->
<!-- (no standalone lem:robust). Port + estimator-side extension of riccastep 13-payoff-v2. STANDALONE: the full -->
<!-- dichotomy and both estimators live here (this development subsumes the earlier exponential-only treatment). -->
<!-- sec:payoff — main text -->
### The estimators and their common covariance

Two estimators of the state $x(T)$ from $\{y_0,\dots,y_T\}$ are of interest. The **Full-Information Estimator** (FIE) minimizes the full-horizon least-squares cost penalizing the prior deviation and every process/measurement residual; the **Time-Varying Kalman Filter** (TVKF) is the recursion `eq:filter`. For the linear-Gaussian model `eq:linsys` both return the conditional mean $\mathbb E[x(T)\mid y_{0:T}]$ — the minimum-variance estimate — so **they coincide**, with common error covariance $\Sigma_T$ (`fact:filter-opt`) and common error map $F_T$ (`eq:filter`). The dichotomy `thm:main` therefore governs both at once; we state the payoff for the pair.

<!-- thm:payoff -->
### Theorem (thm:payoff) — Stability of the FIE/TVKF

Let C1 hold, so the strong solution $\Sigma_\infty$ exists (`fact:dare-strong`), and let $e^\star(T) := x(T) - \hat x(T\mid T)$ be the estimation error. (The estimator-error statements below concern the error *dynamics*; the covariance results of `thm:main` they build on need no assumption on the marginal Jordan structure.)

<!-- thm:payoff-1 -->
**1. (Limiting error map — reflection.)** When C2w also holds, $\Sigma_T\to\Sigma_\infty$ (`thm:main`-1) and $F_T\to F_\infty$, whose spectrum reflects the uncontrollable–unstable modes into the closed disk (`eq:Finf-spec`): each antistable uncontrollable $\lambda$ ($|\lambda|>1$) appears as $\lambda^{-1}$ (inside), each marginal uncontrollable $\lambda$ ($|\lambda|=1$) is unmoved (on the circle), the stabilizable modes sit at $\operatorname{spec}(A_c)$ (inside).

<!-- thm:payoff-2 -->
**2. (The estimator dichotomy.)**

<!-- eq:payoff-dich -->
$$ \text{C1}+\text{C2}+\text{C3w} \iff \text{FIE/TVKF is RGES}, \qquad\qquad \text{C1}+\text{C2w} \ (\text{marginal modes semisimple}) \iff \text{FIE/TVKF is RGAS}. \tag{eq:payoff-dich} $$

Under C1+C2+C3w the error map is uniformly exponentially stable and the estimator is **robustly globally exponentially stable**: $\|e^\star(T)\| \le c\,\gamma^T\|e^\star(0)\| + \sum_{k<T} c\,\gamma^{T-1-k}\|d_k\|$ for bounded disturbances $d_k$, some $\gamma<1$. Under C1+C2w without C3w the covariance still converges but the estimator is no longer exponential: with the marginal modes **semisimple** (the marginally-stable case) it is **robustly globally asymptotically stable** — the error is uniformly bounded and ISS, carrying undamped ripples along the marginal uncontrollable modes; with a defective unit-circle marginal block the error map inherits that block's polynomial growth, so the covariance converges (polynomially) yet the homogeneous error is only polynomially bounded.

*Proof.* Part 1 is `eq:Finf-spec` (`lem:structure-marg`).

Part 2, **RGES.** Under C1+C2+C3w, $\Sigma_T\to\Sigma_\infty$ exponentially and $\rho(F_\infty)<1$ (`thm:main`-2). Since $F_T\to F_\infty$ ($F$ continuous in $\Sigma$) with Schur limit, the time-varying error map is uniformly exponentially stable (`fact:uniexp`): the homogeneous transition $\Phi(T,k) := F_{T-1}\cdots F_k$ satisfies $\|\Phi(T,k)\|\le c\gamma^{T-k}$, $\gamma<1$, uniformly in $k$. Robustness is then automatic: a perturbed run (perturbed prior, gain, or an additive disturbance $d_k$ entering the error recursion $e^\star(T+1)=F_T e^\star(T)+d_T$) has $e^\star(T)=\Phi(T,0)e^\star(0)+\sum_{k<T}\Phi(T,k+1)d_k$, and the difference between two error trajectories is carried by the same uniformly-bounded transition (`eq:diff-unroll`, $\Phi_T$ the error-map product), giving the displayed ISS bound. So the estimator is RGES. Conversely, RGES forces exponential covariance convergence, hence C2w (`thm:necessity`) and — absent a marginal block, else the approach is only polynomial (`lem:marginal`) contradicting exponential — C3w, i.e. C2 (`thm:main`-2).

Part 2, **RGAS.** Under C1+C2w, $\Sigma_T\to\Sigma_\infty$ (`thm:main`-1) and $\sup_T\Sigma_T\preceq\bar\Pi<\infty$ (`eq:bounded`), so $F_T\to F_\infty$ with $\rho(F_\infty)\le1$; on the marginal block $\Sigma_\infty\!\mid_{mm}=0$ (`eq:marg-extinct`), the mode is estimated exactly, the gain vanishes, and $F_\infty$ restricts there to $A_m$. When $A_m$'s unit-circle eigenvalues are semisimple, $F_\infty$ is power-bounded, so $\Phi(T,k)$ is uniformly bounded and $\|e^\star(T)\|\le c(\|e^\star(0)\|+\sup_k\|d_k\|)$: the noise-free error converges to bounded marginal-mode ripples — RGAS, not RGES. If instead $A_m$ has a defective unit-circle block, $\|A_m^{\,k}\|$ grows polynomially, so $\Phi(T,k)$ and the homogeneous error grow polynomially — the covariance is unaffected (it converges, `thm:main`-1) but uniform boundedness of the error fails. Conversely RGAS gives covariance convergence, hence C2w (`thm:necessity`). ∎

<!-- cor:every-prior -->
### Corollary (cor:every-prior) — Every-prior stability is a controllability property

<!-- eq:every-prior -->
$$ \big(\text{FIE/TVKF RGAS for every prior }\Sigma_0\succeq0\big) \iff \mathcal X_{a,uc}(A,G)=\{0\}, \qquad \big(\text{RGES for every prior}\big) \iff (A,G)\ \text{stabilizable}. \tag{eq:every-prior} $$

*Proof.* By `thm:payoff`, stability for a given prior is a condition on $\ker\Sigma_0$ (C2w or C2). C2w holds for **every** $\Sigma_0$ iff $\mathcal X_{a,uc}=\{0\}$: if $\mathcal X_{a,uc}\ne\{0\}$, a prior singular on an antistable uncontrollable direction violates C2w (`eq:prior-pos`); if $\mathcal X_{a,uc}=\{0\}$, then $\ker\Sigma_0\cap\mathcal X_{a,uc}=\{0\}$ automatically. For RGES, C2+C3w for every $\Sigma_0$ needs C2 for every prior, i.e. $\mathcal X_{u,uc}=\{0\}$, which already entails C3w (no uncontrollable unit-circle mode) and is exactly stabilizability of $(A,G)$. ∎

**Remark (the practical reading).** Detectability buys the strong solution and hence a stable estimator for any admissible prior; whether that estimator is *exponentially* stable is a separate, controllability-side question. If every uncontrollable mode is stable — $(A,G)$ stabilizable — the FIE/TVKF is RGES for every prior. If some uncontrollable modes sit on the unit circle, the best attainable even with a perfectly chosen prior is the strong solution: the covariance still converges (now only polynomially) and the estimator is RGAS, but the steady error carries undamped marginal ripples, and an exponentially stabilizing gain must be sought outside the optimal filter. C2w is the sharp frontier — a *semidefinite*-prior kernel condition, weaker than positive-definiteness or domination of $\Sigma_\infty$ — separating the estimator that forgets its prior from the one that never does. This is the discrete, estimation-side image of the critical-mode phenomenon of Callier and Winkin (1995); it sharpens the positive-definite-prior filtering results of de Souza, Gevers and Goodwin (1986) to semidefinite priors with an explicit rate.

<!-- verify: F_inf -> Schur iff C3w (riccastep check_Fspec.py, rho 0.667 vs 1.0). RGES: fact:uniexp (time-varying -> Schur limit) + eq:diff-unroll (ISS via the error-map product Phi_T, bounded, a02-machinery). RGAS: eq:bounded + eq:marg-extinct (F_inf marginal = A_m). SEMISIMPLE/DEFECTIVE (check_defective_marginal.py): F_inf|mm = A_m confirmed (marginal eigenvalues match). Semisimple A_m (rotation): ||F_inf^k|| flat 2.63->2.97 => power-bounded => RGAS. DEFECTIVE A_m (Jordan block at lambda=1): ||F_inf^k|| grows ~linearly 2.81->708 => error UNBOUNDED (RGAS fails), yet covariance Sigma_T->Sigma_inf converges (7.6e-2) and Sigma_inf|mm->0 either way. So RGAS is conditioned on semisimple marginals; the covariance dichotomy thm:main is not. Corollaries via thm:main with boundary priors. -->
<!-- verify: deps — eq:filter/eq:linsys (00-problem), fact:filter-opt (FIE=TVKF=MMSE, common Sigma_T), fact:dare-strong, thm:main-1/-2, eq:Finf-spec/lem:structure-marg (reflection + marginal semisimple), fact:uniexp (RGES), eq:diff-unroll (robustness/ISS), eq:bounded (RGAS boundedness), thm:necessity (converses), lem:marginal (poly => not exp), eq:prior-pos (every-prior). No standalone lem:robust — robustness folded in (Part 2). PORT+extension of riccastep 13-payoff-v2. -->
<!-- verify: STANDALONE — the full FIE/TVKF dichotomy (RGES + RGAS) lives here; this development subsumes the exponential-only treatment. Positioning: sharpens DSGG 1986 (positive-definite/dominating priors, no rate) to semidefinite priors + explicit rate + estimator payoff; discrete CW critical-mode image. -->

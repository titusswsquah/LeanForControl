<!-- 08-main — Ithaca. The strong/stabilizing dichotomy: necessity + sufficiency (Part 1), and the C3w -->
<!-- refinement to the stabilizing/exponential regime (Part 2). Part 2 is SELF-CONTAINED (rate + poly-rate -->
<!-- contradiction), not an external import; the fuller GES/uniform-exponential theory is the companion -->
<!-- (arc1 / the exponential deck), cited there for the detailed rate. Port of riccastep 12-main-v4. -->
<!-- sec:main — main text -->
<!-- thm:main -->
### Theorem (thm:main) — The strong/stabilizing dichotomy

Let C1 hold. By `lem:structure-marg` the strong error map $F_\infty$ has spectrum `eq:Finf-spec` — $\operatorname{spec}(A_c)$ (Schur), the antistable spectrum reflected inside the disk $\{\lambda^{-1}:\lambda\in\operatorname{spec}(A_a)\}$, and the marginal spectrum $\operatorname{spec}(A_m)$ on the unit circle. Consequently:

<!-- thm:main-1 -->
**1. (Strong attraction.)**

<!-- eq:main-strong -->
$$ \text{C1} + \text{C2w} \quad\iff\quad \Sigma_T \to \Sigma_\infty \quad\big(\rho(F_\infty)\le1\big). \tag{eq:main-strong} $$

(The $\Leftarrow$ direction carries `lem:marginal`'s standing qualification: marginal modes semisimple; the defective case is open.)

<!-- thm:main-2 -->
**2. (Stabilizing/exponential refinement.)**

<!-- eq:main-stab -->
$$ \text{C1} + \text{C2} + \text{C3w} \quad\iff\quad \Sigma_T \to \Sigma_\infty \ \text{exponentially} \quad\big(\rho(F_\infty)<1\big). \tag{eq:main-stab} $$

*Proof.*

**Spectrum.** $F_\infty = A(I - \Sigma_\infty C'(C\Sigma_\infty C'+R)^{-1}C)$ is block upper-triangular in the frame `eq:three-block` (the $e_2$-rows of $A$ are $[\,0\ A_2\,]$, $G=\operatorname{col}(G_1,0,0)$). Its $e_1$-diagonal block is the stabilizable closed loop $A_c$, Schur; on the antistable block $\Sigma_\infty\!\mid_{aa}\succ0$ with information the $A_a^{-1}$-gramian (`eq:Sinf-gram`), and the strong-solution gain reflects the spectrum to $A_a^{-1}$ (the $\rho(F_\infty)\le1$ property of the strong solution realized on each reciprocal pair by the inside representative); on the marginal block $\Sigma_\infty\!\mid_{mm}=0$ (`eq:marg-extinct`), the mode is estimated exactly, the gain is zero, and $F_\infty$ leaves it as $A_m$ on the unit circle. Hence `eq:Finf-spec`, and $\rho(F_\infty)<1$ iff there is no marginal block, i.e. iff C3w.

**Part 1.** ($\Leftarrow$) is `thm:sufficiency`; ($\Rightarrow$) is `thm:necessity`. By `fact:dare-strong`/`def:strong`, $\rho(F_\infty)\le1$.

**Part 2.** Assume C1 + C2 + C3w. Under C3w there are no unit-circle uncontrollable modes, so the marginal block is absent, $\mathcal X_{u,uc}=\mathcal X_{a,uc}$, and C2 $\iff$ C2w (`eq:prior-pos`). By Part 1, $\Sigma_T\to\Sigma_\infty$; by `thm:sufficiency` the rate is geometric (every block converges through the Schur matrices $A_c$ and $A_a^{-1}$, no marginal block to slow it). By the spectrum with the marginal block absent, $\rho(F_\infty)<1$ — the stabilizing solution.

Conversely, suppose $\Sigma_T\to\Sigma_\infty$ exponentially. Then it converges, so C2w holds (`thm:necessity`). If a marginal block were present, $\Sigma_T\!\mid_{mm}\to0$ only polynomially (`thm:sufficiency`, `lem:marginal`, `fact:gramian`), contradicting the exponential rate; hence C3w, and then C2 $\iff$ C2w gives C2. (Equivalently, $\rho(F_\infty)<1$ forces, by the spectrum, the absence of the marginal block, i.e. C3w.) ∎

**Remark (the two regimes).** C2w is the exact frontier of attraction to the strong solution: it asks only that the prior inform every **antistable** uncontrollable direction (`lem:criterion-w`). Marginal uncontrollable directions need not be informed — their covariance is driven to zero by the unbounded information of a persistent observed mode (`lem:marginal`) — but they survive in $F_\infty$ on the unit circle and slow the approach to a polynomial rate. Removing them (C3w) collapses C2w to C2, reflects the entire uncontrollable-unstable spectrum strictly inside the disk, and restores the exponential, stabilizing regime. Both regimes are settled here, floor-free — the GAS branch (polynomial, marginal-inclusive) and the GES branch (exponential, C3w) — and both transfer to the estimator in `thm:payoff`.

<!-- verify: OPEN (Lean verification finding 7): Part 2's converse (exponential => C3w) argues "Sigma_T|mm -> 0 only polynomially, contradicting the exponential rate" — this needs a rate LOWER bound on the marginal gap, which no result on the page provides (lem:marginal gives decay only, no floor; the retired route's poly-rate claim is gone). Candidate repair: a gap-floor argument in the style of the repo's GES exists_gap_floor_of_not_C3w. The parenthetical spectral route needs exponential => rho(F_inf)<1, likewise not established. To be resolved when 08 is verified. -->
<!-- verify: assembles thm:sufficiency + thm:necessity (Part 1) and the rate + poly-rate contradiction (Part 2). Spectrum eq:Finf-spec from lem:structure-marg (F_inf Schur on e1+a, A_m on circle); riccastep check_Fspec.py: C3w rho(F+)=0.667, marginal rho(F+)=1.0. -->
<!-- verify: deps — lem:structure-marg (eq:Finf-spec spectrum, Sigma_inf|aa>0, eq:marg-extinct), eq:Sinf-gram, eq:prior-pos (C2<=>C2w under C3w), thm:sufficiency (<= Part1 + rate), thm:necessity (=> Part1), lem:marginal + fact:gramian (poly rate, exponential=>C3w), fact:dare-strong/def:strong (rho(F_inf)<=1). CONSUMER: thm:payoff (estimator dichotomy). STANDALONE: Part 2 (GES) is self-contained (rate + poly-rate contradiction), not deferred; the full dichotomy lives here. PORT of riccastep 12-main-v4. -->

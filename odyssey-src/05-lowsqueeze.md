<!-- 05-lowsqueeze — Scylla, the lower anchor of the GAS squeeze. A universal (every-prior), C2w-tight, slaved -->
<!-- seed whose trajectory converges to the strong solution FLOOR-FREE. Two results: lem:slaved-seed (the seed, -->
<!-- ported from riccastep 06) and lem:lowsqueeze (the convergence, assembled on 04-evolution). The convergence -->
<!-- is the discrete dual of CW lem:lowsqueeze (eq:lowsqueeze): the rank-minimal slaved seed forgets geometrically, -->
<!-- with the marginal riding the antistable (lem:loading) and e_1 conditionally filtered (lem:condfilter). -->

<!-- lem:slaved-seed -->
### Lemma (lem:slaved-seed) — A C2w-tight, rank-minimal lower initial condition

Work in the frame `eq:three-block`, $\Sigma_0=\operatorname{blkdiag}(\Sigma_1,\Sigma_2)$, with $\Sigma_2=\big[\begin{smallmatrix}\Sigma_{aa}&\Sigma_{am}\\\Sigma_{am}'&\Sigma_{mm}\end{smallmatrix}\big]\succeq0$ and $\Sigma_a:=\Sigma_{aa}$. Let $S:=\Sigma_2/\Sigma_{aa}=\Sigma_{mm}-\Sigma_{am}'\Sigma_{aa}^{\dagger}\Sigma_{am}\succeq0$ be the **marginal** (generalized) Schur complement, and define the **slaved antistable part** and the **seed**

<!-- eq:Sig2a -->
$$ \Sigma_2^{(a)} := \Sigma_2 - \operatorname{blkdiag}(0,\,S) = \begin{bmatrix}\Sigma_{aa} & \Sigma_{aa}\Lambda_0'\\ \Lambda_0\Sigma_{aa} & \Lambda_0\Sigma_{aa}\Lambda_0'\end{bmatrix} = \begin{bmatrix}I\\ \Lambda_0\end{bmatrix}\Sigma_{aa}\begin{bmatrix}I & \Lambda_0'\end{bmatrix},\qquad \Lambda_0:=\Sigma_{am}'\Sigma_{aa}^{\dagger}=\Sigma_{ma}\Sigma_{aa}^{\dagger}, \tag{eq:Sig2a} $$

<!-- eq:Ldef-slaved -->
$$ \underline\Sigma_0 := \operatorname{blkdiag}\big(0_{e_1},\ \delta\,\Sigma_2^{(a)}\big), \qquad \delta\in(0,1]. \tag{eq:Ldef-slaved} $$

Then, **for every prior** $\Sigma_0$:

<!-- lem:slaved-seed-1 -->
**1. (Universal lower bound.)** $\underline\Sigma_0 \preceq \Sigma_0$, with no condition on $\Sigma_0$.

<!-- lem:slaved-seed-2 -->
**2. (C2w characterization.)** $\underline\Sigma_0\!\mid_{aa} = \delta\Sigma_a$, so the antistable block is nondegenerate iff C2w:

<!-- eq:Lc2w -->
$$ \underline\Sigma_0\!\mid_{aa} = \delta\Sigma_a \succ 0 \quad\iff\quad \text{C2w}. \tag{eq:Lc2w} $$

<!-- lem:slaved-seed-3 -->
**3. (Rank-minimal and slaved.)** $\Sigma_2^{(a)}$ has zero marginal Schur complement and $\operatorname{rank}\Sigma_2^{(a)}=\operatorname{rank}\Sigma_{aa}$; under C2w, $\operatorname{rank}(\underline\Sigma_0\!\mid_{22})=n_a$ and the seed is **slaved** with loading $\Lambda_0=\Sigma_{ma}\Sigma_{aa}^{-1}$,

<!-- eq:seed-slaved -->
$$ \underline\Sigma_0\!\mid_{m,:} = \Lambda_0\,\underline\Sigma_0\!\mid_{a,:}. \tag{eq:seed-slaved} $$

*Proof.* **Part 1.** For PSD $\Sigma_2$, $\operatorname{range}\Sigma_{am}\subseteq\operatorname{range}\Sigma_{aa}$, so $\Sigma_{aa}\Sigma_{aa}^\dagger\Sigma_{am}=\Sigma_{am}$ and `eq:Sig2a` holds with $\Sigma_2^{(a)}=\big[\begin{smallmatrix}I\\\Lambda_0\end{smallmatrix}\big]\Sigma_{aa}\big[\begin{smallmatrix}I&\Lambda_0'\end{smallmatrix}\big]\succeq0$ (`fact:schur`). Then $\Sigma_0-\underline\Sigma_0=\operatorname{blkdiag}(\Sigma_1,\ \Sigma_2-\delta\Sigma_2^{(a)})$ with $\Sigma_2-\delta\Sigma_2^{(a)}=(1-\delta)\Sigma_2^{(a)}+\operatorname{blkdiag}(0,S)\succeq0$ ($\Sigma_1\succeq0$, $\Sigma_2^{(a)}\succeq0$, $S\succeq0$, $1-\delta\ge0$) — for **every** $\Sigma_0$, no threshold. **Part 2.** By `eq:Sig2a`, $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_{aa}=\delta\Sigma_a$; by `eq:prior-pos`(b) ($\Sigma_a\succ0\iff$ C2w) this gives `eq:Lc2w`. **Part 3.** The outer factor $[I;\Lambda_0]$ has full column rank $n_a$, so $\operatorname{rank}\Sigma_2^{(a)}=\operatorname{rank}\Sigma_{aa}$; its marginal Schur complement is $\Lambda_0\Sigma_{aa}\Lambda_0'-(\Lambda_0\Sigma_{aa})\Sigma_{aa}^\dagger(\Sigma_{aa}\Lambda_0')=0$. Under C2w, $\Sigma_{aa}\succ0$, so $\Lambda_0=\Sigma_{ma}\Sigma_{aa}^{-1}$ and the marginal row $\underline\Sigma_0\!\mid_{m,:}=[\,0,\ \delta\Lambda_0\Sigma_{aa},\ \delta\Lambda_0\Sigma_{aa}\Lambda_0'\,]=\Lambda_0[\,0,\ \delta\Sigma_{aa},\ \delta\Sigma_{aa}\Lambda_0'\,]=\Lambda_0\,\underline\Sigma_0\!\mid_{a,:}$, which is `eq:seed-slaved`. ∎

**Remark (the seed that makes the anchor geometric).** The lower anchor must inject the *smallest* antistable prior information compatible with $\Sigma_0$ and nothing else. The full seed $\operatorname{blkdiag}(0,\delta\Sigma_2)$ injects the marginal Schur complement $\delta S$ as *independent* marginal covariance, drained only through the marginal's divergent $A_m^{-1}$-gramian at the polynomial $1/T$ rate. The slaved seed `eq:Ldef-slaved` removes exactly $S$ — leaving the rank-$n_a$ antistable-supported $\Sigma_2^{(a)}$ — so the marginal carries no covariance of its own at $T=0$, `lem:loading` holds it slaved for all $T$, and the anchor forgets geometrically. **Condition hygiene:** Parts 1, 3 use no condition; C2w enters only in Part 2; C3w not at all. *(Port of riccastep 06-slaved-seed-v2, arc-2 antistable-first frame.)*

<!-- lem:lowsqueeze -->
### Lemma (lem:lowsqueeze) — The universal, C2w-tight lower anchor converges, floor-free

Let C1 and C2w hold. For every prior $\Sigma_0$, the slaved lower trajectory $\underline\Sigma_T$ seeded at `eq:Ldef-slaved` satisfies

<!-- eq:lowsqueeze -->
$$ \underline\Sigma_0 \preceq \Sigma_0 \quad\Longrightarrow\quad \underline\Sigma_T \preceq \Sigma_T \ \ (T\ge0), \qquad\text{and}\qquad \underline\Sigma_T \longrightarrow \Sigma_\infty \quad\text{(exp. fast, floor-free).} \tag{eq:lowsqueeze} $$

*Proof.* **Domination.** $\underline\Sigma_0\preceq\Sigma_0$ for every prior (`lem:slaved-seed`-1); the recursion is monotone in the initial condition (`eq:comparison`), so $\underline\Sigma_T=\mathcal R^T(\underline\Sigma_0)\preceq\mathcal R^T(\Sigma_0)=\Sigma_T$ for all $T$.

**The anchor collapses to its $(1a)(1a)$ block.** Full-row slaving (`eq:row-slaved`) makes the marginal row a $\Lambda_{ma}$-readout of the antistable row, so the whole matrix is carried by its leading $e_1\oplus e_a$ block $\underline\Sigma_T^{ea}:=\underline\Sigma_T\!\mid_{(1a)(1a)}$:

<!-- eq:pi-collapse -->
$$ \underline\Sigma_T = \Pi_T\,\underline\Sigma_T^{ea}\,\Pi_T', \qquad \Pi_T := \begin{bmatrix} I_{n_1} & 0 \\ 0 & I_{n_a} \\ 0 & \Lambda_{ma} \end{bmatrix}, \tag{eq:pi-collapse} $$

as read off block by block from `eq:row-slaved` ($\underline\Sigma_T\!\mid_{1m}=\underline\Sigma_T\!\mid_{1a}\Lambda_{ma}'$, $\underline\Sigma_T\!\mid_{am}=\underline\Sigma_T\!\mid_{aa}\Lambda_{ma}'$, $\underline\Sigma_T\!\mid_{mm}=\Lambda_{ma}\underline\Sigma_T\!\mid_{aa}\Lambda_{ma}'$).

**The $(1a)(1a)$ block homes.** Its three sub-blocks converge, each to the corresponding block of $\Sigma_\infty$:
- *antistable:* $J_1\to(\Sigma_\infty\!\mid_{aa})^{-1}$ (`lem:jtransform`, `eq:J1-home`), so $\underline\Sigma_T\!\mid_{aa}=J_1^{-1}\to\Sigma_\infty\!\mid_{aa}$, floor-free;
- *cross:* $\underline\Sigma_T\!\mid_{1a}=\Lambda_{1a}\,\underline\Sigma_T\!\mid_{aa}\to\Lambda_{1a}^\infty\,\Sigma_\infty\!\mid_{aa}=\Sigma_\infty\!\mid_{1a}$ (`lem:condfilter`-3 and the line above);
- *stabilizable:* $\underline\Sigma_T\!\mid_{11}=P_T+\Lambda_{1a}\,\underline\Sigma_T\!\mid_{aa}\,\Lambda_{1a}'\to P_\infty+\Lambda_{1a}^\infty\,\Sigma_\infty\!\mid_{aa}\,\Lambda_{1a}^{\infty\prime}=\Sigma_\infty\!\mid_{11}$ (`eq:condcov`, `lem:condfilter`-1,3).

The three limits are the strong-solution blocks: $P_\infty$ and $\Lambda_{1a}^\infty$ are the unique fixed points of `eq:condric` and `eq:cf-rec`, which the values $\Sigma_\infty\!\mid_{1|a}$, $\Sigma_\infty\!\mid_{1a}(\Sigma_\infty\!\mid_{aa})^{-1}$ read off $\Sigma_\infty$ also satisfy, so they coincide (uniqueness, as in `lem:jtransform`). Hence $\underline\Sigma_T^{ea}\to\Sigma_\infty\!\mid_{(1a)(1a)}$.

**Assembly.** $\Lambda_{ma}\to0$ (`eq:loading-conv`), so $\Pi_T\to\Pi_\infty=[\,I_{n_1};\,I_{n_a};\,0\,]$, and by `eq:pi-collapse`
$$ \underline\Sigma_T = \Pi_T\,\underline\Sigma_T^{ea}\,\Pi_T' \longrightarrow \Pi_\infty\big(\Sigma_\infty\!\mid_{(1a)(1a)}\big)\Pi_\infty' = \operatorname{blkdiag}\big(\Sigma_\infty\!\mid_{(1a)(1a)},\,0\big) = \Sigma_\infty, $$
the last equality by marginal extinction $\Sigma_\infty\!\mid_{\cdot\,m}=0$ (`eq:marg-extinct`). Every constituent rate is $<1$ — antistable $\rho(A_a^{-1})^2$, loadings $\rho(A_a^{-1})$, conditional $\rho(L_\infty)$ — and **no marginal unit-circle eigenvalue appears** (the marginal enters only through $\Lambda_{ma}$, where $|\lambda(A_m)|=1$ is multiplied by $\rho(A_a^{-1})<1$); so the approach is exponential, and **floor-free**: no lower bound on $\underline\Sigma_T\!\mid_{aa}$ was used — its information is bounded above by the convergent $A_a^{-1}$-gramian of `lem:jtransform`, whose source is bounded by the conditional filter (`lem:condfilter`), not by any assumed floor. ∎

**Remark (C2w-tightness and the role in the squeeze).** The anchor is nondegenerate exactly under C2w (`eq:Lc2w`): if C2w fails, $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_a$ is singular and the antistable chart `eq:jchart` degenerates on the uninformed direction — the seed cannot inject the antistable information the strong solution demands, and attraction fails there (the necessity direction, treated separately). Paired with the dominating upper anchor (Charybdis, `lem:supremal`), `eq:lowsqueeze` is the lower half of the GAS squeeze $\underline\Sigma_T\preceq\Sigma_T\preceq\overline\Sigma_T$ (`thm:sufficiency`). This is the discrete dual of CW's exponentially-converging lower bound (`eq:lowsqueeze` of riccaflow): the rank-minimal slaved seed, the marginal riding the antistable, the geometric forgetting — with the one discrete addition that $e_1$ is conditionally filtered rather than folded into an antistrong block.

<!-- verify: LEAN (phase B): lem:slaved-seed = Estimation/Dare/SlavedSeed.lean: Part 1 = slavedSeed_le_Sig0 (via the conditional completed square Sig₂_quadForm_decomp and smar_posSemidef; verified under C2w with the real inverse — the dagger-general form is not consumed downstream), Part 2 = slavedSeed_corner(_posDef) via the verified criterion_w, Part 3 = slavedSeed_slaved. lem:lowsqueeze = lowsqueeze_tendsto (LowSqueeze.lean): the trajectory rides the explicit chart (lowTraj_decomp — the Lean's implementation of eq:pi-collapse: the decomposition IS the Pi-collapse, with P_T the conditional block), all four data converge (redP -> P_inf by the ReducedImport, Lam1a by lem:condfilter-3, Lamma -> 0 by lem:loading, Saa -> Sigma_inf|aa by lem:jtransform), and the assembly converges in norm. Domination = slavedSeed_le_Sig0 + dareIter_mono. Convergence only — the deck's exponential-rate claim is not formalized (it is visible in the displayed geometric bounds but not extracted). Axioms clean. -->
<!-- verify: GATE-2. Pi_T collapse eq:pi-collapse: ||Pi_T Sig^ea Pi_T' - Sig_T|| < 3.8e-16 over delta in {1,1e-3,1e-6}, T=0..399 (check_pi_collapse.py). Full convergence ||Sig_T - Sig_inf|| -> 0 delta-independent, all blocks (check_full_conv.py, check_pi_collapse.py): Sig|11->1.22, Sig|1a->1.10, Sig|aa->13.85, Sig|mm->0. Domination Sigma0 - underSigma0 >= -1e-8 over 2000 random priors (lem:slaved-seed, check_slaved_seed.py). Block-limit identification -> values at Sigma_inf, diffs 1e-6 at T=400 (check_limits_match.py). -->
<!-- verify: hypotheses/DAG. lem:slaved-seed: fact:schur, eq:three-block + eq:prior-pos(b) (Sig_a>0<=>C2w). NO floor, NO C3w. lem:lowsqueeze: lem:slaved-seed (domination, seed), eq:comparison (monotone-in-IC), lem:loading (eq:row-slaved slaving, eq:loading-conv Lambda_ma->0), lem:jtransform (eq:J1-home antistable homes floor-free), lem:condfilter (eq:condcov/eq:condric/eq:cf-rec: P_T, Lambda_1a bounded/convergent), lem:structure-marg (eq:marg-extinct Sigma_inf|.m=0). CONSUMER: 06-sufficiency (lower half of the squeeze). -->
<!-- verify: CONFINEMENT — MARGINAL (GAS) branch. Does NOT read C3w. Floor-free: the antistable floor is EARNED (lem:jtransform source-boundedness via lem:condfilter), not assumed; the retired riccastep floors (eq:Jaa-bound/eq:Lfloor), lem:reduced-forget, omega-limit, lem:robust-with-floor are all DROPPED. Discrete dual of CW eq:lowsqueeze. -->

<!-- 04-evolution — MAIN TEXT: the discrete J-transform on the slaved block. -->
<!-- This is arc2's core contribution — the discrete image of the Callier-Winkin J-transform — so it is a -->
<!-- main-text anchor lemma feeding the lower anchor 05-lowsqueeze, not an appendix result. -->
<!-- The rank-chart isolates the antistable information J_1 = (Sigma|aa)^{-1} from the rank-deficient -->
<!-- (marginal-slaved) e2-block; J_1 rides a FIXED A_a^{-1}-Stein recursion driven by a data source Xi_T. -->
<!-- Source-boundedness is the antistable-DARE floor, and it closes NON-CIRCULARLY via the conditional-filter -->
<!-- loading lem:condfilter: e_1 is conditionally FILTERED (its own isolated Kalman-Riccati), not slaved. -->
<!-- Discrete dual of CW app:evolution eq:Jsys/eq:J12-decay/eq:J1-limit; the second loading Lambda_1a has no -->
<!-- CW analog (CW's antistrong coordinates carry no stable block), and is exactly what this file must earn. -->
<!-- sec:evolution — main text -->
### The discrete $J$-transform (main text)

The lower anchor's evolution is read on a chart of the singular uncontrollable block: the antistable information plus two loadings. Two of the three pieces are slaved-block dynamics — the marginal loading `lem:loading` (this section) and the antistable information `lem:jtransform` — while the stabilizable loading `lem:condfilter` is the conditionally-filtered piece with no continuous-time analog. We first record the marginal slaving.

<!-- lem:loading -->
### Lemma (lem:loading) — Full marginal slaving and the loading dynamics

Seed the lower trajectory with the slaved $\underline\Sigma_0$ of `lem:slaved-seed` (`eq:Ldef-slaved`): its uncontrollable block is rank-$n_a$, antistable-supported, with $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_a\succ0$ (C2w) and marginal row slaved (`eq:seed-slaved`) by the seed loading $\Lambda_{ma,0}=\Sigma_{ma}\Sigma_{aa}^{-1}$. Define the **marginal loading** $\Lambda_{ma} := \underline\Sigma_T\!\mid_{ma}(\underline\Sigma_T\!\mid_{aa})^{-1}$ (well defined, $\underline\Sigma_T\!\mid_{aa}\succ0$ by `lem:structure`-3). Then for every $T\ge0$:

<!-- lem:loading-a -->
**(a) (Full row slaving.)** The whole marginal row is the antistable row scaled by the loading,

<!-- eq:row-slaved -->
$$ \underline\Sigma_T\!\mid_{m,:} = \Lambda_{ma}\,\underline\Sigma_T\!\mid_{a,:}, \tag{eq:row-slaved} $$

so $\underline\Sigma_T\!\mid_{mm}=\Lambda_{ma}\underline\Sigma_T\!\mid_{am}$, $\underline\Sigma_T\!\mid_{m1}=\Lambda_{ma}\underline\Sigma_T\!\mid_{a1}$ — the marginal carries no covariance independent of the antistable, in *any* block. The measurement update preserves it with the **same** loading, $\hat\Lambda_{ma}=\Lambda_{ma}$.

<!-- lem:loading-b -->
**(b) (Loading recursion and geometric decay.)** In the dynamics-decoupled frame `eq:three-block` ($A_{ma}=0$),

<!-- eq:loading-rec -->
$$ \Lambda_{ma}^+ = A_m\,\Lambda_{ma}\,A_a^{-1}, \tag{eq:loading-rec} $$

a Stein map with $\rho = \rho(A_m)\rho(A_a^{-1}) = \rho(A_a^{-1}) < 1$ (`eq:A2-inv`), so

<!-- eq:loading-conv -->
$$ \Lambda_{ma,T} \longrightarrow 0 \quad\text{geometrically at rate } \rho(A_a^{-1}). \tag{eq:loading-conv} $$

*Proof.* **(a),(b) by induction.** At $T=0$, `eq:seed-slaved` gives the base case. Assume `eq:row-slaved` at $T$. Since $(\Sigma C')\!\mid_{m,:}=\Lambda_{ma}(\Sigma C')\!\mid_{a,:}$, the update inherits it: $\mathcal U(\underline\Sigma_T)\!\mid_{m,:}=\Lambda_{ma}\,\mathcal U(\underline\Sigma_T)\!\mid_{a,:}$, i.e. $\hat\Lambda_{ma}=\Lambda_{ma}$. With $A\!\mid_{m,:}=[\,0\ A_m\ 0\,]$ (decoupled, $A_{ma}=0$), $A\!\mid_{a,:}=[\,0\ 0\ A_a\,]$, $G\!\mid_{m,:}=0$, prediction gives $\underline\Sigma_{T+1}\!\mid_{m,:}=A_m\,\mathcal U\!\mid_{m,:}\,A'=A_m\Lambda_{ma}\,\mathcal U\!\mid_{a,:}\,A'$ and $\underline\Sigma_{T+1}\!\mid_{a,:}=A_a\,\mathcal U\!\mid_{a,:}\,A'$, so $\underline\Sigma_{T+1}\!\mid_{m,:}=A_m\Lambda_{ma}A_a^{-1}\,\underline\Sigma_{T+1}\!\mid_{a,:}$ — this is `eq:row-slaved` at $T+1$ with the loading `eq:loading-rec`. The Stein spectrum is the product set $\{\mu\eta:\mu\in\operatorname{spec}(A_m),\eta\in\operatorname{spec}(A_a^{-1})\}$; every $|\mu|=1$, $|\eta|<1$, so $\rho<1$ and `eq:loading-conv` follows (`fact:schur-decay`; a defective marginal Jordan block contributes only a bounded polynomial factor absorbed into the rate, since $\rho(A_a^{-1})$ strictly dominates). ∎

**Remark (why the marginal does not obstruct the forgetting).** The marginal's whole contribution to $\underline\Sigma_T$ is the deterministic readout `eq:row-slaved` of the antistable block through $\Lambda_{ma}$; both factors converge geometrically (`eq:loading-conv` and `lem:jtransform`), so the marginal blocks converge *with* them at the antistable rate $\rho(A_a^{-1})$, never at the unit-circle rate of $A_m$ — the eigenvalues of $A_m$ enter only multiplied by $\rho(A_a^{-1})$. This is CW's $J_{12}$-decay (`eq:J12-decay`), discretized. **Condition hygiene:** uses only $\delta\Sigma_a\succ0$ (via `lem:structure`-3) and `eq:A2-inv`; no floor, no C3w.

<!-- verify: LEAN (phase B): lem:loading = RowSlaved + RowSlaved.updM (hatLam = Lam) + RowSlaved.dareStep (eq:loading-rec) + rowSlaved_dareIter (closed form Lam_T = Am^T Lam0 (Aa^-1)^T) + Aa_inv_isSchurStable + loading_tendsto (eq:loading-conv), Estimation/Dare/Loading.lean; base case = slavedSeed_slaved (SlavedSeed.lean). Matrix-row implementation of eq:row-slaved (embM' Sigma = Lam embA' Sigma). Axioms clean. -->
<!-- verify: (a) full-row slaving ||Sig|m,: - Lambda_ma Sig|a,:|| < 1.1e-14 incl. e1-marginal cross, T=1..11; hatLam_ma=Lambda_ma exact (check_full_slaving.py). (b) ||Lam_{T+1} - A_m Lam_T A_a^-1|| < 3e-15, T=0..9; ||Lam_ma|| -> 0 at ratio -> rho(A_a^-1) (check_loading_rec.py). Binding case (defective marginal Jordan / unit-circle A_m): rho unchanged = rho(A_m)rho(A_a^-1). PORT of riccastep 07-loading-v4 (decoupled-frame specialization A_ma=0). -->
<!-- verify: deps — a02-machinery (Rmap/U, the A|m,:=[0 A_m 0]/A|a,:=[0 0 A_a]/G no-e2-row structure of eq:three-block), eq:A2-inv, lem:structure-3 (Sig_T|aa>0), fact:schur-decay, lem:slaved-seed (eq:seed-slaved base case). CONSUMERS: lem:condfilter (hatLam_ma=Lambda_ma, Lambda_ma->0), lem:jtransform (Ceff convergence), 05-lowsqueeze (marginal half of the anchor). -->

The lower anchor stays slaved for all $T$ (`lem:loading`): its uncontrollable block $\underline\Sigma_T\!\mid_{22}$ is rank-$n_a$, supported on the antistable coordinates, with $\underline\Sigma_T\!\mid_{aa}\succ0$ (`lem:structure`-3, since $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_a\succ0$ under C2w). The full block is singular and cannot be inverted; instead **chart it by its full-rank antistable corner** — the antistable information and the two loadings

<!-- eq:jchart -->
$$ J_1 := (\underline\Sigma_T\!\mid_{aa})^{-1}, \qquad \Lambda_{ma} := \underline\Sigma_T\!\mid_{ma}(\underline\Sigma_T\!\mid_{aa})^{-1}, \qquad \Lambda_{1a} := \underline\Sigma_T\!\mid_{1a}(\underline\Sigma_T\!\mid_{aa})^{-1}, \tag{eq:jchart} $$

with the marginal recovered by slaving, $\underline\Sigma_T\!\mid_{mm} = \Lambda_{ma}\,\underline\Sigma_T\!\mid_{aa}\,\Lambda_{ma}'$. Invert only the antistable corner; carry the loadings separately. On this chart the antistable information rides a *fixed* $A_a^{-1}$-Stein recursion (`lem:jtransform`, the discrete image of the Callier–Winkin $J$-transform `eq:Jsys`), whose source is the measurement's antistable information increment. The marginal loading $\Lambda_{ma}$ decays autonomously (`lem:loading`, CW's $J_{12}$). The *second* loading $\Lambda_{1a}$ — the stabilizable block's regression onto the antistable — has no CW analog: it exists only because the strong (not antistrong) closed loop retains a stable block $A_c=e_1$, and controlling it is the one genuinely new step. It closes because **$e_1$ is not slaved but conditionally filtered**, `lem:condfilter`.

<!-- lem:condfilter -->
### Lemma (lem:condfilter) — The conditional-filter loading is bounded and homes

On the slaved lower trajectory, write the **conditional covariance** of $e_1$ given $e_a$,

<!-- eq:condcov -->
$$ P_T := \underline\Sigma_T\!\mid_{11} - \Lambda_{1a}\,\underline\Sigma_T\!\mid_{aa}\,\Lambda_{1a}' \;=\; \underline\Sigma_T\!\mid_{11} - \underline\Sigma_T\!\mid_{1a}(\underline\Sigma_T\!\mid_{aa})^{-1}\underline\Sigma_T\!\mid_{a1} \;\succeq\;0, \tag{eq:condcov} $$

and the conditional-filter gain and error map

<!-- eq:condgain -->
$$ K_T := P_T C_1'\big(R + C_1 P_T C_1'\big)^{-1}, \qquad L_T := A_1\big(I - K_T C_1\big). \tag{eq:condgain} $$

Then:

<!-- lem:condfilter-1 -->
**1. (The conditional covariance is an isolated $e_1$-filter, independent of the antistable scale.)** $P_T$ obeys the Kalman–Riccati recursion of the reduced system $(A_1, C_1, G_1)$,

<!-- eq:condric -->
$$ P_{T+1} = A_1\big(I - K_T C_1\big) P_T A_1' + G_1 Q G_1' \;=\; L_T P_T A_1' + G_1 Q G_1', \tag{eq:condric} $$

in which the antistable block $\underline\Sigma_T\!\mid_{aa}$ does not appear. By C1 (its restriction $(A_1,C_1)$ detectable) and $(A_1,G_1)$ stabilizable, $P_T\to P_\infty$, so $K_T$ is bounded, $L_T\to L_\infty$, and $\rho(L_\infty) < 1$ (`fact:schur-decay`): the transition products $\Phi_L(T,j) := L_{T-1}\cdots L_j$ are uniformly bounded, $\sup_{T\ge j}\|\Phi_L(T,j)\| \le c_L < \infty$.

<!-- lem:condfilter-2 -->
**2. (Loading recursion.)** The measurement sends the loading through the conditional error map, $\hat\Lambda_{1a} = (I - K_T C_1)\Lambda_{1a} - K_T(C_a + C_m\Lambda_{ma})$, and prediction closes it:

<!-- eq:cf-rec -->
$$ \Lambda_{1a}^+ = L_T\,\Lambda_{1a}\,A_a^{-1} + d_T, \qquad d_T := \big[\,A_{1a} + A_{1m}\Lambda_{ma} - A_1 K_T(C_a + C_m\Lambda_{ma})\,\big]A_a^{-1}. \tag{eq:cf-rec} $$

<!-- lem:condfilter-3 -->
**3. (Bounded, and homes.)** $\sup_{T\ge0}\|\Lambda_{1a,T}\| < \infty$, and $\Lambda_{1a,T}\to\Lambda_{1a}^\infty$, the unique fixed point of $\Lambda = L_\infty\Lambda A_a^{-1} + d_\infty$.

*Proof.*

**Part 1.** Slaving decomposes the covariance through the regression $(x_1, x_a, x_m) = M(e, x_a)$, $e := x_1 - \Lambda_{1a}x_a$, $x_m = \Lambda_{ma}x_a$, with $M = \big[\begin{smallmatrix} I & \Lambda_{1a} \\ 0 & I \\ 0 & \Lambda_{ma}\end{smallmatrix}\big]$ and $(e, x_a)$ uncorrelated of covariance $\operatorname{blkdiag}(P_T, \underline\Sigma_T\!\mid_{aa})$. Hence $C M = [\,C_1,\ C_{\mathrm{eff}}\,]$ with the **effective antistable observation**

<!-- eq:Ceff -->
$$ C_{\mathrm{eff}} := C_a + C_1\Lambda_{1a} + C_m\Lambda_{ma}, \tag{eq:Ceff} $$

so $C\underline\Sigma_T C' + R = C_1 P_T C_1' + C_{\mathrm{eff}}\,\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}' + R$. Conditioning on $x_a$, the measurement residual is $y - C_{\mathrm{eff}}x_a = C_1 e + v$ with $v\sim(0,R)$: the conditional part $e$ is observed through $(A_1, C_1)$ with noise $R$ alone. Its update is the Kalman contraction $\mathcal U_1(P) = (I - K_T C_1)P = P - P C_1'(C_1 P C_1' + R)^{-1}C_1 P$, and its one-step prediction is $A_1(\cdot)A_1' + G_1 Q G_1'$ ($x_a^+ = A_a x_a$ is deterministic given $x_a$, contributing no conditional covariance). Composing gives `eq:condric`, in which $\underline\Sigma_T\!\mid_{aa}$ is absent. The pair $(A_1, C_1)$ is detectable and $(A_1, G_1)$ stabilizable (C1, restricted to $e_1$), so `eq:condric` converges to the reduced stabilizing solution $P_\infty$ (`fact:dare-strong` on the reduced system), whose closed loop $L_\infty = A_1(I - K_\infty C_1)$ is Schur; $L_T\to L_\infty$ gives uniformly bounded products (`fact:schur-decay`).

**Part 2.** With $S := C\underline\Sigma_T C' + R$ and the slaving identities $\underline\Sigma_T\!\mid_{a\bullet}C' = \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'$, $\underline\Sigma_T\!\mid_{1\bullet}C' = P_T C_1' + \Lambda_{1a}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'$, the update blocks are
$$ \mathcal U(\underline\Sigma_T)\!\mid_{aa} = \big(I - \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\big)\underline\Sigma_T\!\mid_{aa}, \qquad \mathcal U(\underline\Sigma_T)\!\mid_{1a} = \big[\Lambda_{1a} - P_T C_1'S^{-1}C_{\mathrm{eff}} - \Lambda_{1a}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\big]\underline\Sigma_T\!\mid_{aa}. $$
Dividing and applying the push-through identity $S^{-1}C_{\mathrm{eff}}\big(I - \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\big)^{-1} = \tilde S^{-1}C_{\mathrm{eff}}$, where $\tilde S := S - C_{\mathrm{eff}}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}' = R + C_1 P_T C_1'$, collapses the post-update loading to
$$ \hat\Lambda_{1a} := \mathcal U(\underline\Sigma_T)\!\mid_{1a}\big(\mathcal U(\underline\Sigma_T)\!\mid_{aa}\big)^{-1} = \Lambda_{1a} - P_T C_1'\tilde S^{-1}C_{\mathrm{eff}} = \Lambda_{1a} - K_T C_{\mathrm{eff}} = (I - K_T C_1)\Lambda_{1a} - K_T(C_a + C_m\Lambda_{ma}), $$
the last step by `eq:Ceff`. The marginal row, being slaved, keeps its loading through the update, $\hat\Lambda_{ma} = \Lambda_{ma}$ (`lem:loading`, Part (a)). Feeding both post-update loadings through the cross-block prediction identity $\underline\Sigma_{T+1}\!\mid_{1a} = A_{1\bullet}\,\mathcal U(\underline\Sigma_T)\!\mid_{\bullet a}\,A_a'$ (valid since $GQG'\!\mid_{1a}=0$; the same identity that drives `lem:structure`-3 on the diagonal) and dividing by $\underline\Sigma_{T+1}\!\mid_{aa} = A_a\,\mathcal U(\underline\Sigma_T)\!\mid_{aa}\,A_a'$:
$$ \Lambda_{1a}^+ = \big(A_1\hat\Lambda_{1a} + A_{1a} + A_{1m}\hat\Lambda_{ma}\big)A_a^{-1} = A_1\big[(I - K_T C_1)\Lambda_{1a} - K_T(C_a + C_m\Lambda_{ma})\big]A_a^{-1} + \big(A_{1a} + A_{1m}\Lambda_{ma}\big)A_a^{-1}, $$
which regroups to `eq:cf-rec`.

**Part 3.** Unrolling `eq:cf-rec`,
$$ \Lambda_{1a,T} = \Phi_L(T,0)\,\Lambda_{1a,0}\,A_a^{-T} + \sum_{j=0}^{T-1}\Phi_L(T,j+1)\,d_j\,A_a^{-(T-1-j)}. $$
Each summand is bounded on the left by $\|\Phi_L\|\le c_L$ (Part 1) and on the right by $\|A_a^{-(T-1-j)}\|\le c_a\gamma^{\,T-1-j}$, $\gamma := \rho(A_a^{-1})+\epsilon < 1$ (`eq:A2-inv`, `fact:schur-decay`); the drive is bounded, $\|d_j\|\le \bar d < \infty$, since $\Lambda_{ma}\to0$ and $K_T$ is bounded (Part 1). Hence $\|\Lambda_{1a,T}\| \le c_L c_a\|\Lambda_{1a,0}\|\gamma^T + c_L c_a\bar d\sum_{k\ge0}\gamma^k < \infty$, uniformly in $T$ — a two-sided sandwich, decaying on **both** ends. (The per-step ratio $\hat\Lambda_{1a}/\Lambda_{1a}$ may be arbitrarily large; it is not the transition operator, $\Phi_L$ is.) For convergence, $L_T\to L_\infty$ and $d_T\to d_\infty := [A_{1a} - A_1 K_\infty C_a]A_a^{-1}$ (using $\Lambda_{ma}\to0$), and the limiting Stein operator $\Lambda\mapsto L_\infty\Lambda A_a^{-1}$ has spectral radius $\rho(L_\infty)\rho(A_a^{-1}) < 1$, so the asymptotically-autonomous recursion `eq:cf-rec` converges to its unique fixed point $\Lambda_{1a}^\infty = (I - L_\infty(\cdot)A_a^{-1})^{-1}d_\infty$. ∎

<!-- lem:jtransform -->
### Lemma (lem:jtransform) — Antistable information homes, floor-free

On the slaved lower trajectory, the antistable information $J_1 = (\underline\Sigma_T\!\mid_{aa})^{-1}$ obeys the fixed $A_a^{-1}$-Stein recursion

<!-- eq:J1-rec -->
$$ J_1^+ = A_a^{-1\prime}\big[\,J_1 + \Xi_T\,\big]A_a^{-1}, \qquad \Xi_T := \big(\mathcal U(\underline\Sigma_T)\!\mid_{aa}\big)^{-1} - (\underline\Sigma_T\!\mid_{aa})^{-1} = C_{\mathrm{eff}}'\,\tilde S^{-1}\,C_{\mathrm{eff}} \;\succeq\;0, \tag{eq:J1-rec} $$

with $C_{\mathrm{eff}}$ of `eq:Ceff` and $\tilde S = R + C_1 P_T C_1'$. The source is bounded and convergent, and

<!-- eq:J1-home -->
$$ \Lambda_{ma}\to0, \qquad \Lambda_{1a}\to\Lambda_{1a}^\infty, \qquad J_1 \longrightarrow (\Sigma_\infty\!\mid_{aa})^{-1} \quad\text{(exp. fast, floor-free).} \tag{eq:J1-home} $$

*Proof.* **The recursion.** The unconditional $(a,a)$-block identity (`app:machinery`-2, $GQG'\!\mid_{aa}=0$, $A_2 = A_a\oplus A_m$ block-diagonal) is $\underline\Sigma_{T+1}\!\mid_{aa} = A_a\,\mathcal U(\underline\Sigma_T)\!\mid_{aa}\,A_a'$; inverting (both sides $\succ0$ by `lem:structure`-3, $A_a$ nonsingular by `eq:A2-inv`) gives the first form of `eq:J1-rec`, with $\Xi_T = (\mathcal U(\underline\Sigma_T)\!\mid_{aa})^{-1} - (\underline\Sigma_T\!\mid_{aa})^{-1}\succeq0$ (the update contracts the block, `fact:update-kernel`). The closed form $\Xi_T = C_{\mathrm{eff}}'\tilde S^{-1}C_{\mathrm{eff}}$ is the Woodbury dual of the antistable update block computed in `lem:condfilter`-2. Writing $S := C\underline\Sigma_T C' + R$, that block is $\mathcal U(\underline\Sigma_T)\!\mid_{aa} = \underline\Sigma_T\!\mid_{aa} - \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\,\underline\Sigma_T\!\mid_{aa}$; the matrix-inversion lemma gives
$$ \big(\underline\Sigma_T\!\mid_{aa} - \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\,\underline\Sigma_T\!\mid_{aa}\big)^{-1} = (\underline\Sigma_T\!\mid_{aa})^{-1} + C_{\mathrm{eff}}'\big(S - C_{\mathrm{eff}}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'\big)^{-1}C_{\mathrm{eff}}, $$
and the reduced innovation $S - C_{\mathrm{eff}}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}' = R + C_1 P_T C_1' = \tilde S$ (the $C_{\mathrm{eff}}\underline\Sigma_T\!\mid_{aa}C_{\mathrm{eff}}'$ terms cancel, `lem:condfilter`-1), so the increment is $\Xi_T = C_{\mathrm{eff}}'\tilde S^{-1}C_{\mathrm{eff}}$.

**Source-boundedness (the antistable floor).** $\tilde S = R + C_1 P_T C_1'\succeq R\succ0$ is bounded below, and bounded above since $P_T$ is bounded (`lem:condfilter`-1); $C_{\mathrm{eff}} = C_a + C_1\Lambda_{1a} + C_m\Lambda_{ma}$ is bounded since both loadings are (`lem:condfilter`-3, `lem:loading`). Hence $\sup_T\|\Xi_T\| < \infty$: the source is bounded with **no floor on $\underline\Sigma_T\!\mid_{aa}$ assumed** — the would-be circularity ($\Xi_T$ bounded $\iff\underline\Sigma_T\!\mid_{aa}$ floored) is broken because the loadings are controlled by the conditional filter, whose recursion `eq:condric` never reads $\underline\Sigma_T\!\mid_{aa}$.

**Homing.** Unrolling `eq:J1-rec` is `eq:Jgram` restricted to the antistable corner,
$$ J_{1,T} = \big(A_a^{-T}\big)'J_{1,0}\,A_a^{-T} + \sum_{j=0}^{T-1}\big(A_a^{-(T-1-j)}\big)'\,W_j\,A_a^{-(T-1-j)}, \qquad W_j := A_a^{-1\prime}\Xi_j A_a^{-1}\succeq0. $$
The seed term vanishes ($A_a^{-1}$ Schur, `eq:A2-inv`). By `lem:condfilter`-3 and `lem:loading` the loadings converge, so $C_{\mathrm{eff}}\to C_a + C_1\Lambda_{1a}^\infty$ and $\tilde S\to R + C_1 P_\infty C_1'$, whence $\Xi_T\to\Xi_\infty$ and $W_j\to W_\infty$; the gramian of a convergent source against the Schur weight $A_a^{-1}$ converges (exp. fast, dominated by $\gamma^{2(T-j)}$). The limit solves the Stein equation $J_1^\infty = A_a^{-1\prime}(J_1^\infty + \Xi_\infty)A_a^{-1}$. Its coefficients match those at the fixed point: $P_\infty$ and $\Lambda_{1a}^\infty$ are the unique fixed points of `eq:condric` and `eq:cf-rec`, which are also solved by the values $\Sigma_\infty\!\mid_{1|a}$ and $\Sigma_\infty\!\mid_{1a}(\Sigma_\infty\!\mid_{aa})^{-1}$ read off the strong solution (the DARE fixed point satisfies both recursions), so by uniqueness $\Xi_\infty = C_{\mathrm{eff}}(\Sigma_\infty)'\tilde S(\Sigma_\infty)^{-1}C_{\mathrm{eff}}(\Sigma_\infty)$ is the steady antistable increment at $\Sigma_\infty$. But $(\Sigma_\infty\!\mid_{aa})^{-1}$ solves that same Stein equation (`eq:Sinf-gram`, `lem:structure`-1 / `lem:structure-marg`), so by uniqueness of the Stein solution ($A_a^{-1}$ Schur) $J_1^\infty = (\Sigma_\infty\!\mid_{aa})^{-1}$, which is `eq:J1-home`. The rate is geometric, set by $\max\{\rho(A_a^{-1})^2,\ \rho(L_\infty),\ \rho(A_a^{-1})\}$ — all $<1$, no marginal eigenvalue among them: the marginal enters only through $\Lambda_{ma}$, and there $|\lambda(A_m)|=1$ is multiplied by $\rho(A_a^{-1})<1$ (`lem:loading`). ∎

<!-- verify: LEAN (phase B): lem:condfilter Parts 1-2 = the conditional-chart step (Estimation/Dare/CondChart.lean): the decomposition Sigma = e1 P e1' + V Saa V' (V = e1 Lam1a + eA + eM Lamma) is preserved by the measurement update (chart_updM, via the generic twoblock_update whose push-through identities inv_bracket/pushthrough/uhat_mul_inv_form are all consequences of S = Stil + Ceff Saa Ceff') and by prediction (chart_dareStep: P -> the ISOLATED reduced Riccati eq:condric in which Saa never appears — the non-circular foothold, verified by construction of redP; Lam1a -> eq:cf-rec via lamNext; Saa -> the (a,a)-identity). Part 3 = lowLam1a_tendsto (LowSqueeze.lean): gain/loop/drive continuity + the fixed point from strong_chart_fixed + lam_unroll against the transition products + the geometric-kernel convolution. The analytic import is DISCHARGED (phase D): the reduced fact:dare-strong is a theorem — redP_exists_stabilizing (Estimation/Dare/Reduced.lean: zero-seed monotone-bounded convergence via monotone_psd_tendsto + eq:bounded, fixed point via dareStep_diff, Schur loop via the one-step PBH-Stein fixed_point_schur, uniqueness) — with the limit identified as the strong chart component (redP_tendsto_infP, Estimation/Dare/ReducedFacts.lean) and the product bound proved geometric (redProdF_geometric via fact:uniexp's verified half). The exponential-rate qualifier is now VERIFIED (phase E): lowLam1a_geometric (Estimation/Dare/LowRate.lean; lam_unroll against the geometric products redProdF_geometric with Lipschitz drive errors + the geometric convolution geom_conv_le), riding redP_geometric (the exact two-seed factorization of the reduced Riccati). -->
<!-- verify: LEAN (phase B): lem:jtransform: eq:J1-rec = lowJ_rec (CondChart.lean; the Woodbury dual is uhat_inv_eq, U-hat^-1 = Saa^-1 + Ceff' Stil^-1 Ceff, proved from S = Stil + Ceff Saa Ceff' alone); source-boundedness/convergence = ceff_tendsto + redStilInv_tendsto (the R-floor via Loewner inversion — no Saa-floor anywhere); homing eq:J1-home = lowSaa_tendsto (LowSqueeze.lean): conj_unroll of the information error against the Schur Aa^-1 powers (rho = rho(Aa^-1)^2) + inversion continuity under the eq:bounded ceiling; the RATE is now verified (phase E): lowJ_geometric (kernel rho(Aa^-1)^2 exactly as displayed) + lowSaa_geometric (resolvent transfer; Estimation/Dare/LowRate.lean). Limit identification: instead of the deck's uniqueness-of-fixed-points prose, the Lean gives Sigma_inf its own chart (strong_decomp, zero marginal loading by eq:marg-extinct) and reads the fixed-point identities off chart extraction (strong_chart_fixed) — same content, constructive. Axioms clean. -->
<!-- verify: GATE-2 all recursions on the slaved trajectory, delta in {1, 1e-3, 1e-6}, and on 300-400 random 3-block C3w-marginal systems. -->
<!-- eq:J1-rec: J_1^+ = A_a^-T'[J_1 + Xi]A_a^-1 with Xi = (U|aa)^-1 - (Sig|aa)^-1, resid 0 exactly (the inverted (a,a)-identity); check_A_corrected.py, check_full_conv.py. -->
<!-- eq:condric: P_T = Sigma_{1|a} obeys the ISOLATED e1 Kalman-Riccati P^+ = A1(I-KC1)P A1' + G1QG1', NO Sigma_aa; resid 4e-16 (check_condfilter.py). Non-circular foothold. -->
<!-- eq:cf-rec: Lambda_1a^+ = A1(I-K_TC1)Lambda_1a A_a^-1 + d_T, resid 1e-16 (check_condfilter.py). Post-update hatLam_1a = Lam_1a - K Ceff (push-through), resid 1e-4 modulo conditioning across 300 random systems; the +K sign in the first-pass was wrong (check_condfilter2.py). -->
<!-- Boundedness: naive per-step ratio ||hatLam||/||Lam|| hits 206-457x on adversarial systems, but sup_T||Lambda_1a|| bounded (65.8 worst) via the stable product Phi_L; the ratio is NOT the transition operator (check_postupdate_loading.py, check_condfilter2.py). -->
<!-- ADVERSARIAL GATE (Call D, check_condfilter_adversarial.py): on the witness stablistep-handoff §3 NAMES (strong antistable<->e_1 running-prior correlation, weighted antistable obs), the NAIVE bound W_T <= Wbar:=A_a^{-'}C_a'R^{-1}C_a A_a^{-1} FAILS on ~all steps (599999 violations / 200 trials) — we are squarely in the §3 trap regime — yet lem:condfilter holds: worst sup_T||Lambda_1a||=14.5 bounded, min eig(Sigma_T|aa)=1.4e-2>0 floored, 200/200 converge. The floor is closed with the handoff's own discipline (adversarial, not benign, witness) satisfied. -->
<!-- Homing/identification: Lambda_1a, P=Sig_1|a, J_1=1/Saa all -> their values AT Sigma_inf (diffs 1e-6 at 400 steps), so J_1 -> (Sigma_inf|aa)^-1 the CORRECT limit (check_limits_match.py). rho(L_inf)=0.234<1, loading rate rho(L)rho(A_a^-1)=0.117. -->
<!-- verify: hypotheses/DAG. lem:condfilter: C1 (restricted (A1,C1) detectable), (A1,G1) stabilizable, app:machinery ((a,a) and (1,a) block identities via GQG'|1a=GQG'|aa=0), eq:A2-inv, lem:loading (Lambda_ma slaved, hatLam_ma=Lambda_ma, ->0), fact:dare-strong (reduced e1 stabilizing solution), fact:schur-decay. NO Sigma_aa-floor, NO C3w. lem:jtransform: app:machinery-2, eq:A2-inv, fact:update-kernel, lem:structure-3 (Sig_aa>0), lem:condfilter + lem:loading (source bdd/convergent), eq:Sinf-gram + lem:structure-1/lem:structure-marg (limit identification). CONSUMER: 05-lowsqueeze (antistable half of the lower anchor). Confinement: MARGINAL branch, does not read C3w. -->
<!-- verify: CW correspondence. eq:J1-rec = discrete dual of CW eq:Jsys (dot J_1 = -J_1 A_-1* - A_-1 J_1 + (B_1+J_12 B_2)(...)*), with A_a^{-1} <-> Hurwitz -A_-1, Xi_T = Ceff' Stil^-1 Ceff <-> the (B_1+J_12 B_2)(...)* input-Gram, Lambda_ma <-> J_12 (both autonomous, ->0). The EXTRA piece Lambda_1a (=> lem:condfilter) has NO CW analog: CW's antistrong coordinates carry no stable block, so its source has one loading; the discrete strong solution keeps A_c=e_1, forcing the second. -->

<!-- app:machinery — the engines of the squeeze: comparison, the e2-information A2^{-1} reversal, and the -->
<!-- gap engine (difference identity + gap-Riccati). The gap engine is promoted here because all three -->
<!-- consumers (upper anchor, lower forgetting, robustness) use it. -->
<!-- app:machinery -->
### Comparison principle, the $A_2^{-1}$ information recursion, and the gap engine

Write the recursion `eq:cov-rec` as $\Sigma_{T+1} = \mathcal{R}(\Sigma_T)$ with

<!-- eq:Rmap -->
$$ \mathcal{R}(\Sigma) := A\, \mathcal{U}(\Sigma)\, A' + GQG' \qquad \mathcal{U}(\Sigma) := \Sigma - \Sigma C'\big(C\Sigma C' + R\big)^{-1} C\Sigma \tag{eq:Rmap} $$

$\mathcal{U}$ is the measurement update; for $\Sigma \succ 0$, $\mathcal{U}(\Sigma) = (\Sigma^{-1} + C'R^{-1}C)^{-1}$ (information form). We work in the frame `eq:three-block`, $A = \big[\begin{smallmatrix} A_1 & A_{12} \\ 0 & A_2 \end{smallmatrix}\big]$ in the $(e_1, e_2)$ split, $G = \operatorname{col}(G_1, 0)$, $A_2 = A_a \oplus A_m$ nonsingular (`eq:A2-inv`).

<!-- app:machinery-1 -->
**1. (Comparison principle — monotonicity in the initial condition.)** $\mathcal{R}$ is monotone in the Löwner order, and hence so is every iterate:

<!-- eq:comparison -->
$$ L_1 \preceq L_2 \quad\Longrightarrow\quad \mathcal{R}^T(L_1) \preceq \mathcal{R}^T(L_2) \qquad T \ge 0 \tag{eq:comparison} $$

This is the one result we import rather than re-derive: the monotone dependence of the Riccati recursion on its initial condition (Poubelle, Petersen, Gevers and Bitmead 1986; Bitmead, Gevers and Petersen 1985; De Nicolao and Gevers 1992, Lemma 1). We include its short proof for completeness; everything downstream — both anchors of the squeeze — is built on it and re-derived in-deck.

<!-- app:machinery-2 -->
**2. (The $e_2$-information reverses by $A_2^{-1}$.)** Suppose $\Sigma_T\!\mid_{22} \succ 0$ for $T \ge T_0$ (supplied by the antistable seed, `lem:structure`-3). The $e_2$-block information $J_T := (\Sigma_T\!\mid_{22})^{-1}$ obeys the **linear** recursion

<!-- eq:Jrec -->
$$ J_{T+1} = A_2^{-1\prime}\, J_T\, A_2^{-1} + W_T \qquad W_T = W_T' \succeq 0 \tag{eq:Jrec} $$

so, unrolling from $T_0$,

<!-- eq:Jgram -->
$$ J_T = \big(A_2^{-(T-T_0)}\big)'\, J_{T_0}\, A_2^{-(T-T_0)} + \sum_{j=T_0}^{T-1} \big(A_2^{-(T-1-j)}\big)'\, W_j\, A_2^{-(T-1-j)} \tag{eq:Jgram} $$

an $A_2^{-1}$-driven gramian — the discrete object on which the whole development turns.

<!-- app:machinery-3 -->
**3. (The gap engine — difference identity and gap-Riccati.)** For $A_\sharp, B_\sharp = A_\sharp', B_\sharp' \succeq 0$, with $F(\Sigma) := A(I - L(\Sigma)C)$, $L(\Sigma) = \Sigma C'(C\Sigma C'+R)^{-1}$ (the error map `eq:filter`),

<!-- eq:diff-id -->
$$ \mathcal{R}(A_\sharp) - \mathcal{R}(B_\sharp) = F(A_\sharp)\,\big(A_\sharp - B_\sharp\big)\,F(B_\sharp)' \tag{eq:diff-id} $$

Unrolling along two trajectories $P_T^X := \mathcal{R}^T(X)$, $P_T^Y := \mathcal{R}^T(Y)$, with error-map products $\Phi_T^X := F(P_{T-1}^X)\cdots F(P_0^X)$ (newest factor first) and likewise $\Phi_T^Y$,

<!-- eq:diff-unroll -->
$$ P_T^X - P_T^Y = \Phi_T^X\,(X - Y)\,(\Phi_T^Y)' \tag{eq:diff-unroll} $$

Writing $F_\infty := F(\Sigma_\infty)$ and $S_V := C(\Sigma_\infty + V)C' + R \succ 0$, the gain expands about $\Sigma_\infty$ as $F(\Sigma_\infty + V) = F_\infty(I - VC'S_V^{-1}C)$; hence for $V \succeq 0$,

<!-- eq:gap-ric -->
$$ \mathcal{R}(\Sigma_\infty + V) - \Sigma_\infty = F_\infty\, V\, F_\infty' \;-\; F_\infty\, V\, C'\, S_V^{-1}\, C\, V\, F_\infty' \;\preceq\; F_\infty\, V\, F_\infty' \tag{eq:gap-ric} $$

the subtracted term being $\succeq 0$. **Above $\Sigma_\infty$ the gap is dominated by the fixed strong loop $F_\infty$** (a two-sided Stein contraction, rate $\rho(F_\infty)^2$); **below $\Sigma_\infty$**, `eq:diff-id` at the fixed point $B_\sharp = \Sigma_\infty$ carries the *fixed* $F_\infty$ on one side and a time-varying error map on the other (a one-sided contraction, rate $\rho(F_\infty)$) — the asymmetry the two anchors exploit.

*Proof.*

**Part 1.** $\mathcal{U}$ is monotone: completing the square, $\mathcal{U}(\Sigma) = \min_K\big[(I - KC)\Sigma(I - KC)' + KRK'\big]$ (the Joseph form, minimized over the gain $K$, optimum $K = \Sigma C'(C\Sigma C' + R)^{-1}$). For fixed $K$ the bracket is affine and monotone in $\Sigma$; a pointwise minimum of monotone maps is monotone, so $L_1 \preceq L_2 \Rightarrow \mathcal{U}(L_1) \preceq \mathcal{U}(L_2)$. Then $\Sigma \mapsto A\Sigma A' + GQG'$ is monotone, so $\mathcal{R}$ is monotone; iterating gives `eq:comparison`.

**Part 2.** Because $G = \operatorname{col}(G_1, 0)$ and $A$ has $e_2$-row $[\,0\ \ A_2\,]$, the $(2,2)$ block of $\mathcal{R}(\Sigma)$ is $\mathcal{R}(\Sigma)\!\mid_{22} = A_2\, \mathcal{U}(\Sigma)\!\mid_{22}\, A_2'$, so $\Sigma_{T+1}\!\mid_{22} = A_2\, \mathcal{U}(\Sigma_T)\!\mid_{22}\, A_2'$, and since $A_2$ is nonsingular (`eq:A2-inv`), $J_{T+1} = A_2^{-1\prime}\, (\mathcal{U}(\Sigma_T)\!\mid_{22})^{-1}\, A_2^{-1}$. Set $W_T := A_2^{-1\prime}\big[\,(\mathcal{U}(\Sigma_T)\!\mid_{22})^{-1} - (\Sigma_T\!\mid_{22})^{-1}\,\big] A_2^{-1}$, so `eq:Jrec` holds by construction. The update never increases the covariance, $\mathcal{U}(\Sigma) \preceq \Sigma$, and a principal block inherits the order, so $\mathcal{U}(\Sigma_T)\!\mid_{22} \preceq \Sigma_T\!\mid_{22}$; both $\succ 0$, inversion reverses, $(\mathcal{U}(\Sigma_T)\!\mid_{22})^{-1} \succeq (\Sigma_T\!\mid_{22})^{-1}$; congruence by $A_2^{-1}$ preserves $\succeq 0$, so $W_T \succeq 0$. Unrolling gives `eq:Jgram`.

**Part 3.** For `eq:diff-id`: the update obeys $\mathcal{U}(A_\sharp) - \mathcal{U}(B_\sharp) = (I - L(A_\sharp)C)(A_\sharp - B_\sharp)(I - L(B_\sharp)C)'$ — the Kalman update-difference, the bilinear remainder collapsing by the resolvent identity $S_\sharp^{-1} - S_\flat^{-1} = -S_\sharp^{-1}C(A_\sharp-B_\sharp)C'S_\flat^{-1}$ ($S_\sharp := CA_\sharp C'+R$); conjugating by $A$ and cancelling $GQG'$ gives `eq:diff-id`, and iterating gives `eq:diff-unroll`. For `eq:gap-ric`: $L(\Sigma_\infty + V) - L(\Sigma_\infty) = (I - L(\Sigma_\infty)C)VC'S_V^{-1}C$ gives the gain expansion; substituting into $\mathcal{R}(\Sigma_\infty+V) = F(\Sigma_\infty+V)(\Sigma_\infty+V)F(\Sigma_\infty+V)' + \cdots$ and using $\mathcal{R}(\Sigma_\infty)=\Sigma_\infty$ yields the displayed identity, whose subtracted term is a congruence of $S_V^{-1}\succ0$, hence $\succeq 0$. ∎

**Remark (why $A_2^{-1}$, and only $A_2$).** The measurement information propagates through the *inverse* of the dynamics on the uncontrollable–unstable block, legal precisely because $A_2$ is nonsingular (`eq:A2-inv`) — the open-loop $A$ and the stabilizable block $A_1$ are never inverted. On the antistable part $A_a^{-1}$ is Schur, so `eq:Jgram` converges (finite gramian, finite steady covariance); on the marginal part $A_m^{-1}$ sits on the unit circle, so it diverges (unbounded information, vanishing covariance). Under C3w the marginal block is absent and `eq:Jgram` is the convergent antistable gramian throughout.

<!-- verify: comparison (eq:comparison) and the linear A2^{-1} recursion (eq:Jrec, W_T>=0) validated in scratch/check_a03.py [D],[B]. Gap engine eq:diff-id resid 2e-16 (check_forget.py[1]); eq:gap-ric resid 1e-15/5e-10 (check_gapric.py). Ordering: A_2 = A_a (+) A_m (antistable first). W_T>=0 from U(Sigma)|22 <= Sigma|22. -->
<!-- verify: LIVE consumers — eq:Rmap feeds thm:formula (04, the Mobius/gap engine); app:machinery-2 (e2 identity, eq:Jrec/eq:Jgram) feeds lem:structure (antistable gramian eq:Sinf-gram); eq:diff-id/eq:diff-unroll feed lem:robust (08) / thm:payoff (robustness). eq:gap-ric (two-sided Stein) and eq:comparison are no longer on the arc-1 sufficiency path (their consumers were the retired squeeze anchors) — retained as standard tools / rate confirmation and for Arc 2. -->
<!-- verify: LEAN (phase A): eq:comparison = Dare.dareIter_mono (Estimation/Dare/Update.lean, via the Joseph-form gain minimization joseph_sub_updM); eq:Jrec = Dare.jRec + jRec_increment_posSemidef (Estimation/Dare/BlockInfo.lean; increment PSD via the new Löwner inversion-antitone lemma); eq:Jgram = pending (unroll lands with its consumer); eq:diff-id = Dare.dareStep_diff, eq:diff-unroll = Dare.dareIter_diff, eq:gap-ric = Dare.gapRic / gapRic_le (Estimation/Dare/GapEngine.lean). Axioms clean. -->

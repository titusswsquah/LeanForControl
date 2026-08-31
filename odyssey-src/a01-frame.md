<!-- app:frame — the antistable-marginal frame, justified by DARE similarity-covariance. -->
<!-- app:frame -->
### The antistable–marginal frame

The development of `00-setup` works, without loss of generality, in the frame `eq:three-block`. This appendix supplies the reduction and its justification, which rests only on the covariance of the DARE `eq:dare` under state similarity.

**1. (Similarity-covariance of the DARE.)** Let $T$ be nonsingular and write $\tilde A := T A T^{-1}$, $\tilde G := T G$, $\tilde C := C T^{-1}$. Then for every $\Sigma = \Sigma' \succeq 0$,

<!-- eq:dare-cov -->
$$ \mathcal{R}_{\tilde A, \tilde G, \tilde C}\big( T\Sigma T' \big) = T\, \mathcal{R}_{A, G, C}(\Sigma)\, T' \qquad \tilde F = T F T^{-1} \tag{eq:dare-cov} $$

where $\mathcal{R}_{A,G,C}(\Sigma) := A[\Sigma - \Sigma C'(C\Sigma C' + R)^{-1}C\Sigma]A' + GQG'$ is the recursion map of `eq:cov-rec` and $F$ its error map `eq:filter`.

*Proof.* $\tilde C\, (T\Sigma T')\, \tilde C' = C T^{-1} T \Sigma T' T^{-\prime} C' = C\Sigma C'$, so the innovation block and $R$ are untouched; hence $T\Sigma T'\, \tilde C'(\tilde C T\Sigma T' \tilde C' + R)^{-1}\tilde C\, T\Sigma T' = T\big[\Sigma C'(C\Sigma C' + R)^{-1}C\Sigma\big]T'$. Conjugating by $\tilde A = TAT^{-1}$ and adding $\tilde G Q \tilde G' = T GQG' T'$ gives the first identity; factoring $T$ out of $\tilde A(I - \cdots \tilde C)$ gives $\tilde F = TFT^{-1}$. ∎

Consequently, seeding `eq:cov-rec` at $\tilde\Sigma_0 = T\Sigma_0 T'$ produces $\tilde\Sigma_T = T\Sigma_TT'$ for all $T$; the error map conjugates to $\tilde F_T = T F_T T^{-1}$ with $\rho(\tilde F_T) = \rho(F_T)$; and $\tilde\Sigma_T \to \Sigma_\infty$ iff $\Sigma_T \to T^{-1}\Sigma_\infty T^{-\prime}$. So **attraction, the spectrum of the error map, and the strong/stabilizing classification are all similarity-covariant**: the prior transforms by the congruence $\Sigma_0 \mapsto T\Sigma_0 T'$, and we may choose $T$ freely. The conditions C1/C2/C2w/C3w are spectral/subspace statements about $(A, G, C)$ and $\ker\Sigma_0$, hence similarity-invariant.

**2. (The frame, in three similarities.)** Compose:

- *(Stabilizability canonical form.)* A similarity puts $(A, G)$ in $A = \big[\begin{smallmatrix} A_1 & A_{12} \\ 0 & A_2 \end{smallmatrix}\big]$, $G = \big[\begin{smallmatrix} G_1 \\ 0 \end{smallmatrix}\big]$ with $(A_1, G_1)$ stabilizable and $A_2$ carrying exactly the uncontrollable modes with $|\lambda| \ge 1$ (stable uncontrollable modes are absorbed into $A_1$). By C1, $(A_1, C_1)$ is detectable, so the stabilizable block is closed to a Schur $A_c$ (its $e_1$-diagonal block of $F_\infty$) by the strong-solution gain (`eq:Finf-spec`) — no separate stabilizing feedback need be constructed.
- *(Antistable–marginal separation.)* Within $A_2$, the spectra outside and on the unit circle are disjoint, $\operatorname{spec}(A_a) \cap \operatorname{spec}(A_m) = \varnothing$, so the Sylvester equation $A_a X - X A_m = -A_{am}$ has a unique solution and the similarity $\big[\begin{smallmatrix} I & X \\ 0 & I \end{smallmatrix}\big]$ block-diagonalizes $A_2$ into $A_a \oplus A_m$ — $A_a$ antistable ($A_a^{-1}$ Schur), $A_m$ on the circle. This **decouples** the antistable dynamics from the marginal ones, so backward propagation by $A_a^{-1}$ later cannot drive the marginal block. The **antistable block is placed first** within $A_2$, so the reduced $e_1\oplus e_a$ system occupies the leading principal block of the frame.
- *(Prior congruence.)* A block-triangular congruence across the stabilizable cut block-diagonalizes the prior, $\Sigma_0 \mapsto \operatorname{diag}(\Sigma_1, \Sigma_2)$, while preserving the upper-triangular structure of $A$ and $G = \operatorname{col}(G_1, 0, 0)$. The $(a, m)$ coupling **inside** $\Sigma_2 = \big[\begin{smallmatrix} \Sigma_{aa} & \Sigma_{am} \\ \Sigma_{am}' & \Sigma_{mm} \end{smallmatrix}\big]$ is retained (only the dynamics decouple, not the prior).

The composite similarity yields `eq:three-block`, and by Part 1 the entire development may be read there.

**3. (Prior positivity from C2 / C2w.)** Writing $\Sigma_a := \Sigma_{aa}$ for the antistable diagonal block of the lumped prior,

<!-- eq:prior-pos -->
$$ \textbf{(a)}\quad \text{C2} \iff \Sigma_2 \succ 0 \qquad\qquad \textbf{(b)}\quad \text{C2w} \iff \Sigma_a \succ 0 \tag{eq:prior-pos} $$

*Proof.* In the frame, $\mathcal{X}_{u,uc} = \{0\}^{n_1} \times \mathbb{R}^{n_2}$ and a vector $v = \operatorname{col}(0, v_2)$ lies in $\ker\Sigma_0 = \ker\Sigma_1 \times \ker\Sigma_2$ iff $\Sigma_2 v_2 = 0$, so $\ker\Sigma_0 \cap \mathcal{X}_{u,uc} \cong \ker\Sigma_2$, trivial iff $\Sigma_2 \succ 0$ — this is **(a)**. For **(b)**, $\mathcal{X}_{a,uc} = \{0\}^{n_1} \times \mathbb{R}^{n_a} \times \{0\}^{n_m}$, and $v = \operatorname{col}(0, v_a, 0) \in \ker\Sigma_0$ iff $\Sigma_2 \operatorname{col}(v_a, 0) = 0$; since $\Sigma_2 \succeq 0$, a vector lies in its kernel iff it annihilates the quadratic form, so this is $v_a' \Sigma_a v_a = 0$. Hence $\ker\Sigma_0 \cap \mathcal{X}_{a,uc} = \{0\}$ iff $\Sigma_a \succ 0$ — this is **(b)**. ∎

Part (b) is the prior-positivity form of the attraction criterion: the antistable prior block carries strictly positive information. The coupling matters — $\ker\Sigma_2$ may contain *mixed* antistable–marginal directions even when $\Sigma_a \succ 0$ — so C2w forbids only a *purely* antistable kernel direction. Under C3w the marginal block is empty, $\mathcal{X}_{a,uc} = \mathbb{R}^{n_2}$, and `eq:prior-pos`(b) becomes $\Sigma_2 \succ 0$, recovering (a) as C2 $\iff$ C2w.

<!-- verify: Part 1 (eq:dare-cov) licenses the frame using only DARE similarity-covariance. Part 3 (eq:prior-pos) is consumed by the criterion slice (C2w <=> Sigma_a > 0). Ordering: antistable e_a FIRST within A_2, marginal e_m LAST, so e_1(+)e_a is the leading principal block (reduced problem in the top-left corner). -->
<!-- verify: LEAN (phase A): eq:three-block = structure DareSystem (Estimation/Dare/System.lean; C1/C2/C2w in kernel form); eq:prior-pos(a) = DareSystem.criterion, (b) = DareSystem.criterion_w; eq:A2-inv = DareSystem.isUnit_A₂_det. Part 1 (eq:dare-cov similarity covariance): not formalized — the Lean development works in-frame; a transfer layer would consume it. -->

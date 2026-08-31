<!-- 02-criterion — the prior-positivity form of C2w: the seed the antistable information needs. -->
<!-- Port of riccastep 04-criterion-v2; restated for the slaved frame (name lem:criterion-w). -->
<!-- sec:criterion — main text -->
<!-- lem:criterion-w -->
### Lemma (lem:criterion-w) — C2w in prior-block coordinates

In the frame `eq:three-block`, with $\Sigma_a := \Sigma_{aa}$ the antistable diagonal block of the prior,

<!-- eq:criterion -->
$$ \text{C2w} \quad\iff\quad \Sigma_a \succ 0. \tag{eq:criterion} $$

Equivalently, C2w is exactly the statement that the antistable information $J_0^{aa} := \Sigma_a^{-1}$ — the seed of the recursion `eq:Jrec` on the antistable block — is **finite**.

*Proof.* The equivalence is `eq:prior-pos`(b): $\mathcal X_{a,uc}$ is the $e_a$ coordinate block, and $\ker\Sigma_0\cap\mathcal X_{a,uc}=\{0\}$ holds iff the antistable diagonal block $\Sigma_a$ of the (possibly coupled) prior block $\Sigma_2$ is nonsingular. Finiteness of $J_0^{aa}=\Sigma_a^{-1}$ is then immediate. ∎

**Remark (why this is the criterion).** The antistable block of the covariance is **uncontrollable** — no process noise refreshes it — so its information is never created by the recursion; it can only be inherited from the prior and propagated by $A_a^{-1}$ (`app:machinery`, `eq:Jrec`). C2w ($\Sigma_a\succ0$) is the demand that this inherited antistable information be finite in every direction. When it holds, the prior seed $J_0^{aa}$ is finite, the discrete $J$-transform contracts it and the steady $A_a^{-1}$-gramian $(\Sigma_\infty\!\mid_{aa})^{-1}$ takes over (`lem:jtransform`, `lem:lowsqueeze`); when it fails, some antistable direction carries infinite information — zero covariance — merely rotated, never resolved (`thm:necessity`). This is the discrete, estimation-side image of the antistable-coordinate positivity condition of Callier and Winkin (1995). The coupling matters: $\ker\Sigma_2$ may contain *mixed* antistable–marginal directions even when $\Sigma_a\succ0$, so C2w forbids only a *purely* antistable kernel direction (`eq:prior-pos`).

<!-- verify: eq:criterion is eq:prior-pos(b) (a01-frame), validated structurally there; seed-finiteness is its restatement. Deps: eq:three-block, eq:prior-pos, eq:Jrec/app:machinery. CONSUMERS: lem:slaved-seed (eq:Lc2w restates it on the seed), lem:lowsqueeze / lem:jtransform (finite J_0^aa under C2w), thm:sufficiency (C2w through it), thm:main. PORT of riccastep 04-criterion-v2. -->
<!-- verify: LEAN (phase A): lem:criterion-w / eq:criterion = DareSystem.criterion_w (Estimation/Dare/System.lean; C2w defined in the paper's kernel form, positivity proved); axioms clean. -->

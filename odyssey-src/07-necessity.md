<!-- 07-necessity — Tiresias. C2w is NECESSARY for attraction to the strong solution. -->
<!-- Crux: an antistable-uncontrollable direction the prior already knows exactly stays known forever; -->
<!-- its zero-covariance direction is merely rotated by A_2^{-1}, so the antistable block stays singular -->
<!-- while Sigma_inf|aa > 0. Uses C1 only; no controllability, no squeeze. Port of riccastep 03-necessity-v2. -->
<!-- sec:necessity — main text -->
<!-- thm:necessity -->
### Theorem (thm:necessity) — Necessity of C2w

Let C1 hold. If the recursion `eq:cov-rec` is attracted to the strong solution, $\Sigma_T\to\Sigma_\infty$, then C2w holds:

<!-- eq:necessity -->
$$ \ker\Sigma_0 \cap \mathcal X_{a,uc}(A,G) = \{0\}. \tag{eq:necessity} $$

*Proof.* The contrapositive. Suppose C2w fails: there is $v\ne0$ in $\ker\Sigma_0\cap\mathcal X_{a,uc}$. In the frame `eq:three-block`, $\mathcal X_{a,uc}$ is the antistable coordinate block, so $v$ is an $e_a$-vector with $v\in\ker\Sigma_2$ (`eq:prior-pos`), hence $v\in\ker(\Sigma_0\!\mid_{22})$.

**Image confinement by $A_2$.** By `app:machinery`-2, $\Sigma_{T+1}\!\mid_{22} = A_2\,\mathcal U(\Sigma_T)\!\mid_{22}\,A_2'$. The update never increases the covariance, $\mathcal U(\Sigma)\preceq\Sigma$, so $\mathcal U(\Sigma_T)\!\mid_{22}\preceq\Sigma_T\!\mid_{22}$; a smaller PSD matrix has the larger kernel, so $\operatorname{im}\mathcal U(\Sigma_T)\!\mid_{22}\subseteq\operatorname{im}\Sigma_T\!\mid_{22}$. Therefore $\operatorname{im}\Sigma_{T+1}\!\mid_{22} = A_2\operatorname{im}\mathcal U(\Sigma_T)\!\mid_{22} \subseteq A_2\operatorname{im}\Sigma_T\!\mid_{22}$, and unrolling from $\Sigma_0\!\mid_{22}=\Sigma_2$,

<!-- eq:image-shadow -->
$$ \operatorname{im}\Sigma_T\!\mid_{22} \subseteq A_2^{\,T}\operatorname{im}\Sigma_2 \qquad T\ge0. \tag{eq:image-shadow} $$

**A persistent kernel direction.** Taking orthogonal complements, $\ker\Sigma_T\!\mid_{22}\supseteq(A_2')^{-T}\ker\Sigma_2$. Since $v\in\ker\Sigma_2$ and $A_2$ is nonsingular (`eq:A2-inv`),
$$ w_T := (A_2')^{-T}v = (A_a')^{-T}v \ne 0, \qquad w_T\in\ker\Sigma_T\!\mid_{22} $$
($A_2' = A_a'\oplus A_m'$ keeps $w_T$ antistable, as $v$ is an $e_a$-vector). Embedding $w_T$ by zero on $e_1$, $w_T'\Sigma_T w_T = w_T'(\Sigma_T\!\mid_{22})w_T = 0$ for every $T$.

**No convergence.** By `lem:structure-marg` (equally `lem:structure`-1), the strong solution is positive definite on the antistable block, $\Sigma_\infty\!\mid_{aa}\succ0$. Normalizing $\hat w_T := w_T/\|w_T\|$ — an antistable unit vector — gives $\hat w_T'\Sigma_\infty\hat w_T \ge \lambda_{\min}(\Sigma_\infty\!\mid_{aa})>0$ while $\hat w_T'\Sigma_T\hat w_T = 0$. Hence
$$ \|\Sigma_T - \Sigma_\infty\| \ge \hat w_T'(\Sigma_\infty - \Sigma_T)\hat w_T = \hat w_T'\Sigma_\infty\hat w_T \ge \lambda_{\min}(\Sigma_\infty\!\mid_{aa}) > 0 $$
for all $T$, so $\Sigma_T\not\to\Sigma_\infty$ — contradicting the hypothesis, and proving `eq:necessity`. ∎

**Remark (the mechanism).** A purely antistable, uncontrollable direction $v$ the prior already knows exactly ($v\in\ker\Sigma_0$) stays known exactly forever: uncontrollable, so no process noise injects fresh uncertainty; a measurement update only removes covariance. Its zero-covariance direction is merely rotated by $A_2^{-1}$ each step (`eq:image-shadow`), so the antistable block of $\Sigma_T$ stays singular while $\Sigma_\infty\!\mid_{aa}\succ0$ is full — the gap cannot close. C2w is exactly the demand that the prior leave no such direction; it is the mirror of the lower anchor, where the C2w seed is what the $J$-transform needs to floor the antistable block (`lem:criterion-w`, `lem:lowsqueeze`).

<!-- verify: GATE-2 (riccastep check_necessity.py check 8): C2w fails (Sigma_a singular) => ||Sigma_T - Sigma_inf|| stuck at 3.1e2, min eig(Sigma_T|aa)=0 all T; C2w holds => converges 2e-12. Uses C1 only (Sigma_inf existence + Sigma_inf|aa>0 via lem:structure-marg/lem:structure-1); image confinement elementary (U<=Sigma, A2 nonsingular eq:A2-inv). The kernel direction w_T=(A2')^{-T}v is nonzero and antistable (e_a-block A2'-invariant), so hat w_T'Sigma_inf hat w_T >= lambda_min(Sigma_inf|aa) is legitimate. -->
<!-- verify: deps — eq:cov-rec, eq:three-block, eq:prior-pos (X_{a,uc}=e_a block, ker Sigma_2), app:machinery-2, eq:A2-inv, lem:structure-marg (Sigma_inf|aa>0, marginal-inclusive). No controllability, no squeeze, no C3w. CONSUMER: thm:main (Part 1, with thm:sufficiency). PORT of riccastep 03-necessity-v2. -->
<!-- verify: LEAN (phase B): thm:necessity / eq:necessity = DareSystem.necessity (Estimation/Dare/Necessity.lean). Same mechanism, quadratic-form implementation: instead of image confinement + orthogonal complements, the phi-quadratic along the backward-transported witness w_T = (Aa')^{-T}v is shown nonincreasing from zero (dare_quadForm_transported_eq_zero, via margPhi_step + update contraction), which is the persistent-kernel statement in quadForm language; the floor is strong_corner_posDef + quadForm_le_card_norm. Hypotheses even weaker than the deck's: no C1 — IsStrongSolution Sinf is hypothesized directly (C1's only role here is Sigma_inf's existence). Axioms clean. -->

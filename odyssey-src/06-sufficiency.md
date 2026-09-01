<!-- 06-sufficiency — the GAS squeeze: C1 + C2w => Sigma_T -> Sigma_inf from EVERY prior. A sandwich between -->
<!-- the two anchors, both attracted to Sigma_inf: upper = lem:supremal (Charybdis, from above, fixed F_inf), -->
<!-- lower = lem:lowsqueeze (Scylla, from below, the slaved J-transform, FLOOR-FREE). C2w enters in exactly -->
<!-- one place: the antistable seed of the lower anchor (eq:Lc2w). Cleaner than riccastep thm:sufficiency -->
<!-- (no omega-limit, no reduction lemma) because the lower anchor is the marginal-slaved lem:lowsqueeze. -->
<!-- sec:sufficiency — main text -->
<!-- thm:sufficiency -->
### Theorem (thm:sufficiency) — Sufficiency of C2w

Let C1 and C2w hold, with semisimple marginal modes when a marginal block is present (`lem:marginal`; the defective case is open). Then the recursion is attracted to the strong solution from **every** prior $\Sigma_0$: $\Sigma_T \to \Sigma_\infty$ — at a geometric rate when C3w also holds; no rate is claimed in the marginal case.

*Proof.* A squeeze between two initial conditions, both attracted to $\Sigma_\infty$.

**The two anchors.** Take $\overline\Sigma_0 = \Sigma_0 + \Sigma_\infty$ — manifestly $\succeq \Sigma_0$ and $\succeq \Sigma_\infty$, with no threshold to choose — and let $\underline\Sigma_0$ be the slaved seed `eq:Ldef-slaved` (any $\delta\in(0,1]$). By `lem:slaved-seed`-1, $\underline\Sigma_0\preceq\Sigma_0$; by construction $\Sigma_0\preceq\overline\Sigma_0$; so the prior is framed,

<!-- eq:framed -->
$$ \underline\Sigma_0 \;\preceq\; \Sigma_0 \;\preceq\; \overline\Sigma_0. \tag{eq:framed} $$

Comparison (`eq:comparison`) propagates `eq:framed` to every horizon,

<!-- eq:squeeze -->
$$ \underline\Sigma_T \;\preceq\; \Sigma_T \;\preceq\; \overline\Sigma_T \qquad T\ge0. \tag{eq:squeeze} $$

**Both anchors converge to $\Sigma_\infty$.** The upper trajectory converges by `lem:supremal` (`eq:above`), $\overline\Sigma_T\to\Sigma_\infty$, using only $\overline\Sigma_0\succeq\Sigma_\infty$ and C1. The lower trajectory converges by `lem:lowsqueeze` (`eq:lowsqueeze`), $\underline\Sigma_T\to\Sigma_\infty$, **floor-free** — this is where C2w enters: by `lem:slaved-seed`-2 (`eq:Lc2w`), C2w is exactly the nondegeneracy $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_a\succ0$ of the antistable seed, which the discrete $J$-transform (`lem:jtransform`) then carries to $\Sigma_\infty\!\mid_{aa}\succ0$ without any assumed floor, the marginal riding the antistable (`lem:loading`).

**Squeeze.** Both bounds in `eq:squeeze` converge to the *same* fixed point $\Sigma_\infty$ — the unique strong solution (`fact:dare-strong`) — so $\Sigma_T\to\Sigma_\infty$. No separate limit identification is needed: each anchor converges *to $\Sigma_\infty$* by construction.

**Rate.** Under C3w there is no marginal block: $F_\infty$ is Schur outright (`eq:Finf-c3w`; classically $A_c$ and the reflected $A_a^{-1}$), the from-above gap (`eq:gap-ric`) and the from-below anchor (`lem:jtransform`, rate $\max\{\rho(A_a^{-1})^2,\rho(L_\infty)\}$) both contract geometrically, and $\Sigma_T\to\Sigma_\infty$ at the geometric rate. Otherwise the marginal block is present and converges by `lem:marginal` with no rate claimed (the previously asserted polynomial rate rested on `lem:marginal`'s retired route; the numerics show $\sim 1/T$). ∎

**Remark (the squeeze block by block).** The **antistable** block is held *above* collapse by the nondegenerate C2w seed forgotten through $A_a^{-1}$ (`lem:jtransform`, source-bounded by the conditional filter `lem:condfilter`, not by an assumed floor) and *below* $\Sigma_\infty\!\mid_{aa}$ by the upper trajectory's convergence from above (`eq:above`); the **marginal** block is driven to zero by unbounded observation information from above (`eq:marg-zero`) and rides the antistable from below (`lem:loading`); the **stabilizable** block follows the Schur closed loop $A_c$ from above and its conditional filter from below (`lem:condfilter`). C2w enters in exactly one place — making the antistable prior seed nondegenerate (`eq:Lc2w`) so the forgetting can take over. Drop C2w and the lower anchor loses its antistable seed; the run is no longer pinned from below, and indeed fails to converge (`thm:necessity`). This is cleaner than the marginal-zero route: because the lower anchor's marginal is *slaved* (`lem:lowsqueeze`), the squeeze needs no omega-limit and no reduction lemma.

<!-- verify: LEAN (phase B): thm:sufficiency = DareSystem.sufficiency_tendsto (Estimation/Dare/Sufficiency.lean): the framing eq:framed/eq:squeeze via dareIter_mono, both anchors verified (supremal_tendsto with seed Sig0 + Sigma_inf per finding 10, lowsqueeze_tendsto with delta = 1), and the Loewner sandwich carried to the norm by polarization (symm_norm_le_of_abs_quadForm_le). Hypotheses = C1 + C2w + the deck's remaining imports (power-bounded marginal, ReducedImport = the reduced fact:dare-strong); the eq:Finf-spec hypothesis is discharged inside by strong_Fs_schur (phase D, Estimation/Dare/Spectrum.lean). The C3w rate refinement is not formalized (thm:main Part 2 territory, finding 7). Axioms clean. -->
<!-- verify: GATE-2. Full squeeze eq:squeeze with both anchors -> Sigma_inf, end to end: underSig_T <= Sig_T <= barSig_T all T, all -> Sigma_inf, delta-independent (check_pi_collapse.py lower, check_dsgg_upper.py upper, domination min eig >= -1e-9). Under C2w holds => convergence; C2w fails => stuck (thm:necessity side). -->
<!-- verify: deps — eq:comparison (propagate framing), lem:slaved-seed-1 (underSig0 <= Sig0), lem:slaved-seed-2 (eq:Lc2w, C2w = antistable seed nondegenerate), lem:supremal (eq:above upper anchor), lem:lowsqueeze (eq:lowsqueeze lower anchor, floor-free), lem:jtransform/lem:condfilter/lem:loading (the lower-anchor engine + rate), fact:dare-strong (unique Sigma_inf), eq:Finf-spec + lem:marginal + fact:gramian/fact:poly-growth (rate). CONSUMER: thm:main (Part 1, with thm:necessity). -->
<!-- verify: CONFINEMENT — C2w is the strong-solution frontier (Part 1). C3w/geometric is only the rate refinement here; the exponential/GES theory is thm:main Part 2 (imported from arc1). The lower anchor is FLOOR-FREE: no eq:Jaa-bound/eq:Lfloor, no lem:reduced-forget, no omega-limit -- retired. Discrete dual of CW's finite-horizon squeeze. -->

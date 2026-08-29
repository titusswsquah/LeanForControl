# Lean-verifying `costogo.tex` — scope, decisions, and milestones

Companion to `costogo-formalization-plan.md` (environment + mathlib audit; still
accurate). This note records the **scoping decisions made 2026-08-29** and the
resulting work breakdown: what must be built, what is staged, what is defined
away, and in what order.

Targets:

* `../2025h_est_claude/costogo.tex` — the value-function route.
  Headline: `thm:gas-ges-fi` (GAS ⟺ C1∧C2, GES ⟺ C1∧C2∧C3w).
* `../2025h_est_claude/15-gas-lyap-draft/gas-lyap-draft.md` — the Lyapunov
  draft. Consulted for one load-bearing observation (below); its GAS proof
  route is **not** the one being formalized.

## Decisions (agreed with Titus)

1. **Estimator definition — deterministic, no probability.** The Lyapunov
   draft's `lem:semiPT` shows the FIE/KF correspondence is provable with zero
   probability theory: define the time-varying Kalman filter as the
   deterministic recursion (`Σ_{T+1}` covariance update,
   `L_T = AΣ_T C'(CΣ_T C'+R)⁻¹`, `x̂⁺ = Ax̂ + L_T(y − Cx̂)`), define the FIE as
   the least-squares problem `𝕡_Te`, and prove the bridge by the forward
   arrival-cost DP of the draft (`lem:arrival-kkt`, `lem:arrival-step`).
   Gaussians never appear. The stability theorems are stated about the FIE
   minimizer `e*(T|T)`; the bridge (milestone M3) transfers them to the actual
   filter error `e(T)` via `e*(T|T) = e(T)`.
2. **Coordinates — reduced block form.** Main theorems are stated for systems
   *given in* stabilizability canonical coordinates with block-diagonal prior:
   `A = fromBlocks A₁ A₁₂ 0 A₂`, `G = col(G₁, 0)`, `Σ₀ = diag(Σ₁, Σ₂)`,
   with hypotheses `(A₁,G₁)` stabilizable and `A₂` antistable (every eigenvalue
   `|λ| ≥ 1`). The Kalman/stabilizability decomposition and the congruence of
   `app:congruence` (which need real invariant-subspace splitting, absent from
   mathlib) are deferred to milestone M4, which generalizes the statement
   without touching the proofs.
3. **Classical core — blueprint-staged.** `fact:lqr` (Riccati/LQR convergence
   to the stabilizing DARE solution) and `fact:detect-inj` are stated precisely
   in Lean now, carried as `sorry`'d blueprint leaf nodes, and discharged in
   milestone M2. Until then the headline theorems build but carry `sorryAx`;
   the README's no-sorry claim must be qualified while M2 is open (see Risks).
4. **C1 necessity — proved directly for the linear case.** The paper cites
   Allan–Rawlings–Teel 2021 (nonlinear) for necessity of C1 in `prop:gas`; we
   prove the linear special case ourselves so the full iff survives.
5. **C2 necessity — formalize the patched argument from
   `../rawlings_quah_mueller_2026a/paper.tex` (commit `dcdb3d8`,
   "c2-necessity, facts as intended"), not costogo's paragraph.** costogo's
   version claims the support constraint "pins `χ₂(0) = v₂`", which is too
   strong — the constraint pins only the component along the witness. The
   patched proof (paper.tex, proof of `prop:tvkf`) is the correct one; see
   "C2-necessity, patched version" below for its structure and the new
   dependencies it introduces. costogo.tex should eventually receive the same
   patch.

## The three-bucket scope picture

* **Bucket A — base infrastructure to build (M0).** Spectral toolkit +
  definitions. Everything here is derivable from what the pinned mathlib has
  (Gelfand formula, generalized eigenspaces, Hermitian spectral theorem, Schur
  complements, matrix order). Independently useful to the repo.
* **Bucket B — the expensive classical core (M2).** `fact:lqr` and
  `fact:detect-inj`. One hard theorem seen twice (`detect-inj` follows from
  `lqr` by duality). Never formalized in any proof assistant as far as we
  know; likely comparable in size to the whole rest of the project. Staged so
  it is off the critical path.
* **Bucket C — reductions defined away.** Probability/Gaussian layer (gone
  permanently, decision 1), canonical-form decomposition + congruence
  (deferred to M4, decision 2).

## Milestones

### M0 — definitions and spectral toolkit (Bucket A)

Files: extend `LinearSystems/` (defs are repo-wide useful), new
`Estimation/` modules for the rest.

| Item | Route | Size guess |
|---|---|---|
| `IsSchurStable` (ρ(A) < 1) + API | `spectralRadius` of the ℂ-matrix; ℝ-matrix → ℂ entrywise map (repo's existing ℝ/ℂ pattern from `Hautus.lean`) | small |
| Schur ⟺ `∃ c ρ<1, ‖Aᵏ‖ ≤ c ρᵏ` | Gelfand formula (`Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`) | medium |
| `IsDetectable`, `IsStabilizable` (Hautus form) | beside `Hautus.lean`; duality via `controllabilityMatrix_transpose` | small–medium |
| C1 / C2 / C3w | on top of the above; C2 needs `ker Σ₀ ⊓ 𝒳_{u,uc} = ⊥` — in reduced coordinates this is just `Σ₂ ≻ 0` (`lem:Sigma2-pd` becomes near-trivial) | small |
| `fact:poly-growth` `‖Aᵏ‖ ≤ c(1+k)^{m−1}` | no Jordan form in mathlib; use generalized-eigenspace decomposition + `A = λI + N` binomial expansion, nilpotency index per eigenvalue | medium–large |
| `fact:no-decay` | per generalized eigenspace: `{Nʳu}` independent, top coefficient `λ^{k−d}·C(k,d)` does not vanish | medium |
| `fact:eig-orbit` | eigenbasis of the unit-circle eigenspace, `σ_min(V)`-type bounds | small–medium |
| `fact:gramian`, quantitative form (`W_T ⪰ c_B T I`, paper.tex `eq:gramian`) | per generalized eigenspace + the polynomial sampling lemma `eq:polysample` (Lagrange stride interpolation; proof in paper.tex); subsumes costogo's divergence-only statement | medium |
| `fact:schur`, `fact:psd-bounds` | essentially mathlib (`SchurComplement.lean`, PosSemidef eigenvalue API); glue only | small |
| `fact:uniexp` (Zhou–Zhao) | direct Lyapunov-norm proof once Schur API exists: pick equivalent norm with `‖F‖ < 1`, absorb the tail where `F(k) ≈ F` | medium |
| PSD pseudoinverse `Σ†` | for **symmetric PSD only**, via `Matrix.IsHermitian.spectral_theorem`; needed for the prior penalty and (M3) arrival recursion. No general Moore–Penrose. | medium |

Ballpark: 2–4k lines.

### M1 — the paper layer, in reduced coordinates (the results we care about)

Prereq: M0, plus the two staged facts of M2 as `sorry`'d statements.

1. **Problem setup.** `𝕡_Te` as a finite-dimensional quadratic minimization
   over `(e(0|T), ω : Fin T → input)`; GAS/GES per `def:gas`/`def:ges-fi`
   (pure sequence bounds on `T ↦ e*(T|T)` — no dynamical-systems framework
   needed). Block index via sum types / `Matrix.fromBlocks`.
2. **`lem:prelim`** (app. C): backward DP induction defining `P/Y/S`
   recursions and proving they represent the tail value; horizon-shift
   identities; part (3) consumes `fact:lqr`; part (4) consumes `fact:uniexp`.
   Biggest single file of M1; long but mechanical.
3. **`lem:coercive`**: finite-window coercivity (`W_m ≻ 0` via
   Cayley–Hamilton + `fact:no-decay`), the two-sided bracket, and the C3w
   refinement. Heavy constant bookkeeping.
4. **`prop:infhor`**: monotone value limit, Cauchy convergence of minimizers
   via the exact gap `eq:quad-gap`, identification of the limit
   (`fact:gramian` kills `e₂(0)`). Infinite-horizon cost as `tsum` with a
   finite-cost feasibility predicate.
5. **`prop:gas`** (both directions; C1-necessity proved directly per
   decision 4, C2-necessity via the patched argument per decision 5),
   **`lem:val-rate`**, **`thm:ges-fi`**, assembled into **`thm:gas-ges-fi`**.

#### C2-necessity, patched version (from `paper.tex@dcdb3d8`)

Structure of the correct proof, replacing costogo's necessity paragraph:

1. Witness `ξ = (0, ξ₂) ≠ 0` in `ker Σ₀ ∩ 𝒳_{u,uc}`; choose `x(0) = 0`,
   `x̄₀ = −ξ` (side remark: C1 + ¬C2 force `C ≠ 0`).
2. **Component pinning (the fix):** the support constraint gives only
   `⟨ξ, x̂(0|T)⟩ = −‖ξ‖²`, hence `‖x̂₂(0|T)‖ ≥ ‖ξ‖` by Cauchy–Schwarz —
   the full block is *not* pinned.
3. **Value grows linearly:** sum the quadratic IOSS-Lyapunov dissipation
   inequality (from C1) along the optimal trajectory, convert its right side
   into `V_T⁰` via norm-equivalence bounds (`eq:rangebound` for the `Σ₀†`
   term), and lower-bound its left side by the autonomous block via the
   quantitative Gramian bound `Σ_{k<T} ‖A₂ᵏ w‖² ≥ c_B T ‖w‖²`; conclude
   `liminf V_T⁰/T > 0`.
4. **Value bounded by cumulative estimate energy:** one-stage extension
   feasibility gives `V_{T+1}⁰ ≤ V_T⁰ + c_y ‖x̂(T)‖²`, so
   `V_T⁰ ≤ c_y Σ_{k<T} ‖x̂(k)‖²`.
5. Chain 3–4: the running average of `‖x̂(k)‖²` is bounded away from zero,
   so by Cesàro `x̂(k) ↛ 0`; with `x(k) = 0` the error does not converge.

New dependencies this introduces (all elementary, slotting into M0):

* **Quantitative Gramian growth** (`eq:gramian`): `W_T ⪰ c_B T I` for every
  `B` with all `|λ| ≥ 1` — *upgrades* costogo's `fact:gramian` (mere
  divergence). Proved in paper.tex via Jordan blocks + the polynomial
  sampling lemma; in Lean, route per generalized eigenspace as with
  `fact:poly-growth`.
* **Polynomial sampling lemma** (`eq:polysample`):
  `Σ_{k<T} |q(k)|² ≥ γ_d T |q(0)|²` for polynomials of degree ≤ d, by
  Lagrange interpolation on stride nodes with binomial coefficient bounds —
  self-contained, fully elementary, proof included in paper.tex.
* **Quadratic IOSS-Lyapunov function from detectability**
  (`eq:iioss-bounds`/`eq:iioss-dec`, Cai–Teel 2008): derivable in Lean from
  `fact:detect-inj` + a discrete Lyapunov equation (write
  `x⁺ = (A−LC)x + Ly + Gw` and solve `(A−LC)'P(A−LC) − P = −I`), so it
  stages behind `detect-inj` in M2 but needs no new machinery.
* Cesàro convergence (trivial) and the PSD-range bound `eq:rangebound`
  (covered by the M0 pseudoinverse work).

Ballpark: 3–5k lines. Everything here is elementary analysis/algebra; the risk
is bookkeeping volume, not depth.

### M2 — discharge the classical core (Bucket B)

`fact:lqr`: finite-horizon Riccati values are monotone nondecreasing and
bounded under stabilizability (feasible stabilizing rollout), converge to some
`P ⪰ 0`; detectability makes `A − BK` Schur and `P` the unique stabilizing DARE
solution. Then `fact:detect-inj` by duality. This is its own project; plan it
separately when M1 has fixed the exact statements consumed. Ballpark: 3–6k
lines. Until it lands, `#print axioms` on the headline shows `sorryAx` — that
is the accepted, documented state.

### M3 — the Kalman-filter bridge (optional upgrade, independent of M1/M2)

Deterministic TVKF recursion + `lem:semiPT` via the Lyapunov draft's arrival
machinery (`lem:arrival-kkt`, `lem:meas-square`, `lem:arrival-step`,
`fact:eq-quad`, `fact:min-quad-linear` — all finite-dimensional
completion-of-squares). Upgrades the headline from "the FIE minimizer is
stable" to "the Kalman filter error is stable". Needs the PSD pseudoinverse
and support-constrained quadratic minimization from M0/M1 but none of the
stability results. Ballpark: 1.5–3k lines.

### M4 — general coordinates (deferred)

Kalman/stabilizability decomposition with unit-circle spectral split of the
uncontrollable block (real invariant subspaces — hard), plus `app:congruence`.
Generalizes the theorem statements from reduced block form to arbitrary
`(A, G, C, Σ₀)`. Not scheduled; scope only after M1 is done.

## Explicitly out of scope

* All probability: Gaussians, conditional distributions, `lem:semiPT` in its
  probabilistic reading. Permanently, by decision 1.
* General Moore–Penrose pseudoinverse (PSD-symmetric special case only).
* The Lyapunov draft's GAS proof route (arrival Lyapunov function,
  `lem:decrement`, i-IOSS) — same theorem, different proof; not formalized.
* The companion Part I (information-matrix route).

## Design decisions locked in

* ℝ dynamics, ℂ eigenvalues — the `Hautus.lean` pattern; one entrywise
  `ℝ → ℂ` bridge with `mulVec`/`spectrum` transfer lemmas, built once in M0.
* Reduced coordinates use sum-type indices + `Matrix.fromBlocks`, matching the
  repo's product-index convention.
* Value functions are *defined by the backward recursion* and then proved to
  equal the optimization value (the Lean-natural direction for `lem:prelim`).
* Named constants (`c₁…c₅, c_Φ, ρ_c, ρ₂, σ, γ`, …) become explicit `∃`-bound
  packages per lemma, not global `def`s, to keep statements self-contained.
* Blueprint discipline: every paper label gets a blueprint node; the M2 facts
  are leaf nodes marked not-yet-proved so the dependency graph is honest.

## Risks / open items

1. **`fact:lqr` size uncertainty** is the dominant unknown; nothing in M1
   caps it. Mitigated by staging (M1 lands meaningful, checkable content
   regardless).
2. **README** claims no `sorry`/axioms; while M2 is open this is false for the
   Estimation track. Add a "staged assumptions" section to README (and note the
   pre-existing `contDiffOn_extension` sorry already breaks the claim on
   `main` — see the plan note's repo-issues list).
3. **GAS definition mismatch**: `costogo.tex` `def:gas` (uniform `σ_T‖a‖`
   bound) vs. the Lyapunov draft's ε–δ + convergence. We formalize the
   costogo form; if M3 lands, prove the implication to the classical form as a
   corollary.
4. Constant bookkeeping in `lem:coercive`/`lem:val-rate` is the likeliest
   source of grinding; consider a small `Bound` helper API early if it drags.
5. **costogo.tex lags paper.tex on patched proofs.** The C2-necessity fix is
   handled by decision 5 (formalize `paper.tex@dcdb3d8`'s argument). More
   generally, paper.tex has received proof patches (`16b7de3`, `dcdb3d8`)
   that costogo.tex has not: the `prop:infhor` restatement (`it:xTT` as
   `x̂(T|T) − x̂(T|∞) → 0` with an output-injection proof, the `½`-factor in
   `it:Vlim`), the `1/σ̄(Σ₀)` rescaling in the `lem:unibounded` bound, and
   the quantitative Gramian fact. When a costogo statement and its paper.tex
   counterpart disagree, prefer paper.tex and flag the divergence so
   costogo.tex can be patched to match what was formalized.

## Suggested first PRs

1. M0: `IsSchurStable` + Schur ⟺ exponential decay + ℝ/ℂ bridge.
2. M0: `IsDetectable`/`IsStabilizable` + Hautus characterizations.
3. M0: `fact:poly-growth` / `no-decay` / `eig-orbit` / `gramian`.
4. M1: problem setup + `lem:prelim` part (1) (the DP induction), with
   `fact:lqr`/`fact:uniexp` stated and staged.

# Sprint: Lean-verify `prop:infhor` of `../rawlings_quah_mueller_2026a/paper.tex`

**Verdict: yes, we can Lean-verify it.** The statement is stable even
though the proof wording is in flux, and roughly 70% of the required
machinery already exists from the costogo track (the trajectory-deviation
gap formula, the general-coordinates problem layer, the C2 reduction, the
output-injection deviation device, the infinite-horizon `tsum` cost, and
— already sorry-free — `eq:polysample` and `eq:gramian`). Estimated
800–1500 lines, 1–2 sessions. Details, findings for the authors, design
decisions, and tasks below.

## What `prop:infhor` (paper.tex) says, vs. what we already have

Paper statement (line ~1092): for `ℙ_T` (original χ-coordinates,
`lem:semiPT` form, nominal measurements `y(k) = CA^k x(0)`,
`Σ₀ ⪰ 0`):

1. **it:zlim** (C2 alone): `x̂(0|T)` and each `ŵ(j|T)` converge as
   `T → ∞`.
2. **it:xTT** (C1 additionally): `x̂(T|T) − x̂(T|∞) → 0`, where
   `x̂(·|∞)` is the rollout of the limit pair.
3. **it:Vlim** (C2 alone): `V_∞` evaluated at the limit pair equals
   `V_∞⁰ := lim V_T⁰`.

This is *not* the costogo `prop:infhor` we already formalized
(`Estimation/Infhor.lean`): that one is in reduced coordinates, assumes
C1 ∧ C2 throughout, and identifies the limit as the unique minimizer of
`ℙ_∞e`. The paper version is general-coordinates, C2-only for (1)/(3),
and its (3) is the weaker cost-consistency claim (no minimizer
identification). So the statements are new, but they sit squarely on
existing machinery — in particular the `GeneralSystem` layer and the C2
reduction built in the generality sprint apply verbatim, because **every
part of `prop:infhor` assumes C2**, which is exactly when the reduction
is available.

## Findings for the authors (useful now, while wording is in flux)

1. **`lem:unibounded` claims C2 alone but its deferred proof uses C1.**
   The deferred proof (sec:proofs) invokes preliminary fact `eq:cc`,
   whose hypotheses include `(A, Q̃^{1/2})` detectable, and says
   explicitly "(A₁, R^{−1/2}C₁) is detectable since (A,C) is
   detectable" — that is C1, inside a lemma stated under C2 alone. And
   `prop:infhor` items (1)/(3) inherit "C2 alone" from `lem:unibounded`.
   **The claim is true under C2 alone**; the fix is to restate `eq:cc`
   for an *arbitrary stabilizing feedback*: `(A,B)` stabilizable gives
   `K̃` with `A+BK̃` Schur; the Lyapunov equation
   `S − (A+BK̃)'S(A+BK̃) = Q̃ + K̃'R̃K̃` has a PSD solution for any Schur
   closed loop, and the rollout cost is `½x₀'Sx₀ ≤ ½λ̄(S)‖x₀‖²`.
   Detectability is only needed to make the *optimal* LQR feedback
   stabilizing — irrelevant for an upper bound by a chosen feedback.
   We will formalize the C2-only version this way.
2. **Both `it:xTT` proof variants are verifiable; the statement is
   wording-proof.** The active IOSS-Lyapunov variant needs the quadratic
   IOSS fact (`eq:iioss-bounds`/`eq:iioss-dec`) formalized; the
   commented-out output-injection variant maps 1:1 onto machinery we
   already built (the GAS deviation estimate in `Estimation/GAS.lean` is
   literally that convolution bound). Plan: verify `it:xTT` via
   output-injection now; formalize the IOSS-Lyapunov fact as a stretch —
   it is needed anyway for `prop:tvkfQuns` (next sprint candidate), via
   `x⁺ = (A−LC)x + LCx̃-terms` and a discrete Lyapunov solution, so
   nothing about the final wording choice blocks us.
3. Minor wording nits in the current proof text: stray "()" in
   "Refactoring `V_T` about `ẑ_T` ()"; the `F_T` clause "up to a
   z-independent term" earns one more clause noting `δν` is *linear*
   (not affine) in `δz`, which is why the refactored gap picks up
   `‖δν‖²_{R⁻¹}` exactly; the index scoping "`j ∈ [0:T−1]`" in
   `it:zlim`'s statement reads oddly for a `T → ∞` limit (each fixed
   `j ≥ 0` is meant).
4. Good news to record: the paper's `eq:polysample` (stride Lagrange
   interpolation) and `eq:gramian` (quantitative Gramian via Jordan
   blocks) are **already machine-verified** —
   `LinearSystems/SpectralGrowth.lean` (`pow_mulVec_le_poly` route and
   `end_gramian_growth`/`gramian_growth`), sorry-free, from the costogo
   sprint. (Our Gramian proof is Jordan-free — mathlib has no real
   Jordan form — but proves the same statement.)

## Design decisions

- **D1 (coordinates).** Formalize the content on `GeneralSystem` (error
  coordinates, `a := x(0) − x̄₀`), then add a thin **`ℙ_T` wrapper**: the
  χ-decision problem with data `y(k) = CA^k x(0)`, cost
  `ℓ_x(χ(0)−x̄₀) + Σ ℓ(ω,ν)`, and the support constraint stated as
  `χ(0) − x̄₀ ∈ range Σ₀`. The bijection `(χ, ω) ↦ (e = A^k x(0) − χ, ω)`
  is affine, cost-preserving, and support-preserving, so every
  `prop:infhor` object (`x̂(0|T)`, `ŵ(j|T)`, `x̂(T|T)`, `V_T⁰`)
  transports. For faithfulness to the paper's `U₂'(χ(0)−x̄₀) = 0`, prove
  the SVD-free equivalence: for PSD `Σ₀`,
  `v ∈ range Σ₀ ⟺ ∀ z, Σ₀ z = 0 → z ⬝ v = 0` (range = kernel-annihilator;
  spectral machinery for this exists in `SymmPinv.lean`). No `U`-matrices
  in Lean.
- **D2 (route).** Prove C2-only statements by **transfer through the
  reduction** (`redSys`, `red_value`, `red_optInit`, `red_cost`, …, all
  valid under C2) wherever possible; replay directly at the general
  level only where transfer is awkward (value monotonicity replays
  easily from `value_le_gCost` + cost-splitting, like
  `GeneralNecessity.value_succ_le`).
- **D3 (it:xTT).** Output-injection device (existing), not IOSS.
- **D4 (gap formula).** Obtain the general `eq:gap` under C2 by
  transferring `fieCost_gap` (the deviation pair is itself a
  corresponded feasible pair; the deviation's prior penalty transfers
  because both optima are feasible, so the difference lies in
  `range Σ₀`). Note: `eq:gap` is true without C2 (pure quadratic
  algebra), but the C2-scoped version suffices for the whole
  proposition; a C2-free general gap is out of scope.

## Tasks

### S1. `ℙ_T` wrapper layer *(small)*
`Estimation/ChiProblem.lean`: χ-cost with nominal data; correspondence
`V_T(χ,ω) = gCost a e₀ ω T` under `e₀ = x(0) − χ(0)`; range ⟺
kernel-annihilator feasibility lemma; transport of optimizers
(uniqueness on both sides) and of `x̂(k|T)`-trajectories.

### S2. General gap formula under C2 *(small–medium)*
`red_gCost_gap`: for feasible `(e₀, ω)`,
`gCost a e₀ ω T − V_T⁰ = ½‖δe₀‖²_{Σ₀†-on-range} + ½Σ(‖δω‖²_{Q⁻¹} + ‖δν‖²_{R⁻¹})`
by transfer from `FIESystem.fieCost_gap`. Also the norm-equivalence
corollary (`eq:rangebound` + `eq:quadbound`, both existing) bounding
`‖δe₀‖² + Σ‖δω‖² + Σ‖δν‖²` by a constant times the gap.

### S3. `lem:exist`, joint uniqueness *(small)*
Existence ✓ exists (`exists_isStationary` + attainment). New: joint
uniqueness of `(e₀, ω̂(0:T−1))` — zero gap forces `δω = 0` (`Q⁻¹ ≻ 0`)
and `δe₀ = 0` (pinv-image + kernel pinning, same ending as
`isStationary_unique`). C2-free, as in the paper.

### S4. `lem:unibounded`, general, C2 only *(medium)*
- Reduced side: C2-only uniform bound — candidate `e(0) = (a₁, 0)`
  (feasible since `Σ₂ ≻ 0` under C2), `K̃`-rollout on block 1 with the
  Lyapunov-equation cost bound (no C1; `exists_stabilizing_gain` and the
  `rollE₁` machinery exist; the Lyapunov series bound is new but small).
- Transfer: `V_T⁰(a) ≤ c_v‖a‖²` for the general problem.
- Monotonicity of `V_T⁰` (truncation inequality, general replay) and
  convergence to `V_∞⁰`; the `eq:ellT` tail
  `ℓ(ŵ(T|T+1), ν̂(T|T+1)) → 0`.

### S5. `it:zlim` *(medium)*
C2-only Cauchy convergence of `optInit` **and of each `ŵ(j|T)`** (the
control limits are new even on the reduced side — our old Infhor proved
optimizer convergence under C1∧C2): apply S2's gap to truncations of
`p`-optima at horizon `m`, exactly the paper's `eq:gapopt` step. Define
`e₀∞`, `ω̂∞` by choice; export the limit statements.

### S6. `it:Vlim` *(medium — the bookkeeping risk)*
Infinite-horizon cost of the limit pair as a `tsum` (reduced-side
infrastructure in `Infhor.lean`; general analog by transfer or direct
definition). Two inequalities exactly as in the paper: `≤` via pointwise
limits at fixed `N`, dropping tails, then monotone convergence in `N`;
`≥` via prefix feasibility of the limit pair. C2 only.

### S7. `it:xTT` *(small–medium)*
Deviation-energy bound from S2/S5 (`… ≤ c_ε ε` for `T ≥ K(ε)`), then the
existing output-injection propagation bound
(`‖δe(T)‖ ≤ c_L‖δe(0)‖ + c(Σ‖δν‖² + ‖δω‖²)^{1/2}`) gives
`x̂(T|T) − x̂(T|∞) → 0` (no rate claimed — plain `Tendsto`). Needs C1
via `detect_inj` ✓ existing.

### S8. Assembly + wrap-up *(small)*
`prop_infhor` as a three-part theorem on the S1 wrapper, quoting the
paper's statement shape (hypothesis split C2 / C2∧C1 exactly as
printed); `#print axioms` audit; both notes updated; mapping-table rows;
PR.

**Stretch (deferred, feeds the next sprint):** quadratic IOSS-Lyapunov
fact (`eq:iioss-bounds`/`eq:iioss-dec`) from `detect_inj` + discrete
Lyapunov series — wanted for `prop:tvkfQuns`/`prop:modQgas`, which are
the natural next target after this sprint (their remaining inputs —
`lem:unibounded`, `prop:infhor`, quantitative Gramian, `eq:rangebound` —
will all be in place).

## Done criteria

1. `lake build` green; zero new sorries.
2. `#print axioms` on `prop_infhor` parts:
   `[propext, Classical.choice, Quot.sound]` only.
3. Hypothesis bookkeeping matches the paper's split (it:zlim/it:Vlim
   under C2 alone — i.e., the C1 leak of finding 1 is *fixed* in the
   formalization, not reproduced).
4. Notes updated; PR body drafted (no `gh` on this machine — compare
   link as before).

## Working agreements

As before: work independently, commit per landed cluster, prefer
paper.tex over costogo.tex where they disagree, and flag every
divergence here so the paper can be patched to match what was verified.

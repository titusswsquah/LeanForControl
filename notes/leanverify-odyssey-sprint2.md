# Odyssey full-completion sprint (sprint 2): everything to tier 1

Goal: **every statement in `odyssey-src/` is a Lean theorem, and every
deck proof matches its Lean proof** (implementation deviations only,
documented in `LEAN:` lines). No hypothesized imports left in the main
theorems; no rate claim, spectrum claim, or payoff claim without a
Lean head; `a00-facts` reduced to pointers at theorems (or explicit
eliminations). The one statement allowed to remain unproven is the
one the deck itself declares open: the **defective-marginal case** —
deck and Lean agree on the semisimple qualification, which is tier-1
by our definition (deck claims = Lean theorems).

Continues `notes/leanverify-odyssey-sprint.md` (Phases A–C, closed
2026-09-01) under the same conventions
(`notes/verified-deck-convention.md`): upstream never touched, deck
edits in `odyssey-src/` with per-finding commits + re-stitch
(`./flow.sh --md`), Gate-2 numeric checks before writing Lean or
prose, `#print axioms` = `[propext, Classical.choice, Quot.sound]` on
every head, no `sorry` in the landed tree, findings mirrored in
`notes/leanverify-odyssey-findings.md` (next number: 14).

## Where we stand (tier map after sprint 1)

Tier 1 (verified, deck = lean): the covariance main line —
comparison/gap engine/`eq:bounded`/structure/extinction/criteria,
`lem:marginal` (repaired), `lem:supremal`, `thm:necessity`,
slaved seed + loading, `lem:condfilter` 1–2 + `eq:J1-rec`,
`lem:lowsqueeze`, `thm:sufficiency`, `thm:main`-1, `thm:main`-2
converse (`marg_not_exponential`).
Tier 2 (verified modulo declared imports): `IsStrongSolution`
existence (`fact:dare-strong`), `eq:Finf-spec` restricted
(`IsSchurStable` hypothesis), `ReducedImport` (reduced
`fact:dare-strong` + product bound), power-bounded marginal.
Tier 3 (deck-level only): all rate claims, 08's Spectrum paragraph,
`thm:payoff` (frame transfer, Part 1, ISS), `cor:every-prior`,
Arc 1 (`a03-formula`, `a04-subspace`), `lem:slaved-seed`-1 general
form, no concrete instance.

## Phase D — Discharge the imports: spectrum, strong solution, reduced filter

The deepest phase: turn every tier-2 hypothesis into a theorem.

- **D0 (Gate 2).** Numeric pre-checks for the new claims: the
  spec-split `spec(F∞) = spec(Fs) ⊔ spec(Aₘ)`, the PBH–Stein
  eigenvector kill at `|μ| ≥ 1`, closed-loop product bounds along the
  reduced run, the chart-assembled Σ∞ against a solver.
- **D1 (`eq:Finf-spec` → theorem).** Key structural fact already in
  hand: `embMᵀF∞ = AₘembMᵀ` ⇒ `embMᵀF∞embS = 0` — F∞ is genuinely
  block-triangular w.r.t. (e₁⊕a | m), so
  `spec(F∞) = spec(Fs) ⊔ spec(Aₘ)` (charpoly of block-triangular).
  Then `strong_Fs_schur : IsSchurStable Fs` by the **PBH–Stein
  argument**: an eigenvector `w` of `F∞ᵀ` at `|μ| ≥ 1` collapses the
  predictor Stein relation (`strong_stein`) — killing
  `K∞ᵀAᵀw = 0` and `fullGᵀw = 0` — hence `w` is a left eigenvector of
  `A` with `Gᵀw = 0`: its e₁ part dies by `hStab` (PBH), its a part
  by `hAnti`, so `w` is m-supported and cannot come from the
  Fs-block (handle the `μ ∈ spec(Aₘ)` coincidence via the
  quasi-eigenvector telescope, the m-contamination killed by
  extinction `Σ∞·embM = 0`). Complex bookkeeping via the existing
  re/im transport patterns (KernelInvariance/StrongSolution).
  Corollary: `ρ(F∞) ≤ 1` from the split. **Discharges `hFs` in
  `supremal_tendsto`, `sufficiency_tendsto`,
  `strong_attraction_iff_C2w`.** Deck: 08's Spectrum paragraph
  rewritten to the PBH–Stein route (the current "reflection realized
  by the inside representative" parenthetical is a hand-wave —
  expected finding 14) + lean-sync.
- **D2 (reduced stabilizing solution).** Monotone-PSD-convergence
  lemma (quadForm monotone bounded → polarization → entrywise
  limit). Reduced system (A₁, C₁, G₁): zero-seed run is monotone
  nondecreasing (`dareIter_mono`) and bounded (`exists_dare_bound`
  restricted) ⇒ limit `P∞` exists; fixedness by `dareStep`
  continuity at the limit (innov-inverse continuity, existing
  patterns); `ρ(L∞) < 1` by the reduced PBH–Stein argument (no
  uncontrollable-unstable e₁ modes: `hStab`); uniqueness of the
  stabilizing fixed point via `dareStep_diff` between two Schur
  loops.
- **D3 (`ReducedImport` → theorem).** `L_t → L∞` (gain continuity,
  existing); the **eventually-contracting products** lemma: powers of
  the Schur limit contract in `n₀` steps, convergence puts each
  `n₀`-block within reach ⇒ uniform product bound and geometric
  block decay (this is `fact:uniexp`'s core, reused in F2). Then
  `dareIter_diff` + the product bound ⇒ **geometric** `P_T → P∞`
  (feeds E2). Deliverable: `reducedImport_holds : S.ReducedImport
  Sinf` (with `infP Sinf = P∞` via D2-uniqueness) — **discharges the
  `himp` hypothesis everywhere.**
- **D4 (`fact:dare-strong` → theorem).** Existence by
  **chart-assembly**: `P∞` from D2; `Λ∞ := Σₖ L∞ᵏ d∞ (Aₐ⁻¹)ᵏ`
  (monotone/partial-sum limits — no tsum needed); the information
  gramian `J∞ := Σₖ (Aₐ⁻ᵀ)ᵏ⁺¹ Ξ∞ Aₐ^{-(k+1)}` with `J∞ ≻ 0` from C1
  by PBH (an annihilated direction is an undetectable antistable
  mode) — this is `lem:structure`-1's true content and likely a deck
  repair (its `eq:Sinf-gram` display becomes the verified
  construction); assemble `Σ∞ := e₁P∞e₁ᵀ + V∞·J∞⁻¹·V∞ᵀ`; fixedness
  via `chart_dareStep` read backwards (all chart data fixed);
  `specLe` via D1's argument applied to the constructed solution
  (extinction holds by construction). Uniqueness: a second strong
  solution is a C2w-prior fixed run, pinned by `sufficiency_tendsto`.
  Deliverable: `exists_isStrongSolution (hC1 …) : ∃ Sinf,
  S.IsStrongSolution Sinf` (+ uniqueness); main theorems restated in
  ∃-form; `a00-facts`' `fact:dare-strong` becomes a pointer.

Exit criterion: `strong_attraction_iff_C2w` holds under **C1 +
power-bounded marginal only** (both power directions where used).

## Phase E — Rates and Arc 1: the quantitative deck

- **E1 (rate engine).** Rate-carrying convolution:
  `x T ≤ a·ρᵀ + Σ ρ^{T-1-j}·e j` with `e j ≤ E·σʲ` gives
  `x T ≤ C·ρ'ᵀ` for any `ρ' ∈ (max ρ σ, 1)` (dodge the equal-rate
  log factor by widening). Rate-composition helpers mirroring the
  `tendsto_mat*` family (`le_geo_mul`, `le_geo_add`, …).
- **E2 (geometric lower anchor).** Thread rates through the Phase-B
  chain: `Λₘₐ` (already geometric), `P` (D3), `K/L/d/ε` (continuity
  chains with rate), `Λ₁ₐ` (lam_unroll + E1), `Ξ`, `J`
  (conj_unroll + E1), `Saa` (inversion with rate), assembly ⇒
  `lowsqueeze_geometric`. Lean-syncs the "exp. fast" claims of
  `lem:condfilter`-3, `eq:J1-home`, `eq:lowsqueeze`.
- **E3 (C3w branch = `thm:main`-2 forward).** With `nm = 0` the
  upper gap is a pure Löwner–Schur iterate (X ≡ 0) — geometric via
  D1's `Fs = F∞` Schur; lower from E2 ⇒ `thm:sufficiency`'s rate
  paragraph verified ⇒ **Part 2 forward verified**; with the Phase-C
  converse, `eq:main-stab` is fully tier 1.
- **E4 (Arc 1).** `a03-formula`: the deck's own proof of
  `thm:formula` is a **direct induction** on exactly our toolbox —
  `eq:gap-ric` exact step, the push-through
  `Γᵀ(S∞ + ΓXΓᵀ)⁻¹ = (I + ΩX)⁻¹ΓᵀS∞⁻¹` (uhat-style), and the
  Sylvester determinant identity (`det(I + AB) = det(I + BA)`) for
  the nonsingular slide. Verify: the pencil-triangularization
  identities id1/id2 + `eq:pencil-block` (matrix-multiplication
  checks), `eq:formula` by induction, the gramian limit
  (monotone-PSD, D2 lemma) and the `ρ(F∞)²` rate corollary. The
  pencil *derivation* stays as narrative with a `LEAN:` note (the
  formula is the theorem). `a04-subspace`: `lem:sysinterp`
  (transversality of the prior plane to the antistable deflating
  subspace ⟺ C2) — subspace geometry over ℂ; scope on reading, may
  yield a finding if the deflating-subspace language resists a
  kernel-form restatement.
- **E5 (`lem:slaved-seed`-1 general).** Restate Part 1 without the
  pseudoinverse (existential loading: `range Σₐₘ ⊆ range Σₐₐ` gives
  `Λ₀` with `Σₐₘ = ΣₐₐΛ₀ᵀ`; mathlib has no Moore–Penrose to lean
  on) and verify for every PSD prior; deck edit accordingly.

Exit criterion: every displayed equation and every rate/spectrum
claim in 00–08 + a00–a04 has a Lean head.

## Phase F — The payoff frame, instances, closure

- **F1 (payoff in-frame).** Frame transfer `DareSystem → FIESystem`
  (lump `a ⊕ m` into `n₂`; `hAnti` |λ|≥1 holds for `Aₐ⊕Aₘ`):
  construct the instance, prove the condition correspondences
  (C1 ↔ C1, C2 ↔ C2, C3w ↔ C3w in kernel/PBH forms), and transport
  the verified arc1 dichotomy (`gas_ges_dichotomy`) and the
  FIE↔TVKF bridge (`isGASkf_iff_isGAS`) into 3-block-frame
  statements of `thm:payoff` Part 2. Part 1 = D1's spectrum theorem
  restated. Deck: payoff LEAN lines lose the "frame transfer
  deck-level" flag.
- **F2 (robustness/ISS).** Full-system uniform-exponential products
  under C1+C2+C3w (D3's eventually-contracting machinery at the full
  level + E3's covariance rate for `F_T → F∞` summability) ⇒ the ISS
  display of `thm:payoff` verified (disturbance-driven error
  recursion, unrolled bound). GAS-branch claims stay qualitative
  (as repaired in Phase C — no ISS claimed there).
- **F3 (`cor:every-prior`).** Verify both halves: covariance —
  (∀ priors, C2w) ⟺ `na = 0` (i.e. `𝒳ₐ,ᵤ𝒸 = 0` in-frame);
  error — (∀ priors, C2) ⟺ `na = nm = 0` ⟺ `(A,G)` stabilizable
  (Hautus bridge), and every-prior GAS = GES.
- **F4 (hypothesis hygiene).** (a) Attempt
  `semisimple marginal ⇒ Aₘ, Aₘ⁻¹ power-bounded` to replace the
  power-bound hypotheses with the deck's own wording; fallback: align
  the deck to state power-boundedness (with semisimplicity as the
  classical sufficient condition, cited). (b) A concrete
  `DareSystem` instance (small blocks, decide/norm_num spectra +
  PBH) discharging *all* standing hypotheses at once — kills the
  vacuity caveat. (c) `a00-facts` sweep: every fact is a pointer to
  a Lean head or marked eliminated; `fact:gramian`,
  `fact:poly-growth` retired if no longer cited.
- **F5 (closure).** Full adversarial audit (statement-by-statement
  deck ⇄ Lean diff; axiom sweep; vacuity; stale-prose grep); final
  lean-sync so **no** `LEAN:` line says "imported" or "not
  formalized" except the declared defective-marginal open problem;
  findings + PR body (`notes/leanverify-odyssey-pr.md`) updated to
  the completed state.

Exit criterion (sprint): a reader of `odyssey.md` finds, at every
result, a `LEAN:` line naming its theorem; the only forward reference
to unproven mathematics anywhere is the deck's own open problem.

## Risks and pre-commitments

- **D4 is the deepest** (existence). Fallback order inside D4: the
  chart-assembly is designed so each piece lands separately (P∞,
  Λ∞, J∞ ≻ 0, assembly, specLe); if `J∞ ≻ 0` via detectability-PBH
  stalls, it isolates cleanly as the one remaining hypothesis and the
  phase still discharges everything else.
- **E4/a04**: `lem:sysinterp` is unscoped until read; the formula
  (`thm:formula`) is low-risk. If the deflating-subspace statement
  resists, repair the deck to the kernel-form criterion it actually
  uses (finding, per convention).
- **F4(a)** semisimple ⇒ power-bounded may exceed its value; the
  deck-alignment fallback is explicitly acceptable (tier 1 = deck
  says what Lean proves).
- Rate constants are existential throughout (no explicit-constant
  claims in the deck; keep it that way).
- Watch for new findings: D1 (08's reflection parenthetical), D4
  (`lem:structure`-1's gramian display), E4 (a03/a04 narrative),
  each gets its own numbered finding + per-finding commit.

## Phase-order rationale

D before E because every rate proof wants the discharged spectrum
(Fs Schur) and the reduced geometric convergence; E before F because
the payoff's ISS needs E3's rate and F1's Part 1 needs D1. Inside
each phase, Gate-2 checks precede Lean, Lean precedes deck edits,
deck edits precede lean-sync — as in sprint 1.

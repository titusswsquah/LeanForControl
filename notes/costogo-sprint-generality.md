# Sprint: close the generality gap (`thm:gas-ges-fi` in the paper's own coordinates)

**Goal.** Upgrade the verified headline from "GAS/GES dichotomy for the
*reduced-coordinates* `FIESystem`" to the paper's actual statement:
`thm:gas-ges-fi` for a general system `(A, G, C)` with prior `Σ₀ ⪰ 0`,
`Q ≻ 0`, `R ≻ 0`, with C1/C2/C3w stated **invariantly** and stability
measured on the general error-coordinate problem `ℙ_Te` (`eq:PTe`'s
un-reduced ancestor). Zero sorries; the axiom check on the general
headline must again show only `propext, Classical.choice, Quot.sound`.
Outcome feeds the paper remark ("machine-verified, no caveats about
coordinates").

**Why now.** The disclosure-version remark would disclose away the wrong
thing: C2 — the paper's novel condition — only acquires its invariant
meaning (`ker Σ₀ ∩ 𝒳_{u,uc}(A,G) = 0`) through the reduction we
currently assume. Everything below is linear-algebra plumbing on top of
machinery that already exists in the repo (Bezout spectral projections,
Hautus infrastructure, the outer-KKT parameterization); the risk profile
is tedium, not depth.

## Structural findings that shape the plan (verified against costogo.tex)

1. **`def:gas`/`def:ges-fi` are defined on `ℙ_Te`** ("the trajectory
   that solves the error-coordinate problem"), *not* on the Kalman
   recursion. So `lem:semiPT` (M3) is interpretive and **out of scope**
   for matching the headline's generality. Likewise the data-driven
   `ℙ_T → ℙ_Te` substitution is presentation, not hypothesis.
2. **The paper's own congruence appendix (`app:congruence`) validates
   the parameterized-penalty route**: it notes explicitly that
   `𝒯⁻ᵀ Σ₀† 𝒯⁻¹ ≠ (𝒯Σ₀𝒯')†` off the range, and that the transfer works
   because both forms agree *on `R(Σ₀)`, where the support constraint
   confines `u`*. Our formalization already proves the two-way
   equivalence between the `Σ†`-penalty-plus-range-constraint form and
   the `e₀ = a + Σv` parameterization (`feasible_iff`,
   `quadForm_symmPinv_image`, the outer-KKT layer). **Route every
   penalty transfer through the parameterization** and the congruence
   step becomes exact quadratic-form algebra — and, as a bonus, the
   staircase transformation `T₁` need not be orthogonal (any invertible
   adapted basis works), which kills the Gram–Schmidt/EuclideanSpace
   friction entirely.
3. The reduction has **two stages**, and C2 is consumed between them:
   `T₁` (stabilizability staircase: `A` block-triangular, `A₂`
   completely unstable, `G = col(G₁,0)`) → `lem:Sigma2-pd`
   (C2 ⟹ `Σ₂ ≻ 0`) → `T₂ = [[I, −Σ₁₂Σ₂⁻¹],[0, I]]` (prior
   block-diagonalization; class-preserving: only `A₁₂`, `C₂`, `Σ₁`
   change, `A₁`, `A₂`, `G₁`, `Σ₂` survive).

## Tasks

### S1. Vacuity guard: explicit instances *(small; do first)*
Construct a concrete `FIESystem` instance (e.g. `n₁ = n₂ = m = p = 1`,
`A₂ = 2`, everything else `1`) and, once S2 lands, a general-coordinates
instance. Purpose: certify the hypothesis classes are consistent so no
theorem is vacuous. Also the cheapest possible failure detector for S2's
definitions.

### S2. The general problem layer *(medium)*
New file `Estimation/General.lean` (or similar):
- `structure GeneralSystem`: `A, G, C, Sig0, Qn, Rn` with `Sig0.PosSemidef`,
  `Qn.PosDef`, `Rn.PosDef` — **no structural hypotheses**.
- General `ℙ_Te`: cost `‖e₀−a‖²_{Σ₀†} + Σ (‖Ce‖²_{R⁻¹} + ‖ω‖²_{Q⁻¹})`
  with support constraint phrased as `e₀ − a ∈ range Σ₀` (equivalent to
  the paper's `M₂'(e₀−a) = 0` SVD form; avoids formalizing the SVD).
  Reuse the `LQSystem` layer for dynamics/cost verbatim.
- General stationarity/optimizer: mirror the reduced outer-KKT
  (existence via `PosSemidef.exists_mulVec_eq`, uniqueness via the gap
  formula — the proofs are coordinate-free already; consider
  generalizing the existing FIE outer layer rather than duplicating).
- `IsGAS`/`IsGES` verbatim on the general optimizer's terminal error.
- Invariant standing conditions:
  - **C1**: `IsDetectable (complexify A) (complexify C)` — already have.
  - **C3w**: PBH form — no `μ` with `‖μ‖ = 1` admits a left eigenvector
    of `A` annihilated by `Gᵀ` (matches "no uncontrollable unit-circle
    eigenvalues"; dual-Hautus style, matches existing infra).
  - **C2**: see Design decision D1 below.

### S3. Real spectral split *(medium)*
Real versions of `stabPoly`/`antiPoly`: the stable factor of a real
characteristic polynomial is real (conjugation-invariance of the root
multiset filtered by modulus; `‖conj λ‖ = ‖λ‖`). Then real Bezout
projections `Ps, Pa` (polynomials in `A`, idempotent, commuting — same
skeleton as `StabilizableBound`, over ℝ), giving the **stable subspace**
`Xs := range Ps` and its complement data. Estimated 200–350 lines.
Reuse note: the ℂ-side proofs in `StabilizableBound.lean` are the
template; only the realness of the factors is new.

### S4. Staircase construction `T₁` *(large — the riskiest task)*
- `V₁ := reachableSubspace(A,G) ⊔ Xs` (A-invariant, contains `range G`).
- Build invertible `T₁` from a basis of `V₁` extended to `ℝⁿ`
  (`Submodule` basis + `Basis.extend`; **no orthogonality needed** per
  finding 2).
- Prove, for `A' = T₁⁻¹AT₁`, `G' = T₁⁻¹G`:
  block-triangularity (invariance of `V₁`), `G' = col(G₁, 0)`
  (`range G ⊆ V₁`), `(A₁, G₁)` stabilizable (Hautus transfer: an
  unstable left-eigenvector of `A₁` ⊥ `G₁` lifts to one of `A` ⊥ `G`),
  and `A₂` completely unstable (a stable eigenvalue of `A₂` would put a
  generalized eigenvector inside `Xs ⊆ V₁` — argue via the `Ps/Pa`
  projections, not Jordan forms).
- Risk: basis/`toMatrix` bookkeeping. Mitigation: state everything as
  matrix identities against a fixed `Basis.toMatrix`-built `T₁`; budget
  1.5× the naive estimate. 400–600 lines.

### S5. `lem:Sigma2-pd` + congruence `T₂` *(small–medium)*
- C2 (invariant, via D1) ⟹ `Σ₂ ≻ 0` in staircase coordinates — the
  paper's three-line pairing argument.
- `T₂`-congruence: explicit `[[I, −Σ₁₂Σ₂⁻¹],[0,I]]`; show it maps the
  staircase class to our `FIESystem` class (recompute `A₁₂`, `C₂`,
  `Σ₁ − Σ₁₂Σ₂⁻¹Σ₁₂ᵀ`; `fromBlocks` algebra we have in bulk).

### S6. Transfer theorems *(medium)*
For a single invertible `T` (compose `T₁`, `T₂` or do two steps):
- Feasible-set bijection and **value equality** via the parameterized
  penalty (finding 2).
- Optimizer correspondence: `e*'(k|T) = T⁻¹ e*(k|T)` (uniqueness on
  both sides via the respective stationarity systems), hence terminal
  errors related by `T`.
- `IsGAS ↔ IsGAS'`, `IsGES ↔ IsGES'` (norm equivalence `‖T‖, ‖T⁻¹‖`
  and the `a ↦ T⁻¹a` bijection of prior mismatches).
- Condition equivalences: C1 ⟺ `Sys.C1` (similarity invariance of
  detectability), C3w ⟺ `Sys.C3w` (left-eigenvector transfer;
  spectrum of `A₂` = unit-circle-free), C2 ⟺ `Sys.C2` (**both**
  directions — the necessity direction of the headline needs
  ¬C2 ⟹ `Σ₂` singular; short once D1 is fixed and
  `𝒳_{u,uc}`-in-coordinates is identified).

### S7. General headline + audit *(small)*
`thm:gas-ges-fi` on `GeneralSystem`, by transfer from
`gas_ges_dichotomy`. Re-run `#print axioms`. General-coordinates
instance from S1. Update the paper-label ↔ Lean-name mapping table.

### S8. Wrap-up *(small)*
Scope-note update; draft the paper remark for costogo.tex (and the
C2-necessity remark for the 2026a paper); PR to `main`.

**Stretch (explicitly deferred, not part of "no cheating"):**
`ℙ_T → ℙ_Te` data substitution; `lem:semiPT` (M3); blueprint enrichment;
lint cleanup.

## Design decisions to confirm before/during S2

- **D1 — SETTLED (from the 2026a paper).** The 2026a proof of
  `lem:unibounded` defines the unstable, uncontrollable subspace as
  `span E₂`, `E₂ = col(0, I_{n₂})`, *in the coordinates of the
  orthogonal canonical form* `eq:contrb`. In original coordinates that
  is the dot-product annihilator of the stabilizable subspace:
  `𝒳_{u,uc} := {v | ∀ u ∈ V₁, u ⬝ᵥ v = 0}` with
  `V₁ := reachableSubspace(A,G) ⊔ Xs(A)`, and
  `C2 := ker Σ₀ ⊓ 𝒳_{u,uc} = ⊥`. Key computations validating the
  non-orthogonal route: for any invertible `T₁` adapted to `V₁`,
  `T₁⁻ᵀ (0 ⊕ ℝ^{n₂}) = 𝒳_{u,uc}` exactly (pairing
  `⟨T₁⁻ᵀ(0,v₂), T₁(x₁,0)⟩ = (0,v₂)⬝(x₁,0) = 0`, plus surjectivity of
  `T₁⁻ᵀ` for the reverse inclusion — no dimension theory), so
  `lem:Sigma2-pd` and its converse transfer through the quadratic form
  `v₂'Σ₂'v₂ = ξ'Σ₀ξ`, `ξ := T₁⁻ᵀ(0,v₂)`.
- **D1a — proofs for S4's staircase properties, de-risked.** Both key
  facts fall to polynomial calculus, no quotients/dimension counting:
  (i) *`A₂` completely unstable*: a stable eigenvalue `μ` of `A₂` is a
  stable root of `χ_{A'} = χ_{A₁}·χ_{A₂} = χ_A` (block-triangular
  charpoly product via `det_fromBlocks_zero₂₁`; similarity invariance),
  so `χs(μ) = 0`; then the second block of `Pa'y`, `y := (0,v₂)`, is
  `u(μ)χs(μ)v₂ = 0` while `Ps'y` has second block `0`
  (`range Ps ⊆ Xs ⊆ V₁`), forcing `v₂ = 0`.
  (ii) *`(A₁,G₁)` stabilizable*: a left eigenvector `φ` of `A₁` with
  `|μ| ≥ 1` and `φ ⊥ G₁` kills `R'` (`φ∘A₁^k G₁ = μ^k φ∘G₁ = 0`) and
  kills `Xs'` (`0 = φ(χs(A₁)x₁) = χs(μ)φ(x₁)` with `χs(μ) ≠ 0` since
  `|μ| ≥ 1`), hence kills `block1 = R' + Xs'`, so `φ = 0`.
- **D2 (one `T` or two).** Two-stage (staircase, then congruence)
  mirrors the paper and keeps each transfer lemma simple; a single
  composed `T` halves the transfer boilerplate. Default: two-stage,
  since C2 is consumed between the stages.
- **D3 (generalize vs duplicate the outer-KKT layer).** The reduced
  outer machinery (`exists_isStationary`, `outerObj_gap`,
  `isStationary_unique`) is block-shaped (`Jmat = diag(Σ₁,Σ₂)`). For S2
  we need the single-block version — which
  `LinearSystems/ConstrainedQuadratic.lean` almost is. Default: extend
  `ConstrainedQuadratic` to a full mini outer-KKT (existence, gap,
  uniqueness) over one PSD `Σ`, and use it for the general layer; leave
  the reduced layer untouched.

## Done criteria

1. `lake build` green; **zero sorries** repo-wide in the costogo track.
2. `#print axioms` on the general `thm:gas-ges-fi`:
   `[propext, Classical.choice, Quot.sound]` only.
3. Both instances (reduced + general) compile — no vacuous hypotheses.
4. Mapping table current; scope note updated; PR opened with the
   verification statement.

## Working agreements

Same as previous sessions: work independently, commit at each landed
lemma-cluster, keep the scope note's status current. Estimated total:
~1500–2500 lines, 2–3 sessions; S4 carries the schedule risk.

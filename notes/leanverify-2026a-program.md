# Program: Lean-verify the *entire* `../rawlings_quah_mueller_2026a/paper.tex`

**Verdict: yes — the whole paper is verifiable.** Every theorem-level
claim is either already machine-verified (from the costogo track),
directly formalizable on existing machinery, or has a written proof to
formalize against (`lem:semiPT` via the arrival-cost machinery of
`../2025h_est_claude/gas-lyap-draft.tex`, `lem:arrival`). The in-flux
wording of `prop:infhor` does not block anything: its statement is
stable, and both candidate proof routes for `it:xTT` are verifiable.
Estimated total: ~3.5–7k new lines, 4–7 sessions, organized as four
sprints below. Sprint A is next.

## Claim-by-claim inventory

| Paper item | Status / plan |
|---|---|
| `eq:dre`, `L(k)`, `M(k)`, `ê(k) = M(k)ê(0)`; `Σ(k) ⪰ 0` well-posedness | Sprint C definitions; PSD preservation of the measurement update via the Schur-complement bound (machinery exists) |
| `eq:contrb` (orthogonal canonical form, "WLOG") | already surpassed: the staircase reduction (costogo M4) *derives* the form; statements stay invariant, no WLOG needed |
| **`prop:tvkf`** (headline: TVKF AS ⟺ C1 ∧ C2) | Sprint B proves it for the ℙ-optimizer; Sprint C transfers to the Kalman filter via `lem:semiPT` |
| `lem:semiPT` (KF ⟷ `ℙ_T`) | **stated without proof in paper.tex**; Sprint C formalizes it following `gas-lyap-draft.tex` `lem:arrival` (arrival quadratic `𝒥_T(ξ) = V_T⁰ + ½‖ξ−e*(T|T)‖²_{Σ_T†}`, support `im Σ_T`, DRE propagation) — this is the deferred costogo milestone M3, now load-bearing |
| `lem:exist` | mostly exists (`exists_isStationary` + attainment); joint `(e₀, ω̂)` uniqueness from the gap formula — Sprint A |
| `lem:unibounded` (+ `eq:ellT`) | Sprint A, C2-only, with the `eq:cc` fix (finding 1) |
| **`prop:infhor`** (it:zlim, it:xTT, it:Vlim) | Sprint A (detailed tasks below) |
| `def:modQ`, `prop:modQgas` (classical + KL proofs) | Sprint B; quadratic-μ specialization (decision D5); KL bound built directly, linearity-of-optimizer lemma replaces nothing-but-citations |
| `prop:tvkfQuns` (modified Q-function exists under C1∧C2) | Sprint B; needs the quadratic IOSS-Lyapunov fact + `lem:unibounded` + `eq:rangebound` (exists) + `V_io` rescaling |
| C2-necessity (inside `prop:tvkf` proof) | **content already verified** (`GeneralSystem.C2_of_isGAS`, incl. `eq:pin` pinning and the `eq:Venergy` cap); Sprint B optionally re-derives the growth step via IOSS for line-faithfulness (cheap once IOSS exists) |
| C1-necessity (cited to Allan–Rawlings–Teel) | **already verified directly** (`GeneralSystem.C1_of_isGAS`); Sprint B adds the KL-form → σ-form bridge via optimizer linearity |
| sec:proofs fact `eq:quadmin` | trivial / exists |
| `eq:quadbound`, `eq:rangebound` | exist (`QuadForm.lean`) |
| `eq:cc` (LQR upper bound) | Sprint A/B, restated for an arbitrary stabilizing feedback (finding 1) |
| `eq:iioss-bounds`/`eq:iioss-dec` (quadratic IOSS from detectability) | Sprint B, from `detect_inj` + discrete Lyapunov series (~200–400 lines) |
| `eq:polysample` | **already verified** (`SpectralGrowth.lean`) |
| `eq:gramian` (quantitative) | **already verified** (`SpectralGrowth.lean`; Jordan-free proof of the same statement) |
| Example 1 (Σ(k) = α^{2k}I, candidate V constant) | Sprint D, small algebraic instance (optional) |
| Example 2 (divergence under p(k) = 1/√(k+2)) | Sprint D stretch: the divergence is analytically provable (Σ(k) = 1/(k+1), telescoping gives ê(k) ~ (2/3)√k → ∞); the figure itself is not a verification target |
| Remarks / discussion / conclusions | expository, not verification targets |

Already in the bank from the costogo track and reusable verbatim:
`GeneralSystem` problem layer, C2 staircase-plus-decoupling reduction,
trajectory-deviation gap formula (`fieCost_gap`), output-injection
deviation device, infinite-horizon `tsum` cost, `detect_inj`, `lqr`,
`symmPinv` calculus, C1/C2-necessity, spectral growth facts.

## Findings for the authors (act on these while the text is in flux)

1. **`lem:unibounded` claims C2 alone but its deferred proof uses C1.**
   It invokes `eq:cc` (hypotheses include `(A, Q̃^{1/2})` detectable) and
   says "(A₁,R^{−1/2}C₁) is detectable since (A,C) is detectable" — C1
   inside a C2-only lemma; `prop:infhor` it:zlim/it:Vlim inherit the
   leak. The claim IS true under C2 alone: restate `eq:cc` for an
   *arbitrary stabilizing feedback* — `(A,B)` stabilizable gives `K̃`
   with `A+BK̃` Schur; the Lyapunov equation
   `S − (A+BK̃)'S(A+BK̃) = Q̃ + K̃'R̃K̃` has a PSD solution for any Schur
   closed loop, giving cost `≤ ½λ̄(S)‖x₀‖²`. Detectability is only
   needed to make the LQR-*optimal* feedback stabilizing, which an upper
   bound never needs. The formalization proves the C2-only version.
2. **`lem:semiPT` carries no proof in paper.tex.** The gas-lyap-draft's
   `lem:arrival` is a complete proof; formalizing it (Sprint C) will
   certify the statement — consider citing or absorbing that argument
   (or RMD20) so the paper's one unproven lemma has a source.
3. **`it:xTT` wording flux is harmless.** Both variants verify: the
   commented-out output-injection route maps 1:1 onto existing
   machinery; the active IOSS route needs the IOSS fact we must build
   for `prop:tvkfQuns` anyway. Plan: Sprint A verifies the statement via
   output-injection; Sprint D optionally re-proves via IOSS for
   line-faithfulness.
4. **`def:modQ`'s K∞-functions are only ever quadratic.**
   `prop:tvkfQuns` supplies quadratic μ's and `prop:modQgas` composes
   them; we verify the quadratic form (explicit √-formulas for
   `μ₁⁻¹∘μ₀`), with the general-K∞ statement a free generalization
   (mathlib has no K∞/KL classes; we hand-roll the product form
   `β(r,k) = r·α(k)`, which is all the linear case needs).
5. **KL uniformization has a bridge-free alternative.** The KL proof
   uses `M(k)` (DRE side). The ℙ-optimizer is itself linear in
   `a = x(0) − x̄₀` (KKT linearity + uniqueness), so the same
   pointwise-to-uniform column trick runs on `N(k)` without the KF
   bridge; we prove the linearity lemma in Sprint B and verify the
   paper's `M(k)` version in Sprint C.
6. Minor nits: stray "()" in "Refactoring `V_T` about `ẑ_T` ()"; the
   `F_T` "up to a z-independent term" clause deserves a note that `δν`
   is *linear* (not affine) in `δz`; `it:zlim`'s "`j ∈ [0:T−1]`" index
   scoping reads oddly for a `T → ∞` limit (each fixed `j ≥ 0` is
   meant).
7. Good news: `eq:polysample`, `eq:gramian`, and the entire
   C2-necessity content are already machine-verified, sorry-free.

## Design decisions

- **D1 (coordinates & wrapper).** Formalize content on `GeneralSystem`
  (error coordinates, `a := x(0) − x̄₀`); add a thin `ℙ_T` wrapper
  (χ-decisions, data `y(k) = CA^k x(0)`) so Lean statements quote the
  paper. Support constraint as `∈ range Σ₀`, with the SVD-free
  equivalence `v ∈ range Σ₀ ⟺ ∀ z, Σ₀z = 0 → z⬝v = 0` standing in for
  `U₂'v = 0`. No `U`-matrices in Lean.
- **D2 (route).** Every part of the paper's analysis assumes C2, so the
  costogo reduction is available throughout: prove C2-only statements on
  the reduced side and transfer; replay directly only where transfer is
  awkward.
- **D3 (it:xTT).** Output-injection now; IOSS-faithful variant in D.
- **D4 (gap).** General `eq:gap` under C2 by transferring
  `fieCost_gap`; the C2-free version is true but out of scope.
- **D5 (Q-function).** `def:modQ` specialized to quadratic μ's;
  `prop:modQgas` proved in KL-product form `β(r,k) = r·α(k)`.
- **D6 (estimator object).** Sprints A–B state theorems about the
  ℙ-optimizer (as in the costogo track); Sprint C upgrades every
  statement to the Kalman filter via `lem:semiPT`, making `prop:tvkf`
  literally the paper's sentence.

## Sprint A (next): `prop:infhor` and its foundations

*(~800–1500 lines; all C2-scoped transfer work)*

1. **A1 — `ℙ_T` wrapper layer** *(small)*: χ-cost with nominal data;
   `V_T(χ,ω) = gCost a e₀ ω T` under the affine bijection; range ⟺
   kernel-annihilator lemma; optimizer/trajectory transport.
2. **A2 — general gap formula under C2** *(small–medium)*:
   `red_gCost_gap` by transfer from `fieCost_gap` (the deviation of two
   feasible pairs is range-feasible, so penalty transfer applies);
   norm-equivalence corollary via `eq:rangebound`/`eq:quadbound`.
3. **A3 — `lem:exist`** *(small)*: joint uniqueness of `(e₀, ω̂)` from
   zero gap (`Q⁻¹ ≻ 0` + pinv-image pinning). C2-free, as in the paper.
4. **A4 — `lem:unibounded`, C2 only** *(medium)*: reduced-side candidate
   `e(0) = (a₁, 0)` (feasible since `Σ₂ ≻ 0` under C2) + `K̃`-rollout
   with the Lyapunov-equation cost bound (no C1; fixes finding 1);
   transfer; value monotonicity (truncation) and convergence; `eq:ellT`.
5. **A5 — `it:zlim`** *(medium)*: C2-only Cauchy convergence of
   `optInit` *and each `ŵ(j|T)`* via the gap applied to truncations
   (`eq:gapopt`); limit objects by choice.
6. **A6 — `it:Vlim`** *(medium, main bookkeeping risk)*: `tsum` cost of
   the limit pair; `≤` by pointwise limits + monotone convergence, `≥`
   by prefix feasibility. C2 only.
7. **A7 — `it:xTT`** *(small–medium)*: deviation energies from A2/A5,
   output-injection propagation (existing), plain `Tendsto` — C1∧C2.
8. **A8 — assembly**: three-part `prop_infhor` on the A1 wrapper with
   the paper's exact hypothesis split; axiom audit; notes; PR.

## Sprint B: Q-function layer → `prop:tvkf` for the optimizer

*(~1000–1600 lines)*

1. **B1 — quadratic IOSS-Lyapunov fact** (`eq:iioss-bounds`/`dec`):
   from `detect_inj`, solve `(A−LC)'P(A−LC) − P = −I` by the geometric
   series; dissipation by Young's inequality; rescaling lemma.
2. **B2 — partial costs and `Z(j|k)`**: `V⁰(j|k)`, `Z ≥ 0` (partial ≤
   total ≤ `V∞⁰`), the exact decrease identity.
3. **B3 — `prop:tvkfQuns`**: `Q(j|k) := Z(j|k) + V_io(x̂(j|k) − x(j))`;
   the three properties with quadratic μ's (`QunsInitUB` via
   `lem:unibounded` + `eq:rangebound` + the rescaling
   `2λ̄(P)λ̄(Σ₀) ≤ 1`; decrease via `c₁ ≤ ½λ̲(Q⁻¹)`, `c₂ ≤ ½λ̲(R⁻¹)`).
4. **B4 — `prop:modQgas`**: `Q(j|∞)` limits from it:zlim + continuity;
   monotone convergence, `μ₃⁻¹` squeeze, it:xTT transfer ⟹ attraction;
   optimizer-linearity lemma (`e*(·|·)` linear in `a`); pointwise →
   uniform via columns; `α(k) := sup`-tail; KL-product GAS.
5. **B5 — necessity assembly**: KL-GAS ⟹ σ-GAS (linearity) ⟹ existing
   `C1_of_isGAS`, `C2_of_isGAS`. Optionally re-derive the C2 growth
   step via B1's IOSS (`eq:iosssum`/`eq:rhs-bound`/`eq:lhs-bound`) for
   faithfulness.
6. **B6 — `prop:tvkf`, optimizer form**: AS ⟺ C1∧C2 for the
   full-information estimate `x̂(k|k)`; audit; notes.

## Sprint C: the Kalman-filter bridge (`lem:semiPT`, costogo M3)

*(~1500–3000 lines — the big rock; follow `gas-lyap-draft.tex`)*

1. **C1 — DRE layer**: `Σ(k)` recursion, PSD preservation
   (Schur-complement bound), gains `L(k)`, transition `M(k)`,
   `ê(k) = M(k)ê(0)`.
2. **C2 — arrival cost** (`lem:arrival`): forward induction — the
   horizon-`T` arrival quadratic is
   `𝒥_T(ξ) = V_T⁰ + ½‖ξ − e*(T|T)‖²_{Σ_T†}` with feasibility exactly on
   `e*(T|T) + im Σ_T`, and `Σ_T` follows the DRE. Uses
   `ConstrainedQuadratic`/`symmPinv` machinery; the one-step propagate +
   measurement-update completion of squares with singular priors is the
   hard induction.
3. **C3 — `lem:semiPT`**: `x̂(T|T) = x̂ᵏᶠ(T)` for all `T` and data;
   covariance identification `Σ_T = Σ(T)`.
4. **C4 — headline transfer**: `prop:tvkf` restated about the
   time-varying Kalman filter (paper's literal sentence); the KL proof's
   `M(k)`-version verified as written; audit.

## Sprint D: polish and faithfulness *(~300–800 lines, optional items)*

Example 1 instance; Example 2 divergence proof (`ê(k) ~ (2/3)√k`);
IOSS-faithful `it:xTT`; general-K∞ `def:modQ`; paper remark drafts
(what-is-verified statement for the paper); final mapping table; PR.

## Done criteria (program level)

1. `lake build` green; zero new sorries; every theorem/lemma/fact of
   paper.tex (per the inventory) has a Lean counterpart or a recorded
   deliberate exclusion (figures, expository remarks).
2. `#print axioms` on `prop_tvkf` (KF form), `prop_infhor`,
   `prop_modQgas`, `prop_tvkfQuns`, `lem_semiPT`:
   `[propext, Classical.choice, Quot.sound]` only.
3. Hypothesis bookkeeping matches the paper's intended splits (C2-only
   claims verified without C1 — finding 1 fixed, not reproduced).
4. Mapping table (paper label ↔ Lean name) complete; scope notes
   updated; PRs per sprint.

## Working agreements

As before: work independently, commit per landed cluster; prefer
paper.tex where costogo.tex disagrees; every divergence and every
supplied-but-unstated step gets recorded here so the paper can be
patched to match what was verified.

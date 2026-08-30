# Program: Lean-verify the *entire* `../rawlings_quah_mueller_2026a/paper.tex`

**Verdict: yes — the whole paper is verifiable.** Every theorem-level
claim is either already machine-verified (from the costogo track),
directly formalizable on existing machinery, or has a written proof to
formalize against (`lem:semiPT` via the arrival-cost machinery of
`../2025h_est_claude/gas-lyap-draft.tex`, `lem:arrival`). The in-flux
wording of `prop:infhor` does not block anything: its statement is
stable, and both candidate proof routes for `it:xTT` are verifiable.
Estimated total: ~3–6k new lines, 4–6 sessions, organized as two
phases below. **Phase 1 is complete; Phase 2 is next.** Examples are
excluded by decision (see inventory).

**Program goal (sharpened after Phase 1, agreed with Titus):** verify
the paper *and its proof routes* — each 2026a theorem should be proven
in the manner of paper.tex, not merely certified true via
costogo-track machinery. Phase 1 established every statement; the
route-faithfulness gaps it left (recorded in the audit below) are
folded into Phase 2 as Stage 2a.

## Claim-by-claim inventory

| Paper item | Status / plan |
|---|---|
| `eq:dre`, `L(k)`, `M(k)`, `ê(k) = M(k)ê(0)`; `Σ(k) ⪰ 0` well-posedness | Phase 2 definitions; PSD preservation of the measurement update via the Schur-complement bound (machinery exists) |
| `eq:contrb` (orthogonal canonical form, "WLOG") | already surpassed: the staircase reduction (costogo M4) *derives* the form; statements stay invariant, no WLOG needed |
| **`prop:tvkf`** (headline: TVKF AS ⟺ C1 ∧ C2) | Phase 1 proves it for the ℙ-optimizer; Phase 2 transfers to the Kalman filter via `lem:semiPT` |
| `lem:semiPT` (KF ⟷ `ℙ_T`) | **stated without proof in paper.tex**; Phase 2 formalizes it following `gas-lyap-draft.tex` `lem:arrival` (arrival quadratic `𝒥_T(ξ) = V_T⁰ + ½‖ξ−e*(T|T)‖²_{Σ_T†}`, support `im Σ_T`, DRE propagation) — this is the deferred costogo milestone M3, now load-bearing |
| `lem:exist` | mostly exists (`exists_isStationary` + attainment); joint `(e₀, ω̂)` uniqueness from the gap formula — Phase 1 |
| `lem:unibounded` (+ `eq:ellT`) | Phase 1, C2-only, with the `eq:cc` fix (finding 1) |
| **`prop:infhor`** (it:zlim, it:xTT, it:Vlim) | Phase 1 (detailed tasks below) |
| `def:modQ`, `prop:modQgas` (classical + KL proofs) | Phase 1; quadratic-μ specialization (decision D5); KL bound built directly, linearity-of-optimizer lemma replaces nothing-but-citations |
| `prop:tvkfQuns` (modified Q-function exists under C1∧C2) | Phase 1; needs the quadratic IOSS-Lyapunov fact + `lem:unibounded` + `eq:rangebound` (exists) + `V_io` rescaling |
| C2-necessity (inside `prop:tvkf` proof) | **content already verified** (`GeneralSystem.C2_of_isGAS`, incl. `eq:pin` pinning and the `eq:Venergy` cap); Phase 1 optionally re-derives the growth step via IOSS for line-faithfulness (cheap once IOSS exists) |
| C1-necessity (cited to Allan–Rawlings–Teel) | **already verified directly** (`GeneralSystem.C1_of_isGAS`); Phase 1 adds the KL-form → σ-form bridge via optimizer linearity |
| sec:proofs fact `eq:quadmin` | trivial / exists |
| `eq:quadbound`, `eq:rangebound` | exist (`QuadForm.lean`) |
| `eq:cc` (LQR upper bound) | Phase 1, restated for an arbitrary stabilizing feedback (finding 1) |
| `eq:iioss-bounds`/`eq:iioss-dec` (quadratic IOSS from detectability) | Phase 1, from `detect_inj` + discrete Lyapunov series (~200–400 lines) |
| `eq:polysample` | **already verified** (`SpectralGrowth.lean`) |
| `eq:gramian` (quantitative) | **already verified** (`SpectralGrowth.lean`; Jordan-free proof of the same statement) |
| Examples 1–2 | **excluded by decision** (illustrative; recorded as deliberate exclusions — Example 2's divergence claim is analytically provable if ever wanted) |
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
   `lem:arrival` is a complete proof; formalizing it (Phase 2) will
   certify the statement — consider citing or absorbing that argument
   (or RMD20) so the paper's one unproven lemma has a source.
3. **`it:xTT` wording flux is harmless.** Both variants verify: the
   commented-out output-injection route maps 1:1 onto existing
   machinery; the active IOSS route needs the IOSS fact we must build
   for `prop:tvkfQuns` anyway. Plan: Phase 1 verifies the statement via
   output-injection (and builds IOSS regardless, for `prop:tvkfQuns`);
   an IOSS-faithful re-proof is a cheap Phase 2 option.
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
   bridge; we prove the linearity lemma in Phase 1 and verify the
   paper's `M(k)` version in Phase 2.
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
- **D2 (route) — superseded by the program goal.** Phase 1 used the
  costogo reduction for speed; Stage 2a replaces every 2026a-facing
  proof that leans on it with the paper's own route (the reduction
  remains in the repo as costogo's verification and as scaffolding).
- **D3 (it:xTT) — superseded.** Phase 1 verified via output-injection;
  Stage 2a re-proves via the active IOSS summation (F3).
- **D4 (gap) — superseded.** Phase 1 transferred `fieCost_gap` under
  C2; Stage 2a proves `eq:gap` directly at the general level,
  C2-free, by the paper's flat completing-of-squares (F1).
- **D5 (Q-function).** `def:modQ` specialized to quadratic μ's;
  `prop:modQgas` proved in KL-product form `β(r,k) = r·α(k)`.
- **D6 (estimator object).** Phase 1 states theorems about the
  ℙ-optimizer (as in the costogo track); Phase 2 upgrades every
  statement to the Kalman filter via `lem:semiPT`, making `prop:tvkf`
  literally the paper's sentence.
- **D7 (examples).** Examples 1–2 are excluded from the verification
  scope (illustrative content).

## Phase 1 (COMPLETE 2026-08-30): the optimization-side paper — `prop:infhor`, the Q-function layer, and `prop:tvkf` for the optimizer

*(~1800–3100 lines, 2–4 sessions; all C2-scoped work rides the existing
reduction)*

### Stage 1a — `prop:infhor` foundations

1. **P1.1 — `ℙ_T` wrapper layer** *(small)*: χ-cost with nominal data;
   `V_T(χ,ω) = gCost a e₀ ω T` under the affine bijection; range ⟺
   kernel-annihilator lemma; optimizer/trajectory transport.
2. **P1.2 — general gap formula under C2** *(small–medium)*:
   `red_gCost_gap` by transfer from `fieCost_gap` (the deviation of two
   feasible pairs is range-feasible, so penalty transfer applies);
   norm-equivalence corollary via `eq:rangebound`/`eq:quadbound`.
3. **P1.3 — `lem:exist`** *(small)*: joint uniqueness of `(e₀, ω̂)` from
   zero gap (`Q⁻¹ ≻ 0` + pinv-image pinning). C2-free, as in the paper.
4. **P1.4 — `lem:unibounded`, C2 only** *(medium)*: reduced-side
   candidate `e(0) = (a₁, 0)` (feasible since `Σ₂ ≻ 0` under C2) +
   `K̃`-rollout with the Lyapunov-equation cost bound (no C1; fixes
   finding 1); transfer; value monotonicity (truncation) and
   convergence; `eq:ellT`.
5. **P1.5 — `it:zlim`** *(medium)*: C2-only Cauchy convergence of
   `optInit` *and each `ŵ(j|T)`* via the gap applied to truncations
   (`eq:gapopt`); limit objects by choice.
6. **P1.6 — `it:Vlim`** *(medium, main bookkeeping risk of the stage)*:
   `tsum` cost of the limit pair; `≤` by pointwise limits + monotone
   convergence, `≥` by prefix feasibility. C2 only.
7. **P1.7 — `it:xTT`** *(small–medium)*: deviation energies from
   P1.2/P1.5, output-injection propagation (existing), plain `Tendsto` —
   C1∧C2. Assemble the three-part `prop_infhor` on the P1.1 wrapper with
   the paper's exact hypothesis split.

### Stage 1b — Q-function layer → `prop:tvkf` (optimizer form)

8. **P1.8 — quadratic IOSS-Lyapunov fact** (`eq:iioss-bounds`/`dec`):
   from `detect_inj`, solve `(A−LC)'P(A−LC) − P = −I` by the geometric
   series; dissipation by Young's inequality; rescaling lemma.
9. **P1.9 — partial costs and `Z(j|k)`**: `V⁰(j|k)`, `Z ≥ 0` (partial ≤
   total ≤ `V∞⁰`), the exact decrease identity.
10. **P1.10 — `prop:tvkfQuns`**: `Q(j|k) := Z(j|k) + V_io(x̂(j|k) −
    x(j))`; the three properties with quadratic μ's (`QunsInitUB` via
    `lem:unibounded` + `eq:rangebound` + the rescaling
    `2λ̄(P)λ̄(Σ₀) ≤ 1`; decrease via `c₁ ≤ ½λ̲(Q⁻¹)`,
    `c₂ ≤ ½λ̲(R⁻¹)`).
11. **P1.11 — `prop:modQgas`**: `Q(j|∞)` limits from it:zlim +
    continuity; monotone convergence, `μ₃⁻¹` squeeze, it:xTT transfer ⟹
    attraction; optimizer-linearity lemma (`e*(·|·)` linear in `a`);
    pointwise → uniform via columns; `α(k) := sup`-tail; KL-product GAS.
12. **P1.12 — necessity assembly + `prop:tvkf` (optimizer form)**:
    KL-GAS ⟹ σ-GAS (linearity) ⟹ existing `C1_of_isGAS`,
    `C2_of_isGAS`; optionally re-derive the C2 growth step via P1.8's
    IOSS (`eq:iosssum`/`eq:rhs-bound`/`eq:lhs-bound`) for faithfulness.
    Conclude AS ⟺ C1∧C2 for the full-information estimate `x̂(k|k)`;
    axiom audit; notes; PR.

## Route-faithfulness audit (post-Phase 1)

Where Phase 1 certified a statement by a route other than the paper's:

| Item | Phase 1 route | Paper's route | Fix |
|---|---|---|---|
| `eq:gap` | transfer of `fieCost_gap` through the reduction (C2-scoped) | direct completing-of-squares in `z = (α₁, ω)`, no C2 | F1 |
| `it:zlim` | reduced-side Cauchy argument + transfer | same argument, run directly on `ℙ_T`/general problem | F1 |
| `lem:unibounded` feasibility | `Σ₂ ≻ 0` in staircase coordinates | `U₂/E₂` independence ⟺ invariantly `range Σ₀ + V₁ = ℝⁿ` under C2 | F2 |
| `it:xTT` | output-injection convolution (commented-out variant) | IOSS summation (active wording) | F3 |
| C2-necessity growth step | window coercivity (costogo route) | `eq:iosssum` IOSS chain | F4 |
| KL uniformization | optimizer linearity (`N(k)` columns) | `M(k)` from the DRE | F5 (Stage 2b — needs the DRE) |
| `value`/`optCtrl` definitions | Riccati-backed construction, variational facts as theorems | optimization problem primary | F6 (certify, don't refactor) |

Faithful already (the paper's manner, verbatim in structure):
`prop:tvkfQuns`, `prop:modQgas`, `it:Vlim`, the `lem:unibounded`
candidate/rollout idea, `lem:exist`'s uniqueness-by-strict-convexity
content, and the IOSS fact itself (paper cites Cai–Teel; we supplied
the linear-case proof it reduces to).

## Phase 2: route faithfulness + the Kalman-filter bridge

*(~2100–4000 lines, 3 sessions — Stage 2a is the folded-in
faithfulness pass; Stage 2b's `lem:semiPT` is the big rock; follow
`gas-lyap-draft.tex`)*

### Stage 2a — prove the optimization side in the paper's manner (ex-"Phase 1.5", ~600–1000 lines)

1. **F1 — direct `eq:gap`, C2-free** *(medium)*: flat quadratic
   expansion of `gCost` about the optimizer in the decisions
   (`eq:quadmin` style, single-block prior, no reduction); then re-run
   `it:zlim`'s truncation-Cauchy argument directly on the general
   problem. Retire the C2-scoping of the gap and the reduction
   dependence of `prop_infhor_zlim`.
2. **F2 — `lem:unibounded` feasibility the paper's way** *(small–medium)*:
   C2 ⟹ `range Σ₀ + V₁ = ℝⁿ` by the annihilator computation
   (`(range Σ₀ + V₁)ᗮ = ker Σ₀ ∩ 𝒳_{u,uc} = 0`) — the invariant form of
   the `U₁₂`-full-column-rank argument, in original coordinates;
   rebuild the candidate feasibility on it.
3. **F3 — `it:xTT` via IOSS** *(small)*: replace the output-injection
   step with the `eq:iioss-dec` summation
   (`a₁‖δx̂(T)‖² ≤ a₂‖δx̂(0)‖² + c₁Σ‖δŵ‖² + c₂Σ‖δv̂‖²`), matching the
   active wording.
4. **F4 — C2-necessity via `eq:iosssum`** *(medium)*: re-derive the
   linear-growth step with the IOSS chain
   (`eq:iosssum`/`eq:rhs-bound`/`eq:lhs-bound`) in place of window
   coercivity, feeding the existing `eq:pin` pinning, quantitative
   Gramian, `eq:Venergy` cap, and Cesàro ending; conclude a
   paper-faithful `C2_of_isGAS`.
5. **F6 — variational front door** *(small)*: `value_isLeast` — certify
   `V_T⁰ = min` of the feasible costs so the Riccati appears only as a
   construction witness inside definitions, never as an analysis tool
   in any 2026a-facing statement.

### Stage 2b — the Kalman-filter bridge and the literal headline

6. **P2.1 — DRE layer**: `Σ(k)` recursion, PSD preservation
   (Schur-complement bound), gains `L(k)`, transition `M(k)`,
   `ê(k) = M(k)ê(0)`.
7. **P2.2 — arrival cost** (`lem:arrival`): forward induction — the
   horizon-`T` arrival quadratic is
   `𝒥_T(ξ) = V_T⁰ + ½‖ξ − e*(T|T)‖²_{Σ_T†}` with feasibility exactly on
   `e*(T|T) + im Σ_T`, and `Σ_T` follows the DRE. Uses
   `ConstrainedQuadratic`/`symmPinv` machinery; the one-step propagate +
   measurement-update completion of squares with singular priors is the
   hard induction.
8. **P2.3 — `lem:semiPT`**: `x̂(T|T) = x̂ᵏᶠ(T)` for all `T` and data;
   covariance identification `Σ_T = Σ(T)`.
9. **P2.4 — headline transfer and wrap-up**: `prop:tvkf` restated about
   the time-varying Kalman filter (the paper's literal sentence); the KL
   proof's `M(k)`-version verified as written (F5); paper remark drafts
   (what-is-verified statement), final mapping table; axiom audit; PR.

## Done criteria (program level)

1. `lake build` green; zero new sorries; every theorem/lemma/fact of
   paper.tex (per the inventory) has a Lean counterpart or a recorded
   deliberate exclusion (figures, expository remarks).
2. `#print axioms` on `prop_tvkf` (KF form), `prop_infhor`,
   `prop_modQgas`, `prop_tvkfQuns`, `lem_semiPT`:
   `[propext, Classical.choice, Quot.sound]` only.
3. Hypothesis bookkeeping matches the paper's intended splits (C2-only
   claims verified without C1 — finding 1 fixed, not reproduced).
4. **Route faithfulness**: every 2026a-facing theorem's proof follows
   the paper's own argument (audit table cleared — F1–F6 landed); the
   costogo reduction appears in no 2026a proof where the paper does
   not use a change of coordinates.
5. Mapping table (paper label ↔ Lean name) complete; scope notes
   updated; one PR per phase.

## Working agreements

As before: work independently, commit per landed cluster; prefer
paper.tex where costogo.tex disagrees; every divergence and every
supplied-but-unstated step gets recorded here so the paper can be
patched to match what was verified.

## Phase 1 outcome (2026-08-30) — COMPLETE

All Stage 1a and 1b targets landed, sorry-free; `lake build` green;
`#print axioms` on every headline item:
`[propext, Classical.choice, Quot.sound]` only.

- **P1.1** `Estimation/ChiProblem.lean`: the `ℙ_T` problem in χ-coordinates
  with nominal data; `U₂'`-constraint as the SVD-free kernel-annihilator
  criterion (`mem_range_iff_forall_ker`, new in `SymmPinv.lean` along
  with `self_mul_symmPinv_comm`); affine bijection to the
  error-coordinate `GeneralSystem` problem; `lem:exist` in `ℙ_T` form.
- **P1.2–P1.3** `Estimation/InfhorGeneral.lean`: general `eq:gap` under
  C2 (transfer from `fieCost_gap`), energy corollary, joint optimizer
  uniqueness (C2-free, via the new `LQSystem.optCtrl_unique`).
- **P1.4** C2-only `lem:unibounded`: `LQSystem.exists_cost_feedback_bound`
  (geometric feedback rollout, no Riccati/detectability) +
  `FIESystem.exists_value_bound_C2` + general transfer; value
  monotonicity/convergence; `eq:ellT`. The Infhor limit layer was
  refactored to C2-only hypotheses (finding 1 fixed, not reproduced).
- **P1.5–P1.7** `it:zlim` (C2), `it:Vlim` (C2, `tsum` infinite cost),
  `it:xTT` (C1∧C2, via output injection); assembled as
  `prop_infhor_zlim`/`prop_infhor_Vlim`/`prop_infhor_xTT` in the
  paper's variables in `ChiProblem.lean`.
- **P1.8** `LinearSystems/IOSS.lean`: the quadratic IOSS-Lyapunov fact
  (`eq:iioss-bounds`/`eq:iioss-dec`) via the Lyapunov matrix series for
  the output-injection closed loop.
- **P1.9–P1.12** `Estimation/QFunction.lean`: partial costs and
  `Z(j|k)`; **`prop:tvkfQuns`** (`exists_modQ`, quadratic μ's);
  **`prop:modQgas`** (`isGAS_of_modQ`); optimizer linearity +
  pointwise-to-uniform upgrade; **`prop:tvkf` (optimizer form)** —
  `IsGAS ↔ C1 ∧ C2` by the paper's Q-function route
  (`prop_tvkf_optimizer`), and in the paper's `def:GAS` KL formulation
  (`prop_tvkf_optimizer_kl` via `isGAS_iff_kl`).

### New finding for the authors (8)

**`def:modQ`/`prop:modQgas` carry a hidden hypothesis.** The
`prop:modQgas` proof takes `Q(j|∞) := lim_k Q(j|k)` to exist "by
`prop:infhor` and continuity" — but that argument is specific to the
*constructed* Q of `prop:tvkfQuns`; an arbitrary function satisfying
only `eq:QunsInitUB`/`eq:QunsLBUB`/`eq:QunsDecrease` need not converge
along horizons. Suggested patch: either add the existence of the
horizon limits to `def:modQ`, or state `prop:modQgas` for Q-functions
with convergent horizon limits (our `isGAS_of_modQ` does the latter,
and `exists_modQ` supplies the convergence for the constructed Q).

### Mapping table (Phase 1)

| Paper | Lean |
|---|---|
| `ℙ_T` (`lem:semiPT` form) | `GeneralSystem.chiCost`/`ChiFeasible` (+ `chiFeasible_iff_ker` for `U₂'`) |
| `lem:exist` | `chiOpt_unique` / `optimal_pair_unique` (+ existing existence) |
| `lem:unibounded` | `exists_value_bound_C2` (FIE + general), `valueLim_le_bound`; `eq:ellT` = `tendsto_lastStage` |
| `eq:gap` | `gCost_gap`; energy corollary `exists_gap_energy_bound` |
| `prop:infhor` it:zlim | `prop_infhor_zlim` (C2 alone) |
| `prop:infhor` it:xTT | `prop_infhor_xTT` (C1 ∧ C2) |
| `prop:infhor` it:Vlim | `prop_infhor_Vlim` (C2 alone) |
| `eq:iioss-bounds`/`eq:iioss-dec` | `LinearSystems.exists_ioss_lyapunov` |
| `prop:tvkfQuns` | `GeneralSystem.exists_modQ` |
| `prop:modQgas` | `GeneralSystem.isGAS_of_modQ` (+ `isGAS_of_pointwise`) |
| `def:GAS` (KL) | `GeneralSystem.IsGASkl`; bridge `isGAS_iff_kl` |
| `prop:tvkf` (optimizer estimator) | `prop_tvkf_optimizer`, `prop_tvkf_optimizer_kl` |
| C1/C2 necessity | existing `C1_of_isGAS`, `C2_of_isGAS` |

Deferred to Phase 2 — Stage 2a (route faithfulness, F1–F4/F6: direct
`eq:gap` + direct `it:zlim`, annihilator-form `lem:unibounded`
feasibility, IOSS-route `it:xTT` and C2-necessity, `value_isLeast`)
and Stage 2b (`lem:semiPT` KF bridge, DRE layer, `prop:tvkf` as the
literal Kalman-filter sentence, `M(k)`-version of the KL
uniformization, F5). Deliberately excluded: examples (D7).

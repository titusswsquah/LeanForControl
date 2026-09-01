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

---

## Phase D — CLOSED (2026-09-01)

All four items landed; the exit criterion is met and exceeded:
`main_strong_attraction` (Dare/Main.lean) states `thm:main` Part 1
with **existence internal** — hypotheses are C1 + power-bounded
marginal only.

- **D0**: GATE-2 numerics (scratch/check_spectrum_split.py,
  check_Ac_identification.py): split exact, Fs Schur, unit
  eigenvectors m-supported, products bounded, chart assembly matches,
  J ≻ 0; plus the finding-15 refutation.
- **D1** (`Dare/Spectrum.lean`): `strong_Fs_schur` — the one-step
  PBH–Stein kill (no power induction: the rotation cancels in
  re²+im², the marginal drift dies inside the Σ∞-energy by
  extinction); `strong_spec_split`;
  `strong_exists_unit_eigenvalue`. `hFs` discharged in
  sufficiency/thm:main (supremal keeps it as a general-lemma
  hypothesis). **Findings 14** (the "inside representative"
  parenthetical was a hand-wave; verified route in deck) **and 15**
  (`A_c` was NOT the e₁-diagonal block of F∞ — numerically refuted;
  redefined as the reduced stabilizing loop; F∞ is (e₁⊕a|m)
  triangular by *extinction*, not by the frame).
- **D2** (`Dare/Reduced.lean`): `monotone_psd_tendsto` (polarization
  limit), `exists_stabilizing_solution` (zero-seed monotone +
  eq:bounded; fixed point via dareStep_diff Lipschitz-ness — no
  inverse continuity needed), **`fixed_point_schur`** (every PSD
  fixed point has a Schur loop from stabilizability alone — the
  key alignment lemma), `stabilizing_fixed_unique`.
- **D3** (`Dare/ReducedFacts.lean`): gain/loop continuity
  (resolvent + R-floor), `redP_tendsto_infP` (infP Σ∞ is a fixed
  point by strong_chart_fixed, Schur-looped, so uniqueness
  identifies), `redProdF_geometric` (fact:uniexp consumed — feeds
  E2), `reducedImport_holds`. `himp` dropped from
  sufficiency/thm:main.
- **D4** (`Dare/Sylvester.lean`, `Dare/Existence.lean`,
  `Dare/Main.lean`): Sylvester fixed points with Schur factors;
  `gramian_fixed_posDef` (kernel eigenvector lifts through the
  loading identity to an undetectable antistable mode);
  `assembled_lam_fixed`/`assembled_Saa_fixed` (chart_dareStep read
  backwards, uhat_inv_eq); `fixed_specLe` (strict one-step
  over-balance at |μ|>1 puts the eigenvector in ker Σ AND unexcited;
  corner-PD kills a, marginal can't exceed the circle);
  **`exists_strong_solution` under C1 alone**;
  `strong_solution_unique` (supremal seeded at Σ+Σ');
  `existsUnique_strong_solution`; `strong_isSchurStable_iff_C3w`
  (eq:Finf-c3w verified); the two assembled `main_*` heads.

Remaining imports anywhere in the main line: the power-bounded
marginal (semisimple qualification — F4 target), and among a00's
facts only maximality (unconsumed) and the reciprocal-pairing fine
form (Arc-1). Deck synced (findings 14–15 + three sync commits);
sorry-free; all heads axiom-clean; build green (2989 jobs).

Next: Phase E (rates + Arc 1), starting E1 (the rate-carrying
convolution) — note `redProdF_geometric` already gives the geometric
product bound E2 needs.

## Phase E — CLOSED (2026-09-01)

Every rate/spectrum claim in 04–08 and every displayed equation in
a03/a04 now has a Lean head; the exit criterion holds. All heads
sorry-free, axioms = [propext, Classical.choice, Quot.sound], build
green (2994 jobs).

- **E1 (rate engine, RateEngine.lean).** `geom_conv_le` (widened
  geometric convolution: two rates below ρ' convolve to Cρ'^T),
  `rate_of_unroll_bound` (an unrolled affine bound with geometric
  kernel forces a geometric rate — midpoint-rate extraction), and
  the Lipschitz stack `innovInv/kGain/errMap_diff_norm_le`.
- **E2 (lower-anchor rates, LowRate.lean).** `GeoDecay` + closure
  combinators; per-datum rates `redP_geometric`,
  `lowLam1a_geometric`, `ceff_geometric`, `lowXi_geometric`,
  `lowJ_geometric`, `lowSaa_geometric`; assembled
  `lowsqueeze_geometric` — the slaved anchor converges
  exponentially, floor-free.
- **E3 (thm:main Part 2 forward, MainRate.lean).**
  `supremal_geometric` (Loewner-monotone iterates + psd-norm
  squeeze), `dare_sandwich_norm` (polarization sandwich),
  `sufficiency_geometric` (C1+C2w+C3w ⇒ ‖Σ_T−Σ∞‖ ≤ Cρ^T from any
  PSD prior), `main_stab_forward` (with existence: C1+C2 alone).
  Both directions of thm:main-2 closed (converse was Phase D's
  `main_marg_not_exponential`).
- **E4a (thm:formula + cor:phi, Formula.lean).** `formula` — the
  deck's joint induction verified verbatim (N_T det-unit AND the
  closed form), inversion-free, exact at det A = 0; pencil
  identities `pencil_block_M/L`, `strong_id1/2`, Ω-identities;
  `fwdGram_posSemidef/eq_sylvIter/tendsto_stein`; `formula_rate`;
  cor:phi = `errProd_closed`/`errProd_eq` via `slide_swap`.
  `gapRic`/`oneSubKC_add` hypotheses generalized to PSD sums.
- **E4b (lem:sysinterp, Subspace.lean).** `structure DeflatingPair`
  is the ONE Lancaster–Rodman import (Xm/Ym/Em Schur, pencil rows,
  frame surjectivity); verified on top: `intertwine/sylv/link`
  (Sylvester uniqueness replaces every telescoping series),
  `perstep`, `lagrangian` (Stein K=E'KE ⇒ K=0), `energy_fix`,
  `kernel_sub` (finding 16: output injection replaces the L⁻/L^≥
  split), `transversal`, `info_fix`, `sysinterp_nonsingular` (C2 ⇒
  M∞ unit) and `sysinterp_singular` (¬C2w ⇒ kernel vector — the
  necessity half at the kernel level, un-flagging cor:necessity).
- **E5 (slaved seed, general form, SlavedSeed.lean).**
  `exists_loading_of_posSemidef` (kernel-inclusion + rank–nullity:
  ∃Z, AZ = B for PSD blocks — no pseudoinverse),
  `exists_loading`, and the general seed `slavedSeedOf` with all
  three lemma parts C2w-free (`slavedSeedOf_le_Sig0/corner/slaved`)
  plus the C2w specialization `slavedSeedOf_lam0`.

Findings this phase: 16 (a04 orbit collapse simplification,
deck repaired). Deck synced: 04/05/06/08 (E2/E3 commits),
a03 + 05 (E4a/E5), a04 (E4b/finding 16); odyssey.md re-stitched
each time.

Next: Phase F — F1 (payoff frame transfer), F2 (ISS display),
F3 (cor:every-prior), then sprint close.

## Phase F — CLOSED (2026-09-01) — SPRINT COMPLETE

All heads sorry-free; the 28-head grand sweep shows axioms
= [propext, Classical.choice, Quot.sound] everywhere; build green
(2999 jobs).

- **F1 (Payoff.lean).** `toFIE` (a⊕m lumped via `finSumFinEquiv`,
  covariances → penalties, `hAnti` from the eigenvector block-split);
  reindex transports (spectrum / detectability / PosDef under a
  symmetric equiv); `toFIE_C1/C2/C3w_iff`; `payoff_dichotomy`
  (`eq:payoff-dich` stated in the deck's three-block frame);
  `payoff_errMap_tendsto` (Part 1's map convergence).
- **F2 (Robust.lean + UniformExpStability generalized).**
  `transitionProd` machinery made index-generic (`Fintype.card`
  replaces the `Fin n` dimension factor); `fullProd_geometric`
  (`fact:uniexp` on the full three-block run under C1+C2+C3w);
  `errTraj`/`errTraj_unroll` (`eq:diff-unroll`); `payoff_iss` — the
  deck's ISS display verified.
- **F3 (EveryPrior.lean).** `withPrior`; `everyPrior_C2w_iff` (↔ na=0)
  and `everyPrior_attraction_iff` (every-prior Σ_T → Σ∞ ↔ 𝒳ₐ,ᵤ𝒸 = 0);
  `everyPrior_C2_iff` (↔ na=nm=0); `fullStab_iff` (the Hautus bridge);
  `everyPrior_gas_iff`/`everyPrior_ges_iff` (each ↔ stabilizability)
  and `everyPrior_gas_iff_ges` (every-prior GAS = GES).
- **F4 (Semisimple.lean + Instance.lean).** `MargSemisimple` ⇒ both
  power bounds (`marg_powers_bounded`; diagonal similarity, unit
  moduli from `hMarg` by eigenvector extraction, inverse through the
  same frame) — the deck's semisimple wording is now a theorem, with
  assembled forms `main_strong_attraction_semisimple` /
  `main_marg_not_exponential_semisimple`; `marg_gramian_growth`
  instantiates the verified `gramian_growth` (2026a fact 7, per the
  user's memo) as the identified defective-case tool. `exampleDare`
  (three nonempty blocks, C1 by scalar PBH, C2, semisimple marginal)
  realizes the dichotomy: attracted, GAS, NOT GES, not exponentially
  attracted — vacuity killed.
- **F5 (closure).** `jGram` (the last displayed equation, eq:Jgram's
  backward-gramian unroll); stale markers retired (a02 "pending", 06
  "imported from arc1", a01 Part-1 wording, a00 observable-injection
  staleness, 09 deps); deck LEAN lines complete (09-payoff's three
  former gaps closed; cor:every-prior line added); PR body updated to
  the completed state.

Remaining declared imports (all explicit): the defective-marginal open
problem (tool identified), DeflatingPair (a04), fact:filter-opt (09's
probabilistic identification), maximality + reciprocal pairing
(unconsumed citations), the three-block staircase into the frame
(deck-level; both neighbors verified). Findings: 16 total. Exit
criterion met: every result in odyssey.md carries a LEAN line naming
its theorem; the only forward reference to unproven mathematics is the
declared open problem.

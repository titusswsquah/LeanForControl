# PR: Lean verification of the odyssey deck (DARE strong/stabilizing attraction dichotomy)

Branch: `feat/costogo-fie-stability` (continues from the costogo/2026a
work). Sprint plan: `notes/leanverify-odyssey-sprint.md`; findings:
`notes/leanverify-odyssey-findings.md`; convention:
`notes/verified-deck-convention.md`.

## What this PR contains

**Lean** (all sorry-free; every head's `#print axioms` is exactly
`[propext, Classical.choice, Quot.sound]`; full `lake build` green):

- `LeanForControl/Estimation/Dare/` — 18 files formalizing the deck's
  three-block DARE frame end to end:
  - Phase A: update/gap machinery, the frame + criteria
    (`criterion_w` = `eq:prior-pos`), `eq:bounded`, kernel invariance,
    `Σ∞|aa ≻ 0` (marginal-inclusive), corner positivity along the run,
    the Stein relation, marginal extinction `eq:marg-extinct`.
  - Phase B: the full squeeze. `marg_block_norm_tendsto` (the repaired
    `lem:marginal`), `necessity` (`thm:necessity`), `supremal_tendsto`
    (`lem:supremal`), the slaved seed + loading, the conditional-chart
    machinery for `lem:condfilter`/`lem:jtransform` (the invariant
    `Σ = e₁Pe₁ᵀ + V·Σₐₐ·Vᵀ`; all Woodbury content from
    `S = S̃ + C_eff Σₐₐ C_effᵀ` alone), `lowsqueeze_tendsto`
    (`lem:lowsqueeze`), `sufficiency_tendsto` (`thm:sufficiency`), and
    `strong_attraction_iff_C2w` (`thm:main` Part 1: attraction ⟺ C2w).
  - Phase C: `marg_not_exponential` + `marg_rows_stay_zero`
    (`Dare/RateFloor.lean`) — the repaired `thm:main` Part 2 converse
    core and the counterexample mechanism (finding 7).

**Deck** (`odyssey-src/`, stitched `odyssey.md` current): per-finding
repairs with one finding per commit, `LEAN:` traceability lines on
every verified result, and the finding-7/11/12/13 corrections to
`thm:main`-2, `thm:payoff`, and `cor:every-prior`.

## Headline mathematical outcomes

1. **`thm:main` Part 1 verified end to end**: under C1 (with the
   deck's declared imports as hypotheses), the run from the prior is
   attracted to the strong solution **iff** C2w.
2. **One hole found and repaired in Phase B** (finding 5,
   `lem:marginal`): the windowed-coercivity route was broken; replaced
   by a covariance-side Y-transport/φ-telescope proof, fully verified.
3. **`thm:main` Part 2 was false as stated** (finding 7, escalated):
   for a fixed prior, exponential convergence does *not* imply C3w —
   a prior with exactly known marginal block runs as a marginal-free
   subsystem (mechanism verified: `marg_rows_stay_zero`). Repaired
   statement quantifies over C2 priors; the repaired converse is
   verified (`marg_not_exponential`) by a new argument needing **no
   polynomial floor**: transported marginal energy along the exact
   `eq:gap-ric` recursion + an ε-scaling contradiction.
4. **`thm:payoff` corrected** (findings 11–13): the error-side GAS
   frontier is **C2**, not C2w (an uninformed marginal error is never
   corrected); the transition-product boundedness inference was
   invalid; `cor:every-prior`'s RGAS characterization was the
   covariance-side one. The corrected error-side dichotomy is exactly
   the repo's previously verified arc1 layer
   (`gas_ges_dichotomy`, `isGAS_iff_C1_and_C2`,
   `exists_gap_floor_of_not_C3w`, `isGASkf_iff_isGAS`), now cited as
   the verified core. The deliberate asymmetry — covariance frontier
   C2w vs. error frontier C2 — is now stated as such.
5. Ten further findings (1–4, 6, 8–10): eliminated imports
   (`fact:filter-opt`), simplified/strengthened statements, and the
   threshold-free upper-anchor seed `Σ₀ + Σ∞`.

## Declared imports (hypotheses, matching the deck's own DAG)

- `IsStrongSolution Σ∞` (existence via `fact:dare-strong`);
- forward power-bounded `Aₘ` (backward too, for the Part-2 converse) —
  the semisimple-marginal qualification (defective case open, as
  flagged in the deck);
- `eq:Finf-spec` restricted to `e₁⊕a` as `IsSchurStable`;
- `ReducedImport`: the reduced-`e₁` `fact:dare-strong` (`P_T → P∞`
  from the zero seed) + the closed-loop product bound.

## Known limitations (honest scope)

- Rates are not formalized: the Lean proves convergence; the deck's
  geometric-rate qualifiers (C3w branch, `lem:jtransform`) and the
  forward direction of the repaired Part 2 remain deck-level.
- No concrete `DareSystem` instance discharges the hypothesis bundles
  in Lean; joint satisfiability rests on the deck's GATE-2 numerics
  and standard theory.
- The ISS/robustness additions in `thm:payoff` and the 2-block ↔
  3-block frame transfer for the arc1 citations are deck-level.
- `lem:slaved-seed` Part 1 is verified under C2w (real inverse); the
  deck's pseudoinverse-general form is not consumed downstream.

## Follow-ups

- Port `odyssey-src/` back upstream to `../2025h_est_claude/10-odyssey`
  (manual, per the working-copy convention).
- Fold `notes/verified-deck-convention.md` into the proof-engineering
  skill (deferred by request).
- Open problems on record: defective-marginal `lem:marginal`;
  formalized rates; a concrete instantiation of the import bundles.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_018YHn2k9L8EFFwFS7cTPqqZ

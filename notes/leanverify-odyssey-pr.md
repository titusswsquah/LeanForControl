# PR: Lean verification of the odyssey deck (DARE strong/stabilizing attraction dichotomy)

Branch: `feat/costogo-fie-stability` (continues from the costogo/2026a
work). Sprint plan: `notes/leanverify-odyssey-sprint.md`; findings:
`notes/leanverify-odyssey-findings.md`; convention:
`notes/verified-deck-convention.md`.

## What this PR contains

**Lean** (all sorry-free; every head's `#print axioms` is exactly
`[propext, Classical.choice, Quot.sound]`; full `lake build` green):

- `LeanForControl/Estimation/Dare/` — 30 files formalizing the deck's
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
  - Phase D (sprint 2): **every declared import discharged.**
    `strong_Fs_schur`/`strong_spec_split`/`strong_exists_unit_eigenvalue`
    (the spectrum of `F∞` from the bundle alone, one-step PBH–Stein);
    the reduced `fact:dare-strong` proved (`exists_stabilizing_solution`,
    `fixed_point_schur`, `redP_tendsto_infP`, `reducedImport_holds`);
    **existence of the strong solution under C1 alone**
    (`exists_strong_solution`, chart assembly with Sylvester fixed
    points) and uniqueness (`existsUnique_strong_solution`);
    `main_strong_attraction` states `thm:main`-1 with existence
    internal — hypotheses C1 + power-bounded marginal only.
  - Phase E: **all rates.** The rate engine (`geom_conv_le`,
    `rate_of_unroll_bound`), the geometric lower anchor
    (`lowsqueeze_geometric`), `thm:main`-2 forward
    (`sufficiency_geometric`, `main_stab_forward` — both directions of
    Part 2 closed); **`thm:formula` verified by the deck's own joint
    induction** (`formula`, inversion-free, exact at `det A = 0`) with
    `cor:phi` (`errProd_closed`); **`lem:sysinterp` both halves**
    (`sysinterp_nonsingular`/`sysinterp_singular`) on a single declared
    structural import (`DeflatingPair`, the Lancaster–Rodman pencil
    geometry); `lem:slaved-seed` in the pseudoinverse-free general form
    (`exists_loading`, `slavedSeedOf_*`).
  - Phase F: **the payoff in-frame.** The 3-block → 2-block frame
    transfer (`toFIE`) with condition correspondences and
    `payoff_dichotomy` (`eq:payoff-dich` in the deck's own frame); the
    **ISS display verified** (`fullProd_geometric`, `errTraj_unroll`,
    `payoff_iss`); **`cor:every-prior` both halves**
    (`everyPrior_attraction_iff`, `fullStab_iff` Hautus bridge,
    `everyPrior_gas_iff_ges` — every-prior GAS = GES); the semisimple
    qualification as a theorem (`marg_powers_bounded`) with the
    defective-case tool wired in (`marg_gramian_growth` = 2026a
    fact 7); the concrete witness `exampleDare` realizing the whole
    dichotomy (GAS, not GES, attracted, not exponentially) — the
    vacuity caveat is dead.

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
6. **Sprint 2 (Phases D–F)**: findings 14–16 — the spectrum hand-wave
   in `lem:structure-marg` repaired and verified (14); the `A_c`
   identification refuted and redefined (15); the a04 orbit-collapse
   simplification (one stabilizing output injection replaces the
   `L⁻/L^≥` split and its partial inverse, 16). Every rate claim,
   `thm:formula`, `lem:sysinterp`, the payoff dichotomy in-frame, the
   ISS display, and `cor:every-prior` are now theorems.

## Remaining declared imports (all explicit, none load-bearing for `thm:main`)

After sprint 2, the only unverified inputs anywhere in the line:

- **the defective-marginal case** — the deck's declared open problem;
  the semisimple qualification is now itself a theorem
  (`marg_powers_bounded`), and the identified tool for the defective
  generalization is the verified `gramian_growth` (2026a fact 7,
  in-frame `marg_gramian_growth`);
- **`DeflatingPair`** (a04 only): the Lancaster–Rodman symplectic
  pencil geometry behind `lem:sysinterp`'s frame — a single named
  structural import; everything on top of it is verified;
- **`fact:filter-opt`** (09 only): the probabilistic FIE = TVKF = MMSE
  identification; the error-map bridge itself is verified
  (`isGASkf_iff_isGAS`);
- **maximality** of the strong solution (classical citation, consumed
  nowhere) and the reciprocal-pairing fine form of `eq:Finf-spec`
  (an Arc-1 citation, not consumed by the dichotomy);
- the three-block staircase INTO the frame (`eq:dare-cov` Part 1) is
  deck-level; the two-block analogue (`GeneralSystem.redSys`) and the
  lumping OUT of the frame (`toFIE`) are verified.

## Follow-ups

- Port `odyssey-src/` back upstream to `../2025h_est_claude/10-odyssey`
  (manual, per the working-copy convention).
- Fold `notes/verified-deck-convention.md` into the proof-engineering
  skill (deferred by request).
- Open problem on record: the defective-marginal case (tool
  identified: the verified linear Gramian floor, 2026a fact 7).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_018YHn2k9L8EFFwFS7cTPqqZ

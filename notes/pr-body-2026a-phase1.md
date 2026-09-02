# PR: 2026a paper Phase 1 — prop:infhor, the Q-function route, and prop:tvkf (optimizer form)

## Summary

Phase 1 of Lean-verifying `rawlings_quah_mueller_2026a/paper.tex` in
full: everything except the Kalman-filter bridge (`lem:semiPT`, Phase
2). All statements are proven in the paper's variables with the paper's
hypothesis split, sorry-free.

- **`prop:infhor`**: `it:zlim` and `it:Vlim` under **C2 alone**,
  `it:xTT` under C1 ∧ C2 — on the `ℙ_T` problem in original
  χ-coordinates with nominal data (`Estimation/ChiProblem.lean`), via
  the error-coordinate general layer (`Estimation/InfhorGeneral.lean`).
- **`lem:exist`** (joint uniqueness, hypothesis-free) and
  **`lem:unibounded`** (uniform value bound + convergence + `eq:ellT`)
  under **C2 alone** — fixing the paper's `eq:cc` detectability leak by
  an arbitrary-stabilizing-feedback rollout bound
  (`LQSystem.exists_cost_feedback_bound`).
- **`eq:iioss-bounds`/`eq:iioss-dec`**: the quadratic IOSS-Lyapunov
  fact from detectability (`LinearSystems/IOSS.lean`, Lyapunov matrix
  series).
- **`prop:tvkfQuns`** (modified Q-function with quadratic bounds) and
  **`prop:modQgas`** (modified Q ⟹ GAS), stated as in the revised
  paper: the horizon limits and the diagonal transfer
  `x̂(T|T) − x̂(T|∞) → 0` are explicit hypotheses (no C1 ∧ C2),
  supplied for the constructed Q by `exists_modQ`.
- **`prop:tvkf`, optimizer form**: GAS ⟺ C1 ∧ C2 by the paper's
  Q-function route, both in σ-form and in the paper's KL `def:GAS`
  formulation.

## Verification

`lake build` green; `#print axioms` on `prop_infhor_*`,
`exists_modQ`, `isGAS_of_modQ`, `prop_tvkf_optimizer(_kl)`,
`exists_ioss_lyapunov`, `exists_value_bound_C2`:
`[propext, Classical.choice, Quot.sound]` only.

Findings for the authors recorded in
`notes/leanverify-2026a-program.md` (eq:cc C1-leak; def:modQ hidden
convergence hypothesis; minor wording nits).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01GL917HdRfpxs8t3bsTdS1N

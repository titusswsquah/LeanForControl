# PR: costogo FIE stability — full formalization of thm:gas-ges-fi, in the paper's general coordinates

## Summary

Complete, sorry-free formalization of the headline theorem of
`costogo.tex` ("State estimation of unstabilizable linear systems,
Part II"): the full-information estimator is **GAS ⟺ C1 ∧ C2** and
**GES ⟺ C1 ∧ C2 ∧ C3w** — first in the reduced block coordinates
(`FIESystem.gas_ges_dichotomy`), and then in the paper's **full
generality** (`GeneralSystem.gas_ges_dichotomy`): arbitrary `(A, G, C)`
with PSD prior `Σ₀` and PD weights, no canonical-form or
block-diagonal-prior hypotheses, conditions stated invariantly
(C2 as `ker Σ₀ ∩ 𝒳_{u,uc} = {0}` with the unstable–uncontrollable
subspace defined as the annihilator of `reachable ⊔ stable`).

## Highlights

- **Reduced-coordinates track (M1)**: outer KKT via range
  parameterization, window coercivity + Gramian growth, the variational
  gap formula, GAS sufficiency/necessity (C2-necessity follows the
  *patched* argument of the 2026a paper, not costogo's flawed
  paragraph), GES via slide-rate/value-rate arguments.
- **Classical core discharged (M2)**: `fact:lqr` (Riccati convergence +
  closed-loop Schur stability) and `fact:detect-inj` proven, not
  assumed.
- **Generality layer (M4)**: real spectral split (conjugation-invariant
  Bezout projections), staircase decomposition with derived
  stabilizability/antistability of the blocks, prior-decoupling
  congruence, full problem transfer (value, optimizers, terminal
  errors, GAS/GES), `lem:Sigma2-pd` both directions, and general-level
  replays of C1/C2 necessity (which cannot route through the reduction,
  since the reduction itself needs C2).
- **Vacuity guards**: concrete instances for both system classes.

## Verification

- `lake build` green; zero sorries in the costogo track (the single
  repo sorry is the pre-existing Lyapunov-track one).
- `#print axioms` on `GeneralSystem.gas_ges_dichotomy`,
  `FIESystem.gas_ges_dichotomy`, `lqr_convergence`, `detect_inj`:
  `[propext, Classical.choice, Quot.sound]` only.

Notes: `notes/costogo-scope.md` (decisions + milestones),
`notes/costogo-sprint-generality.md` (generality sprint + label ↔ name
mapping table).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01GL917HdRfpxs8t3bsTdS1N

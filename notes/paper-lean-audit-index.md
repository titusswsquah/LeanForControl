# `paper.tex` ↔ Lean semantic audit

Pinned Lean snapshot: `f83321c8896778cef6af93709add4f439a4feb6c`

This package is a reading guide for the 70 declarations selected for manual semantic audit. Lean code is copied from the pinned snapshot. “Rendered meaning” explains the declaration without Lean syntax. “Paper counterpart” restates the corresponding `paper.tex` passage in ordinary Markdown, Unicode mathematics, and plain English. It deliberately uses no LaTeX commands. When the paper has no direct counterpart, that fact is stated rather than manufacturing one.

```mermaid
flowchart TD
  Data[GeneralSystem: A, G, C, Σ₀, Q⁻¹, R⁻¹] --> GLQ[glq: error dynamics and stage cost]
  Data --> Chi[χ trajectory, nominal y, residual ν]
  Data --> KFData[Q, R, innovation covariance]

  GLQ --> GenCost[priorPen + Feasible + gCost]
  Chi --> ChiCost[ChiFeasible + chiCost]
  ChiCost --> CoordBridge[χ/error-coordinate bridges]
  CoordBridge --> GenCost

  GenCost --> Optimizer[optInit + value + optTerm]
  Data --> Conditions[C1 + C2]
  Conditions --> Reduction[reduced-coordinate C1/C2/value bridges]
  Reduction --> Bounds[uniform value bound]
  Optimizer --> Bounds
  Bounds --> Infinite[finite-horizon and infinite-horizon convergence]

  KFData --> DRE[dreStep + dre]
  DRE --> Gain[kfGain + errF]
  Gain --> M[kfErrTrans M(k)]
  Optimizer --> Arrival[arrSet + arrC + arrV]
  Arrival --> SemiPT[optTerm = arrC = M(T)a]
  M --> SemiPT

  Infinite --> ModQ[exists_modQ]
  Optimizer --> ModQ
  ModQ --> ModQGAS[isGAS_of_modQ]
  Infinite --> ModQGAS
  ModQGAS --> OptimizerHeadline[prop_tvkf_optimizer]
  Conditions --> OptimizerHeadline
  OptimizerHeadline --> SemiPT
  SemiPT --> Headline[prop_tvkf: Kalman GAS ↔ C1 ∧ C2]
```

## Reading order and count

| Group | Items | Notes |
|---|---:|---|
| Definitions in the five paper-facing files | 47 | Five definition files below |
| Paper-result theorem statements | 14 | `paper-lean-audit-results.md` |
| Additional coordinate/semantic bridges | 9 | `paper-lean-audit-bridges.md` |
| **Total distinct manual items** | **70** | `semiPT_error` is counted as a result, not counted again as a bridge |

Recommended order:

1. [General estimation definitions](paper-lean-audit-general-definitions.md)
2. [Paper-coordinate optimization definitions](paper-lean-audit-chi-definitions.md)
3. [Kalman and Riccati definitions](paper-lean-audit-kalman-definitions.md)
4. [Arrival-cost definitions](paper-lean-audit-arrival-definitions.md)
5. [Modified-Q definitions](paper-lean-audit-qfunction-definitions.md)
6. [Semantic and coordinate bridges](paper-lean-audit-bridges.md)
7. [Paper-result declaration interfaces](paper-lean-audit-results.md)

## Notation used in the prose

- `a = x(0) − x̄₀` is the initial nominal estimation error.
- `e₀` is the initial error selected by the error-coordinate optimization.
- `χ₀` is the initial estimate selected by the paper-coordinate optimization.
- `ω` is the selected process-noise sequence.
- `Σ₀†` is the symmetric pseudoinverse of the semidefinite prior covariance.
- `M(T)` is the product of the time-varying Kalman error-transition matrices.
- Lean's vector norm here is the finite-dimensional supremum norm. The paper writes an unspecified/Euclidean norm; this is qualitatively equivalent for finite-dimensional GAS, but constants differ.

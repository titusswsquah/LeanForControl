import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import LeanForControl.LinearSystems.Hautus

/-!
# `Estimation.Basic`

Shared imports and conventions for the `Estimation` track, which formalizes the
full-information-estimator (FIE) stability dichotomy of *State estimation of
unstabilizable linear systems: the optimization perspective, Part II — the
value-function route*.

This file holds *only* shared imports and documentation, mirroring
`LinearSystems.Basic`. Definitions and proofs live in sibling modules.

## Conventions

The paper works with the discrete-time linear-Gaussian model

* `x⁺ = A x + G w`, `y = C x + v`,

with `x 0 ~ N (x₀, Σ₀)`, `w k ~ N (0, Q)`, `v k ~ N (0, R)`, and standing
hypotheses `Q ≻ 0`, `R ≻ 0`, `Σ₀ ⪰ 0`. Following `LinearSystems`:

* scalars are real (`ℝ`) for the estimator itself; eigenvalue-side arguments
  pass to `ℂ`, as in `LinearSystems.Hautus`;
* dimensions are natural numbers `n m p : ℕ`;
* state matrix `A : Matrix (Fin n) (Fin n) ℝ`;
* noise-input matrix `G : Matrix (Fin n) (Fin m) ℝ`;
* output matrix `C : Matrix (Fin p) (Fin n) ℝ`;
* matrix-vector multiplication is mathlib's `*ᵥ` (`Matrix.mulVec`).

The three standing conditions of the paper are named `C1`, `C2`, `C3w`:

* **C1** — `(A, C)` is detectable.
* **C2** — `ker Σ₀` meets the unstable uncontrollable subspace of `(A, G)`
  only at zero.
* **C3w** — `(A, G)` has no uncontrollable eigenvalues on the unit circle.

`LinearSystems.Hautus` already supplies the observability/controllability
side of this vocabulary (`unobservableSubspace`, `isObservable_iff_hautus`,
`isControllable_iff_isObservable_transpose`); detectability and stabilizability
are the natural next definitions and do not yet exist here or in mathlib.

## Status

Scaffold only — no results are claimed in this module. See
`notes/costogo-formalization-plan.md` for the dependency audit and the
suggested order of attack.
-/

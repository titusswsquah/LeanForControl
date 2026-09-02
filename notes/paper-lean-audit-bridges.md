# Semantic and coordinate bridges — 9 items

These are the nine additional declarations that make the formal objects denote the paper's objects. `semiPT_error` would naturally belong here too, but it is counted among the 14 paper results so that the 70-item total has no duplicate.

The Lean blocks give the exact declaration interfaces from the pinned snapshot. Proof bodies are not repeated: this document audits what Lean proves, while the kernel/build audit checks that Lean accepted the proof.

## 1. `chiFeasible_iff_ker`

Source: `LeanForControl/Estimation/ChiProblem.lean`.

```lean
lemma chiFeasible_iff_ker (xbar χ₀ : Fin n → ℝ) :
    S.ChiFeasible xbar χ₀
      ↔ ∀ u, S.Sig0 *ᵥ u = 0 → u ⬝ᵥ (χ₀ - xbar) = 0 := by
```

**Rendered meaning.** χ₀−x̄ lies in range Σ₀ exactly when it is orthogonal to every vector in null Σ₀.

**Paper counterpart.** With Σ₀ = U₁Σ̃₀U₁ᵀ and U₂ spanning null Σ₀, the paper imposes U₂ᵀ(χ(0)−x̄₀)=0. This theorem is the basis-independent equivalence between that equation and `ChiFeasible`.

**Audit question.** Confirm the matrix is symmetric and that the inner product/range-nullspace theorem applies over the exact real coordinate space used here.

## 2. `chiCost_eq_gCost`

Source: `LeanForControl/Estimation/ChiProblem.lean`.

```lean
theorem chiCost_eq_gCost (x₀ xbar χ₀ : Fin n → ℝ)
    (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    S.chiCost x₀ xbar χ₀ ω T
      = S.gCost (x₀ - xbar) (x₀ - χ₀) ω T := by
```

**Rendered meaning.** Under a = x₀−x̄ and e₀ = x₀−χ₀, the paper-coordinate objective equals the error-coordinate objective for the same ω and horizon.

**Paper counterpart.** The paper's nominal data make e = x−χ satisfy e⁺=Ae−Gω and ν=Ce. Thus P_T can be analyzed in error coordinates without changing its cost.

**Audit question.** Check the signs, endpoint convention, sum range 0…T−1, and common omission of the factor one half.

## 3. `chiFeasible_iff`

Source: `LeanForControl/Estimation/ChiProblem.lean`.

```lean
lemma chiFeasible_iff (x₀ xbar χ₀ : Fin n → ℝ) :
    S.ChiFeasible xbar χ₀ ↔ S.Feasible (x₀ - xbar) (x₀ - χ₀) := by
```

**Rendered meaning.** The initial estimate satisfies the paper's support constraint exactly when the associated initial error satisfies the error-coordinate support constraint.

**Paper counterpart.** χ₀−x̄₀ belongs to range Σ₀ if and only if (x₀−χ₀)−(x₀−x̄₀) belongs to range Σ₀; the two vectors differ by a sign.

**Audit question.** Ensure the two uses of x₀ are the nominal true initial state and do not smuggle actual noisy data into the nominal theorem.

## 4. `red_value`

Source: `LeanForControl/Estimation/Reduction.lean`.

```lean
theorem red_value (hC2 : S.C2) (a : Fin n → ℝ) (T : ℕ) :
    S.redSys.value (S.redT *ᵥ a) T = S.value a T := by
```

**Rendered meaning.** Assuming C2, the reduced-coordinate problem and the general-coordinate problem have the same optimal finite-horizon value after transforming a.

**Paper counterpart.** The paper changes to an orthogonal stabilizability canonical form and analyzes the two state blocks without changing the optimization value.

**Audit question.** Check that `redT` is genuinely invertible, preserves all feasible decisions under C2, and does not discard a zero-cost or infeasible direction.

## 5. `red_C1_iff`

Source: `LeanForControl/Estimation/Reduction.lean`.

```lean
theorem red_C1_iff : S.redSys.C1 ↔ S.C1 := by
```

**Rendered meaning.** Detectability is invariant under the chosen invertible state-coordinate transformation.

**Paper counterpart.** Passing to the orthogonal stabilizability canonical form does not change whether (A,C) is detectable.

**Audit question.** Confirm `redSys.C1` uses the transformed full A and C, not merely the stabilizable block.

## 6. `red_C2_iff`

Source: `LeanForControl/Estimation/Reduction.lean`.

```lean
theorem red_C2_iff : S.redSys.C2 ↔ S.C2 :=
  (S.C2_iff_stairSig₂_posDef).symm
```

**Rendered meaning.** The prior/nonstabilizable-subspace intersection condition is invariant under the reduction.

**Paper counterpart.** In canonical coordinates C2 says the prior has no null vector supported in the unstable uncontrollable second block.

**Audit question.** This compact proof delegates the semantic burden to `C2_iff_stairSig₂_posDef`; inspect that theorem even though it is outside the 70 paper-facing items.

## 7. `optTerm_eq_arrC`

Source: `LeanForControl/Estimation/Arrival.lean`.

```lean
theorem optTerm_eq_arrC (a : Fin n → ℝ) (T : ℕ) :
    S.optTerm a T = S.arrC a T := by
```

**Rendered meaning.** The terminal state of the optimal horizon-T error trajectory equals the center of the quadratic arrival cost.

**Paper counterpart.** This is one half of the optimization/Kalman correspondence used by the paper: the least-squares terminal estimate error is the arrival-cost center.

**Audit question.** Check that the arrival representation applies at T=0 and for semidefinite Σ₀, and that “center” is unique even when the arrival covariance is singular.

## 8. `arrC_eq_kfErrTrans`

Source: `LeanForControl/Estimation/Arrival.lean`.

```lean
theorem arrC_eq_kfErrTrans (a : Fin n → ℝ) : ∀ T : ℕ,
    S.arrC a T = S.kfErrTrans T *ᵥ a
```

**Rendered meaning.** The recursively defined arrival center is exactly M(T)a.

**Paper counterpart.** The paper states ê(T)=M(T)ê(0), where M(T) is the ordered product of A−L(k)C.

**Audit question.** Check multiplication order and the indexing of the covariance/gain at each transition.

## 9. `isGASkf_iff_isGAS`

Source: `LeanForControl/Estimation/Arrival.lean`.

```lean
theorem isGASkf_iff_isGAS : S.IsGASkf ↔ S.IsGAS := by
```

**Rendered meaning.** Stability of the recursive Kalman error and stability of the optimal terminal error are equivalent.

**Paper counterpart.** The paper relies on a one-to-one optimization/Kalman correspondence to use optimization arguments to establish stability of the filter.

**Audit question.** This equivalence uses only the nominal terminal-error identity `semiPT_error`; it does not by itself formalize the paper's broader assertion of a one-to-one correspondence for arbitrary measurement sequences and all optimizer components.


# Arrival-cost definitions — 5 items

Source at the pinned snapshot: `LeanForControl/Estimation/Arrival.lean`.

## 1. `arrSet`

```lean
def arrSet (a : Fin n → ℝ) (T : ℕ) (ξ : Fin n → ℝ) : Set ℝ :=
  {c | ∃ e₀ ω, S.Feasible a e₀ ∧ S.glq.traj e₀ ω T = ξ
    ∧ c = S.gCost a e₀ ω T}
```

**Rendered meaning.** `arrSet a T ξ` contains exactly the costs of feasible error-coordinate decisions that reach terminal state ξ at time T.

**Paper counterpart.** The paper does not name an arrival-cost set. This formalizes the cost-to-arrive implicit in the least-squares/Kalman correspondence.

## 2. `arrC`

```lean
noncomputable def arrC (a : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => a
  | T + 1 => S.errF (S.dre T) *ᵥ arrC a T
```

**Rendered meaning.** The center starts at a and follows the time-varying Kalman error recursion.

**Paper counterpart.** ê(0) = x(0) − x̄₀ and ê(k+1) = [A−L(k)C]ê(k).

## 3. `arrV`

```lean
noncomputable def arrV (a : Fin n → ℝ) : ℕ → ℝ
  | 0 => 0
  | T + 1 => arrV a T
      + quadForm (S.innovS (S.dre T))⁻¹ (S.C *ᵥ S.arrC a T)
```

**Rendered meaning.** Accumulate the quadratic innovation energy along the arrival-center recursion.

**Paper counterpart.** The paper states that the optimization and Kalman filter have identical solutions but does not give this accumulated-innovation expression for V_T⁰.

## 4. `updCoord`

```lean
noncomputable def updCoord (Sg : Matrix (Fin n) (Fin n) ℝ)
    (z e : Fin n → ℝ) : Fin n → ℝ :=
  (1 + S.Cᵀ * S.Ri * (S.C * Sg))
    *ᵥ (z + S.Cᵀ *ᵥ ((S.innovS Sg)⁻¹ *ᵥ (S.C *ᵥ e)))
```

**Rendered meaning.** This is a change of variables used to complete the square in one arrival-cost update.

**Paper counterpart.** There is no direct named formula in the paper. It is proof infrastructure for showing that the least-squares arrival center follows the Kalman recursion.

## 5. `IsGASkf`

```lean
def IsGASkf : Prop :=
  ∃ σ : ℕ → ℝ, Filter.Tendsto σ Filter.atTop (nhds 0) ∧
    ∀ (T : ℕ) (a : Fin n → ℝ), ‖S.kfErrTrans T *ᵥ a‖ ≤ σ T * ‖a‖
```

**Rendered meaning.** There is one time-dependent scalar rate tending to zero that uniformly bounds M(T)a for every initial error a.

**Paper counterpart.** The paper defines GAS by a KL function β satisfying ‖x(k)−x̂(k)‖ ≤ β(‖x(0)−x̄₀‖,k). Its linearity argument specializes this to β(r,k)=rα(k). As with `IsGAS`, Lean's σ-form does not itself require monotonicity or explicit positivity.


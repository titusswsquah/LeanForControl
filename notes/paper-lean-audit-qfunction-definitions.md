# Modified-Q definitions — 3 items

Source at the pinned snapshot: `LeanForControl/Estimation/QFunction.lean`.

## 1. `eTraj`

```lean
noncomputable def eTraj (a : Fin n → ℝ) (k j : ℕ) : Fin n → ℝ :=
  S.glq.traj (S.optInit a k) (S.glq.optCtrl (S.optInit a k) k) j
```

**Rendered meaning.** For a horizon-k optimization, `eTraj a k j` is its optimal estimation error at internal time j.

**Paper counterpart.** This is x(j) − x̂(j | k) under nominal measurements.

## 2. `partialCost`

```lean
noncomputable def partialCost (a : Fin n → ℝ) (j k : ℕ) : ℝ :=
  S.priorPen a (S.optInit a k)
    + ∑ i ∈ Finset.range j,
        S.gStage (S.optInit a k) (S.glq.optCtrl (S.optInit a k) k) i
```

**Rendered meaning.** For the horizon-k optimizer, this is the prior cost plus the stages from 0 through j−1.

**Paper counterpart.** The proof of `prop:tvkfQuns` defines V⁰(j | k) as the prior penalty plus the sum from i=0 through j−1 of the optimal process and residual stage costs. Lean uses the doubled-cost convention.

## 3. `IsGASkl`

```lean
def IsGASkl : Prop :=
  ∃ α : ℕ → ℝ, Antitone α ∧ Tendsto α atTop (nhds 0) ∧
    ∀ (k : ℕ) (a : Fin n → ℝ), ‖S.optTerm a k‖ ≤ α k * ‖a‖
```

**Rendered meaning.** The product bound β(r,k)=α(k)r holds and α is nonincreasing and tends to zero.

**Paper counterpart.** The paper defines α(k)=supreme over j≥k of ‖M(j)‖ and β(r,k)=rα(k), calling β a KL function. Audit warning: the Lean declaration does not explicitly require α(k)>0 or strict decrease; it captures the bound and L-like limiting behavior, but not every textbook side condition of class KL.


# General estimation definitions — 18 items

Source at the pinned snapshot: `LeanForControl/Estimation/General.lean`.

## 1. `GeneralSystem`

```lean
structure GeneralSystem (n m p : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  G : Matrix (Fin n) (Fin m) ℝ
  C : Matrix (Fin p) (Fin n) ℝ
  Sig0 : Matrix (Fin n) (Fin n) ℝ
  Qi : Matrix (Fin m) (Fin m) ℝ
  Ri : Matrix (Fin p) (Fin p) ℝ
  hSig0 : Sig0.PosSemidef
  hQi : Qi.PosDef
  hRi : Ri.PosDef
```

**Rendered meaning.** A system contains the state, process-input, and output matrices; a positive-semidefinite initial covariance; and positive-definite process and measurement penalty matrices. `Qi` and `Ri` represent Q⁻¹ and R⁻¹, not Q and R.

**Paper counterpart.** The model is x⁺ = Ax + Gw and y = Cx + v, with x(0) distributed with mean x̄₀ and covariance Σ₀. The paper assumes Q > 0, R > 0, and Σ₀ ≥ 0. The optimization penalizes w with Q⁻¹ and v with R⁻¹.

## 2. `glq`

```lean
noncomputable def glq : LQSystem (Fin n) (Fin m) where
  A := S.A
  B := -S.G
  Qs := S.Cᵀ * S.Ri * S.C
  Ru := S.Qi
  hQs := by
    have h := S.hRi.posSemidef.mul_mul_conjTranspose_same S.Cᵀ
    rwa [show (S.Cᵀ)ᴴ = S.C from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]]
      at h
  hRu := S.hQi
```

**Rendered meaning.** This packages the nominal error system e⁺ = Ae − Gω with stage cost eᵀCᵀR⁻¹Ce + ωᵀQ⁻¹ω.

**Paper counterpart.** Under nominal measurements, x − χ obeys e⁺ = Ae − Gω and ν = Ce. The paper's stage penalty is one half of the same two quadratic terms. Lean consistently omits the common factor one half.

## 3. `priorPen`

```lean
noncomputable def priorPen (a e₀ : Fin n → ℝ) : ℝ :=
  quadForm (symmPinv S.hSig0.1) (e₀ - a)
```

**Rendered meaning.** The initial penalty is (e₀ − a)ᵀΣ₀†(e₀ − a).

**Paper counterpart.** The semidefinite initial penalty is one half of the squared Σ₀†-weighted norm of χ(0) − x̄₀. Since e₀ − a = −(χ(0) − x̄₀), the quadratic value is the same. Lean omits the common one-half factor.

## 4. `Feasible`

```lean
def Feasible (a e₀ : Fin n → ℝ) : Prop :=
  ∃ z, e₀ - a = S.Sig0 *ᵥ z
```

**Rendered meaning.** The selected initial-error displacement e₀ − a must lie in the range of Σ₀.

**Paper counterpart.** The paper writes U₂ᵀ(χ(0) − x̄₀) = 0. For symmetric Σ₀, this is equivalent to χ(0) − x̄₀ lying in range Σ₀; the sign change in error coordinates does not change membership in the range.

## 5. `gCost`

```lean
noncomputable def gCost (a e₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ)
    (T : ℕ) : ℝ :=
  S.priorPen a e₀ + S.glq.cost e₀ ω T
```

**Rendered meaning.** The horizon-T error-coordinate objective is the prior penalty plus the first T error-system stage costs.

**Paper counterpart.** P_T minimizes an initial Σ₀† penalty plus the sum from k = 0 through T − 1 of process and measurement residual penalties. Lean uses twice the paper's objective because it omits every factor one half; the minimizer is unchanged.

## 6. `IsStationary`

```lean
def IsStationary (a e₀ : Fin n → ℝ) (T : ℕ) : Prop :=
  S.Feasible a e₀ ∧ ∀ d : Fin n → ℝ, (∃ z, d = S.Sig0 *ᵥ z) →
    (symmPinv S.hSig0.1 *ᵥ (e₀ - a)) ⬝ᵥ d
      + (S.glq.ric T *ᵥ e₀) ⬝ᵥ d = 0
```

**Rendered meaning.** A feasible initial error is stationary when the directional derivative of the reduced quadratic objective vanishes in every direction allowed by range Σ₀.

**Paper counterpart.** The paper argues existence and uniqueness after using χ(0) − x̄₀ = U₁α₁ and optimizing over the free coordinate α₁. It does not name a stationarity predicate, but this is the same first-order condition in invariant coordinates.

## 7. `optInit`

```lean
noncomputable def optInit (a : Fin n → ℝ) (T : ℕ) : Fin n → ℝ :=
  Classical.choose (S.exists_isStationary a T)
```

**Rendered meaning.** Choose the stationary, hence optimal and unique, initial error for horizon T.

**Paper counterpart.** This is x(0) − x̂(0 | T) in error coordinates. The paper defines x̂(0 | T) as the initial component of the unique minimizer of P_T.

## 8. `value`

```lean
noncomputable def value (a : Fin n → ℝ) (T : ℕ) : ℝ :=
  S.priorPen a (S.optInit a T)
    + quadForm (S.glq.ric T) (S.optInit a T)
```

**Rendered meaning.** The optimal horizon-T value is the prior penalty at the optimal initial error plus the Riccati quadratic giving the optimal tail cost.

**Paper counterpart.** This is the paper's V_T⁰, except Lean uses the doubled-cost convention. The paper says V_T⁰ exists and the minimizer is unique.

## 9. `optTerm`

```lean
noncomputable def optTerm (a : Fin n → ℝ) (T : ℕ) : Fin n → ℝ :=
  S.glq.optTraj (S.optInit a T) T T
```

**Rendered meaning.** Roll out the horizon-T optimal error trajectory and take its terminal error at time T.

**Paper counterpart.** This is x(T) − x̂(T | T), the final element of the optimal estimate trajectory under nominal measurements.

## 10. `IsGAS`

```lean
def IsGAS : Prop :=
  ∃ σ : ℕ → ℝ, Tendsto σ atTop (nhds 0) ∧
    ∀ (T : ℕ) (a : Fin n → ℝ), ‖S.optTerm a T‖ ≤ σ T * ‖a‖
```

**Rendered meaning.** There is a scalar rate σ(T) tending to zero that bounds every optimal terminal error by σ(T) times the initial-error norm.

**Paper counterpart.** GAS means there is a KL bound β with ‖x(k) − x̂(k)‖ ≤ β(‖x(0) − x̄₀‖, k). For a linear map, the paper constructs the product form β(r,k) = rα(k). Lean's σ-form records that product bound but does not require σ to be monotone or explicitly nonnegative.

## 11. `IsGES`

```lean
def IsGES : Prop :=
  ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧
    ∀ (T : ℕ) (a : Fin n → ℝ), ‖S.optTerm a T‖ ≤ c * ρ ^ T * ‖a‖
```

**Rendered meaning.** The optimal error decays uniformly at a geometric rate.

**Paper counterpart.** The current paper explicitly says that it proves asymptotic stability and defers the exponential case to a later paper. This definition is supporting infrastructure, not a claim established by `paper.tex`.

## 12. `realReachMap`

```lean
noncomputable def realReachMap :
    (Fin n → Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := fun us => ∑ j : Fin n, (S.A ^ (j : ℕ) * S.G) *ᵥ us j
  map_add' := fun us vs => by
    simp only [Pi.add_apply, Matrix.mulVec_add]
    rw [Finset.sum_add_distrib]
  map_smul' := fun c us => by
    simp only [Pi.smul_apply, Matrix.mulVec_smul, RingHom.id_apply]
    rw [Finset.smul_sum]
```

**Rendered meaning.** This linear map sends n process-input vectors to Σⱼ AʲGuⱼ. Its range is the ordinary finite-dimensional reachable subspace.

**Paper counterpart.** The paper uses an orthogonal stabilizability decomposition in which (A₁,G₁) is stabilizable and the second block is uncontrollable. It does not define the reachability map explicitly.

## 13. `reachSub`

```lean
noncomputable def reachSub : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.range S.realReachMap
```

**Rendered meaning.** The reachable subspace is the image of the finite-horizon reachability map.

**Paper counterpart.** This is the controllable/reachable component implicit in the paper's stabilizability canonical form.

## 14. `stabilizableSub`

```lean
noncomputable def stabilizableSub : Submodule ℝ (Fin n → ℝ) :=
  S.reachSub ⊔ stableSub S.A
```

**Rendered meaning.** The stabilizable subspace is the span of the reachable states and the strictly stable modes of A.

**Paper counterpart.** This is the first coordinate block in the paper's orthogonal stabilizability canonical form: the block on which (A₁,G₁) is stabilizable.

## 15. `uucSub`

```lean
noncomputable def uucSub : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | ∀ u ∈ S.stabilizableSub, u ⬝ᵥ v = 0}
  add_mem' := fun ha hb u hu => by
    rw [dotProduct_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => by rw [dotProduct_zero]
  smul_mem' := fun c v hv u hu => by
    rw [dotProduct_smul, hv u hu, smul_zero]
```

**Rendered meaning.** The unstable, uncontrollable subspace is defined as the Euclidean orthogonal complement of the stabilizable subspace.

**Paper counterpart.** In the paper's orthogonal canonical coordinates this is the span of vectors with zero first block and arbitrary second block, corresponding to the completely unstable uncontrollable A₂ modes.

## 16. `C1`

```lean
def C1 : Prop := IsDetectable (complexify S.A) (complexify S.C)
```

**Rendered meaning.** The complexified pair (A,C) is detectable: every unobservable eigenmode is strictly inside the unit disk.

**Paper counterpart.** C1: (A,C) is detectable.

## 17. `C2`

```lean
def C2 : Prop := ∀ v : Fin n → ℝ, S.Sig0 *ᵥ v = 0 → v ∈ S.uucSub →
  v = 0
```

**Rendered meaning.** Any real vector that is both killed by Σ₀ and belongs to the unstable, uncontrollable subspace must be zero.

**Paper counterpart.** C2: the intersection of null Σ₀ and the unstable, uncontrollable subspace of (A,G) is {0}. This is a literal match, subject to checking that `uucSub` denotes exactly the paper's second canonical block.

## 18. `C3w`

```lean
def C3w : Prop := ∀ (μ : ℂ) (v : Fin n → ℂ), ‖μ‖ = 1 →
  (complexify S.A)ᵀ *ᵥ v = μ • v → (complexify S.G)ᵀ *ᵥ v = 0 → v = 0
```

**Rendered meaning.** There is no nonzero uncontrollable left eigenvector of A whose eigenvalue lies on the unit circle.

**Paper counterpart.** The present paper discusses uncontrollable unit-circle modes but does not introduce a named C3w condition; it says excluding those modes is associated with exponential stability in later work. This is supporting infrastructure, not part of the C1-and-C2 headline.


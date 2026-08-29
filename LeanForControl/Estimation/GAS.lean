import LeanForControl.Estimation.Infhor
import LeanForControl.LinearSystems.OutputInjection
import Mathlib.LinearAlgebra.Matrix.ToLin
import Architect

/-!
# Global asymptotic stability of the FIE (`prop:gas`, sufficiency layer)

The sufficiency half of `prop:gas` runs through a uniformization step:
the horizon-`T` value `V_T⁰` is a **quadratic form** in the prior
mismatch `a` (because the unique stationary initial error depends
linearly on `a`), hence so is the limiting value `V̄`, and the pointwise
convergence `V_T⁰ ↗ V̄` upgrades to the uniform bound
`V̄(a) - V_T⁰(a) ≤ η_T ‖a‖²` with `η_T → 0` through the matrix
representations `Π_T → Π_∞`.
-/

namespace Estimation

namespace FIESystem

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

variable {n₁ n₂ m p : ℕ} (Sys : FIESystem n₁ n₂ m p)

private lemma continuous_blk₁ :
    Continuous fun e : Fin n₁ ⊕ Fin n₂ → ℝ => blk₁ e :=
  continuous_pi fun i => continuous_apply (Sum.inl i)

/-! ### Linearity of the optimal initial error in the prior mismatch -/

lemma isStationary_add {a b e f : Fin n₁ ⊕ Fin n₂ → ℝ} {T : ℕ}
    (ha : Sys.IsStationary a e T) (hb : Sys.IsStationary b f T) :
    Sys.IsStationary (a + b) (e + f) T := by
  obtain ⟨⟨⟨z, hz⟩, ⟨w, hw⟩⟩, hva⟩ := ha
  obtain ⟨⟨⟨z', hz'⟩, ⟨w', hw'⟩⟩, hvb⟩ := hb
  have hsplit : (e + f) - (a + b) = (e - a) + (f - b) := by abel
  refine ⟨⟨⟨z + z', ?_⟩, ⟨w + w', ?_⟩⟩, ?_⟩
  · rw [hsplit, blk₁_add, hz, hz', Matrix.mulVec_add]
  · rw [hsplit, blk₂_add, hw, hw', Matrix.mulVec_add]
  · intro d hd
    have h1 := hva d hd
    have h2 := hvb d hd
    rw [hsplit, blk₁_add, blk₂_add, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_add, add_dotProduct, add_dotProduct, add_dotProduct]
    linarith

lemma isStationary_smul {a e : Fin n₁ ⊕ Fin n₂ → ℝ} {T : ℕ} (t : ℝ)
    (ha : Sys.IsStationary a e T) :
    Sys.IsStationary (t • a) (t • e) T := by
  obtain ⟨⟨⟨z, hz⟩, ⟨w, hw⟩⟩, hva⟩ := ha
  have hsplit : (t • e) - (t • a) = t • (e - a) := by
    rw [smul_sub]
  refine ⟨⟨⟨t • z, ?_⟩, ⟨t • w, ?_⟩⟩, ?_⟩
  · rw [hsplit, blk₁_smul, hz, Matrix.mulVec_smul]
  · rw [hsplit, blk₂_smul, hw, Matrix.mulVec_smul]
  · intro d hd
    have h1 := hva d hd
    rw [hsplit, blk₁_smul, blk₂_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct,
      smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    rw [← mul_add, ← mul_add, h1, mul_zero]

theorem optInit_add (a b : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.optInit (a + b) T = Sys.optInit a T + Sys.optInit b T :=
  Sys.isStationary_unique (Sys.optInit_isStationary (a + b) T)
    (Sys.isStationary_add (Sys.optInit_isStationary a T)
      (Sys.optInit_isStationary b T))

theorem optInit_smul (t : ℝ) (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.optInit (t • a) T = t • Sys.optInit a T :=
  Sys.isStationary_unique (Sys.optInit_isStationary (t • a) T)
    (Sys.isStationary_smul t (Sys.optInit_isStationary a T))

/-- The matrix of the linear map `a ↦ e*(0|T)`. -/
noncomputable def optInitMat (T : ℕ) :
    Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ :=
  LinearMap.toMatrix'
    { toFun := fun a => Sys.optInit a T
      map_add' := fun a b => Sys.optInit_add a b T
      map_smul' := fun t a => Sys.optInit_smul t a T }

lemma optInitMat_mulVec (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.optInitMat T *ᵥ a = Sys.optInit a T :=
  LinearMap.toMatrix'_mulVec _ a

/-! ### The value as a quadratic form: `V_T⁰(a) = a'Π_T a` -/

/-- The blockwise pseudoinverse prior weight `W_p = diag(Σ₁†, Σ₂†)`. -/
noncomputable def Wp : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ :=
  Matrix.fromBlocks (symmPinv Sys.hSig₁.1) 0 0 (symmPinv Sys.hSig₂.1)

lemma Wp_mulVec (v : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.Wp *ᵥ v
      = Sum.elim (symmPinv Sys.hSig₁.1 *ᵥ blk₁ v)
        (symmPinv Sys.hSig₂.1 *ᵥ blk₂ v) := by
  rw [Wp, Matrix.fromBlocks_mulVec]
  simp [blk₁, blk₂]

lemma quadForm_Wp (v : Fin n₁ ⊕ Fin n₂ → ℝ) :
    quadForm Sys.Wp v
      = quadForm (symmPinv Sys.hSig₁.1) (blk₁ v)
        + quadForm (symmPinv Sys.hSig₂.1) (blk₂ v) := by
  rw [quadForm, Sys.Wp_mulVec, dotProduct_blocks]
  simp [quadForm]

lemma priorPenalty_eq_quadForm_Wp (a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.priorPenalty a e₀ = quadForm Sys.Wp (e₀ - a) := by
  rw [Sys.quadForm_Wp]
  rfl

lemma Wp_transpose : Sys.Wpᵀ = Sys.Wp := by
  rw [Wp, Matrix.fromBlocks_transpose,
    (symmPinv_isHermitian Sys.hSig₁.1).transpose_eq_self,
    (symmPinv_isHermitian Sys.hSig₂.1).transpose_eq_self]
  simp

/-- The value matrix `Π_T`. -/
noncomputable def Pimat (T : ℕ) :
    Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ :=
  (Sys.optInitMat T - 1)ᵀ * Sys.Wp * (Sys.optInitMat T - 1)
    + (Sys.optInitMat T)ᵀ * Sys.lq.ric T * Sys.optInitMat T

lemma Pimat_transpose (T : ℕ) : (Sys.Pimat T)ᵀ = Sys.Pimat T := by
  rw [Pimat, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose,
    Sys.Wp_transpose, Sys.ric_transpose_eq, Matrix.mul_assoc,
    Matrix.mul_assoc]

/-- **`V_T⁰` is the quadratic form of `Π_T`.** -/
theorem value_eq_quadForm_Pimat (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.value a T = quadForm (Sys.Pimat T) a := by
  have hdev : Sys.optInit a T - a = (Sys.optInitMat T - 1) *ᵥ a := by
    rw [Matrix.sub_mulVec, Sys.optInitMat_mulVec, Matrix.one_mulVec]
  unfold value outerObj
  rw [Sys.priorPenalty_eq_quadForm_Wp, hdev, quadForm_mulVec,
    ← Sys.optInitMat_mulVec a T, quadForm_mulVec, Pimat,
    quadForm_add_matrix]

/-! ### The limiting value matrix `Π_∞` and the uniform gap bound -/

private lemma single_dot_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (i j : ι) :
    (Pi.single i 1 : ι → ℝ) ⬝ᵥ (M *ᵥ (Pi.single j 1 : ι → ℝ))
      = M i j := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite,
    Finset.sum_ite_eq']

/-- Entries of a symmetric matrix from polarization of its quadratic
form. -/
private lemma entry_eq_polarization {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : Mᵀ = M) (i j : ι) :
    M i j = (quadForm M (Pi.single i 1 + Pi.single j 1)
      - quadForm M (Pi.single i 1) - quadForm M (Pi.single j 1)) / 2 := by
  rw [quadForm_add]
  have h1 : (Pi.single j 1 : ι → ℝ) ⬝ᵥ (M *ᵥ (Pi.single i 1 : ι → ℝ))
      = M i j := by
    rw [single_dot_mulVec]
    calc M j i = Mᵀ i j := rfl
    _ = M i j := by rw [hM]
  rw [single_dot_mulVec, h1]
  ring

/-- The limiting value matrix `Π_∞`, defined entrywise by polarization
of `V̄`. -/
noncomputable def PimatInf :
    Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ :=
  Matrix.of fun i j =>
    (Sys.valueLim (Pi.single i 1 + Pi.single j 1)
      - Sys.valueLim (Pi.single i 1) - Sys.valueLim (Pi.single j 1)) / 2

/-- Under C1 ∧ C2 the value matrices converge entrywise to `Π_∞`. -/
theorem tendsto_Pimat (hC1 : Sys.C1) (hC2 : Sys.C2) :
    Tendsto (fun T => Sys.Pimat T) atTop (nhds Sys.PimatInf) := by
  have key : ∀ i j, Tendsto (fun T => Sys.Pimat T i j) atTop
      (nhds (Sys.PimatInf i j)) := by
    intro i j
    have hentry : ∀ T, Sys.Pimat T i j
        = (Sys.value (Pi.single i 1 + Pi.single j 1) T
          - Sys.value (Pi.single i 1) T - Sys.value (Pi.single j 1) T) / 2 := by
      intro T
      rw [entry_eq_polarization (Sys.Pimat_transpose T) i j,
        ← Sys.value_eq_quadForm_Pimat, ← Sys.value_eq_quadForm_Pimat,
        ← Sys.value_eq_quadForm_Pimat]
    simp only [hentry]
    exact (((Sys.tendsto_value hC1 hC2 _).sub
      (Sys.tendsto_value hC1 hC2 _)).sub
      (Sys.tendsto_value hC1 hC2 _)).div_const 2
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => key i j

/-- `V̄` is the quadratic form of `Π_∞`. -/
theorem valueLim_eq_quadForm_PimatInf (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.valueLim a = quadForm Sys.PimatInf a := by
  have h1 : Tendsto (fun T => quadForm (Sys.Pimat T) a) atTop
      (nhds (quadForm Sys.PimatInf a)) := by
    have hcont : Continuous fun Mq :
        Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ => quadForm Mq a :=
      Continuous.dotProduct continuous_const
        (continuous_id.matrix_mulVec continuous_const)
    exact (hcont.tendsto _).comp (Sys.tendsto_Pimat hC1 hC2)
  have h2 : Tendsto (fun T => quadForm (Sys.Pimat T) a) atTop
      (nhds (Sys.valueLim a)) := by
    have h3 := Sys.tendsto_value hC1 hC2 a
    simpa only [Sys.value_eq_quadForm_Pimat] using h3
  exact tendsto_nhds_unique h2 h1

private lemma abs_dotProduct_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    |x ⬝ᵥ y| ≤ (Fintype.card ι : ℝ) * ‖x‖ * ‖y‖ := by
  calc |x ⬝ᵥ y| ≤ ∑ i, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
  _ ≤ ∑ _i : ι, ‖x‖ * ‖y‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm y i)
        (abs_nonneg _) (norm_nonneg _)
  _ = (Fintype.card ι : ℝ) * ‖x‖ * ‖y‖ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- **The uniform truncation-gap bound**: under C1 ∧ C2 there is
`η_T → 0` with `V̄(a) - V_T⁰(a) ≤ η_T ‖a‖²` for every `a`. -/
theorem exists_uniform_gap (hC1 : Sys.C1) (hC2 : Sys.C2) :
    ∃ η : ℕ → ℝ, Tendsto η atTop (nhds 0) ∧ (∀ T, 0 ≤ η T) ∧
      ∀ (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ),
        Sys.valueLim a - Sys.value a T ≤ η T * ‖a‖ ^ 2 := by
  refine ⟨fun T => (Fintype.card (Fin n₁ ⊕ Fin n₂) : ℝ)
    * ‖Sys.PimatInf - Sys.Pimat T‖, ?_, ?_, ?_⟩
  · have h1 : Tendsto (fun T => ‖Sys.PimatInf - Sys.Pimat T‖) atTop
        (nhds 0) := by
      have h2 : Tendsto (fun T => Sys.PimatInf - Sys.Pimat T) atTop
          (nhds 0) := by
        have h3 := (Sys.tendsto_Pimat hC1 hC2).const_sub Sys.PimatInf
        simpa using h3
      simpa using h2.norm
    simpa using h1.const_mul _
  · intro T
    positivity
  · intro a T
    rw [Sys.valueLim_eq_quadForm_PimatInf hC1 hC2,
      Sys.value_eq_quadForm_Pimat, ← quadForm_sub_matrix]
    calc quadForm (Sys.PimatInf - Sys.Pimat T) a
        ≤ |a ⬝ᵥ ((Sys.PimatInf - Sys.Pimat T) *ᵥ a)| := le_abs_self _
    _ ≤ (Fintype.card (Fin n₁ ⊕ Fin n₂) : ℝ) * ‖a‖
          * ‖(Sys.PimatInf - Sys.Pimat T) *ᵥ a‖ := abs_dotProduct_le _ _
    _ ≤ (Fintype.card (Fin n₁ ⊕ Fin n₂) : ℝ) * ‖a‖
          * (‖Sys.PimatInf - Sys.Pimat T‖ * ‖a‖) := by
        refine mul_le_mul_of_nonneg_left
          (Matrix.linfty_opNorm_mulVec _ _) ?_
        positivity
    _ = (Fintype.card (Fin n₁ ⊕ Fin n₂) : ℝ)
          * ‖Sys.PimatInf - Sys.Pimat T‖ * ‖a‖ ^ 2 := by ring

/-! ### The infinite-horizon candidate and its deviation -/

/-- The frozen-gain candidate noise, rolled out from the limiting
block-1 initial error. -/
noncomputable def ctrlInf (hC1 : Sys.C1) (a : Fin n₁ ⊕ Fin n₂ → ℝ)
    (j : ℕ) : Fin m → ℝ :=
  -(Sys.lqRed.gainK (Sys.Pinf hC1)
    *ᵥ (Sys.lqRed.Acl (Sys.Pinf hC1) ^ j *ᵥ blk₁ (Sys.optInitLim a)))

lemma optInitLim_eq_sumElim (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.optInitLim a = Sum.elim (blk₁ (Sys.optInitLim a)) 0 := by
  conv_lhs => rw [← sumElim_blk (Sys.optInitLim a)]
  rw [Sys.blk₂_optInitLim_eq_zero hC1 hC2 a]

/-- The candidate trajectory is the frozen-gain block-1 rollout. -/
lemma traj_ctrlInf (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (k : ℕ) :
    Sys.lq.traj (Sys.optInitLim a) (Sys.ctrlInf hC1 a) k
      = Sum.elim (Sys.lqRed.Acl (Sys.Pinf hC1) ^ k
          *ᵥ blk₁ (Sys.optInitLim a)) 0 := by
  have hω : Sys.ctrlInf hC1 a = fun j =>
      -(Sys.lqRed.gainK (Sys.Pinf hC1)
        *ᵥ (Sys.lqRed.Acl (Sys.Pinf hC1) ^ j
          *ᵥ blk₁ (Sys.optInitLim a))) := rfl
  have h := Sys.lq_traj_sumElim_zero (blk₁ (Sys.optInitLim a))
    (Sys.ctrlInf hC1 a) k
  rw [← Sys.optInitLim_eq_sumElim hC1 hC2 a] at h
  rw [h, hω, Sys.lqRed.traj_fixedGain]

/-- The candidate pair spends at most the budget `V̄(a)`. -/
theorem fieCost_ctrlInf_le_valueLim (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.fieCost a (Sys.optInitLim a) (Sys.ctrlInf hC1 a) T
      ≤ Sys.valueLim a := by
  have hbudget := Sys.priorPenalty_add_quadForm_Pinf_le_valueLim hC1 hC2 a
  have hω : Sys.ctrlInf hC1 a = fun j =>
      -(Sys.lqRed.gainK (Sys.Pinf hC1)
        *ᵥ (Sys.lqRed.Acl (Sys.Pinf hC1) ^ j
          *ᵥ blk₁ (Sys.optInitLim a))) := rfl
  have hcost : Sys.lq.cost (Sys.optInitLim a) (Sys.ctrlInf hC1 a) T
      ≤ quadForm (Sys.Pinf hC1) (blk₁ (Sys.optInitLim a)) := by
    have h1 : Sys.lq.cost (Sys.optInitLim a) (Sys.ctrlInf hC1 a) T
        = Sys.lqRed.cost (blk₁ (Sys.optInitLim a))
            (Sys.ctrlInf hC1 a) T := by
      conv_lhs => rw [Sys.optInitLim_eq_sumElim hC1 hC2 a]
      rw [Sys.lq_cost_sumElim_zero]
    rw [h1, hω, Sys.lqRed.cost_fixedGain (Sys.Pinf_posSemidef hC1)
      (Sys.Pinf_fixed hC1)]
    have h2 := (Sys.Pinf_posSemidef hC1).quadForm_nonneg
      (Sys.lqRed.Acl (Sys.Pinf hC1) ^ T *ᵥ blk₁ (Sys.optInitLim a))
    linarith
  unfold fieCost
  linarith

/-- The deviation of the candidate from the horizon-`T` optimum costs at
most the truncation gap. -/
theorem fieCost_dev_le_gap (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.fieCost 0 (Sys.optInitLim a - Sys.optInit a T)
        (fun j => Sys.ctrlInf hC1 a j
          - Sys.lq.optCtrl (Sys.optInit a T) T j) T
      ≤ Sys.valueLim a - Sys.value a T := by
  have hgap := Sys.fieCost_gap (Sys.optInitLim_feasible hC1 hC2 a)
    (Sys.ctrlInf hC1 a) T
  have h1 := Sys.fieCost_ctrlInf_le_valueLim hC1 hC2 a T
  rw [hgap] at h1
  linarith

/-- Uniform linear bound on the limiting block-1 initial error. -/
theorem exists_optInitLim_blk₁_bound (hC1 : Sys.C1) (hC2 : Sys.C2) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Fin n₁ ⊕ Fin n₂ → ℝ,
      ‖blk₁ (Sys.optInitLim a)‖ ≤ c * ‖a‖ := by
  obtain ⟨c₁, hc₁, hb⟩ := Sys.exists_optInit_blk₁_bound hC1 hC2
  refine ⟨c₁ + 1, by linarith, fun a => ?_⟩
  have htd : Tendsto (fun T => ‖blk₁ (Sys.optInit a T)‖) atTop
      (nhds ‖blk₁ (Sys.optInitLim a)‖) :=
    ((continuous_norm.comp continuous_blk₁).tendsto _).comp
      (Sys.tendsto_optInit hC1 hC2 a)
  refine le_of_tendsto htd (Filter.Eventually.of_forall fun T => ?_)
  have h1 := hb a T
  have h2 : ‖blk₁ (Sys.optInit a T)‖
      ≤ ‖blk₁ (Sys.optInit a T - a)‖ + ‖blk₁ a‖ := by
    have h3 : blk₁ (Sys.optInit a T)
        = blk₁ (Sys.optInit a T - a) + blk₁ a := by
      rw [← blk₁_add]
      congr 1
      abel
    rw [h3]
    exact norm_add_le _ _
  have h4 := norm_blk₁_le a
  linarith

private lemma norm_sumElim_zero_le (v : Fin n₁ → ℝ) :
    ‖(Sum.elim v 0 : Fin n₁ ⊕ Fin n₂ → ℝ)‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun i => ?_
  cases i with
  | inl i => exact norm_le_pi_norm v i
  | inr i => simp [norm_nonneg v]

/-! ### `prop:gas`, sufficiency -/

/-- **Global asymptotic stability under C1 ∧ C2** (`prop:gas`,
sufficiency): the optimal terminal error dies out linearly in the prior
mismatch, uniformly over mismatches. -/
theorem isGAS_of_C1_C2 (hC1 : Sys.C1) (hC2 : Sys.C2) : Sys.IsGAS := by
  classical
  obtain ⟨η, hη0, hηnn, hηb⟩ := Sys.exists_uniform_gap hC1 hC2
  obtain ⟨cA, ρ, hcA, hρ0, hρ1, hpowA⟩ :=
    (Sys.Pinf_schur hC1).exists_pow_norm_le
  obtain ⟨c₁, hc₁, hξb⟩ := Sys.exists_optInitLim_blk₁_bound hC1 hC2
  obtain ⟨L, hL⟩ := detect_inj Sys.fullA Sys.fullC hC1
  obtain ⟨cinj, hcinj, hinj⟩ :=
    exists_terminal_sq_bound_of_injection Sys.fullA Sys.fullC Sys.lq.B hL
  obtain ⟨Cr₁, hCr₁, hrb₁⟩ := Sys.hSig₁.exists_sq_norm_mulVec_le
  obtain ⟨Cr₂, hCr₂, hrb₂⟩ := Sys.hSig₂.exists_sq_norm_mulVec_le
  obtain ⟨cQ, hcQ, hQb⟩ := Sys.hQi.exists_le_quadForm
  obtain ⟨cR, hcR, hRb⟩ := Sys.hRi.exists_le_quadForm
  set Cd := cinj * (Cr₁ + Cr₂ + 1 / cR + 1 / cQ) with hCd
  have hCd0 : 0 < Cd := by positivity
  refine ⟨fun T => cA * c₁ * ρ ^ T + Real.sqrt (Cd * η T), ?_, ?_⟩
  · have h1 : Tendsto (fun T : ℕ => cA * c₁ * ρ ^ T) atTop (nhds 0) := by
      have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
      have h3 := h2.const_mul (cA * c₁)
      simpa using h3
    have h4 : Tendsto (fun T => Real.sqrt (Cd * η T)) atTop (nhds 0) := by
      have h5 : Tendsto (fun T => Cd * η T) atTop (nhds 0) := by
        have := hη0.const_mul Cd
        simpa using this
      have h6 := (Real.continuous_sqrt.tendsto 0).comp h5
      simpa [Real.sqrt_zero] using h6
    have h7 := h1.add h4
    simpa using h7
  · intro T a
    set dev := Sys.optInitLim a - Sys.optInit a T with hdev
    set ωdev : ℕ → Fin m → ℝ := fun j => Sys.ctrlInf hC1 a j
      - Sys.lq.optCtrl (Sys.optInit a T) T j with hωdev
    -- deviation cost is within the uniform gap
    have hdevcost : Sys.fieCost 0 dev ωdev T ≤ η T * ‖a‖ ^ 2 := by
      have h1 := Sys.fieCost_dev_le_gap hC1 hC2 a T
      have h2 := hηb a T
      rw [← hdev, ← hωdev] at h1
      linarith
    have hdevcost0 : 0 ≤ Sys.fieCost 0 dev ωdev T :=
      Sys.fieCost_nonneg _ _ _ _
    -- split the deviation cost into prior and tail parts
    have hcost_expand : Sys.fieCost 0 dev ωdev T
        = Sys.priorPenalty 0 dev + Sys.lq.cost dev ωdev T := rfl
    have hcost_nonneg : 0 ≤ Sys.lq.cost dev ωdev T :=
      Finset.sum_nonneg fun k _ => Sys.lq.stage_nonneg _ _
    have hprior_nonneg := Sys.priorPenalty_nonneg 0 dev
    have hprior_le : Sys.priorPenalty 0 dev
        ≤ Sys.fieCost 0 dev ωdev T := by
      rw [hcost_expand]; linarith
    have hcost_le : Sys.lq.cost dev ωdev T
        ≤ Sys.fieCost 0 dev ωdev T := by
      rw [hcost_expand]; linarith
    -- the initial deviation is range-constrained; bound its norm
    obtain ⟨v, hv⟩ := Sys.feasibleDir_sub
      (Sys.optInitLim_feasible hC1 hC2 a) (Sys.optInit_feasible a T)
    have hdev1 : blk₁ dev = Sys.Sig₁ *ᵥ blk₁ v := by
      rw [hdev, hv, Sys.Jmat_mulVec]
      simp
    have hdev2 : blk₂ dev = Sys.Sig₂ *ᵥ blk₂ v := by
      rw [hdev, hv, Sys.Jmat_mulVec]
      simp
    have hprior_eq : Sys.priorPenalty 0 dev
        = quadForm (symmPinv Sys.hSig₁.1) (blk₁ dev)
          + quadForm (symmPinv Sys.hSig₂.1) (blk₂ dev) := by
      unfold priorPenalty
      rw [sub_zero]
    have hb1 : ‖blk₁ dev‖ ^ 2
        ≤ Cr₁ * quadForm (symmPinv Sys.hSig₁.1) (blk₁ dev) := by
      conv_lhs => rw [hdev1]
      rw [hdev1, quadForm_symmPinv_image Sys.hSig₁]
      exact hrb₁ _
    have hb2 : ‖blk₂ dev‖ ^ 2
        ≤ Cr₂ * quadForm (symmPinv Sys.hSig₂.1) (blk₂ dev) := by
      conv_lhs => rw [hdev2]
      rw [hdev2, quadForm_symmPinv_image Sys.hSig₂]
      exact hrb₂ _
    have hq1 := Sys.hSig₁.symmPinv.quadForm_nonneg (blk₁ dev)
    have hq2 := Sys.hSig₂.symmPinv.quadForm_nonneg (blk₂ dev)
    have hdevnorm : ‖dev‖ ^ 2
        ≤ (Cr₁ + Cr₂) * Sys.priorPenalty 0 dev := by
      have h1 := sq_norm_le_blocks dev
      rw [hprior_eq]
      nlinarith
    -- output and input energies of the deviation trajectory
    have hsplit : Sys.lq.cost dev ωdev T
        = ∑ k ∈ Finset.range T,
          (quadForm Sys.lq.Qs (Sys.lq.traj dev ωdev k)
            + quadForm Sys.lq.Ru (ωdev k)) := rfl
    have hsumν : cR * ∑ k ∈ Finset.range T,
        ‖Sys.fullC *ᵥ Sys.lq.traj dev ωdev k‖ ^ 2
          ≤ Sys.lq.cost dev ωdev T := by
      rw [hsplit, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h1 : cR * ‖Sys.fullC *ᵥ Sys.lq.traj dev ωdev k‖ ^ 2
          ≤ quadForm Sys.lq.Qs (Sys.lq.traj dev ωdev k) := by
        rw [Sys.quadForm_Qs]
        exact hRb _
      have h2 : 0 ≤ quadForm Sys.lq.Ru (ωdev k) :=
        Sys.lq.hRu.posSemidef.quadForm_nonneg _
      linarith
    have hsumω : cQ * ∑ k ∈ Finset.range T, ‖ωdev k‖ ^ 2
        ≤ Sys.lq.cost dev ωdev T := by
      rw [hsplit, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h1 : cQ * ‖ωdev k‖ ^ 2 ≤ quadForm Sys.lq.Ru (ωdev k) := hQb _
      have h2 : 0 ≤ quadForm Sys.lq.Qs (Sys.lq.traj dev ωdev k) :=
        Sys.lq.hQs.quadForm_nonneg _
      linarith
    -- terminal bound on the deviation trajectory through the injection
    have hrec : ∀ k, Sys.lq.traj dev ωdev (k + 1)
        = Sys.fullA *ᵥ Sys.lq.traj dev ωdev k + Sys.lq.B *ᵥ ωdev k :=
      fun k => Sys.lq.traj_succ dev ωdev k
    have hxT := hinj (fun k => Sys.lq.traj dev ωdev k) ωdev hrec T
    simp only [LQSystem.traj_zero] at hxT
    have hxT2 : ‖Sys.lq.traj dev ωdev T‖ ^ 2
        ≤ Cd * (η T * ‖a‖ ^ 2) := by
      have hν2 : ∑ k ∈ Finset.range T,
          ‖Sys.fullC *ᵥ Sys.lq.traj dev ωdev k‖ ^ 2
            ≤ (1 / cR) * Sys.fieCost 0 dev ωdev T := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hcR]
        calc (∑ k ∈ Finset.range T,
            ‖Sys.fullC *ᵥ Sys.lq.traj dev ωdev k‖ ^ 2) * cR
            = cR * ∑ k ∈ Finset.range T,
              ‖Sys.fullC *ᵥ Sys.lq.traj dev ωdev k‖ ^ 2 := mul_comm _ _
        _ ≤ Sys.lq.cost dev ωdev T := hsumν
        _ ≤ 1 * Sys.fieCost 0 dev ωdev T := by
            rw [one_mul]; exact hcost_le
      have hω2 : ∑ k ∈ Finset.range T, ‖ωdev k‖ ^ 2
          ≤ (1 / cQ) * Sys.fieCost 0 dev ωdev T := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hcQ]
        calc (∑ k ∈ Finset.range T, ‖ωdev k‖ ^ 2) * cQ
            = cQ * ∑ k ∈ Finset.range T, ‖ωdev k‖ ^ 2 := mul_comm _ _
        _ ≤ Sys.lq.cost dev ωdev T := hsumω
        _ ≤ 1 * Sys.fieCost 0 dev ωdev T := by
            rw [one_mul]; exact hcost_le
      have hd2 : ‖dev‖ ^ 2 ≤ (Cr₁ + Cr₂) * Sys.fieCost 0 dev ωdev T := by
        have h1 : (Cr₁ + Cr₂) * Sys.priorPenalty 0 dev
            ≤ (Cr₁ + Cr₂) * Sys.fieCost 0 dev ωdev T :=
          mul_le_mul_of_nonneg_left hprior_le (by positivity)
        linarith
      have hsum2 : ∑ k ∈ Finset.range T,
          (‖Sys.fullC *ᵥ Sys.lq.traj dev ωdev k‖ ^ 2 + ‖ωdev k‖ ^ 2)
            = (∑ k ∈ Finset.range T,
              ‖Sys.fullC *ᵥ Sys.lq.traj dev ωdev k‖ ^ 2)
              + ∑ k ∈ Finset.range T, ‖ωdev k‖ ^ 2 :=
        Finset.sum_add_distrib
      calc ‖Sys.lq.traj dev ωdev T‖ ^ 2
          ≤ cinj * (‖dev‖ ^ 2 + ∑ k ∈ Finset.range T,
            (‖Sys.fullC *ᵥ Sys.lq.traj dev ωdev k‖ ^ 2
              + ‖ωdev k‖ ^ 2)) := hxT
      _ ≤ cinj * ((Cr₁ + Cr₂ + 1 / cR + 1 / cQ)
            * Sys.fieCost 0 dev ωdev T) := by
          refine mul_le_mul_of_nonneg_left ?_ hcinj.le
          rw [hsum2]
          nlinarith
      _ = Cd * Sys.fieCost 0 dev ωdev T := by rw [hCd]; ring
      _ ≤ Cd * (η T * ‖a‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hdevcost hCd0.le
    have hxTn : ‖Sys.lq.traj dev ωdev T‖
        ≤ Real.sqrt (Cd * η T) * ‖a‖ := by
      have h1 : ‖Sys.lq.traj dev ωdev T‖
          = Real.sqrt (‖Sys.lq.traj dev ωdev T‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      rw [h1]
      have h2 : Cd * (η T * ‖a‖ ^ 2) = Cd * η T * ‖a‖ ^ 2 := by ring
      calc Real.sqrt (‖Sys.lq.traj dev ωdev T‖ ^ 2)
          ≤ Real.sqrt (Cd * η T * ‖a‖ ^ 2) :=
            Real.sqrt_le_sqrt (by linarith [h2 ▸ hxT2])
      _ = Real.sqrt (Cd * η T) * ‖a‖ := by
          rw [Real.sqrt_mul (mul_nonneg hCd0.le (hηnn T)),
            Real.sqrt_sq (norm_nonneg a)]
    -- terminal identity: optimum = candidate − deviation
    have hterm : Sys.optTerm a T
        = Sum.elim (Sys.lqRed.Acl (Sys.Pinf hC1) ^ T
            *ᵥ blk₁ (Sys.optInitLim a)) 0
          - Sys.lq.traj dev ωdev T := by
      have h1 : Sys.optInitLim a = Sys.optInit a T + dev := by
        rw [hdev]; abel
      have h2 : Sys.ctrlInf hC1 a = fun j =>
          Sys.lq.optCtrl (Sys.optInit a T) T j + ωdev j := by
        funext j
        simp only [hωdev]
        abel
      have h3 := Sys.traj_ctrlInf hC1 hC2 a T
      have h5 : Sys.lq.traj (Sys.optInitLim a) (Sys.ctrlInf hC1 a) T
          = Sys.optTerm a T + Sys.lq.traj dev ωdev T := by
        conv_lhs => rw [h1, h2]
        rw [Sys.lq.traj_add]
        congr 1
        rw [Sys.lq.traj_optCtrl]
        rfl
      rw [h5] at h3
      exact eq_sub_of_add_eq h3
    -- assemble
    have hcand : ‖(Sum.elim (Sys.lqRed.Acl (Sys.Pinf hC1) ^ T
        *ᵥ blk₁ (Sys.optInitLim a)) 0 : Fin n₁ ⊕ Fin n₂ → ℝ)‖
          ≤ cA * c₁ * ρ ^ T * ‖a‖ := by
      refine (norm_sumElim_zero_le _).trans ?_
      have h1 : ‖Sys.lqRed.Acl (Sys.Pinf hC1) ^ T
          *ᵥ blk₁ (Sys.optInitLim a)‖
            ≤ ‖Sys.lqRed.Acl (Sys.Pinf hC1) ^ T‖
              * ‖blk₁ (Sys.optInitLim a)‖ :=
        Matrix.linfty_opNorm_mulVec _ _
      have h2 := hpowA T
      have h3 := hξb a
      have h4 : (0:ℝ) ≤ ρ ^ T := pow_nonneg hρ0.le T
      nlinarith [norm_nonneg (blk₁ (Sys.optInitLim a)),
        norm_nonneg (Sys.lqRed.Acl (Sys.Pinf hC1) ^ T), norm_nonneg a]
    rw [hterm]
    calc ‖Sum.elim (Sys.lqRed.Acl (Sys.Pinf hC1) ^ T
          *ᵥ blk₁ (Sys.optInitLim a)) 0 - Sys.lq.traj dev ωdev T‖
        ≤ ‖(Sum.elim (Sys.lqRed.Acl (Sys.Pinf hC1) ^ T
            *ᵥ blk₁ (Sys.optInitLim a)) 0 : Fin n₁ ⊕ Fin n₂ → ℝ)‖
          + ‖Sys.lq.traj dev ωdev T‖ := norm_sub_le _ _
    _ ≤ cA * c₁ * ρ ^ T * ‖a‖ + Real.sqrt (Cd * η T) * ‖a‖ :=
        add_le_add hcand hxTn
    _ = (cA * c₁ * ρ ^ T + Real.sqrt (Cd * η T)) * ‖a‖ := by ring

end FIESystem

end Estimation

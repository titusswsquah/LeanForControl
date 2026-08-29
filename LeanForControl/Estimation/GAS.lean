import LeanForControl.Estimation.Infhor
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

end FIESystem

end Estimation

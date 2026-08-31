import LeanForControl.Estimation.Dare.GapEngine
import Architect

/-!
# The `e₂`-block information recursion (`a02-machinery`-2, `eq:Jrec`)

Under the frame structure — `A` with `e₂`-row `[0 A₂]`, no process
noise reaching `e₂` — the `(2,2)` block of one covariance step is the
pure `A₂`-congruence of the updated block, so (when the block is
positive definite) its information reverses through `A₂⁻¹`:

`J⁺ = A₂⁻ᵀ (J + Ŵ) A₂⁻¹`, `Ŵ := (U(Σ)|₂₂)⁻¹ − (Σ|₂₂)⁻¹ ⪰ 0`.

Also here: block positivity is preserved by the update
(`fact:update-kernel`, block form) — the diagonal sub-block alone
drives the conclusion, no full positive-definiteness of `Σ` required.
Everything is stated over a generic sum index `ι₁ ⊕ ι₂`.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

variable {ι₁ ι₂ κ : Type*} [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype κ] [DecidableEq κ]

/-! ### Block helpers over the sum index -/

lemma toBlocks₂₂_add (M N : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ) :
    (M + N).toBlocks₂₂ = M.toBlocks₂₂ + N.toBlocks₂₂ := rfl

lemma toBlocks₂₂_sub (M N : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ) :
    (M - N).toBlocks₂₂ = M.toBlocks₂₂ - N.toBlocks₂₂ := rfl

lemma toBlocks₂₂_posSemidef {M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ}
    (hM : M.PosSemidef) : M.toBlocks₂₂.PosSemidef :=
  hM.submatrix Sum.inr

/-- The quadratic form of a zero-extended `e₂`-vector reads the
`(2,2)` block. -/
lemma quadForm_elim_zero (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ)
    (v : ι₂ → ℝ) :
    quadForm M (Sum.elim (0 : ι₁ → ℝ) v) = quadForm M.toBlocks₂₂ v := by
  simp [quadForm, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Matrix.toBlocks₂₂]

/-- The `(2,2)` block of the frame conjugation: with `A₂₁ = 0`,
`(A·M·Aᵀ)|₂₂ = A₂·M|₂₂·A₂ᵀ`. -/
lemma conj_toBlocks₂₂ (A₁ : Matrix ι₁ ι₁ ℝ) (A₁₂ : Matrix ι₁ ι₂ ℝ)
    (A₂ : Matrix ι₂ ι₂ ℝ) (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ) :
    (Matrix.fromBlocks A₁ A₁₂ 0 A₂ * M
        * (Matrix.fromBlocks A₁ A₁₂ 0 A₂)ᵀ).toBlocks₂₂
      = A₂ * M.toBlocks₂₂ * A₂ᵀ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]
  simp [Matrix.transpose_zero]

/-! ### Block positivity is preserved by the update -/

/-- `fact:update-kernel`, block form: `Σ|₂₂ ≻ 0 ⇒ U(Σ)|₂₂ ≻ 0` — the
diagonal sub-block alone drives the conclusion. -/
lemma updM_toBlocks₂₂_posDef {C : Matrix κ (ι₁ ⊕ ι₂) ℝ}
    {R : Matrix κ κ ℝ} {Sg : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ}
    (hR : R.PosDef) (hSg : Sg.PosSemidef)
    (h22 : Sg.toBlocks₂₂.PosDef) :
    (updM C R Sg).toBlocks₂₂.PosDef := by
  have hU := updM_posSemidef (C := C) hR hSg
  have hU22 : (updM C R Sg).toBlocks₂₂.PosSemidef :=
    toBlocks₂₂_posSemidef hU
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hU22.1 fun v hv => ?_
  rcases lt_or_eq_of_le (hU22.quadForm_nonneg v) with h | h
  · exact h
  · exfalso
    have hker : updM C R Sg *ᵥ Sum.elim (0 : ι₁ → ℝ) v = 0 :=
      hU.mulVec_eq_zero_of_quadForm_eq_zero
        (by rw [quadForm_elim_zero]; exact h.symm)
    have hSgker : Sg *ᵥ Sum.elim (0 : ι₁ → ℝ) v = 0 :=
      (updM_mulVec_eq_zero_iff hR hSg).mp hker
    have hq : quadForm Sg.toBlocks₂₂ v = 0 := by
      rw [← quadForm_elim_zero, quadForm, hSgker, dotProduct_zero]
    exact absurd hq (ne_of_gt (h22.quadForm_pos hv))

/-! ### The `(2,2)` step identity and the information recursion -/

variable {C : Matrix κ (ι₁ ⊕ ι₂) ℝ} {R : Matrix κ κ ℝ}
variable {A₁ : Matrix ι₁ ι₁ ℝ} {A₁₂ : Matrix ι₁ ι₂ ℝ}
variable {A₂ : Matrix ι₂ ι₂ ℝ}
variable {Qw Sg : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ}

/-- **The unconditional `(2,2)`-block identity** (`app:machinery`-2):
`R(Σ)|₂₂ = A₂·U(Σ)|₂₂·A₂ᵀ`, valid for every `Σ ⪰ 0`. -/
theorem dareStep_toBlocks₂₂ (hQw : Qw.toBlocks₂₂ = 0) :
    (dareStep C R (Matrix.fromBlocks A₁ A₁₂ 0 A₂) Qw Sg).toBlocks₂₂
      = A₂ * (updM C R Sg).toBlocks₂₂ * A₂ᵀ := by
  unfold dareStep
  rw [toBlocks₂₂_add, hQw, add_zero, conj_toBlocks₂₂]

/-- Block positivity propagates along the recursion
(`lem:structure`-3 shape): `Σ|₂₂ ≻ 0` and `A₂` nonsingular give
`R(Σ)|₂₂ ≻ 0`. -/
theorem dareStep_toBlocks₂₂_posDef (hR : R.PosDef) (hSg : Sg.PosSemidef)
    (h22 : Sg.toBlocks₂₂.PosDef) (hQw : Qw.toBlocks₂₂ = 0)
    (hA₂ : IsUnit A₂.det) :
    (dareStep C R (Matrix.fromBlocks A₁ A₁₂ 0 A₂) Qw Sg).toBlocks₂₂.PosDef := by
  rw [dareStep_toBlocks₂₂ hQw]
  have hU22 := updM_toBlocks₂₂_posDef (C := C) hR hSg h22
  have hherm : (A₂ * (updM C R Sg).toBlocks₂₂ * A₂ᵀ).IsHermitian := by
    have h := hU22.posSemidef.mul_mul_conjTranspose_same A₂
    rw [show A₂ᴴ = A₂ᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h
    exact h.1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun v hv => ?_
  have hAv : A₂ᵀ *ᵥ v ≠ 0 := by
    intro h0
    apply hv
    have h1 := congrArg (fun w => (A₂ᵀ)⁻¹ *ᵥ w) h0
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose]),
      Matrix.one_mulVec] at h1
  have hq : quadForm (updM C R Sg).toBlocks₂₂ (A₂ᵀ *ᵥ v)
      = quadForm (A₂ * (updM C R Sg).toBlocks₂₂ * A₂ᵀ) v := by
    rw [quadForm_mulVec, Matrix.transpose_transpose]
  show 0 < quadForm (A₂ * (updM C R Sg).toBlocks₂₂ * A₂ᵀ) v
  rw [← hq]
  exact hU22.quadForm_pos hAv

/-- **`eq:Jrec`**: with `Σ|₂₂ ≻ 0`, the `e₂`-block information
reverses through `A₂⁻¹`:
`(R(Σ)|₂₂)⁻¹ = A₂⁻ᵀ·(U(Σ)|₂₂)⁻¹·A₂⁻¹`. -/
theorem jRec (hR : R.PosDef) (hSg : Sg.PosSemidef)
    (hQw : Qw.toBlocks₂₂ = 0) :
    ((dareStep C R (Matrix.fromBlocks A₁ A₁₂ 0 A₂) Qw Sg).toBlocks₂₂)⁻¹
      = (A₂⁻¹)ᵀ * ((updM C R Sg).toBlocks₂₂)⁻¹ * A₂⁻¹ := by
  rw [dareStep_toBlocks₂₂ hQw, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

/-- **The information increment is PSD** (`eq:Jrec`'s `Ŵ ⪰ 0`): the
update contracts the block, so its information grows. -/
theorem jRec_increment_posSemidef (hR : R.PosDef) (hSg : Sg.PosSemidef)
    (h22 : Sg.toBlocks₂₂.PosDef) :
    ((((updM C R Sg).toBlocks₂₂)⁻¹ : Matrix ι₂ ι₂ ℝ)
      - (Sg.toBlocks₂₂)⁻¹).PosSemidef := by
  have hU22 := updM_toBlocks₂₂_posDef (C := C) hR hSg h22
  have hcontr : (Sg.toBlocks₂₂ - (updM C R Sg).toBlocks₂₂).PosSemidef := by
    rw [← toBlocks₂₂_sub]
    exact toBlocks₂₂_posSemidef (sub_updM_posSemidef hR hSg)
  exact posSemidef_inv_sub_inv hU22 h22 hcontr

end Dare
end Estimation
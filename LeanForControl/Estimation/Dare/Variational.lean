import LeanForControl.Estimation.Dare.Update
import Architect

/-!
# The innovation-decrease bound (`lem:marginal`(i)'s engine)

One measurement update removes exactly the `S⁻¹`-energy of the
innovation-relevant column,
`quadForm Σ x − quadForm U(Σ) x = quadForm S⁻¹ (CΣx)`, and
Cauchy–Schwarz floors that in every output direction:

`quadForm U(Σ) x ≤ quadForm Σ x − (bᵀCΣx)²/(bᵀSb)`.

This is the per-step decrease that the repaired `lem:marginal`
telescopes. (It is equivalent to the deck's Joseph square at a
rank-one gain, but shorter: `sub_updM_eq` + the PSD Cauchy–Schwarz
of `QuadForm.lean`.)
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ} {Sg : Matrix ι ι ℝ}

/-- **The exact decrease**: `quadForm Σ x − quadForm U(Σ) x =
quadForm S⁻¹ (CΣx)`. -/
lemma quadForm_sub_updM_eq (hSg : Sg.PosSemidef) (x : ι → ℝ) :
    quadForm Sg x - quadForm (updM C R Sg) x
      = quadForm (innov C R Sg)⁻¹ (C *ᵥ (Sg *ᵥ x)) := by
  have h1 : quadForm Sg x - quadForm (updM C R Sg) x
      = quadForm (Sg - updM C R Sg) x := by
    rw [quadForm_sub_matrix]
  rw [h1, sub_updM_eq]
  have h2 : (Sg * Cᵀ * (innov C R Sg)⁻¹ * (C * Sg)) *ᵥ x
      = (Sg * Cᵀ) *ᵥ ((innov C R Sg)⁻¹ *ᵥ (C *ᵥ (Sg *ᵥ x))) := by
    simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [quadForm, h2, dotProduct_mulVec_eq, Matrix.transpose_mul,
    Matrix.transpose_transpose, hSg.1.transpose_eq_self]
  rw [show (C * Sg) *ᵥ x = C *ᵥ (Sg *ᵥ x) from
    (Matrix.mulVec_mulVec _ _ _).symm]
  rfl

/-- **The innovation-decrease bound**: for every output direction
`b ≠ 0`,
`quadForm U(Σ) x ≤ quadForm Σ x − (b⬝(CΣx))²/(quadForm S b)`. -/
theorem updM_quadForm_le_sub (hR : R.PosDef) (hSg : Sg.PosSemidef)
    (x : ι → ℝ) {b : κ → ℝ} (hb : b ≠ 0) :
    quadForm (updM C R Sg) x
      ≤ quadForm Sg x
        - (b ⬝ᵥ (C *ᵥ (Sg *ᵥ x))) ^ 2
            / quadForm (innov C R Sg) b := by
  have hSb : 0 < quadForm (innov C R Sg) b :=
    (innov_posDef hR hSg).quadForm_pos hb
  have hdec := quadForm_sub_updM_eq (C := C) (R := R) hSg x
  set r := C *ᵥ (Sg *ᵥ x) with hr
  -- Cauchy–Schwarz: (b⬝r)² ≤ (quadForm S b)(quadForm S⁻¹ r)
  have hcs : (b ⬝ᵥ r) ^ 2
      ≤ quadForm (innov C R Sg) b * quadForm (innov C R Sg)⁻¹ r := by
    have h := sq_dotProduct_mulVec_le
      ((innov_posDef (C := C) hR hSg).inv.posSemidef)
      (innov C R Sg *ᵥ b) r
    have h1 : r ⬝ᵥ ((innov C R Sg)⁻¹ *ᵥ (innov C R Sg *ᵥ b))
        = r ⬝ᵥ b := by
      rw [Matrix.mulVec_mulVec, innov_inv_mul hR hSg,
        Matrix.one_mulVec]
    have h2 : quadForm (innov C R Sg)⁻¹ (innov C R Sg *ᵥ b)
        = quadForm (innov C R Sg) b := by
      rw [quadForm_mulVec, innov_transpose hR hSg,
        innov_mul_inv hR hSg, Matrix.one_mul]
    rw [h1, h2] at h
    calc (b ⬝ᵥ r) ^ 2 = (r ⬝ᵥ b) ^ 2 := by rw [dotProduct_comm]
    _ ≤ quadForm (innov C R Sg)⁻¹ r * quadForm (innov C R Sg) b := h
    _ = quadForm (innov C R Sg) b * quadForm (innov C R Sg)⁻¹ r :=
        mul_comm _ _
  have hfloor : (b ⬝ᵥ r) ^ 2 / quadForm (innov C R Sg) b
      ≤ quadForm (innov C R Sg)⁻¹ r := by
    rw [div_le_iff₀ hSb]
    calc (b ⬝ᵥ r) ^ 2
        ≤ quadForm (innov C R Sg) b * quadForm (innov C R Sg)⁻¹ r :=
          hcs
    _ = quadForm (innov C R Sg)⁻¹ r * quadForm (innov C R Sg) b := by
          ring
  linarith [hdec, hfloor]

end Dare
end Estimation
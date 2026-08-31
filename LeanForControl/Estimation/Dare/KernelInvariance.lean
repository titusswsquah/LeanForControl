import LeanForControl.Estimation.Dare.BlockInfo
import Architect

/-!
# Kernel invariance at a covariance fixed point

The honest mechanism behind the deck's "a kernel direction of `Σ∞`
stays unreflected" heuristic (`lem:structure`-1 / `lem:structure-marg`,
risk R3 of the sprint plan): at a PSD fixed point `Σ∞` of the
covariance step with `Q_w = GQGᵀ`, `Q ≻ 0`,

1. `ker Σ∞` is `Aᵀ`-invariant,
2. `ker Σ∞ ⊆ ker Gᵀ`,
3. **`F∞ᵀ agrees with `Aᵀ` on `ker Σ∞`** — the filter does not act
   on directions it knows exactly.

(3) needs only `Σ∞(Aᵀw) = 0` and symmetry, no fixed point. Together
these hand `F∞ᵀ` an invariant subspace on which it acts as the raw
dynamics — which is how a nontrivial antistable kernel forces
`ρ(F∞) > 1` (assembled in `StrongSolution.lean`). Numeric check:
scratchpad `check_r3.py`.

Also here: the block-embedding kernel lemmas (a `(2,2)`-block kernel
vector, zero-extended, lies in the full kernel, and conversely).
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

/-! ### Block-embedding kernel lemmas -/

section Blocks

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂]

/-- A `(2,2)`-block kernel vector, zero-extended, lies in the full
kernel (PSD needed: the quadratic form vanishes, hence the vector). -/
lemma mulVec_elim_eq_zero_of_toBlocks₂₂
    {M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ} (hM : M.PosSemidef)
    {v : ι₂ → ℝ} (hv : M.toBlocks₂₂ *ᵥ v = 0) :
    M *ᵥ Sum.elim (0 : ι₁ → ℝ) v = 0 := by
  refine hM.mulVec_eq_zero_of_quadForm_eq_zero ?_
  rw [quadForm_elim_zero, quadForm, hv, dotProduct_zero]

/-- Conversely, the `(2,2)` component of a full-kernel equation reads
the block (pure computation, no PSD). -/
lemma toBlocks₂₂_mulVec_eq_zero
    {M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ} {v : ι₂ → ℝ}
    (h : M *ᵥ Sum.elim (0 : ι₁ → ℝ) v = 0) :
    M.toBlocks₂₂ *ᵥ v = 0 := by
  funext j
  have h1 := congrFun h (Sum.inr j)
  simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.toBlocks₂₂] using h1

end Blocks

/-! ### Kernel invariance at the fixed point -/

variable {ι κ κg : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype κg]

variable {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}
variable {A Qw Sinf : Matrix ι ι ℝ}

/-- **Kernel invariance and noise annihilation** at a PSD fixed point
with `Q_w = GQGᵀ`, `Q ≻ 0`: for `w ∈ ker Σ∞`,
`Aᵀw ∈ ker Σ∞` and `Gᵀw = 0`. -/
theorem ker_fixedPoint (hR : R.PosDef) (hSinf : Sinf.PosSemidef)
    (hfix : dareStep C R A Qw Sinf = Sinf)
    {G : Matrix ι κg ℝ} {Q : Matrix κg κg ℝ} (hQ : Q.PosDef)
    (hQw : Qw = G * Q * Gᵀ)
    {w : ι → ℝ} (hw : Sinf *ᵥ w = 0) :
    Sinf *ᵥ (Aᵀ *ᵥ w) = 0 ∧ Gᵀ *ᵥ w = 0 := by
  -- split 0 = w'Σ∞w = ‖·‖²_{U} (Aᵀw) + ‖·‖²_Q (Gᵀw)
  have hq0 : quadForm Sinf w = 0 := by
    rw [quadForm, hw, dotProduct_zero]
  have hsplit : quadForm (updM C R Sinf) (Aᵀ *ᵥ w)
      + quadForm Q (Gᵀ *ᵥ w) = 0 := by
    have h1 : quadForm (updM C R Sinf) (Aᵀ *ᵥ w)
        = quadForm (A * updM C R Sinf * Aᵀ) w := by
      rw [quadForm_mulVec, Matrix.transpose_transpose]
    have h2 : quadForm Q (Gᵀ *ᵥ w) = quadForm Qw w := by
      rw [quadForm_mulVec, Matrix.transpose_transpose, hQw]
    rw [h1, h2, ← quadForm_add_matrix]
    have h3 : A * updM C R Sinf * Aᵀ + Qw = Sinf := by
      conv_rhs => rw [← hfix]
      rfl
    rw [h3, hq0]
  have hU : (0 : ℝ) ≤ quadForm (updM C R Sinf) (Aᵀ *ᵥ w) :=
    (updM_posSemidef hR hSinf).quadForm_nonneg _
  have hQq : (0 : ℝ) ≤ quadForm Q (Gᵀ *ᵥ w) :=
    hQ.posSemidef.quadForm_nonneg _
  constructor
  · -- U(Σ∞)(Aᵀw) = 0, then kernel preservation
    have hU0 : quadForm (updM C R Sinf) (Aᵀ *ᵥ w) = 0 := by linarith
    have hUker : updM C R Sinf *ᵥ (Aᵀ *ᵥ w) = 0 :=
      (updM_posSemidef hR hSinf).mulVec_eq_zero_of_quadForm_eq_zero hU0
    exact (updM_mulVec_eq_zero_iff hR hSinf).mp hUker
  · -- Q ≻ 0 forces Gᵀw = 0
    have hQ0 : quadForm Q (Gᵀ *ᵥ w) = 0 := by linarith
    by_contra hne
    exact absurd hQ0 (ne_of_gt (hQ.quadForm_pos hne))

/-- **The filter does not act on exactly-known directions**:
`F∞ᵀw = Aᵀw` whenever `Σ∞(Aᵀw) = 0` (no fixed point needed — pure
gain algebra plus symmetry). -/
theorem errMap_transpose_mulVec_eq (hR : R.PosDef)
    (hSinf : Sinf.PosSemidef) {w : ι → ℝ}
    (hw' : Sinf *ᵥ (Aᵀ *ᵥ w) = 0) :
    (errMap C R A Sinf)ᵀ *ᵥ w = Aᵀ *ᵥ w := by
  have hKt : (kGain C R Sinf)ᵀ
      = (innov C R Sinf)⁻¹ * (C * Sinf) := by
    unfold kGain
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, innov_inv_transpose hR hSinf,
      hSinf.1.transpose_eq_self]
  have hexp : (errMap C R A Sinf)ᵀ
      = Aᵀ - Cᵀ * ((innov C R Sinf)⁻¹ * (C * Sinf)) * Aᵀ := by
    unfold errMap
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_mul, hKt, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc]
  rw [hexp, Matrix.sub_mulVec]
  have h0 : (Cᵀ * ((innov C R Sinf)⁻¹ * (C * Sinf)) * Aᵀ) *ᵥ w
      = 0 := by
    have h1 : (Cᵀ * ((innov C R Sinf)⁻¹ * (C * Sinf)) * Aᵀ) *ᵥ w
        = Cᵀ *ᵥ ((innov C R Sinf)⁻¹ *ᵥ (C *ᵥ (Sinf *ᵥ (Aᵀ *ᵥ w)))) := by
      simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h1, hw']
    simp
  rw [h0, sub_zero]

end Dare
end Estimation
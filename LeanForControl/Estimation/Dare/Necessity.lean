import LeanForControl.Estimation.Dare.MarginalUpper
import Architect

/-!
# Necessity of C2w (`thm:necessity`, `eq:necessity`)

If the recursion from the prior is attracted to the strong solution,
C2w holds. Mechanism (the deck's, verified): a prior-kernel direction
in the antistable coordinates stays exactly known forever — its
zero-energy direction is merely rotated backward by `Aₐᵀ⁻¹` (the
φ-quadratic is nonincreasing from zero) — while the strong solution
is positive definite there (`strong_corner_posDef`), so the gap is
pinned off zero.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

/-- A quadratic form is controlled by the matrix norm. -/
lemma quadForm_le_card_norm {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadForm M x ≤ (Fintype.card ι : ℝ) * ‖M‖ * ‖x‖ ^ 2 := by
  calc quadForm M x ≤ |x ⬝ᵥ (M *ᵥ x)| := le_abs_self _
  _ ≤ ∑ i, |x i| * |(M *ᵥ x) i| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun i _ => le_of_eq ?_
      rw [abs_mul]
  _ ≤ ∑ _i : ι, ‖x‖ * (‖M‖ * ‖x‖) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : |x i| ≤ ‖x‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm x i
      have h2 : |(M *ᵥ x) i| ≤ ‖M‖ * ‖x‖ := by
        rw [← Real.norm_eq_abs]
        exact le_trans (norm_le_pi_norm _ i)
          (Matrix.linfty_opNorm_mulVec _ _)
      have h3 : (0:ℝ) ≤ |x i| := abs_nonneg _
      have h4 : (0:ℝ) ≤ ‖M‖ * ‖x‖ := by positivity
      exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  _ = (Fintype.card ι : ℝ) * ‖x‖ * (‖M‖ * ‖x‖) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  _ = (Fintype.card ι : ℝ) * ‖M‖ * ‖x‖ ^ 2 := by ring

/-- Forward-power cancellation. -/
lemma pow_mul_inv_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : IsUnit M.det) (k : ℕ) :
    M ^ k * (M⁻¹) ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc M ^ (k + 1) * (M⁻¹) ^ (k + 1)
        = M ^ k * (M * M⁻¹) * (M⁻¹) ^ k := by
          rw [pow_succ, pow_succ']
          simp only [Matrix.mul_assoc]
    _ = M ^ k * (M⁻¹) ^ k := by
          rw [Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
    _ = 1 := ih

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The inclusion of the antistable block into `e₂`. -/
def ea2 (na nm : ℕ) : Matrix (Fin na ⊕ Fin nm) (Fin na) ℝ :=
  Matrix.fromRows 1 0

lemma emb2_mul_ea2 :
    emb2 n₁ na nm * ea2 na nm = embA n₁ na nm := by
  ext i j
  cases i with
  | inl i₁ =>
    simp [emb2, ea2, embA, Matrix.mul_apply,
      Matrix.fromRows_apply_inl]
  | inr i₂ =>
    cases i₂ with
    | inl ia =>
      simp [emb2, ea2, embA, Matrix.mul_apply,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
        Matrix.one_apply]
    | inr im =>
      simp [emb2, ea2, embA, Matrix.mul_apply,
        Matrix.fromRows_apply_inr, Matrix.one_apply]

lemma A₂_transpose_mul_ea2 :
    S.A₂ᵀ * ea2 na nm = ea2 na nm * S.Aaᵀ := by
  ext i j
  cases i with
  | inl ia =>
    simp [A₂, ea2, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply]
  | inr im =>
    simp [A₂, ea2, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr]

lemma isUnit_Aat_det : IsUnit S.Aaᵀ.det := by
  rw [Matrix.det_transpose]
  exact S.isUnit_Aa_det

lemma A₂t_inv_mul_ea2 :
    (S.A₂ᵀ)⁻¹ * ea2 na nm = ea2 na nm * (S.Aaᵀ)⁻¹ := by
  have hAa : S.Aaᵀ * (S.Aaᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ S.isUnit_Aat_det
  calc (S.A₂ᵀ)⁻¹ * ea2 na nm
      = (S.A₂ᵀ)⁻¹ * ea2 na nm * (S.Aaᵀ * (S.Aaᵀ)⁻¹) := by
        rw [hAa, Matrix.mul_one]
  _ = (S.A₂ᵀ)⁻¹ * (S.A₂ᵀ * ea2 na nm) * (S.Aaᵀ)⁻¹ := by
        rw [S.A₂_transpose_mul_ea2]
        simp only [Matrix.mul_assoc]
  _ = ea2 na nm * (S.Aaᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ S.isUnit_A₂t_det,
          Matrix.one_mul]

lemma A₂t_inv_pow_mul_ea2 (k : ℕ) :
    ((S.A₂ᵀ)⁻¹) ^ k * ea2 na nm = ea2 na nm * ((S.Aaᵀ)⁻¹) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc ((S.A₂ᵀ)⁻¹) ^ (k + 1) * ea2 na nm
        = ((S.A₂ᵀ)⁻¹) ^ k * ((S.A₂ᵀ)⁻¹ * ea2 na nm) := by
          rw [pow_succ, Matrix.mul_assoc]
    _ = ((S.A₂ᵀ)⁻¹) ^ k * ea2 na nm * (S.Aaᵀ)⁻¹ := by
          rw [S.A₂t_inv_mul_ea2, Matrix.mul_assoc]
    _ = ea2 na nm * ((S.Aaᵀ)⁻¹) ^ k * (S.Aaᵀ)⁻¹ := by rw [ih]
    _ = ea2 na nm * ((S.Aaᵀ)⁻¹) ^ (k + 1) := by
          rw [Matrix.mul_assoc, ← pow_succ]

/-- `embA` acts as the C2w test embedding. -/
lemma embA_mulVec (w : Fin na → ℝ) :
    embA n₁ na nm *ᵥ w
      = Sum.elim (0 : Fin n₁ → ℝ)
          (Sum.elim w (0 : Fin nm → ℝ)) := by
  funext i
  cases i with
  | inl i₁ =>
    simp [embA, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inl]
  | inr i₂ =>
    cases i₂ with
    | inl ia =>
      simp [embA, Matrix.mulVec, dotProduct, Matrix.fromRows_apply_inl,
        Matrix.fromRows_apply_inr, Matrix.one_apply]
    | inr im =>
      simp [embA, Matrix.mulVec, dotProduct,
        Matrix.fromRows_apply_inr]

/-- **A prior-kernel antistable direction stays exactly known**: the
transported quadratic vanishes for all time. -/
lemma dare_quadForm_transported_eq_zero {w : Fin na → ℝ}
    (hker : S.Sig0 *ᵥ Sum.elim (0 : Fin n₁ → ℝ)
      (Sum.elim w (0 : Fin nm → ℝ)) = 0) :
    ∀ T, quadForm (S.dare T)
      (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ (ea2 na nm *ᵥ w))) = 0 := by
  intro T
  induction T with
  | zero =>
    have h1 : emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ 0 *ᵥ (ea2 na nm *ᵥ w))
        = embA n₁ na nm *ᵥ w := by
      rw [pow_zero, Matrix.one_mulVec, Matrix.mulVec_mulVec,
        emb2_mul_ea2]
    rw [h1]
    change (embA n₁ na nm *ᵥ w) ⬝ᵥ (S.Sig0 *ᵥ (embA n₁ na nm *ᵥ w)) = 0
    rw [embA_mulVec, hker, dotProduct_zero]
  | succ T ih =>
    have hpsdT := dareIter_posSemidef (C := S.fullC) (A := S.fullA)
      (Qw := S.Qw) S.hR S.Qw_posSemidef S.Sig0_posSemidef T
    have h1 := S.margPhi_step (L₀ := S.Sig0) T (ea2 na nm *ᵥ w)
    have h2 : quadForm (updM S.fullC S.R (S.dare T))
        (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ (ea2 na nm *ᵥ w)))
        ≤ quadForm (S.dare T)
          (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ (ea2 na nm *ᵥ w))) :=
      quadForm_le_quadForm_of_posSemidef_sub
        (sub_updM_posSemidef S.hR hpsdT) _
    have h3 : 0 ≤ quadForm (updM S.fullC S.R (S.dare T))
        (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ (ea2 na nm *ᵥ w))) :=
      (updM_posSemidef S.hR hpsdT).quadForm_nonneg _
    have h4 : quadForm (S.dare (T + 1))
        (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ (T + 1) *ᵥ (ea2 na nm *ᵥ w)))
        = quadForm (updM S.fullC S.R (S.dare T))
          (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ (ea2 na nm *ᵥ w))) :=
      h1
    rw [h4]
    linarith [ih]

/-- **`thm:necessity`**: attraction to the strong solution forces
C2w. -/
theorem necessity {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hS : S.IsStrongSolution Sinf)
    (hconv : Tendsto (fun T => ‖S.dare T - Sinf‖) atTop (nhds 0)) :
    S.C2w := by
  by_contra hn
  unfold C2w at hn
  push Not at hn
  obtain ⟨w, hker, hwne⟩ := hn
  -- the corner floor of the strong solution
  obtain ⟨ca, hca, hcale⟩ :=
    (S.strong_corner_posDef hS).exists_le_quadForm
  -- the pinned direction at time T
  set wT : ℕ → Fin na → ℝ := fun T => ((S.Aaᵀ)⁻¹) ^ T *ᵥ w with hwT
  have hwTne : ∀ T, wT T ≠ 0 := by
    intro T h0
    apply hwne
    simp only [hwT] at h0
    have h1 : (S.Aaᵀ ^ T * ((S.Aaᵀ)⁻¹) ^ T) *ᵥ w = 0 := by
      rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    rwa [pow_mul_inv_pow S.isUnit_Aat_det, Matrix.one_mulVec] at h1
  -- the transported witness is an embA image
  have hwit : ∀ T,
      emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ (ea2 na nm *ᵥ w))
        = embA n₁ na nm *ᵥ wT T := by
    intro T
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, S.A₂t_inv_pow_mul_ea2, ← Matrix.mul_assoc,
      emb2_mul_ea2, ← Matrix.mulVec_mulVec]
  -- zero energy along the run, full energy at the limit
  have hzero := S.dare_quadForm_transported_eq_zero hker
  have hfloor : ∀ T, ca * ‖wT T‖ ^ 2
      ≤ quadForm (Sinf - S.dare T) (embA n₁ na nm *ᵥ wT T) := by
    intro T
    have h1 : quadForm Sinf (embA n₁ na nm *ᵥ wT T)
        = quadForm ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
            (wT T) := quadForm_mulVec _ _ _
    have h2 := hcale (wT T)
    have h3 : quadForm (S.dare T) (embA n₁ na nm *ᵥ wT T) = 0 := by
      rw [← hwit T]
      exact hzero T
    rw [quadForm_sub_matrix, h3, sub_zero, h1]
    exact h2
  -- but the gap norm crushes the quadratic form
  set K : ℝ := (Fintype.card (ix n₁ na nm) : ℝ)
    * ‖embA n₁ na nm‖ ^ 2 with hK
  have hKpos : 0 ≤ K := by positivity
  have hgap : ∀ T, ca ≤ K * ‖Sinf - S.dare T‖ := by
    intro T
    have h1 := hfloor T
    have h2 : quadForm (Sinf - S.dare T) (embA n₁ na nm *ᵥ wT T)
        ≤ (Fintype.card (ix n₁ na nm) : ℝ) * ‖Sinf - S.dare T‖
          * ‖embA n₁ na nm *ᵥ wT T‖ ^ 2 :=
      quadForm_le_card_norm _ _
    have h3 : ‖embA n₁ na nm *ᵥ wT T‖ ≤ ‖embA n₁ na nm‖ * ‖wT T‖ :=
      Matrix.linfty_opNorm_mulVec _ _
    have h4 : ‖embA n₁ na nm *ᵥ wT T‖ ^ 2
        ≤ ‖embA n₁ na nm‖ ^ 2 * ‖wT T‖ ^ 2 := by
      have h5 := norm_nonneg (embA n₁ na nm *ᵥ wT T)
      nlinarith [h3, norm_nonneg (embA n₁ na nm), norm_nonneg (wT T)]
    have h6 : 0 < ‖wT T‖ ^ 2 := by
      have := norm_pos_iff.mpr (hwTne T)
      positivity
    have h7 : ca * ‖wT T‖ ^ 2
        ≤ K * ‖Sinf - S.dare T‖ * ‖wT T‖ ^ 2 := by
      have h8 : (0:ℝ) ≤ ‖Sinf - S.dare T‖ := norm_nonneg _
      calc ca * ‖wT T‖ ^ 2
          ≤ (Fintype.card (ix n₁ na nm) : ℝ) * ‖Sinf - S.dare T‖
            * ‖embA n₁ na nm *ᵥ wT T‖ ^ 2 := le_trans h1 h2
      _ ≤ (Fintype.card (ix n₁ na nm) : ℝ) * ‖Sinf - S.dare T‖
            * (‖embA n₁ na nm‖ ^ 2 * ‖wT T‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left h4 ?_
          positivity
      _ = K * ‖Sinf - S.dare T‖ * ‖wT T‖ ^ 2 := by
          rw [hK]; ring
    exact le_of_mul_le_mul_right h7 h6
  -- contradiction with convergence
  have hnorm : ∀ T, ‖Sinf - S.dare T‖ = ‖S.dare T - Sinf‖ := by
    intro T
    rw [← norm_neg, neg_sub]
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (hconv.eventually_lt_const
      (show 0 < ca / (K + 1) by positivity)) |>.imp fun T h => h T le_rfl
  have h1 := hgap T
  rw [hnorm T] at h1
  have h2 : ca ≤ K * (ca / (K + 1)) := by
    calc ca ≤ K * ‖S.dare T - Sinf‖ := h1
    _ ≤ K * (ca / (K + 1)) :=
        mul_le_mul_of_nonneg_left hT.le hKpos
  have h3 : K * (ca / (K + 1)) < ca := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < K + 1)]
    nlinarith
  linarith

end DareSystem

end Dare
end Estimation

import LeanForControl.Estimation.Dare.Marginal
import LeanForControl.Estimation.Dare.Variational
import LeanForControl.Estimation.Dare.Convolution
import Architect

/-!
# The repaired `lem:marginal`: `Σ̄_T|ₘₘ → 0` (semisimple marginal)

The Lean verification of the deck's repaired route: along any run
from a PSD seed, the backward-transported uncontrollable columns
`Y_T := Σ̄_T E₂ A₂^{-Tᵀ}` have square-summable output energy (the
innovation-decrease telescope of `Variational.lean`), ride the error
map, and die through the detectability injection; power-boundedness
of `Aₘ` closes `Σ̄_T|ₘₘ → 0`. No information coordinates, no
injected-information floors, no corner-positivity hypothesis, and
only *forward* power-boundedness of `Aₘ` is consumed.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

/-! ### Norm helpers -/

section NormHelpers

variable {ι κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ']

/-- Entries of a PSD matrix with a uniform quadratic-form bound. -/
lemma posSemidef_entry_abs_le {M : Matrix ι ι ℝ} (hM : M.PosSemidef)
    {b : ℝ} (hb : 0 ≤ b) (hq : ∀ x, quadForm M x ≤ b * ‖x‖ ^ 2)
    (i j : ι) :
    |M i j| ≤ b := by
  have hqb : ∀ v : ι → ℝ, ‖v‖ ≤ 1 → quadForm M v ≤ b := by
    intro v hv
    calc quadForm M v ≤ b * ‖v‖ ^ 2 := hq v
    _ ≤ b * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hv) hb
    _ = b := mul_one b
  have hsingle : ∀ k : ι, ‖(Pi.single k 1 : ι → ℝ)‖ ≤ 1 := by
    intro k
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k' => ?_
    rcases eq_or_ne k' k with rfl | hk
    · simp
    · simp [Pi.single_apply, hk]
  by_cases hij : i = j
  · subst hij
    have h1 : M i i = quadForm M (Pi.single i 1) := by
      simp [quadForm, Matrix.mulVec, dotProduct, Pi.single_apply,
        mul_ite, Finset.sum_ite_eq']
    rw [abs_of_nonneg (by rw [h1]; exact hM.quadForm_nonneg _)]
    rw [h1]
    exact hqb _ (hsingle i)
  · have hpol : 2 * M i j
        = quadForm M (Pi.single i 1 + Pi.single j 1)
          - quadForm M (Pi.single i 1)
          - quadForm M (Pi.single j 1) := by
      rw [quadForm_add_of_isHermitian hM.1]
      have h1 : (Pi.single i 1 : ι → ℝ) ⬝ᵥ (M *ᵥ Pi.single j 1)
          = M i j := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
          Finset.sum_ite_eq']
      rw [h1]
      ring
    have hnorm1 : ‖(Pi.single i 1 + Pi.single j 1 : ι → ℝ)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
      rcases eq_or_ne k i with rfl | hki
      · simp [Pi.single_apply, hij, Ne.symm hij]
      · rcases eq_or_ne k j with rfl | hkj
        · simp [Pi.single_apply, hki]
        · simp [Pi.single_apply, hki, hkj]
    have hq1 := hqb _ hnorm1
    have hq1' := hM.quadForm_nonneg (Pi.single i 1 + Pi.single j 1)
    have hq2 := hM.quadForm_nonneg (Pi.single i 1)
    have hq3 := hM.quadForm_nonneg (Pi.single j 1)
    have hq4 := hqb _ (hsingle i)
    have hq5 := hqb _ (hsingle j)
    rw [abs_le]
    constructor <;> linarith [hpol]

/-- The `L∞` operator norm is at most the total absolute entry sum. -/
lemma linfty_opNorm_le_sum_abs (M : Matrix ι κ' ℝ) :
    ‖M‖ ≤ ∑ i, ∑ j, |M i j| := by
  have h : ‖M‖₊ ≤ ∑ i, ∑ j, ‖M i j‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    exact Finset.single_le_sum
      (f := fun i' => ∑ j, ‖M i' j‖₊)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  calc ‖M‖ = ((‖M‖₊ : ℝ)) := rfl
  _ ≤ ((∑ i, ∑ j, ‖M i j‖₊ : NNReal) : ℝ) := by exact_mod_cast h
  _ = ∑ i, ∑ j, |M i j| := by
      push_cast
      simp [Real.norm_eq_abs]

/-- A PSD matrix with a uniform quadratic-form bound has bounded
norm. -/
lemma posSemidef_norm_le_of_quadForm_le {M : Matrix ι ι ℝ}
    (hM : M.PosSemidef) {b : ℝ} (hb : 0 ≤ b)
    (hq : ∀ x, quadForm M x ≤ b * ‖x‖ ^ 2) :
    ‖M‖ ≤ (Fintype.card ι : ℝ) ^ 2 * b := by
  calc ‖M‖ ≤ ∑ i, ∑ j, |M i j| := linfty_opNorm_le_sum_abs M
  _ ≤ ∑ _i : ι, ∑ _j : ι, b := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        posSemidef_entry_abs_le hM hb hq i j
  _ = (Fintype.card ι : ℝ) ^ 2 * b := by
      simp [Finset.sum_const, Finset.card_univ]
      ring

/-- Cancellation of inverse powers. -/
lemma inv_pow_mul_pow {M : Matrix ι ι ℝ} (hM : IsUnit M.det) (k : ℕ) :
    (M⁻¹) ^ k * M ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc (M⁻¹) ^ (k + 1) * M ^ (k + 1)
        = (M⁻¹) ^ k * (M⁻¹ * M) * M ^ k := by
          rw [pow_succ, pow_succ']
          simp only [Matrix.mul_assoc]
    _ = (M⁻¹) ^ k * M ^ k := by
          rw [Matrix.nonsing_inv_mul _ hM, Matrix.mul_one]
    _ = 1 := ih

end NormHelpers

/-! ### The `e₂`-inclusion plumbing -/

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The inclusion of the whole uncontrollable block,
`E₂ : ℝ^{e₂} → e₁ ⊕ e₂`. -/
def emb2 (n₁ na nm : ℕ) : Matrix (ix n₁ na nm) (Fin na ⊕ Fin nm) ℝ :=
  Matrix.fromRows 0 1

lemma fullA_transpose_mul_emb2 :
    S.fullAᵀ * emb2 n₁ na nm = emb2 n₁ na nm * S.A₂ᵀ := by
  ext i j
  cases i with
  | inl i₁ =>
    simp [emb2, fullA, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr]
  | inr i₂ =>
    simp [emb2, fullA, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply]

lemma emb2_transpose_mul_fullG :
    (emb2 n₁ na nm)ᵀ * S.fullG = 0 := by
  ext i j
  simp [emb2, fullG, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply]

lemma Qw_mul_emb2 : S.Qw * emb2 n₁ na nm = 0 := by
  unfold Qw
  have h : S.fullGᵀ * emb2 n₁ na nm
      = ((emb2 n₁ na nm)ᵀ * S.fullG)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc S.fullG * S.Q * S.fullGᵀ * emb2 n₁ na nm
      = S.fullG * S.Q * (S.fullGᵀ * emb2 n₁ na nm) := by
        simp only [Matrix.mul_assoc]
  _ = 0 := by
      rw [h, S.emb2_transpose_mul_fullG]
      simp

lemma emb2_Qw_corner :
    (emb2 n₁ na nm)ᵀ * S.Qw * emb2 n₁ na nm = 0 := by
  rw [Matrix.mul_assoc, S.Qw_mul_emb2, Matrix.mul_zero]

/-- The inclusion of the marginal block into `e₂`. -/
def em2 (na nm : ℕ) : Matrix (Fin na ⊕ Fin nm) (Fin nm) ℝ :=
  Matrix.fromRows 0 1

lemma emb2_mul_em2 :
    emb2 n₁ na nm * em2 na nm = embM n₁ na nm := by
  ext i j
  cases i with
  | inl i₁ =>
    simp [emb2, em2, embM, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
  | inr i₂ =>
    cases i₂ with
    | inl ia =>
      simp [emb2, em2, embM, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
        Matrix.one_apply]
    | inr im =>
      simp [emb2, em2, embM, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
        Matrix.one_apply]

lemma A₂_transpose_mul_em2 :
    S.A₂ᵀ * em2 na nm = em2 na nm * S.Amᵀ := by
  ext i j
  cases i with
  | inl ia =>
    simp [A₂, em2, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr]
  | inr im =>
    simp [A₂, em2, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply]

lemma isUnit_A₂t_det : IsUnit S.A₂ᵀ.det := by
  rw [Matrix.det_transpose]
  exact S.isUnit_A₂_det

lemma A₂t_mul_inv : S.A₂ᵀ * (S.A₂ᵀ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ S.isUnit_A₂t_det

lemma A₂t_inv_mul_em2 :
    (S.A₂ᵀ)⁻¹ * em2 na nm = em2 na nm * (S.Amᵀ)⁻¹ := by
  have hAm : S.Amᵀ * (S.Amᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by
      rw [Matrix.det_transpose]; exact S.isUnit_Am_det)
  calc (S.A₂ᵀ)⁻¹ * em2 na nm
      = (S.A₂ᵀ)⁻¹ * em2 na nm * (S.Amᵀ * (S.Amᵀ)⁻¹) := by
        rw [hAm, Matrix.mul_one]
  _ = (S.A₂ᵀ)⁻¹ * (S.A₂ᵀ * em2 na nm) * (S.Amᵀ)⁻¹ := by
        rw [S.A₂_transpose_mul_em2]
        simp only [Matrix.mul_assoc]
  _ = em2 na nm * (S.Amᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ S.isUnit_A₂t_det,
          Matrix.one_mul]

lemma A₂t_inv_pow_mul_em2 (k : ℕ) :
    ((S.A₂ᵀ)⁻¹) ^ k * em2 na nm = em2 na nm * ((S.Amᵀ)⁻¹) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc ((S.A₂ᵀ)⁻¹) ^ (k + 1) * em2 na nm
        = ((S.A₂ᵀ)⁻¹) ^ k * ((S.A₂ᵀ)⁻¹ * em2 na nm) := by
          rw [pow_succ, Matrix.mul_assoc]
    _ = ((S.A₂ᵀ)⁻¹) ^ k * em2 na nm * (S.Amᵀ)⁻¹ := by
          rw [S.A₂t_inv_mul_em2, Matrix.mul_assoc]
    _ = em2 na nm * ((S.Amᵀ)⁻¹) ^ k * (S.Amᵀ)⁻¹ := by rw [ih]
    _ = em2 na nm * ((S.Amᵀ)⁻¹) ^ (k + 1) := by
          rw [Matrix.mul_assoc, ← pow_succ]

lemma A₂t_mul_inv_pow_succ (T : ℕ) :
    S.A₂ᵀ * ((S.A₂ᵀ)⁻¹) ^ (T + 1) = ((S.A₂ᵀ)⁻¹) ^ T := by
  rw [pow_succ', ← Matrix.mul_assoc, S.A₂t_mul_inv, Matrix.one_mul]

/-! ### The `Y`-recursion and the φ-telescope -/

variable {L₀ : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-- The backward-transported uncontrollable columns (`eq:Ydef`). -/
noncomputable def margY (S : DareSystem n₁ na nm m p)
    (L₀ : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) (T : ℕ) :
    Matrix (ix n₁ na nm) (Fin na ⊕ Fin nm) ℝ :=
  S.dareFrom L₀ T * emb2 n₁ na nm * ((S.A₂ᵀ)⁻¹) ^ T

/-- **The `Y`-recursion**: `Y_{T+1} = A·Y_T − A·K_T·(C·Y_T)`. -/
lemma margY_succ (T : ℕ) :
    S.margY L₀ (T + 1)
      = S.fullA * S.margY L₀ T
        - S.fullA * kGain S.fullC S.R (S.dareFrom L₀ T)
            * (S.fullC * S.margY L₀ T) := by
  unfold margY
  rw [show S.dareFrom L₀ (T + 1)
      = dareStep S.fullC S.R S.fullA S.Qw (S.dareFrom L₀ T) from rfl]
  unfold dareStep
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc (S.Qw) _ _,
    ← Matrix.mul_assoc (S.Qw) _ _, S.Qw_mul_emb2, Matrix.zero_mul,
    add_zero]
  have h1 : S.fullA * updM S.fullC S.R (S.dareFrom L₀ T) * S.fullAᵀ
        * emb2 n₁ na nm * ((S.A₂ᵀ)⁻¹) ^ (T + 1)
      = S.fullA * (updM S.fullC S.R (S.dareFrom L₀ T)
          * emb2 n₁ na nm) * ((S.A₂ᵀ)⁻¹) ^ T := by
    calc S.fullA * updM S.fullC S.R (S.dareFrom L₀ T) * S.fullAᵀ
          * emb2 n₁ na nm * ((S.A₂ᵀ)⁻¹) ^ (T + 1)
        = S.fullA * updM S.fullC S.R (S.dareFrom L₀ T)
            * (S.fullAᵀ * emb2 n₁ na nm)
            * ((S.A₂ᵀ)⁻¹) ^ (T + 1) := by
          simp only [Matrix.mul_assoc]
    _ = S.fullA * updM S.fullC S.R (S.dareFrom L₀ T)
          * (emb2 n₁ na nm * S.A₂ᵀ) * ((S.A₂ᵀ)⁻¹) ^ (T + 1) := by
          rw [S.fullA_transpose_mul_emb2]
    _ = S.fullA * (updM S.fullC S.R (S.dareFrom L₀ T)
          * emb2 n₁ na nm)
          * (S.A₂ᵀ * ((S.A₂ᵀ)⁻¹) ^ (T + 1)) := by
          simp only [Matrix.mul_assoc]
    _ = S.fullA * (updM S.fullC S.R (S.dareFrom L₀ T)
          * emb2 n₁ na nm) * ((S.A₂ᵀ)⁻¹) ^ T := by
          rw [S.A₂t_mul_inv_pow_succ]
  rw [h1]
  have h2 : updM S.fullC S.R (S.dareFrom L₀ T) * emb2 n₁ na nm
      = S.dareFrom L₀ T * emb2 n₁ na nm
        - kGain S.fullC S.R (S.dareFrom L₀ T)
            * (S.fullC * (S.dareFrom L₀ T * emb2 n₁ na nm)) := by
    have h3 : updM S.fullC S.R (S.dareFrom L₀ T)
        = S.dareFrom L₀ T
          - kGain S.fullC S.R (S.dareFrom L₀ T)
              * (S.fullC * S.dareFrom L₀ T) := by
      have h4 := sub_updM_eq (C := S.fullC) (R := S.R)
        (Sg := S.dareFrom L₀ T)
      have h5 : kGain S.fullC S.R (S.dareFrom L₀ T)
            * (S.fullC * S.dareFrom L₀ T)
          = S.dareFrom L₀ T * S.fullCᵀ
            * (innov S.fullC S.R (S.dareFrom L₀ T))⁻¹
            * (S.fullC * S.dareFrom L₀ T) := rfl
      rw [h5, ← h4]
      abel
    rw [h3, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_sub S.fullA, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]

/-- **The φ-step**: the transported quadratic advances by the update
alone. -/
lemma margPhi_step (T : ℕ) (u : Fin na ⊕ Fin nm → ℝ) :
    quadForm (S.dareFrom L₀ (T + 1))
        (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ (T + 1) *ᵥ u))
      = quadForm (updM S.fullC S.R (S.dareFrom L₀ T))
          (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ u)) := by
  rw [show S.dareFrom L₀ (T + 1)
      = dareStep S.fullC S.R S.fullA S.Qw (S.dareFrom L₀ T) from rfl]
  unfold dareStep
  rw [quadForm_add_matrix]
  have hQ : quadForm S.Qw
      (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ (T + 1) *ᵥ u)) = 0 := by
    rw [quadForm_mulVec, S.emb2_Qw_corner, quadForm_zero_matrix]
  rw [hQ, add_zero]
  have h1 : quadForm (updM S.fullC S.R (S.dareFrom L₀ T))
        (S.fullAᵀ *ᵥ (emb2 n₁ na nm
          *ᵥ (((S.A₂ᵀ)⁻¹) ^ (T + 1) *ᵥ u)))
      = quadForm
          (S.fullA * updM S.fullC S.R (S.dareFrom L₀ T) * S.fullAᵀ)
          (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ (T + 1) *ᵥ u)) := by
    rw [quadForm_mulVec, Matrix.transpose_transpose]
  rw [← h1]
  congr 1
  calc S.fullAᵀ *ᵥ (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ (T + 1) *ᵥ u))
      = (S.fullAᵀ * emb2 n₁ na nm)
          *ᵥ (((S.A₂ᵀ)⁻¹) ^ (T + 1) *ᵥ u) := by
        rw [Matrix.mulVec_mulVec]
  _ = (emb2 n₁ na nm * S.A₂ᵀ) *ᵥ (((S.A₂ᵀ)⁻¹) ^ (T + 1) *ᵥ u) := by
        rw [S.fullA_transpose_mul_emb2]
  _ = emb2 n₁ na nm *ᵥ ((S.A₂ᵀ * ((S.A₂ᵀ)⁻¹) ^ (T + 1)) *ᵥ u) := by
        rw [← Matrix.mulVec_mulVec]
        congr 1
        rw [Matrix.mulVec_mulVec]
  _ = emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ u) := by
        rw [S.A₂t_mul_inv_pow_succ]

/-! ### Square-summable output energy (`lem:marginal`(i)) -/

/-- Each output entry of `Y` is square-summable: the φ-telescope. -/
lemma margY_output_entry_summable (hC1 : S.C1) (hL₀ : L₀.PosSemidef)
    (i : Fin p) (j : Fin na ⊕ Fin nm) :
    Summable (fun T => ((S.fullC * S.margY L₀ T) i j) ^ 2) := by
  obtain ⟨bSig, hbSig, hbSigle⟩ := exists_dare_bound (C := S.fullC)
    (A := S.fullA) (Qw := S.Qw) S.hR S.Qw_posSemidef hL₀ hC1
  have hbSigle' : ∀ (T : ℕ) (x : ix n₁ na nm → ℝ),
      quadForm (S.dareFrom L₀ T) x ≤ bSig * ‖x‖ ^ 2 :=
    fun T x => hbSigle T x
  obtain ⟨cR, hcR, hcRle⟩ := exists_quadForm_le S.R
  set sb : ℝ := bSig * ‖S.fullCᵀ *ᵥ Pi.single i 1‖ ^ 2
    + cR * ‖(Pi.single i 1 : Fin p → ℝ)‖ ^ 2 with hsb
  have hsingle : (Pi.single i 1 : Fin p → ℝ) ≠ 0 := by
    intro h0
    have := congrFun h0 i
    simp at this
  -- the innovation form at direction i is uniformly bounded by sb
  have hSb : ∀ T, quadForm (innov S.fullC S.R (S.dareFrom L₀ T))
      (Pi.single i 1) ≤ sb := by
    intro T
    have h1 : quadForm (innov S.fullC S.R (S.dareFrom L₀ T))
        (Pi.single i 1)
        = quadForm (S.dareFrom L₀ T) (S.fullCᵀ *ᵥ Pi.single i 1)
          + quadForm S.R (Pi.single i 1) := by
      unfold innov
      rw [quadForm_add_matrix]
      congr 1
      rw [quadForm_mulVec, Matrix.transpose_transpose]
    rw [h1, hsb]
    have h2 := hbSigle' T (S.fullCᵀ *ᵥ Pi.single i 1)
    have h3 := hcRle (Pi.single i 1)
    linarith
  have hSbpos : 0 < sb := by
    have h1 := (innov_posDef (C := S.fullC) S.hR
      (dareIter_posSemidef (C := S.fullC) (A := S.fullA) (Qw := S.Qw)
        S.hR S.Qw_posSemidef hL₀ 0)).quadForm_pos hsingle
    exact lt_of_lt_of_le h1 (hSb 0)
  -- the per-step decrease
  set phi : ℕ → ℝ := fun T => quadForm (S.dareFrom L₀ T)
    (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ Pi.single j 1)) with hphi
  have hphinn : ∀ T, 0 ≤ phi T := fun T =>
    (dareIter_posSemidef (C := S.fullC) (A := S.fullA) (Qw := S.Qw)
      S.hR S.Qw_posSemidef hL₀ T).quadForm_nonneg _
  have hstep : ∀ T,
      phi (T + 1) ≤ phi T
        - ((S.fullC * S.margY L₀ T) i j) ^ 2 / sb := by
    intro T
    have hpsdT := dareIter_posSemidef (C := S.fullC) (A := S.fullA)
      (Qw := S.Qw) S.hR S.Qw_posSemidef hL₀ T
    have h1 := S.margPhi_step (L₀ := L₀) T (Pi.single j 1)
    have h2 := updM_quadForm_le_sub (C := S.fullC) (R := S.R)
      S.hR hpsdT
      (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ Pi.single j 1)) hsingle
    -- identify the numerator with the (i,j) entry of C·Y
    have h3 : Pi.single i 1 ⬝ᵥ (S.fullC *ᵥ (S.dareFrom L₀ T
          *ᵥ (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ Pi.single j 1))))
        = (S.fullC * S.margY L₀ T) i j := by
      have h4 : S.fullC *ᵥ (S.dareFrom L₀ T
            *ᵥ (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ Pi.single j 1)))
          = (S.fullC * S.margY L₀ T) *ᵥ Pi.single j 1 := by
        unfold margY
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [h4]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
        Finset.sum_ite_eq']
    -- monotone denominators
    have h5 : ((S.fullC * S.margY L₀ T) i j) ^ 2 / sb
        ≤ ((S.fullC * S.margY L₀ T) i j) ^ 2
            / quadForm (innov S.fullC S.R (S.dareFrom L₀ T))
                (Pi.single i 1) := by
      refine div_le_div_of_nonneg_left (sq_nonneg _) ?_ (hSb T)
      exact (innov_posDef S.hR hpsdT).quadForm_pos hsingle
    rw [hphi]
    simp only
    rw [h1]
    calc quadForm (updM S.fullC S.R (S.dareFrom L₀ T))
          (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ Pi.single j 1))
        ≤ quadForm (S.dareFrom L₀ T)
            (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ Pi.single j 1))
          - (Pi.single i 1 ⬝ᵥ (S.fullC *ᵥ (S.dareFrom L₀ T
              *ᵥ (emb2 n₁ na nm
                *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ Pi.single j 1))))) ^ 2
              / quadForm (innov S.fullC S.R (S.dareFrom L₀ T))
                  (Pi.single i 1) := h2
    _ ≤ quadForm (S.dareFrom L₀ T)
          (emb2 n₁ na nm *ᵥ (((S.A₂ᵀ)⁻¹) ^ T *ᵥ Pi.single j 1))
        - ((S.fullC * S.margY L₀ T) i j) ^ 2 / sb := by
        rw [h3] at *
        linarith [h5]
  -- telescoping partial sums
  refine summable_of_sum_range_le (c := sb * phi 0)
    (fun T => sq_nonneg _) fun N => ?_
  have htel : ∀ N, ∑ T ∈ Finset.range N,
      ((S.fullC * S.margY L₀ T) i j) ^ 2 / sb ≤ phi 0 - phi N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := hstep N
      linarith
  have h6 := htel N
  have h7 := hphinn N
  have h8 : ∑ T ∈ Finset.range N,
      ((S.fullC * S.margY L₀ T) i j) ^ 2
      = sb * ∑ T ∈ Finset.range N,
          ((S.fullC * S.margY L₀ T) i j) ^ 2 / sb := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    field_simp
  rw [h8]
  calc sb * ∑ T ∈ Finset.range N,
        ((S.fullC * S.margY L₀ T) i j) ^ 2 / sb
      ≤ sb * (phi 0 - phi N) :=
        mul_le_mul_of_nonneg_left h6 hSbpos.le
  _ ≤ sb * phi 0 := by nlinarith [hphinn N, hSbpos]

/-- The output of `Y` dies in norm. -/
lemma margY_output_tendsto (hC1 : S.C1) (hL₀ : L₀.PosSemidef) :
    Tendsto (fun T => ‖S.fullC * S.margY L₀ T‖) atTop (nhds 0) := by
  have hent : ∀ (i : Fin p) (j : Fin na ⊕ Fin nm),
      Tendsto (fun T => |(S.fullC * S.margY L₀ T) i j|)
        atTop (nhds 0) := by
    intro i j
    have h1 := (S.margY_output_entry_summable hC1 hL₀ i j).tendsto_atTop_zero
    have h2 : (fun T => |(S.fullC * S.margY L₀ T) i j|)
        = fun T => Real.sqrt (((S.fullC * S.margY L₀ T) i j) ^ 2) := by
      funext T
      rw [Real.sqrt_sq_eq_abs]
    rw [h2]
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa [Real.sqrt_zero, Function.comp] using h3
  have hsum : Tendsto (fun T => ∑ i, ∑ j,
      |(S.fullC * S.margY L₀ T) i j|) atTop (nhds 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin p))
      (fun i _ => tendsto_finset_sum
        (Finset.univ : Finset (Fin na ⊕ Fin nm))
        (fun j _ => hent i j))
    simpa using h
  refine squeeze_zero (fun T => norm_nonneg _)
    (fun T => linfty_opNorm_le_sum_abs _) hsum

/-- The uniform gain bound along the run. -/
lemma exists_margGain_bound (hC1 : S.C1) (hL₀ : L₀.PosSemidef) :
    ∃ kb : ℝ, 0 ≤ kb ∧ ∀ T,
      ‖kGain S.fullC S.R (S.dareFrom L₀ T)‖ ≤ kb := by
  obtain ⟨bSig, hbSig, hbSigle⟩ := exists_dare_bound (C := S.fullC)
    (A := S.fullA) (Qw := S.Qw) S.hR S.Qw_posSemidef hL₀ hC1
  obtain ⟨cRi, hcRi, hcRile⟩ := exists_quadForm_le S.R⁻¹
  set nn : ℝ := (Fintype.card (ix n₁ na nm) : ℝ) ^ 2 with hnn
  set pp : ℝ := (Fintype.card (Fin p) : ℝ) ^ 2 with hpp
  refine ⟨nn * bSig * ‖S.fullCᵀ‖ * (pp * cRi), ?_, fun T => ?_⟩
  · positivity
  · have hpsdT := dareIter_posSemidef (C := S.fullC) (A := S.fullA)
      (Qw := S.Qw) S.hR S.Qw_posSemidef hL₀ T
    have hSig : ‖S.dareFrom L₀ T‖ ≤ nn * bSig :=
      posSemidef_norm_le_of_quadForm_le hpsdT hbSig.le (hbSigle T)
    have hSinvP : (innov S.fullC S.R (S.dareFrom L₀ T))⁻¹.PosSemidef :=
      (innov_posDef S.hR hpsdT).inv.posSemidef
    have hRS : (innov S.fullC S.R (S.dareFrom L₀ T) - S.R).PosSemidef := by
      have h1 : innov S.fullC S.R (S.dareFrom L₀ T) - S.R
          = S.fullC * S.dareFrom L₀ T * S.fullCᵀ := by
        unfold innov
        abel
      rw [h1]
      have h2 := hpsdT.mul_mul_conjTranspose_same S.fullC
      rwa [show S.fullCᴴ = S.fullCᵀ from
        Matrix.conjTranspose_eq_transpose_of_trivial _] at h2
    have hSinvle : ∀ x, quadForm
        (innov S.fullC S.R (S.dareFrom L₀ T))⁻¹ x
        ≤ cRi * ‖x‖ ^ 2 := by
      intro x
      have h3 := posSemidef_inv_sub_inv S.hR
        (innov_posDef S.hR hpsdT) hRS
      calc quadForm (innov S.fullC S.R (S.dareFrom L₀ T))⁻¹ x
          ≤ quadForm S.R⁻¹ x :=
            quadForm_le_quadForm_of_posSemidef_sub h3 x
      _ ≤ cRi * ‖x‖ ^ 2 := hcRile x
    have hSinv : ‖(innov S.fullC S.R (S.dareFrom L₀ T))⁻¹‖
        ≤ pp * cRi :=
      posSemidef_norm_le_of_quadForm_le hSinvP hcRi.le hSinvle
    unfold kGain
    calc ‖S.dareFrom L₀ T * S.fullCᵀ
          * (innov S.fullC S.R (S.dareFrom L₀ T))⁻¹‖
        ≤ ‖S.dareFrom L₀ T * S.fullCᵀ‖
            * ‖(innov S.fullC S.R (S.dareFrom L₀ T))⁻¹‖ :=
          Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖S.dareFrom L₀ T‖ * ‖S.fullCᵀ‖
          * ‖(innov S.fullC S.R (S.dareFrom L₀ T))⁻¹‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact Matrix.linfty_opNorm_mul _ _
    _ ≤ nn * bSig * ‖S.fullCᵀ‖ * (pp * cRi) := by
          have h8 : ‖S.dareFrom L₀ T‖ * ‖S.fullCᵀ‖
              ≤ nn * bSig * ‖S.fullCᵀ‖ :=
            mul_le_mul_of_nonneg_right hSig (norm_nonneg _)
          refine mul_le_mul h8 hSinv (norm_nonneg _) ?_
          positivity

/-- **The transported columns die**: `‖Y_T‖ → 0`. -/
theorem margY_norm_tendsto (hC1 : S.C1) (hL₀ : L₀.PosSemidef) :
    Tendsto (fun T => ‖S.margY L₀ T‖) atTop (nhds 0) := by
  obtain ⟨L, hL⟩ := detect_inj S.fullA S.fullC hC1
  obtain ⟨c, ρ, hc, hρ0, hρ1, hpow⟩ := hL.exists_pow_norm_le
  obtain ⟨kb, hkb, hkble⟩ := S.exists_margGain_bound hC1 hL₀
  set F := S.fullA - L * S.fullC with hF
  set Dt : ℕ → Matrix (ix n₁ na nm) (Fin na ⊕ Fin nm) ℝ :=
    fun T => (L - S.fullA * kGain S.fullC S.R (S.dareFrom L₀ T))
      * (S.fullC * S.margY L₀ T) with hDt
  have hrec : ∀ T, S.margY L₀ (T + 1) = F * S.margY L₀ T + Dt T := by
    intro T
    rw [S.margY_succ, hF, hDt]
    simp only
    rw [Matrix.sub_mul, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
    abel
  set cD : ℝ := ‖L‖ + ‖S.fullA‖ * kb with hcD
  have hcD0 : 0 ≤ cD := by positivity
  have hDtle : ∀ T, ‖Dt T‖ ≤ cD * ‖S.fullC * S.margY L₀ T‖ := by
    intro T
    rw [hDt]
    simp only
    calc ‖(L - S.fullA * kGain S.fullC S.R (S.dareFrom L₀ T))
          * (S.fullC * S.margY L₀ T)‖
        ≤ ‖L - S.fullA * kGain S.fullC S.R (S.dareFrom L₀ T)‖
            * ‖S.fullC * S.margY L₀ T‖ :=
          Matrix.linfty_opNorm_mul _ _
    _ ≤ cD * ‖S.fullC * S.margY L₀ T‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖L - S.fullA * kGain S.fullC S.R (S.dareFrom L₀ T)‖
            ≤ ‖L‖ + ‖S.fullA * kGain S.fullC S.R (S.dareFrom L₀ T)‖ :=
              norm_sub_le _ _
        _ ≤ ‖L‖ + ‖S.fullA‖ * kb := by
            have h1 : ‖S.fullA * kGain S.fullC S.R (S.dareFrom L₀ T)‖
                ≤ ‖S.fullA‖ * kb := by
              calc ‖S.fullA * kGain S.fullC S.R (S.dareFrom L₀ T)‖
                  ≤ ‖S.fullA‖
                    * ‖kGain S.fullC S.R (S.dareFrom L₀ T)‖ :=
                    Matrix.linfty_opNorm_mul _ _
              _ ≤ ‖S.fullA‖ * kb :=
                  mul_le_mul_of_nonneg_left (hkble T) (norm_nonneg _)
            linarith
        _ = cD := hcD.symm
  -- unroll against the Schur kernel
  have hunroll : ∀ T, S.margY L₀ T
      = F ^ T * S.margY L₀ 0
        + ∑ j ∈ Finset.range T, F ^ (T - 1 - j) * Dt j := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [hrec T, ih, Finset.sum_range_succ]
      have hexp : ∀ j ∈ Finset.range T,
          F ^ (T + 1 - 1 - j) * Dt j = F * (F ^ (T - 1 - j) * Dt j) := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have h1 : T + 1 - 1 - j = (T - 1 - j) + 1 := by omega
        rw [h1, pow_succ', Matrix.mul_assoc]
      rw [Finset.sum_congr rfl hexp]
      have h2 : T + 1 - 1 - T = 0 := by omega
      rw [h2, pow_zero, Matrix.one_mul, Matrix.mul_add, Matrix.mul_sum,
        ← Matrix.mul_assoc, ← pow_succ']
      abel
  -- norm bound and the convolution lemma
  have hbound : ∀ T, ‖S.margY L₀ T‖
      ≤ (c * ‖S.margY L₀ 0‖) * ρ ^ T
        + ∑ j ∈ Finset.range T,
            ρ ^ (T - 1 - j) * (c * cD * ‖S.fullC * S.margY L₀ j‖) := by
    intro T
    rw [hunroll T]
    calc ‖F ^ T * S.margY L₀ 0
          + ∑ j ∈ Finset.range T, F ^ (T - 1 - j) * Dt j‖
        ≤ ‖F ^ T * S.margY L₀ 0‖
          + ‖∑ j ∈ Finset.range T, F ^ (T - 1 - j) * Dt j‖ :=
          norm_add_le _ _
    _ ≤ ‖F ^ T * S.margY L₀ 0‖
          + ∑ j ∈ Finset.range T, ‖F ^ (T - 1 - j) * Dt j‖ := by
          have := norm_sum_le (Finset.range T)
            (fun j => F ^ (T - 1 - j) * Dt j)
          linarith
    _ ≤ (c * ‖S.margY L₀ 0‖) * ρ ^ T
          + ∑ j ∈ Finset.range T,
              ρ ^ (T - 1 - j) * (c * cD * ‖S.fullC * S.margY L₀ j‖) := by
          refine add_le_add ?_ (Finset.sum_le_sum fun j _ => ?_)
          · calc ‖F ^ T * S.margY L₀ 0‖
                ≤ ‖F ^ T‖ * ‖S.margY L₀ 0‖ :=
                  Matrix.linfty_opNorm_mul _ _
            _ ≤ (c * ρ ^ T) * ‖S.margY L₀ 0‖ :=
                  mul_le_mul_of_nonneg_right (hpow T) (norm_nonneg _)
            _ = (c * ‖S.margY L₀ 0‖) * ρ ^ T := by ring
          · calc ‖F ^ (T - 1 - j) * Dt j‖
                ≤ ‖F ^ (T - 1 - j)‖ * ‖Dt j‖ :=
                  Matrix.linfty_opNorm_mul _ _
            _ ≤ (c * ρ ^ (T - 1 - j))
                  * (cD * ‖S.fullC * S.margY L₀ j‖) := by
                  refine mul_le_mul (hpow _) (hDtle j) (norm_nonneg _) ?_
                  positivity
            _ = ρ ^ (T - 1 - j)
                  * (c * cD * ‖S.fullC * S.margY L₀ j‖) := by ring
  refine tendsto_zero_of_geometric_conv
    (by positivity : (0:ℝ) ≤ c * ‖S.margY L₀ 0‖) hρ0 hρ1
    (fun T => norm_nonneg _) (fun j => by positivity) ?_ hbound
  have h1 := S.margY_output_tendsto hC1 hL₀
  have h2 := h1.const_mul (c * cD)
  simpa [mul_assoc] using h2

/-- **The repaired `lem:marginal`, verified** (`eq:marg-zero`): along
any run from a PSD seed, with forward-power-bounded marginal block,
the marginal corner dies: `‖Σ̄_T|ₘₘ‖ → 0`. -/
theorem marg_block_norm_tendsto (hC1 : S.C1) (hL₀ : L₀.PosSemidef)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    Tendsto (fun T => ‖(embM n₁ na nm)ᵀ * S.dareFrom L₀ T
      * embM n₁ na nm‖) atTop (nhds 0) := by
  have hAmT : IsUnit S.Amᵀ.det := by
    rw [Matrix.det_transpose]; exact S.isUnit_Am_det
  -- Σ̄·E_M = Y_T · em2 · (Aₘᵀ)^T
  have hid : ∀ T, S.dareFrom L₀ T * embM n₁ na nm
      = S.margY L₀ T * em2 na nm * (S.Amᵀ) ^ T := by
    intro T
    unfold margY
    calc S.dareFrom L₀ T * embM n₁ na nm
        = S.dareFrom L₀ T * (emb2 n₁ na nm * em2 na nm) := by
          rw [emb2_mul_em2]
    _ = S.dareFrom L₀ T * emb2 n₁ na nm
          * (((S.A₂ᵀ)⁻¹) ^ T * (S.A₂ᵀ) ^ T) * em2 na nm := by
          rw [inv_pow_mul_pow S.isUnit_A₂t_det, Matrix.mul_one]
          rw [Matrix.mul_assoc]
    _ = S.dareFrom L₀ T * emb2 n₁ na nm * ((S.A₂ᵀ)⁻¹) ^ T
          * ((S.A₂ᵀ) ^ T * em2 na nm) := by
          simp only [Matrix.mul_assoc]
    _ = S.dareFrom L₀ T * emb2 n₁ na nm * ((S.A₂ᵀ)⁻¹) ^ T
          * (em2 na nm * (S.Amᵀ) ^ T) := by
          congr 1
          induction T with
          | zero => simp
          | succ T ih =>
            calc (S.A₂ᵀ) ^ (T + 1) * em2 na nm
                = (S.A₂ᵀ) ^ T * (S.A₂ᵀ * em2 na nm) := by
                  rw [pow_succ, Matrix.mul_assoc]
            _ = (S.A₂ᵀ) ^ T * em2 na nm * S.Amᵀ := by
                  rw [S.A₂_transpose_mul_em2, Matrix.mul_assoc]
            _ = em2 na nm * (S.Amᵀ) ^ T * S.Amᵀ := by rw [ih]
            _ = em2 na nm * (S.Amᵀ) ^ (T + 1) := by
                  rw [Matrix.mul_assoc, ← pow_succ]
    _ = S.margY L₀ T * em2 na nm * (S.Amᵀ) ^ T := by
          unfold margY
          simp only [Matrix.mul_assoc]
  have hAmpow : ∀ T : ℕ, ‖(S.Amᵀ) ^ T‖
      ≤ (Fintype.card (Fin nm) : ℝ) * cm := by
    intro T
    rw [← Matrix.transpose_pow]
    calc ‖(S.Am ^ T)ᵀ‖
        ≤ (Fintype.card (Fin nm) : ℝ) * ‖S.Am ^ T‖ :=
          linfty_opNorm_transpose_le' _
    _ ≤ (Fintype.card (Fin nm) : ℝ) * cm :=
          mul_le_mul_of_nonneg_left (hPB T) (Nat.cast_nonneg _)
  set K : ℝ := ‖(embM n₁ na nm)ᵀ‖ * ‖em2 na nm‖
    * ((Fintype.card (Fin nm) : ℝ) * cm) with hK
  have hK0 : 0 ≤ K := by positivity
  have hle : ∀ T, ‖(embM n₁ na nm)ᵀ * S.dareFrom L₀ T * embM n₁ na nm‖
      ≤ K * ‖S.margY L₀ T‖ := by
    intro T
    rw [Matrix.mul_assoc, hid T]
    calc ‖(embM n₁ na nm)ᵀ
          * (S.margY L₀ T * em2 na nm * (S.Amᵀ) ^ T)‖
        ≤ ‖(embM n₁ na nm)ᵀ‖
            * ‖S.margY L₀ T * em2 na nm * (S.Amᵀ) ^ T‖ :=
          Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖(embM n₁ na nm)ᵀ‖ * (‖S.margY L₀ T * em2 na nm‖
          * ‖(S.Amᵀ) ^ T‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖(embM n₁ na nm)ᵀ‖ * ((‖S.margY L₀ T‖ * ‖em2 na nm‖)
          * ((Fintype.card (Fin nm) : ℝ) * cm)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine mul_le_mul (Matrix.linfty_opNorm_mul _ _)
            (hAmpow T) (norm_nonneg _) ?_
          positivity
    _ = K * ‖S.margY L₀ T‖ := by rw [hK]; ring
  refine squeeze_zero (fun T => norm_nonneg _) hle ?_
  have h1 := (S.margY_norm_tendsto hC1 hL₀).const_mul K
  simpa using h1

end DareSystem

end Dare
end Estimation
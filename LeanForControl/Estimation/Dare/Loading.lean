import LeanForControl.Estimation.Dare.SlavedSeed
import Architect

/-!
# Marginal slaving and the loading dynamics (`lem:loading`)

Full row slaving `eq:row-slaved`: the marginal rows of the lower
trajectory are the antistable rows scaled by the loading. The
measurement update preserves the loading (it acts on rows from the
right), and prediction rotates it by the autonomous Stein map
`Λ⁺ = Aₘ·Λ·Aₐ⁻¹` (`eq:loading-rec`), whose closed form
`Λ_T = Aₘᵀ·Λ₀·Aₐ⁻ᵀ` decays geometrically (`eq:loading-conv`):
`Aₐ⁻¹` is Schur and the marginal powers are bounded.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- **Row slaving** (`eq:row-slaved`): the marginal rows are the
antistable rows scaled by the loading `Λ`. -/
def RowSlaved (Λ : Matrix (Fin nm) (Fin na) ℝ)
    (Sg : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) : Prop :=
  (embM n₁ na nm)ᵀ * Sg = Λ * ((embA n₁ na nm)ᵀ * Sg)

/-- Row maps commute with right factors. -/
lemma RowSlaved.mul_right {Λ : Matrix (Fin nm) (Fin na) ℝ}
    {Sg : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (h : RowSlaved Λ Sg) (X : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) :
    (embM n₁ na nm)ᵀ * (Sg * X)
      = Λ * ((embA n₁ na nm)ᵀ * (Sg * X)) := by
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.mul_assoc]

/-- The measurement update preserves the loading
(`lem:loading`(a), `Λ̂ = Λ`). -/
lemma RowSlaved.updM {Λ : Matrix (Fin nm) (Fin na) ℝ}
    {Sg : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (h : RowSlaved Λ Sg) :
    RowSlaved Λ (updM S.fullC S.R Sg) := by
  unfold RowSlaved
  have hupd : Dare.updM S.fullC S.R Sg
      = Sg - Sg * (S.fullCᵀ * ((innov S.fullC S.R Sg)⁻¹
          * (S.fullC * Sg))) := by
    have h1 : Sg - Dare.updM S.fullC S.R Sg
        = Sg * S.fullCᵀ * (innov S.fullC S.R Sg)⁻¹ * (S.fullC * Sg) :=
      sub_updM_eq
    have h2 : Sg * S.fullCᵀ * (innov S.fullC S.R Sg)⁻¹
        * (S.fullC * Sg)
        = Sg * (S.fullCᵀ * ((innov S.fullC S.R Sg)⁻¹
            * (S.fullC * Sg))) := by
      simp only [Matrix.mul_assoc]
    rw [← h2, ← h1]
    abel
  rw [hupd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_sub, h,
    h.mul_right]

/-- The prediction step rotates the loading by the Stein map
(`eq:loading-rec`, `Λ⁺ = Aₘ·Λ·Aₐ⁻¹`). -/
lemma RowSlaved.dareStep {Λ : Matrix (Fin nm) (Fin na) ℝ}
    {Sg : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (h : RowSlaved Λ Sg) :
    RowSlaved (S.Am * Λ * S.Aa⁻¹)
      (dareStep S.fullC S.R S.fullA S.Qw Sg) := by
  have hMA : (embM n₁ na nm)ᵀ * S.fullA = S.Am * (embM n₁ na nm)ᵀ := by
    have h1 := congrArg Matrix.transpose S.fullA_transpose_mul_embM
    rwa [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose] at h1
  have hAA : (embA n₁ na nm)ᵀ * S.fullA = S.Aa * (embA n₁ na nm)ᵀ := by
    have h1 := congrArg Matrix.transpose S.fullA_transpose_mul_embA
    rwa [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose] at h1
  have hMQ : (embM n₁ na nm)ᵀ * S.Qw = 0 := by
    unfold Qw
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      S.embM_transpose_mul_fullG, Matrix.zero_mul, Matrix.zero_mul]
  have hAQ : (embA n₁ na nm)ᵀ * S.Qw = 0 := by
    unfold Qw
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      S.embA_transpose_mul_fullG, Matrix.zero_mul, Matrix.zero_mul]
  have hU := h.updM S
  unfold RowSlaved at hU ⊢
  have hstep : Dare.dareStep S.fullC S.R S.fullA S.Qw Sg
      = S.fullA * Dare.updM S.fullC S.R Sg * S.fullAᵀ + S.Qw := rfl
  -- the antistable rows of the successor determine the update rows
  have hMrow : (embM n₁ na nm)ᵀ
      * Dare.dareStep S.fullC S.R S.fullA S.Qw Sg
      = S.Am * (Λ * ((embA n₁ na nm)ᵀ
          * (Dare.updM S.fullC S.R Sg * S.fullAᵀ))) := by
    rw [hstep, Matrix.mul_add, hMQ, add_zero, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hMA,
      Matrix.mul_assoc S.Am (embM n₁ na nm)ᵀ
        (Dare.updM S.fullC S.R Sg), hU]
    simp only [Matrix.mul_assoc]
  have hArow : (embA n₁ na nm)ᵀ
      * Dare.dareStep S.fullC S.R S.fullA S.Qw Sg
      = S.Aa * ((embA n₁ na nm)ᵀ
          * (Dare.updM S.fullC S.R Sg * S.fullAᵀ)) := by
    rw [hstep, Matrix.mul_add, hAQ, add_zero, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hAA]
    simp only [Matrix.mul_assoc]
  have hAa1 : S.Aa⁻¹ * S.Aa = 1 :=
    Matrix.nonsing_inv_mul _ S.isUnit_Aa_det
  rw [hMrow, hArow]
  calc S.Am * (Λ * ((embA n₁ na nm)ᵀ
        * (Dare.updM S.fullC S.R Sg * S.fullAᵀ)))
      = S.Am * Λ * ((S.Aa⁻¹ * S.Aa) * ((embA n₁ na nm)ᵀ
          * (Dare.updM S.fullC S.R Sg * S.fullAᵀ))) := by
        rw [hAa1, Matrix.one_mul, Matrix.mul_assoc]
  _ = S.Am * Λ * S.Aa⁻¹ * (S.Aa * ((embA n₁ na nm)ᵀ
        * (Dare.updM S.fullC S.R Sg * S.fullAᵀ))) := by
      simp only [Matrix.mul_assoc]

/-- **`lem:loading`(a)+(b)**: along any run from a `Λ₀`-slaved seed,
the trajectory stays slaved with the closed-form loading
`Λ_T = Aₘᵀ·Λ₀·(Aₐ⁻¹)ᵀ`. -/
theorem rowSlaved_dareIter {Λ₀ : Matrix (Fin nm) (Fin na) ℝ}
    {L : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (h0 : RowSlaved Λ₀ L) :
    ∀ T, RowSlaved (S.Am ^ T * Λ₀ * (S.Aa⁻¹) ^ T)
      (S.dareFrom L T) := by
  intro T
  induction T with
  | zero =>
    simpa using h0
  | succ T ih =>
    have hstep := RowSlaved.dareStep S ih
    have heq : S.Am * (S.Am ^ T * Λ₀ * (S.Aa⁻¹) ^ T) * S.Aa⁻¹
        = S.Am ^ (T + 1) * Λ₀ * (S.Aa⁻¹) ^ (T + 1) := by
      rw [pow_succ' S.Am T, pow_succ (S.Aa⁻¹) T]
      simp only [Matrix.mul_assoc]
    rw [heq] at hstep
    exact hstep

/-- The inverse antistable dynamics are Schur: `|λ(Aₐ⁻¹)| < 1`. -/
lemma Aa_inv_isSchurStable : IsSchurStable S.Aa⁻¹ := by
  intro μ hμ
  have hspec : μ ∈ spectrum ℂ (Matrix.toLin' (complexify S.Aa⁻¹)) := by
    rw [Matrix.spectrum_toLin']
    exact hμ
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    hspec).exists_hasEigenvector
  have hAv : complexify S.Aa⁻¹ *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  have hvne : v ≠ 0 := hv.2
  have hinv : complexify S.Aa * complexify S.Aa⁻¹ = 1 := by
    rw [← complexify_mul, Matrix.mul_nonsing_inv _ S.isUnit_Aa_det,
      complexify_one]
  rcases eq_or_ne μ 0 with h0 | hne
  · rw [h0, norm_zero]
    norm_num
  · have h1 : complexify S.Aa *ᵥ v = μ⁻¹ • v := by
      have h2 := congrArg (fun w => complexify S.Aa *ᵥ w) hAv
      simp only [Matrix.mulVec_smul] at h2
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2
      have h3 := congrArg (fun w => μ⁻¹ • w) h2
      simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h3
      exact h3.symm
    have h4 := S.hAnti μ⁻¹ (mem_spectrum_of_mulVec_eq_smul hvne h1)
    rw [norm_inv, lt_inv_comm₀ (by norm_num) (norm_pos_iff.mpr hne)]
      at h4
    simpa using h4

/-- **`eq:loading-conv`**: the loading decays to zero (geometrically —
`Aₐ⁻¹` Schur against power-bounded `Aₘ`). -/
theorem loading_tendsto (Λ₀ : Matrix (Fin nm) (Fin na) ℝ)
    {cm : ℝ} (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    Tendsto (fun T => ‖S.Am ^ T * Λ₀ * (S.Aa⁻¹) ^ T‖) atTop
      (nhds 0) := by
  obtain ⟨ca, γ, hca, hγ0, hγ1, hpow⟩ :=
    S.Aa_inv_isSchurStable.exists_pow_norm_le
  have hcm0 : (0:ℝ) ≤ cm := le_trans (norm_nonneg _) (hPB 0)
  have hb : ∀ T, ‖S.Am ^ T * Λ₀ * (S.Aa⁻¹) ^ T‖
      ≤ cm * ‖Λ₀‖ * ca * γ ^ T := by
    intro T
    calc ‖S.Am ^ T * Λ₀ * (S.Aa⁻¹) ^ T‖
        ≤ ‖S.Am ^ T‖ * ‖Λ₀‖ * ‖(S.Aa⁻¹) ^ T‖ := norm_triple_le _ _ _
    _ ≤ (cm * ‖Λ₀‖) * (ca * γ ^ T) := by
        refine mul_le_mul ?_ (hpow T) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right (hPB T) (norm_nonneg _)
    _ = cm * ‖Λ₀‖ * ca * γ ^ T := by ring
  refine squeeze_zero (fun T => norm_nonneg _) hb ?_
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1
  simpa using h.const_mul (cm * ‖Λ₀‖ * ca)

/-- The lower trajectory (`eq:Ldef-slaved` seed) stays slaved for all
time with the closed-form loading. -/
theorem lowTraj_rowSlaved (hSa : S.Siga.PosDef) (δ : ℝ) (T : ℕ) :
    RowSlaved (S.Am ^ T * S.lam0 * (S.Aa⁻¹) ^ T)
      (S.dareFrom (S.slavedSeed δ) T) :=
  S.rowSlaved_dareIter (S.slavedSeed_slaved hSa δ) T

end DareSystem

end Dare
end Estimation

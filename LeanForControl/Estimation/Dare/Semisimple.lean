import LeanForControl.Estimation.Dare.Main
import LeanForControl.LinearSystems.SpectralGrowth
import Architect

/-!
# The semisimple qualification (F4a)

The odyssey line's marginal hypotheses are power bounds:
`‖Aₘᵏ‖ ≤ cₘ` (forward, `thm:main`-1) and `‖Aₘ⁻ᵏ‖ ≤ cₘ` (backward,
`thm:main`-2 converse). The deck words them as the *semisimple*
qualification. Here the deck's wording becomes a theorem: a
diagonalizable marginal block (over `ℂ`) has both power families
bounded — `‖Aₘᵏ‖, ‖Aₘ⁻ᵏ‖ ≤ ‖P‖·‖P⁻¹‖` — so `MargSemisimple`
discharges every standing power-bound hypothesis
(`main_strong_attraction_semisimple`,
`main_marg_not_exponential_semisimple`).

For the *defective* marginal (the deck's declared open problem), the
identified tool is the verified linear Gramian floor
`LinearSystems.gramian_growth` (2026a, fact 7): even defective
unit-circle blocks satisfy `∑_{k<T} ‖Aₘᵏv‖² ≥ c T ‖v‖²`
(`marg_gramian_growth` below) — a lower bound where no upper power
bound exists.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

open scoped Matrix.Norms.Operator

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The deck's semisimple qualification, in matrix form: the
complexified marginal block is diagonalizable. -/
def MargSemisimple : Prop :=
  ∃ (P : Matrix (Fin nm) (Fin nm) ℂ) (d : Fin nm → ℂ),
    IsUnit P.det ∧ complexify S.Am = P * Matrix.diagonal d * P⁻¹

/-- **F4a**: a semisimple marginal block has uniformly bounded forward
*and* backward powers — the deck's wording implies the Lean line's
standing hypotheses. -/
theorem marg_powers_bounded (hss : S.MargSemisimple) :
    ∃ cm : ℝ, 0 ≤ cm ∧ (∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm)
      ∧ (∀ k : ℕ, ‖S.Am⁻¹ ^ k‖ ≤ cm) := by
  obtain ⟨P, d, hP, hAm⟩ := hss
  have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hPinv' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  -- the diagonal entries are unit-modulus eigenvalues
  have hd1 : ∀ i : Fin nm, ‖d i‖ = 1 := by
    intro i
    have hvne : P *ᵥ Pi.single i 1 ≠ 0 := by
      intro h0
      have h1 := congrArg (fun w => P⁻¹ *ᵥ w) h0
      dsimp only at h1
      rw [Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h1
      have h2 := congrFun h1 i
      simp at h2
    have hveq : complexify S.Am *ᵥ (P *ᵥ Pi.single i 1)
        = d i • (P *ᵥ Pi.single i 1) := by
      rw [hAm, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.mul_assoc, hPinv, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single,
        mul_one]
      have h1 : (Pi.single i (d i) : Fin nm → ℂ)
          = d i • (Pi.single i 1 : Fin nm → ℂ) := by
        funext j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [Pi.single_apply, hji]
      rw [h1, Matrix.mulVec_smul]
    exact S.hMarg (d i) (mem_spectrum_of_mulVec_eq_smul hvne hveq)
  -- similarity powers
  have hpow : ∀ (e : Fin nm → ℂ) (k : ℕ),
      (P * Matrix.diagonal e * P⁻¹) ^ k
        = P * Matrix.diagonal e ^ k * P⁻¹ := by
    intro e k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hPinv']
    | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        calc P * Matrix.diagonal e ^ k * P⁻¹
            * (P * Matrix.diagonal e * P⁻¹)
            = P * Matrix.diagonal e ^ k * (P⁻¹ * P)
              * Matrix.diagonal e * P⁻¹ := by
              simp only [Matrix.mul_assoc]
        _ = P * (Matrix.diagonal e ^ k * Matrix.diagonal e) * P⁻¹ := by
              rw [hPinv, Matrix.mul_one]
              simp only [Matrix.mul_assoc]
  -- diagonal powers have norm at most one
  have hDk : ∀ k : ℕ, ∀ e : Fin nm → ℂ, (∀ i, ‖e i‖ = 1) →
      ‖(Matrix.diagonal e) ^ k‖ ≤ 1 := by
    intro k e he
    rw [Matrix.diagonal_pow, Matrix.linfty_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    rw [Pi.pow_apply, norm_pow, he i, one_pow]
  -- the similarity bound
  have hsim : ∀ (M : Matrix (Fin nm) (Fin nm) ℂ), ‖P * M * P⁻¹‖
      ≤ ‖P‖ * ‖M‖ * ‖P⁻¹‖ := by
    intro M
    refine (Matrix.linfty_opNorm_mul _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _)
      (norm_nonneg _)
  refine ⟨‖P‖ * ‖P⁻¹‖, by positivity, fun k => ?_, fun k => ?_⟩
  · -- forward powers
    rw [← linfty_opNorm_complexify, complexify_pow, hAm, hpow d]
    calc ‖P * Matrix.diagonal d ^ k * P⁻¹‖
        ≤ ‖P‖ * ‖Matrix.diagonal d ^ k‖ * ‖P⁻¹‖ := hsim _
    _ ≤ ‖P‖ * 1 * ‖P⁻¹‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hDk k d hd1) (norm_nonneg _))
          (norm_nonneg _)
    _ = ‖P‖ * ‖P⁻¹‖ := by ring
  · -- backward powers: `Aₘ` is invertible with diagonalizable inverse
    have hdne : ∀ i, d i ≠ 0 := fun i h0 => by
      have h1 := hd1 i
      rw [h0, norm_zero] at h1
      exact one_ne_zero h1.symm
    set N : Matrix (Fin nm) (Fin nm) ℂ :=
      P * Matrix.diagonal (fun i => (d i)⁻¹) * P⁻¹ with hN
    have hdd : Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹)
        = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hdne i)
    have hAmN : complexify S.Am * N = 1 := by
      rw [hAm, hN]
      calc P * Matrix.diagonal d * P⁻¹
          * (P * Matrix.diagonal (fun i => (d i)⁻¹) * P⁻¹)
          = P * Matrix.diagonal d * (P⁻¹ * P)
            * Matrix.diagonal (fun i => (d i)⁻¹) * P⁻¹ := by
            simp only [Matrix.mul_assoc]
      _ = P * (Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹))
            * P⁻¹ := by
            rw [hPinv, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hdd, Matrix.mul_one, hPinv']
    have hAmU : IsUnit S.Am.det := by
      have h1 : IsUnit (complexify S.Am).det := by
        have hdet : (complexify S.Am).det * N.det = 1 := by
          rw [← Matrix.det_mul, hAmN, Matrix.det_one]
        exact ⟨⟨(complexify S.Am).det, N.det, hdet,
          by rwa [mul_comm] at hdet⟩, rfl⟩
      have h2 : (complexify S.Am).det = (S.Am.det : ℂ) :=
        (RingHom.map_det (algebraMap ℝ ℂ) S.Am).symm
      rw [h2] at h1
      rw [isUnit_iff_ne_zero]
      intro h0
      rw [h0] at h1
      simpa using h1
    have hcinv : complexify S.Am⁻¹ = N := by
      have h1 : complexify S.Am⁻¹ * complexify S.Am = 1 := by
        rw [← complexify_mul, Matrix.nonsing_inv_mul _ hAmU,
          complexify_one]
      rw [← Matrix.inv_eq_left_inv h1]
      exact Matrix.inv_eq_right_inv hAmN
    rw [← linfty_opNorm_complexify, complexify_pow, hcinv, hN,
      hpow (fun i => (d i)⁻¹)]
    calc ‖P * Matrix.diagonal (fun i => (d i)⁻¹) ^ k * P⁻¹‖
        ≤ ‖P‖ * ‖Matrix.diagonal (fun i => (d i)⁻¹) ^ k‖ * ‖P⁻¹‖ :=
          hsim _
    _ ≤ ‖P‖ * 1 * ‖P⁻¹‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (hDk k (fun i => (d i)⁻¹) fun i => by
              rw [norm_inv, hd1 i, inv_one])
            (norm_nonneg _))
          (norm_nonneg _)
    _ = ‖P‖ * ‖P⁻¹‖ := by ring

/-- **`thm:main`-1 with the deck's own wording**: attraction ⟺ C2w,
existence internal, under C1 and a semisimple marginal. -/
theorem main_strong_attraction_semisimple (hC1 : S.C1)
    (hss : S.MargSemisimple) :
    ∃ Sinf, S.IsStrongSolution Sinf
      ∧ (Filter.Tendsto (fun T => ‖S.dare T - Sinf‖)
          Filter.atTop (nhds 0) ↔ S.C2w) := by
  obtain ⟨cm, hcm, hPB, _⟩ := S.marg_powers_bounded hss
  exact S.main_strong_attraction hC1 hcm hPB

/-- **`thm:main`-2 converse with the deck's own wording**: with a
semisimple marginal block present, some C2 prior is not exponentially
attracted. -/
theorem main_marg_not_exponential_semisimple (hC1 : S.C1)
    (hnm : Nonempty (Fin nm)) (hss : S.MargSemisimple) :
    ∃ Sinf, S.IsStrongSolution Sinf
      ∧ ¬∃ C ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ T : ℕ,
          ‖S.dareFrom (Sinf + embM n₁ na nm * (embM n₁ na nm)ᵀ) T
            - Sinf‖ ≤ C * ρ ^ T := by
  obtain ⟨cm, hcm, _, hPBi⟩ := S.marg_powers_bounded hss
  exact S.main_marg_not_exponential hC1 hnm hPBi

/-- **The defective-marginal tool** (`fact:gramian` = 2026a fact 7, at
the marginal block): even a defective unit-circle block satisfies the
linear sampled-energy floor `∑_{k<T} ‖Aₘᵏ v‖² ≥ c T ‖v‖²` — the
verified lower bound available where no upper power bound exists,
identified for the declared defective-marginal open problem. -/
theorem marg_gramian_growth :
    ∃ c : ℝ, 0 < c ∧ ∀ (v : Fin nm → ℝ) (T : ℕ), 1 ≤ T →
      c * T * ‖v‖ ^ 2 ≤ ∑ k ∈ Finset.range T, ‖S.Am ^ k *ᵥ v‖ ^ 2 :=
  gramian_growth S.Am (fun μ hμ => (S.hMarg μ hμ).ge)

end DareSystem

end Dare
end Estimation

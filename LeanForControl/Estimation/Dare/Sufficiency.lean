import LeanForControl.Estimation.Dare.ReducedFacts
import Architect

/-!
# The squeeze (`thm:sufficiency`) and the dichotomy (`thm:main`, Part 1)

Frame the prior between the slaved lower anchor and the dominating
upper anchor `Σ₀ + Σ∞`; both converge to the strong solution
(`eq:lowsqueeze`, `eq:above`), and the Löwner sandwich carries the
run with them. Combined with the verified `thm:necessity`, attraction
to the strong solution is *equivalent* to C2w — the strong/stabilizing
attraction dichotomy's GAS half.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

/-- Two-sided quadratic-form control. -/
lemma abs_quadForm_le_card_norm {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    |quadForm M x| ≤ (Fintype.card ι : ℝ) * ‖M‖ * ‖x‖ ^ 2 := by
  rw [abs_le]
  refine ⟨?_, quadForm_le_card_norm M x⟩
  have h := quadForm_le_card_norm (-M) x
  have hneg : quadForm (-M) x = -quadForm M x := by
    unfold quadForm
    rw [Matrix.neg_mulVec, dotProduct_neg]
  rw [hneg, norm_neg] at h
  linarith

/-- The norm of a symmetric matrix from a two-sided quadratic-form
bound, by polarization. -/
lemma symm_norm_le_of_abs_quadForm_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hsym : Mᵀ = M) {b : ℝ}
    (hb : 0 ≤ b) (hq : ∀ x, |quadForm M x| ≤ b * ‖x‖ ^ 2) :
    ‖M‖ ≤ (Fintype.card ι : ℝ) ^ 2 * (3 * b) := by
  have hentry : ∀ i j, |M i j| ≤ 3 * b := by
    intro i j
    have hbasis : (Pi.single i 1 : ι → ℝ)
        ⬝ᵥ (M *ᵥ (Pi.single j 1 : ι → ℝ)) = M i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
        ite_mul, Finset.sum_ite_eq']
    have hcross : (Pi.single j 1 : ι → ℝ)
        ⬝ᵥ (M *ᵥ (Pi.single i 1 : ι → ℝ)) = M i j := by
      rw [dotProduct_mulVec_eq, hsym, dotProduct_comm, hbasis]
    have hpol : quadForm M ((Pi.single i 1 : ι → ℝ) + Pi.single j 1)
        = quadForm M (Pi.single i 1) + quadForm M (Pi.single j 1)
          + 2 * M i j := by
      unfold quadForm
      rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct,
        add_dotProduct, hbasis, hcross]
      ring
    have h1 := hq ((Pi.single i 1 : ι → ℝ) + Pi.single j 1)
    have h2 := hq (Pi.single i 1 : ι → ℝ)
    have h3 := hq (Pi.single j 1 : ι → ℝ)
    have hn1 : ‖(Pi.single i 1 : ι → ℝ) + Pi.single j 1‖ ≤ 2 := by
      calc ‖(Pi.single i 1 : ι → ℝ) + Pi.single j 1‖
          ≤ ‖(Pi.single i 1 : ι → ℝ)‖ + ‖(Pi.single j 1 : ι → ℝ)‖ :=
            norm_add_le _ _
      _ ≤ 1 + 1 := add_le_add (norm_single_le_one i)
          (norm_single_le_one j)
      _ = 2 := by norm_num
    have hn2 := norm_single_le_one (ι := ι) i
    have hn3 := norm_single_le_one (ι := ι) j
    have hs1 : ‖(Pi.single i 1 : ι → ℝ) + Pi.single j 1‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg ((Pi.single i 1 : ι → ℝ) + Pi.single j 1)]
    have hs2 : ‖(Pi.single i 1 : ι → ℝ)‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (Pi.single i 1 : ι → ℝ)]
    have hs3 : ‖(Pi.single j 1 : ι → ℝ)‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (Pi.single j 1 : ι → ℝ)]
    rw [abs_le] at h1 h2 h3 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
      hpol]
  calc ‖M‖ ≤ ∑ i, ∑ j, |M i j| := linfty_opNorm_le_sum_abs M
  _ ≤ ∑ _i : ι, ∑ _j : ι, 3 * b := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hentry i j
  _ = (Fintype.card ι : ℝ) ^ 2 * (3 * b) := by
      simp [Finset.sum_const, Finset.card_univ]
      ring

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

set_option maxHeartbeats 1000000 in
/-- **`thm:sufficiency`, verified**: under C1 and C2w — with the one
remaining import, the power-bounded marginal (`eq:Finf-spec` is
discharged by `strong_Fs_schur`, the reduced `fact:dare-strong` by
`reducedImport_holds`) — the run from the prior is attracted to the
strong solution: the Löwner squeeze between the verified anchors. -/
theorem sufficiency_tendsto (hC1 : S.C1) (hC2w : S.C2w)
    (hS : S.IsStrongSolution Sinf)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    Tendsto (fun T => ‖S.dare T - Sinf‖) atTop (nhds 0) := by
  have hFs := S.strong_Fs_schur hC1 hS
  have himp := S.reducedImport_holds hC1 hS
  have hSa : S.Siga.PosDef := S.criterion_w.mp hC2w
  -- the two anchors converge
  have hdomU : (S.Sig0 + Sinf - Sinf).PosSemidef := by
    rw [add_sub_cancel_right]
    exact S.Sig0_posSemidef
  have hupper := S.supremal_tendsto hC1 hS
    (S.Sig0_posSemidef.add hS.posSemidef) hdomU hcm hPB hFs
  have hlower := S.lowsqueeze_tendsto hC1 hSa hS one_pos himp hPB
  -- the sandwich
  have hlo : ∀ T, (S.dare T
      - S.dareFrom (S.slavedSeed 1) T).PosSemidef := by
    intro T
    exact dareIter_mono (C := S.fullC) (A := S.fullA) (Qw := S.Qw)
      S.hR S.Qw_posSemidef
      (S.slavedSeed_posSemidef hSa one_pos.le) S.Sig0_posSemidef
      (S.slavedSeed_le_Sig0 hSa le_rfl) T
  have hhi : ∀ T, (S.dareFrom (S.Sig0 + Sinf) T
      - S.dare T).PosSemidef := by
    intro T
    have h12 : (S.Sig0 + Sinf - S.Sig0).PosSemidef := by
      rw [add_sub_cancel_left]
      exact hS.posSemidef
    exact dareIter_mono S.hR S.Qw_posSemidef S.Sig0_posSemidef
      (S.Sig0_posSemidef.add hS.posSemidef) h12 T
  -- the run's gap is symmetric
  have hsym : ∀ T, (S.dare T - Sinf)ᵀ = S.dare T - Sinf := by
    intro T
    have h1 : (S.dare T).PosSemidef :=
      dareIter_posSemidef S.hR S.Qw_posSemidef S.Sig0_posSemidef T
    rw [Matrix.transpose_sub, h1.1.transpose_eq_self,
      hS.posSemidef.1.transpose_eq_self]
  -- two-sided quadratic control from the anchors
  set K : ℝ := (Fintype.card (ix n₁ na nm) : ℝ) with hK
  have hKnn : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hq : ∀ T x, |quadForm (S.dare T - Sinf) x|
      ≤ (K * ‖S.dareFrom (S.Sig0 + Sinf) T - Sinf‖
        + K * ‖S.dareFrom (S.slavedSeed 1) T - Sinf‖) * ‖x‖ ^ 2 := by
    intro T x
    have hup : quadForm (S.dare T - Sinf) x
        ≤ quadForm (S.dareFrom (S.Sig0 + Sinf) T - Sinf) x := by
      refine quadForm_le_quadForm_of_posSemidef_sub ?_ x
      have h := hhi T
      have heq : S.dareFrom (S.Sig0 + Sinf) T - Sinf
          - (S.dare T - Sinf)
          = S.dareFrom (S.Sig0 + Sinf) T - S.dare T := by
        abel
      rwa [heq]
    have hdown : quadForm (S.dareFrom (S.slavedSeed 1) T - Sinf) x
        ≤ quadForm (S.dare T - Sinf) x := by
      refine quadForm_le_quadForm_of_posSemidef_sub ?_ x
      have h := hlo T
      have heq : S.dare T - Sinf
          - (S.dareFrom (S.slavedSeed 1) T - Sinf)
          = S.dare T - S.dareFrom (S.slavedSeed 1) T := by
        abel
      rwa [heq]
    have hu2 := abs_quadForm_le_card_norm
      (S.dareFrom (S.Sig0 + Sinf) T - Sinf) x
    have hl2 := abs_quadForm_le_card_norm
      (S.dareFrom (S.slavedSeed 1) T - Sinf) x
    rw [abs_le] at hu2 hl2 ⊢
    have hxnn : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    have hnU : (0:ℝ) ≤ ‖S.dareFrom (S.Sig0 + Sinf) T - Sinf‖ :=
      norm_nonneg _
    have hnL : (0:ℝ) ≤ ‖S.dareFrom (S.slavedSeed 1) T - Sinf‖ :=
      norm_nonneg _
    constructor
    · have := hl2.1
      nlinarith [mul_nonneg (mul_nonneg hKnn hnU) hxnn]
    · have := hu2.2
      nlinarith [mul_nonneg (mul_nonneg hKnn hnL) hxnn]
  -- convergence of the control and squeeze
  have hbT : Tendsto (fun T =>
      K * ‖S.dareFrom (S.Sig0 + Sinf) T - Sinf‖
        + K * ‖S.dareFrom (S.slavedSeed 1) T - Sinf‖) atTop
      (nhds 0) := by
    have h := (hupper.const_mul K).add (hlower.const_mul K)
    simpa using h
  have hnormb : ∀ T, ‖S.dare T - Sinf‖
      ≤ K ^ 2 * (3 * (K * ‖S.dareFrom (S.Sig0 + Sinf) T - Sinf‖
          + K * ‖S.dareFrom (S.slavedSeed 1) T - Sinf‖)) :=
    fun T => symm_norm_le_of_abs_quadForm_le (hsym T)
      (by positivity) (hq T)
  refine squeeze_zero (fun T => norm_nonneg _) hnormb ?_
  have h := hbT.const_mul (K ^ 2 * 3)
  simpa [mul_assoc] using h

/-- **`thm:main`, Part 1, verified** (the strong-attraction
dichotomy's GAS half): under C1 — with the power-bounded marginal as
the one remaining import (`eq:Finf-spec` and the reduced
`fact:dare-strong` are theorems) — the run from the prior is
attracted to the strong solution **iff** C2w. -/
theorem strong_attraction_iff_C2w (hC1 : S.C1)
    (hS : S.IsStrongSolution Sinf)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    Tendsto (fun T => ‖S.dare T - Sinf‖) atTop (nhds 0) ↔ S.C2w :=
  ⟨fun hconv => S.necessity hS hconv,
    fun hC2w => S.sufficiency_tendsto hC1 hC2w hS hcm hPB⟩

end DareSystem

end Dare
end Estimation

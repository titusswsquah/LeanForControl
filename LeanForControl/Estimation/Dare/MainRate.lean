import LeanForControl.Estimation.Dare.LowRate
import Architect

/-!
# The C3w branch: geometric attraction (E3, `thm:main` Part 2 forward)

Under C3w the strong loop is Schur (`strong_isSchurStable_iff_C3w`),
so both squeeze anchors contract geometrically — the from-above gap
by `loewner_iter` against the Schur `F∞` (`supremal_geometric`), the
from-below anchor by `lowsqueeze_geometric` (E2) — and the
polarization sandwich (`dare_sandwich_norm`, the mechanism inside
`thm:sufficiency`) carries the rate to the run itself:

* `sufficiency_geometric` — `thm:sufficiency`'s rate refinement;
* `main_stab_forward` — `eq:main-stab`'s forward direction, with the
  strong solution's existence internal: C1 + C2 + C3w give
  exponential attraction. Together with `marg_not_exponential`
  (Phase C) this closes `thm:main` Part 2.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

set_option maxHeartbeats 1600000 in
/-- **The from-above anchor decays geometrically** when the strong
loop is Schur: the gap rides `eq:gap-ric` under the fixed `F∞`
(`loewner_iter`), and Löwner domination carries to the norm. -/
theorem supremal_geometric (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    {L₀ : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hL₀ : L₀.PosSemidef) (hdom : (L₀ - Sinf).PosSemidef)
    (hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf)) :
    GeoDecay (fun T => ‖S.dareFrom L₀ T - Sinf‖) := by
  obtain ⟨c, γ, hc, hγ0, hγ1, hp⟩ := hFs.exists_pow_norm_le
  set K : ℝ := (Fintype.card (ix n₁ na nm) : ℝ) with hK
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hstep : ∀ T, (errMap S.fullC S.R S.fullA Sinf
      * (S.dareFrom L₀ T - Sinf)
      * (errMap S.fullC S.R S.fullA Sinf)ᵀ
      + (fun _ : ℕ => (0 : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ)) T
      - (S.dareFrom L₀ (T + 1) - Sinf)).PosSemidef := by
    intro T
    have h := S.supremal_gap_step hS hL₀ hdom T
    simpa using h
  have hiter := loewner_iter hstep
  refine ⟨K ^ 3 * (c * ‖L₀ - Sinf‖ * (K * c)), γ * γ,
    by positivity, by positivity, by nlinarith, fun T => ?_⟩
  have hit := hiter T
  have hzero : (∑ j ∈ Finset.range T,
      errMap S.fullC S.R S.fullA Sinf ^ (T - 1 - j)
        * (fun _ : ℕ => (0 : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ)) j
        * (errMap S.fullC S.R S.fullA Sinf ^ (T - 1 - j))ᵀ)
      = 0 := by
    simp
  rw [hzero, add_zero] at hit
  have hnorm := psd_norm_le_of_loewner
    (S.supremal_gap_posSemidef hS hL₀ hdom T) hit
  have hpowT : ‖(errMap S.fullC S.R S.fullA Sinf ^ T)ᵀ‖
      ≤ K * (c * γ ^ T) := by
    refine le_trans (linfty_opNorm_transpose_le' _) ?_
    exact mul_le_mul_of_nonneg_left (hp T) hK0
  calc ‖S.dareFrom L₀ T - Sinf‖
      ≤ K ^ 3 * ‖errMap S.fullC S.R S.fullA Sinf ^ T
          * (S.dareFrom L₀ 0 - Sinf)
          * (errMap S.fullC S.R S.fullA Sinf ^ T)ᵀ‖ := hnorm
  _ ≤ K ^ 3 * ((c * γ ^ T) * ‖L₀ - Sinf‖ * (K * (c * γ ^ T))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine le_trans (norm_triple_le _ _ _) ?_
      refine mul_le_mul (mul_le_mul (hp T) le_rfl
        (norm_nonneg _) (by positivity)) hpowT (norm_nonneg _) ?_
      positivity
  _ = K ^ 3 * (c * ‖L₀ - Sinf‖ * (K * c)) * (γ * γ) ^ T := by
      rw [mul_pow]
      ring

set_option maxHeartbeats 1600000 in
/-- **The polarization sandwich**: the run's gap is normed by the two
anchors (the mechanism inside `thm:sufficiency`'s squeeze). -/
lemma dare_sandwich_norm (hSa : S.Siga.PosDef)
    (hS : S.IsStrongSolution Sinf) :
    ∀ T, ‖S.dare T - Sinf‖
      ≤ (Fintype.card (ix n₁ na nm) : ℝ) ^ 2
        * (3 * ((Fintype.card (ix n₁ na nm) : ℝ)
            * ‖S.dareFrom (S.Sig0 + Sinf) T - Sinf‖
          + (Fintype.card (ix n₁ na nm) : ℝ)
            * ‖S.dareFrom (S.slavedSeed 1) T - Sinf‖)) := by
  intro T
  have hlo : (S.dare T - S.dareFrom (S.slavedSeed 1) T).PosSemidef :=
    dareIter_mono (C := S.fullC) (A := S.fullA) (Qw := S.Qw)
      S.hR S.Qw_posSemidef
      (S.slavedSeed_posSemidef hSa one_pos.le) S.Sig0_posSemidef
      (S.slavedSeed_le_Sig0 hSa le_rfl) T
  have hhi : (S.dareFrom (S.Sig0 + Sinf) T - S.dare T).PosSemidef := by
    have h12 : (S.Sig0 + Sinf - S.Sig0).PosSemidef := by
      rw [add_sub_cancel_left]
      exact hS.posSemidef
    exact dareIter_mono S.hR S.Qw_posSemidef S.Sig0_posSemidef
      (S.Sig0_posSemidef.add hS.posSemidef) h12 T
  have hsym : (S.dare T - Sinf)ᵀ = S.dare T - Sinf := by
    have h1 : (S.dare T).PosSemidef :=
      dareIter_posSemidef S.hR S.Qw_posSemidef S.Sig0_posSemidef T
    rw [Matrix.transpose_sub, h1.1.transpose_eq_self,
      hS.posSemidef.1.transpose_eq_self]
  set K : ℝ := (Fintype.card (ix n₁ na nm) : ℝ) with hK
  have hKnn : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hq : ∀ x, |quadForm (S.dare T - Sinf) x|
      ≤ (K * ‖S.dareFrom (S.Sig0 + Sinf) T - Sinf‖
        + K * ‖S.dareFrom (S.slavedSeed 1) T - Sinf‖) * ‖x‖ ^ 2 := by
    intro x
    have hup : quadForm (S.dare T - Sinf) x
        ≤ quadForm (S.dareFrom (S.Sig0 + Sinf) T - Sinf) x := by
      refine quadForm_le_quadForm_of_posSemidef_sub ?_ x
      have heq : S.dareFrom (S.Sig0 + Sinf) T - Sinf
          - (S.dare T - Sinf)
          = S.dareFrom (S.Sig0 + Sinf) T - S.dare T := by
        abel
      rwa [heq]
    have hdown : quadForm (S.dareFrom (S.slavedSeed 1) T - Sinf) x
        ≤ quadForm (S.dare T - Sinf) x := by
      refine quadForm_le_quadForm_of_posSemidef_sub ?_ x
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
  exact symm_norm_le_of_abs_quadForm_le hsym
    (by positivity) hq

set_option maxHeartbeats 800000 in
/-- **`thm:sufficiency`, rate refinement (E3)**: under C1, C2w and
C3w, the run from the prior is attracted to the strong solution
**geometrically** — the squeeze with both anchors contracting. -/
theorem sufficiency_geometric (hnm : nm = 0) (hC1 : S.C1)
    (hC2w : S.C2w) (hS : S.IsStrongSolution Sinf) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ T, ‖S.dare T - Sinf‖ ≤ C * ρ ^ T := by
  haveI hie : IsEmpty (Fin nm) := by
    subst hnm
    infer_instance
  have hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ (0:ℝ) := fun k =>
    le_of_eq (norm_eq_zero_of_isEmpty _)
  have hSa : S.Siga.PosDef := S.criterion_w.mp hC2w
  have hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf) :=
    (S.strong_isSchurStable_iff_C3w hC1 hS).mpr hnm
  have hup := S.supremal_geometric hC1 hS
    (S.Sig0_posSemidef.add hS.posSemidef)
    (by rw [add_sub_cancel_right]; exact S.Sig0_posSemidef) hFs
  have hlow : GeoDecay
      (fun T => ‖S.dareFrom (S.slavedSeed 1) T - Sinf‖) :=
    S.lowsqueeze_geometric hC1 hSa hS one_pos hPB
  set K : ℝ := (Fintype.card (ix n₁ na nm) : ℝ) with hK
  have hKnn : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hgeo : GeoDecay (fun T => ‖S.dare T - Sinf‖) := by
    refine GeoDecay.mono
      ((hup.const_mul (c := K ^ 2 * 3 * K) (by positivity)).add
        (hlow.const_mul (c := K ^ 2 * 3 * K) (by positivity)))
      fun T => ?_
    dsimp only
    have h := S.dare_sandwich_norm hSa hS T
    rw [← hK] at h
    calc ‖S.dare T - Sinf‖
        ≤ K ^ 2 * (3 * (K * ‖S.dareFrom (S.Sig0 + Sinf) T - Sinf‖
          + K * ‖S.dareFrom (S.slavedSeed 1) T - Sinf‖)) := h
    _ = K ^ 2 * 3 * K * ‖S.dareFrom (S.Sig0 + Sinf) T - Sinf‖
        + K ^ 2 * 3 * K
          * ‖S.dareFrom (S.slavedSeed 1) T - Sinf‖ := by ring
  exact hgeo

/-- **`eq:main-stab`, forward, assembled** (`thm:main` Part 2 with
the Phase-C converse): under C1, C2 and C3w, the strong solution
exists and the run from the prior is exponentially attracted to
it. -/
theorem main_stab_forward (hnm : nm = 0) (hC1 : S.C1) (hC2 : S.C2) :
    ∃ Sinf, S.IsStrongSolution Sinf
      ∧ ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
          ∀ T, ‖S.dare T - Sinf‖ ≤ C * ρ ^ T := by
  obtain ⟨Sg, hSg⟩ := S.exists_strong_solution hC1
  exact ⟨Sg, hSg,
    S.sufficiency_geometric hnm hC1 (S.C2w_of_C2 hC2) hSg⟩

end DareSystem

end Dare
end Estimation

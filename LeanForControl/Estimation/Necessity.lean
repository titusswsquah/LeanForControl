import LeanForControl.Estimation.Coercive
import LeanForControl.LinearSystems.ConstrainedQuadratic
import Architect

/-!
# Necessity of C1 and C2 (`prop:gas`, necessity half)

* **C1 is necessary**: if `(A, C)` has an undetectable mode, its real and
  imaginary parts generate zero-cost data, so the optimizer coincides
  with the prior mismatch and the terminal error follows the free
  dynamics — which do not decay along the undetectable direction.
* **C2 is necessary** (given C1, per the *patched* argument of
  `rawlings_quah_mueller_2026a`): a kernel witness of `Σ₂` pins the
  component of every feasible antistable initial error along itself, so
  window coercivity forces the value to grow linearly in `T`, while the
  horizon-extension inequality caps the value by the cumulative squared
  terminal error; GAS would make that sum sublinear — contradiction.
-/

namespace Estimation

namespace FIESystem

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

variable {n₁ n₂ m p : ℕ} (Sys : FIESystem n₁ n₂ m p)

/-! ### C1 is necessary -/

/-- Along an unobservable real direction, the optimal solution is the
free rollout of the prior mismatch: `e*(T|T) = A^T a`. -/
theorem optTerm_eq_pow_of_unobservable (a : Fin n₁ ⊕ Fin n₂ → ℝ)
    (hCa : ∀ k, Sys.fullC *ᵥ (Sys.fullA ^ k *ᵥ a) = 0) (T : ℕ) :
    Sys.optTerm a T = Sys.fullA ^ T *ᵥ a := by
  classical
  have hfeas : Sys.Feasible a a :=
    ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  -- the candidate `(a, 0)` costs nothing
  have hcost0 : Sys.fieCost a a (fun _ => 0) T = 0 := by
    unfold fieCost priorPenalty
    rw [sub_self]
    have hb1 : blk₁ (0 : Fin n₁ ⊕ Fin n₂ → ℝ) = 0 := rfl
    have hb2 : blk₂ (0 : Fin n₁ ⊕ Fin n₂ → ℝ) = 0 := rfl
    rw [hb1, hb2]
    have hcost : Sys.lq.cost a (fun _ => 0) T = 0 := by
      unfold LQSystem.cost
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Sys.traj_eq_pow_of_zero_inputs a (fun _ => 0) (fun _ _ => rfl)
        k (Finset.mem_range.mp hk).le]
      rw [Sys.quadForm_Qs, hCa k]
      simp [quadForm]
    rw [hcost]
    simp [quadForm]
  have hval0 : Sys.value a T = 0 :=
    le_antisymm
      (le_trans (Sys.value_le_fieCost hfeas _ T) (le_of_eq hcost0))
      (Sys.value_nonneg a T)
  -- the value splits into two nonnegative parts, so both vanish
  have hsplit : Sys.value a T
      = Sys.priorPenalty a (Sys.optInit a T)
        + quadForm (Sys.lq.ric T) (Sys.optInit a T) := rfl
  have hpp := Sys.priorPenalty_nonneg a (Sys.optInit a T)
  have hqq := (Sys.lq.ric_posSemidef T).quadForm_nonneg (Sys.optInit a T)
  have hprior0 : Sys.priorPenalty a (Sys.optInit a T) = 0 := by
    rw [hsplit] at hval0
    linarith
  have hric0 : quadForm (Sys.lq.ric T) (Sys.optInit a T) = 0 := by
    rw [hsplit] at hval0
    linarith
  -- the vanishing prior pins the optimizer to `a`
  have hopt : Sys.optInit a T = a := by
    have hq1 := Sys.hSig₁.symmPinv.quadForm_nonneg
      (blk₁ (Sys.optInit a T - a))
    have hq2 := Sys.hSig₂.symmPinv.quadForm_nonneg
      (blk₂ (Sys.optInit a T - a))
    have hpp' : quadForm (symmPinv Sys.hSig₁.1) (blk₁ (Sys.optInit a T - a))
        + quadForm (symmPinv Sys.hSig₂.1) (blk₂ (Sys.optInit a T - a))
          = 0 := hprior0
    obtain ⟨⟨z, hz⟩, ⟨w, hw⟩⟩ := Sys.optInit_feasible a T
    have hz0 : blk₁ (Sys.optInit a T - a) = 0 := by
      have h1 : quadForm (symmPinv Sys.hSig₁.1)
          (blk₁ (Sys.optInit a T - a)) = 0 := by linarith
      rw [hz, quadForm_symmPinv_image Sys.hSig₁] at h1
      rw [hz]
      exact Sys.hSig₁.mulVec_eq_zero_of_quadForm_eq_zero h1
    have hw0 : blk₂ (Sys.optInit a T - a) = 0 := by
      have h1 : quadForm (symmPinv Sys.hSig₂.1)
          (blk₂ (Sys.optInit a T - a)) = 0 := by linarith
      rw [hw, quadForm_symmPinv_image Sys.hSig₂] at h1
      rw [hw]
      exact Sys.hSig₂.mulVec_eq_zero_of_quadForm_eq_zero h1
    have hdiff : Sys.optInit a T - a = 0 := by
      rw [← sumElim_blk (Sys.optInit a T - a), hz0, hw0]
      funext i
      cases i <;> rfl
    have h2 : Sys.optInit a T = a + 0 := by
      rw [← hdiff]
      abel
    simpa using h2
  -- zero closed-loop cost kills every optimal input
  have hctrl0 : ∀ k < T, Sys.lq.optCtrl (Sys.optInit a T) T k = 0 := by
    have hc : Sys.lq.cost (Sys.optInit a T)
        (Sys.lq.optCtrl (Sys.optInit a T) T) T = 0 := by
      rw [Sys.lq.cost_optCtrl]
      exact hric0
    intro k hk
    have hstage : ∀ j ∈ Finset.range T,
        (0:ℝ) ≤ quadForm Sys.lq.Qs (Sys.lq.traj (Sys.optInit a T)
          (Sys.lq.optCtrl (Sys.optInit a T) T) j)
          + quadForm Sys.lq.Ru (Sys.lq.optCtrl (Sys.optInit a T) T j) :=
      fun j _ => Sys.lq.stage_nonneg _ _
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hstage).mp hc
      k (Finset.mem_range.mpr hk)
    have hQs := Sys.lq.hQs.quadForm_nonneg (Sys.lq.traj (Sys.optInit a T)
      (Sys.lq.optCtrl (Sys.optInit a T) T) k)
    have hRu0 : quadForm Sys.lq.Ru
        (Sys.lq.optCtrl (Sys.optInit a T) T k) = 0 := by
      have hRunn := Sys.lq.hRu.posSemidef.quadForm_nonneg
        (Sys.lq.optCtrl (Sys.optInit a T) T k)
      linarith
    by_contra hne
    exact absurd hRu0 (ne_of_gt (Sys.lq.hRu.quadForm_pos hne))
  -- hence the optimal trajectory is the free rollout
  unfold optTerm
  rw [← Sys.lq.traj_optCtrl,
    Sys.traj_eq_pow_of_zero_inputs _ _ hctrl0 T le_rfl, hopt]

/-- **C1 is necessary for GAS** (`prop:gas`, necessity of
detectability, direct linear argument). -/
theorem C1_of_isGAS (hgas : Sys.IsGAS) : Sys.C1 := by
  classical
  by_contra hnc1
  rw [C1, IsDetectable] at hnc1
  push Not at hnc1
  obtain ⟨μ, v, hμ, hveig, hvC, hvne⟩ := hnc1
  obtain ⟨σ, hσ0, hσb⟩ := hgas
  set vr : Fin n₁ ⊕ Fin n₂ → ℝ := fun i => (v i).re with hvr
  set vi : Fin n₁ ⊕ Fin n₂ → ℝ := fun i => (v i).im with hvi
  -- iterate the eigenrelation
  have heig : ∀ k, (complexify Sys.fullA) ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        hveig, smul_smul, ← pow_succ]
  -- the real and imaginary parts are unobservable directions
  have hre : ∀ k j, (((complexify Sys.fullA) ^ k *ᵥ v) j).re
      = (Sys.fullA ^ k *ᵥ vr) j := by
    intro k j
    rw [← complexify_pow]
    exact complexify_mulVec_re _ v j
  have him : ∀ k j, (((complexify Sys.fullA) ^ k *ᵥ v) j).im
      = (Sys.fullA ^ k *ᵥ vi) j := by
    intro k j
    rw [← complexify_pow]
    exact complexify_mulVec_im _ v j
  have hkerC : ∀ k, complexify Sys.fullC
      *ᵥ ((complexify Sys.fullA) ^ k *ᵥ v) = 0 := by
    intro k
    rw [heig k, Matrix.mulVec_smul, hvC, smul_zero]
  have hCr : ∀ k, Sys.fullC *ᵥ (Sys.fullA ^ k *ᵥ vr) = 0 := by
    intro k
    funext i
    have h1 : ((complexify Sys.fullC
        *ᵥ ((complexify Sys.fullA) ^ k *ᵥ v)) i).re = 0 := by
      rw [hkerC k]
      rfl
    rw [complexify_mulVec_re] at h1
    have h2 : (fun j => (((complexify Sys.fullA) ^ k *ᵥ v) j).re)
        = Sys.fullA ^ k *ᵥ vr := funext fun j => hre k j
    rw [h2] at h1
    exact h1
  have hCi : ∀ k, Sys.fullC *ᵥ (Sys.fullA ^ k *ᵥ vi) = 0 := by
    intro k
    funext i
    have h1 : ((complexify Sys.fullC
        *ᵥ ((complexify Sys.fullA) ^ k *ᵥ v)) i).im = 0 := by
      rw [hkerC k]
      rfl
    rw [complexify_mulVec_im] at h1
    have h2 : (fun j => (((complexify Sys.fullA) ^ k *ᵥ v) j).im)
        = Sys.fullA ^ k *ᵥ vi := funext fun j => him k j
    rw [h2] at h1
    exact h1
  -- the eigenvector has a nonvanishing coordinate
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hvne (funext hall)
  have hjpos : 0 < ‖v j‖ := norm_pos_iff.mpr hj
  -- the GAS bound forces the free rollouts to die — contradiction
  have hgrow : ∀ T, ‖v j‖ ≤ σ T * (‖vr‖ + ‖vi‖) := by
    intro T
    have h1 : ‖μ ^ T • v j‖ = ‖μ‖ ^ T * ‖v j‖ := by
      rw [norm_smul, norm_pow]
    have h2 : ‖v j‖ ≤ ‖μ ^ T • v j‖ := by
      rw [h1]
      have h3 : (1:ℝ) ≤ ‖μ‖ ^ T := one_le_pow₀ hμ
      nlinarith
    have h4 : μ ^ T • v j = ((complexify Sys.fullA) ^ T *ᵥ v) j := by
      rw [heig T]
      rfl
    have h5 : ‖μ ^ T • v j‖
        ≤ |(Sys.fullA ^ T *ᵥ vr) j| + |(Sys.fullA ^ T *ᵥ vi) j| := by
      rw [h4]
      have h6 := Complex.norm_le_abs_re_add_abs_im
        (((complexify Sys.fullA) ^ T *ᵥ v) j)
      rw [hre T j, him T j] at h6
      exact h6
    have h7 : |(Sys.fullA ^ T *ᵥ vr) j| ≤ ‖Sys.fullA ^ T *ᵥ vr‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm _ j
    have h8 : |(Sys.fullA ^ T *ᵥ vi) j| ≤ ‖Sys.fullA ^ T *ᵥ vi‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm _ j
    have h9 : ‖Sys.fullA ^ T *ᵥ vr‖ ≤ σ T * ‖vr‖ := by
      have := hσb T vr
      rwa [Sys.optTerm_eq_pow_of_unobservable vr hCr T] at this
    have h10 : ‖Sys.fullA ^ T *ᵥ vi‖ ≤ σ T * ‖vi‖ := by
      have := hσb T vi
      rwa [Sys.optTerm_eq_pow_of_unobservable vi hCi T] at this
    calc ‖v j‖ ≤ ‖μ ^ T • v j‖ := h2
    _ ≤ |(Sys.fullA ^ T *ᵥ vr) j| + |(Sys.fullA ^ T *ᵥ vi) j| := h5
    _ ≤ σ T * ‖vr‖ + σ T * ‖vi‖ := by
        linarith
    _ = σ T * (‖vr‖ + ‖vi‖) := by ring
  have hlim : Tendsto (fun T => σ T * (‖vr‖ + ‖vi‖)) atTop (nhds 0) := by
    have := hσ0.mul_const (‖vr‖ + ‖vi‖)
    simpa using this
  have hev := hlim.eventually_lt_const hjpos
  obtain ⟨T, hT⟩ := hev.exists
  exact absurd (hgrow T) (not_le.mpr hT)

end FIESystem

end Estimation

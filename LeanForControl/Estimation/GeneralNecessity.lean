import LeanForControl.Estimation.Reduction
import LeanForControl.Estimation.Coercive
import Architect

/-!
# Necessity of C1 and C2 at the general level

The necessity halves of the headline theorem cannot be routed through
the reduction of `Estimation.Reduction`, because the correspondence of
prior penalties itself requires C2. This file replays the two necessity
arguments directly on a `GeneralSystem`: the unobservable-direction
argument for C1, and the patched pinned-kernel argument for C2 (linear
window growth against the sublinear GAS cap). The window growth is
imported from the reduced system through the prior-free
`exists_window_ric_growth`, which needs no penalty correspondence.
-/

namespace Estimation

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

namespace GeneralSystem

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-! ### C1 is necessary -/

lemma feasible_self (a : Fin n → ℝ) : S.Feasible a a :=
  ⟨0, by simp⟩

lemma traj_eq_pow_of_zero_inputs (e₀ : Fin n → ℝ)
    (u : ℕ → Fin m → ℝ) {T : ℕ} (hu : ∀ k < T, u k = 0) :
    ∀ k ≤ T, S.glq.traj e₀ u k = S.A ^ k *ᵥ e₀ := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [LQSystem.traj_zero]
  | succ k ih =>
    intro hk
    rw [LQSystem.traj_succ, ih (by omega), hu k (by omega),
      Matrix.mulVec_zero, add_zero, glq_A_eq, Matrix.mulVec_mulVec,
      ← pow_succ']

/-- Along an unobservable real direction, the optimal solution is the
free rollout of the prior mismatch. -/
theorem optTerm_eq_pow_of_unobservable (a : Fin n → ℝ)
    (hCa : ∀ k, S.C *ᵥ (S.A ^ k *ᵥ a) = 0) (T : ℕ) :
    S.optTerm a T = S.A ^ T *ᵥ a := by
  classical
  have hfeas := S.feasible_self a
  have hcost0 : S.gCost a a (fun _ => 0) T = 0 := by
    unfold gCost priorPen
    rw [sub_self]
    have hcost : S.glq.cost a (fun _ => 0) T = 0 := by
      unfold LQSystem.cost
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [S.traj_eq_pow_of_zero_inputs a (fun _ => 0) (fun _ _ => rfl)
        k (Finset.mem_range.mp hk).le]
      rw [S.quadForm_glq_Qs, hCa k]
      simp [quadForm]
    rw [hcost]
    simp [quadForm]
  have hval0 : S.value a T = 0 :=
    le_antisymm
      (le_trans (S.value_le_gCost hfeas _ T) (le_of_eq hcost0))
      (S.value_nonneg a T)
  have hsplit : S.value a T
      = S.priorPen a (S.optInit a T)
        + quadForm (S.glq.ric T) (S.optInit a T) := rfl
  have hpp := S.priorPen_nonneg a (S.optInit a T)
  have hqq := (S.glq.ric_posSemidef T).quadForm_nonneg (S.optInit a T)
  have hprior0 : S.priorPen a (S.optInit a T) = 0 := by
    rw [hsplit] at hval0
    linarith
  have hric0 : quadForm (S.glq.ric T) (S.optInit a T) = 0 := by
    rw [hsplit] at hval0
    linarith
  -- the vanishing prior pins the optimizer to `a`
  have hopt : S.optInit a T = a := by
    obtain ⟨z, hz⟩ := S.optInit_feasible a T
    have h1 : quadForm (symmPinv S.hSig0.1) (S.optInit a T - a) = 0 :=
      hprior0
    rw [hz, quadForm_symmPinv_image S.hSig0] at h1
    have h2 := S.hSig0.mulVec_eq_zero_of_quadForm_eq_zero h1
    rw [← hz] at h2
    have h3 : S.optInit a T = a + 0 := by
      rw [← h2]
      abel
    simpa using h3
  -- zero closed-loop cost kills every optimal input
  have hctrl0 : ∀ k < T, S.glq.optCtrl (S.optInit a T) T k = 0 := by
    have hc : S.glq.cost (S.optInit a T)
        (S.glq.optCtrl (S.optInit a T) T) T = 0 := by
      rw [S.glq.cost_optCtrl]
      exact hric0
    intro k hk
    have hstage : ∀ j ∈ Finset.range T,
        (0:ℝ) ≤ quadForm S.glq.Qs (S.glq.traj (S.optInit a T)
          (S.glq.optCtrl (S.optInit a T) T) j)
          + quadForm S.glq.Ru (S.glq.optCtrl (S.optInit a T) T j) :=
      fun j _ => S.glq.stage_nonneg _ _
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hstage).mp hc
      k (Finset.mem_range.mpr hk)
    have hQs := S.glq.hQs.quadForm_nonneg (S.glq.traj (S.optInit a T)
      (S.glq.optCtrl (S.optInit a T) T) k)
    have hRu0 : quadForm S.glq.Ru
        (S.glq.optCtrl (S.optInit a T) T k) = 0 := by
      have hRunn := S.glq.hRu.posSemidef.quadForm_nonneg
        (S.glq.optCtrl (S.optInit a T) T k)
      linarith
    by_contra hne
    exact absurd hRu0 (ne_of_gt (S.glq.hRu.quadForm_pos hne))
  unfold optTerm
  rw [← S.glq.traj_optCtrl,
    S.traj_eq_pow_of_zero_inputs _ _ hctrl0 T le_rfl, hopt]

/-- **C1 is necessary for GAS** (general coordinates). -/
theorem C1_of_isGAS (hgas : S.IsGAS) : S.C1 := by
  classical
  by_contra hnc1
  rw [C1, IsDetectable] at hnc1
  push Not at hnc1
  obtain ⟨μ, v, hμ, hveig, hvC, hvne⟩ := hnc1
  obtain ⟨σ, hσ0, hσb⟩ := hgas
  set vr : Fin n → ℝ := fun i => (v i).re with hvr
  set vi : Fin n → ℝ := fun i => (v i).im with hvi
  have heig : ∀ k, (complexify S.A) ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        hveig, smul_smul, ← pow_succ]
  have hre : ∀ k j, (((complexify S.A) ^ k *ᵥ v) j).re
      = (S.A ^ k *ᵥ vr) j := by
    intro k j
    rw [← complexify_pow]
    exact complexify_mulVec_re _ v j
  have him : ∀ k j, (((complexify S.A) ^ k *ᵥ v) j).im
      = (S.A ^ k *ᵥ vi) j := by
    intro k j
    rw [← complexify_pow]
    exact complexify_mulVec_im _ v j
  have hkerC : ∀ k, complexify S.C
      *ᵥ ((complexify S.A) ^ k *ᵥ v) = 0 := by
    intro k
    rw [heig k, Matrix.mulVec_smul, hvC, smul_zero]
  have hCr : ∀ k, S.C *ᵥ (S.A ^ k *ᵥ vr) = 0 := by
    intro k
    funext i
    have h1 : ((complexify S.C
        *ᵥ ((complexify S.A) ^ k *ᵥ v)) i).re = 0 := by
      rw [hkerC k]
      rfl
    rw [complexify_mulVec_re] at h1
    have h2 : (fun j => (((complexify S.A) ^ k *ᵥ v) j).re)
        = S.A ^ k *ᵥ vr := funext fun j => hre k j
    rw [h2] at h1
    exact h1
  have hCi : ∀ k, S.C *ᵥ (S.A ^ k *ᵥ vi) = 0 := by
    intro k
    funext i
    have h1 : ((complexify S.C
        *ᵥ ((complexify S.A) ^ k *ᵥ v)) i).im = 0 := by
      rw [hkerC k]
      rfl
    rw [complexify_mulVec_im] at h1
    have h2 : (fun j => (((complexify S.A) ^ k *ᵥ v) j).im)
        = S.A ^ k *ᵥ vi := funext fun j => him k j
    rw [h2] at h1
    exact h1
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hvne (funext hall)
  have hjpos : 0 < ‖v j‖ := norm_pos_iff.mpr hj
  have hgrow : ∀ T, ‖v j‖ ≤ σ T * (‖vr‖ + ‖vi‖) := by
    intro T
    have h1 : ‖μ ^ T • v j‖ = ‖μ‖ ^ T * ‖v j‖ := by
      rw [norm_smul, norm_pow]
    have h2 : ‖v j‖ ≤ ‖μ ^ T • v j‖ := by
      rw [h1]
      have h3 : (1:ℝ) ≤ ‖μ‖ ^ T := one_le_pow₀ hμ
      nlinarith
    have h4 : μ ^ T • v j = ((complexify S.A) ^ T *ᵥ v) j := by
      rw [heig T]
      rfl
    have h5 : ‖μ ^ T • v j‖
        ≤ |(S.A ^ T *ᵥ vr) j| + |(S.A ^ T *ᵥ vi) j| := by
      rw [h4]
      have h6 := Complex.norm_le_abs_re_add_abs_im
        (((complexify S.A) ^ T *ᵥ v) j)
      rw [hre T j, him T j] at h6
      exact h6
    have h7 : |(S.A ^ T *ᵥ vr) j| ≤ ‖S.A ^ T *ᵥ vr‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm _ j
    have h8 : |(S.A ^ T *ᵥ vi) j| ≤ ‖S.A ^ T *ᵥ vi‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm _ j
    have h9 : ‖S.A ^ T *ᵥ vr‖ ≤ σ T * ‖vr‖ := by
      have h := hσb T vr
      rwa [S.optTerm_eq_pow_of_unobservable vr hCr T] at h
    have h10 : ‖S.A ^ T *ᵥ vi‖ ≤ σ T * ‖vi‖ := by
      have h := hσb T vi
      rwa [S.optTerm_eq_pow_of_unobservable vi hCi T] at h
    calc ‖v j‖ ≤ ‖μ ^ T • v j‖ := h2
    _ ≤ |(S.A ^ T *ᵥ vr) j| + |(S.A ^ T *ᵥ vi) j| := h5
    _ ≤ σ T * ‖vr‖ + σ T * ‖vi‖ := by linarith
    _ = σ T * (‖vr‖ + ‖vi‖) := by ring
  have hlim : Tendsto (fun T => σ T * (‖vr‖ + ‖vi‖)) atTop (nhds 0) := by
    have h := hσ0.mul_const (‖vr‖ + ‖vi‖)
    simpa using h
  have hev := hlim.eventually_lt_const hjpos
  obtain ⟨T, hT⟩ := hev.exists
  exact absurd (hgrow T) (not_le.mpr hT)

end GeneralSystem

end Estimation

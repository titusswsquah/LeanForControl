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

/-! ### C2 is necessary (patched argument) -/

/-- The value at horizon zero vanishes. -/
lemma value_zero (a : Fin n₁ ⊕ Fin n₂ → ℝ) : Sys.value a 0 = 0 := by
  refine le_antisymm ?_ (Sys.value_nonneg a 0)
  have hfeas : Sys.Feasible a a := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  refine le_trans (Sys.value_le_fieCost hfeas (fun _ => 0) 0) ?_
  unfold fieCost priorPenalty
  rw [sub_self]
  have hb1 : blk₁ (0 : Fin n₁ ⊕ Fin n₂ → ℝ) = 0 := rfl
  have hb2 : blk₂ (0 : Fin n₁ ⊕ Fin n₂ → ℝ) = 0 := rfl
  rw [hb1, hb2, LQSystem.cost_zero]
  simp [quadForm]

/-- **Horizon extension** (`eq:Venergy` step): one more stage costs at
most the measured output energy of the current terminal error. -/
theorem value_succ_le (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.value a (T + 1)
      ≤ Sys.value a T + quadForm Sys.lq.Qs (Sys.optTerm a T) := by
  classical
  set e₀ := Sys.optInit a T with he₀
  set u : ℕ → Fin m → ℝ := Sys.lq.optCtrl e₀ T with hu
  set u' : ℕ → Fin m → ℝ := fun j => if j < T then u j else 0 with hu'
  have h1 := Sys.value_le_fieCost (Sys.optInit_feasible a T) u' (T + 1)
  rw [← he₀] at h1
  have hc : Sys.lq.cost e₀ u' (T + 1)
      = Sys.lq.cost e₀ u' T
        + (quadForm Sys.lq.Qs (Sys.lq.traj e₀ u' T)
          + quadForm Sys.lq.Ru (u' T)) := by
    unfold LQSystem.cost
    rw [Finset.sum_range_succ]
  have hagree : ∀ j < T, u' j = u j := by
    intro j hj
    rw [hu']
    simp [hj]
  have hcostT : Sys.lq.cost e₀ u' T = Sys.lq.cost e₀ u T := by
    unfold LQSystem.cost
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Sys.lq.traj_congr e₀ fun j hj =>
        hagree j (lt_of_lt_of_le hj (Finset.mem_range.mp hk).le),
      hagree k (Finset.mem_range.mp hk)]
  have huT : u' T = 0 := by
    rw [hu']
    simp
  have hterm : Sys.lq.traj e₀ u' T = Sys.optTerm a T := by
    rw [Sys.lq.traj_congr e₀ fun j hj => hagree j hj, hu,
      Sys.lq.traj_optCtrl]
    rfl
  have h4 : Sys.priorPenalty a e₀ + Sys.lq.cost e₀ u T
      = Sys.value a T := by
    have h5 := Sys.fieCost_optCtrl a T
    unfold fieCost at h5
    rw [← he₀, ← hu] at h5
    exact h5
  have h2 : Sys.fieCost a e₀ u' (T + 1)
      = Sys.value a T + quadForm Sys.lq.Qs (Sys.optTerm a T) := by
    unfold fieCost
    rw [hc, hcostT, huT, hterm]
    have h3 : quadForm Sys.lq.Ru (0 : Fin m → ℝ) = 0 := by
      simp [quadForm]
    rw [h3]
    linarith
  linarith [h2 ▸ h1]

/-- The value is capped by the cumulative measured energy of the
terminal errors (`eq:Venergy`). -/
theorem value_le_sum_optTerm (a : Fin n₁ ⊕ Fin n₂ → ℝ) : ∀ T : ℕ,
    Sys.value a T
      ≤ ∑ k ∈ Finset.range T, quadForm Sys.lq.Qs (Sys.optTerm a k)
  | 0 => by
    rw [Sys.value_zero]
    simp
  | T + 1 => by
    rw [Finset.sum_range_succ]
    have h1 := Sys.value_succ_le a T
    have h2 := value_le_sum_optTerm a T
    linarith

/-- **C2 is necessary for GAS given C1** (`prop:gas`, necessity of C2,
per the patched argument): a kernel witness of `Σ₂` pins the antistable
optimizer's component along itself, so the value grows linearly, while
GAS would cap it sublinearly. -/
theorem C2_of_isGAS (hC1 : Sys.C1) (hgas : Sys.IsGAS) : Sys.C2 := by
  classical
  by_contra hnc2
  -- a kernel witness of the antistable prior block
  obtain ⟨w, hwne, hwker⟩ : ∃ w : Fin n₂ → ℝ, w ≠ 0 ∧
      Sys.Sig₂ *ᵥ w = 0 := by
    by_contra hno
    push Not at hno
    refine hnc2 (Matrix.PosDef.of_dotProduct_mulVec_pos Sys.hSig₂.1
      fun x hx => ?_)
    have h1 : 0 ≤ quadForm Sys.Sig₂ x := Sys.hSig₂.quadForm_nonneg x
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (Sys.hSig₂.mulVec_eq_zero_of_quadForm_eq_zero h.symm)
        (hno x hx)
  set a : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim 0 w with ha
  -- the pinned component of every optimizer
  have hpin : ∀ T, w ⬝ᵥ blk₂ (Sys.optInit a T) = w ⬝ᵥ w := by
    intro T
    obtain ⟨_, ⟨z, hz⟩⟩ := Sys.optInit_feasible a T
    have h2 : blk₂ (Sys.optInit a T) - blk₂ a = Sys.Sig₂ *ᵥ z := by
      rw [← blk₂_sub]
      exact hz
    have h1 : w ⬝ᵥ (blk₂ (Sys.optInit a T) - blk₂ a) = 0 := by
      rw [h2, dotProduct_mulVec_eq, Sys.hSig₂.1.transpose_eq_self,
        hwker, zero_dotProduct]
    have h3 : blk₂ a = w := rfl
    rw [h3] at h1
    rw [dotProduct_sub] at h1
    linarith
  -- pinning bounds the antistable optimizer's norm below
  have hww : 0 < w ⬝ᵥ w := by
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hwne (funext hall)
    have h1 : (0:ℝ) < w j * w j := mul_self_pos.mpr hj
    have h2 : ∀ i ∈ Finset.univ, (0:ℝ) ≤ w i * w i :=
      fun i _ => mul_self_nonneg _
    exact Finset.sum_pos' h2 ⟨j, Finset.mem_univ j, h1⟩
  have hne2 : Nonempty (Fin n₂) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact hwne (funext fun i => (hemp.false i).elim)
  have hcard : (0:ℝ) < (Fintype.card (Fin n₂) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  set c₀ := (w ⬝ᵥ w) / (Fintype.card (Fin n₂) : ℝ) with hc₀
  have hc₀pos : 0 < c₀ := div_pos hww hcard
  have hlow : ∀ T, c₀ ≤ ‖blk₂ (Sys.optInit a T)‖ ^ 2 := by
    intro T
    set x := blk₂ (Sys.optInit a T) with hx
    have hCS : (w ⬝ᵥ x) ^ 2 ≤ (w ⬝ᵥ w) * (x ⬝ᵥ x) := by
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w x
      simpa [dotProduct, sq] using h1
    rw [hpin T] at hCS
    have h2 : w ⬝ᵥ w ≤ x ⬝ᵥ x := by nlinarith
    have h3 : x ⬝ᵥ x ≤ (Fintype.card (Fin n₂) : ℝ) * ‖x‖ ^ 2 :=
      dotProduct_le_card_mul_sq_norm x
    rw [hc₀, div_le_iff₀ hcard]
    calc w ⬝ᵥ w ≤ x ⬝ᵥ x := h2
    _ ≤ (Fintype.card (Fin n₂) : ℝ) * ‖x‖ ^ 2 := h3
    _ = ‖x‖ ^ 2 * (Fintype.card (Fin n₂) : ℝ) := mul_comm _ _
  -- linear growth of the value along full windows
  obtain ⟨β, hβ, hgrow⟩ := Sys.exists_window_value_growth hC1
  set M := n₁ + n₂ with hM
  have hM1 : 1 ≤ M := by
    have h1 : 0 < n₂ := Fin.pos_iff_nonempty.mpr hne2
    omega
  have hlin : ∀ J : ℕ, 1 ≤ J → β * c₀ * J ≤ Sys.value a (M * J) := by
    intro J hJ
    have h1 := hgrow a J (M * J) hJ le_rfl
    have h2 := hlow (M * J)
    have h3 : (0:ℝ) ≤ (J:ℝ) := Nat.cast_nonneg J
    have h4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hβ.le h3)
    calc β * c₀ * (J:ℝ) = β * (J:ℝ) * c₀ := by ring
    _ ≤ β * (J:ℝ) * ‖blk₂ (Sys.optInit a (M * J))‖ ^ 2 := h4
    _ ≤ Sys.value a (M * J) := h1
  -- GAS caps the value sublinearly
  obtain ⟨σ, hσ0, hσb⟩ := hgas
  obtain ⟨cy, hcy, hyb⟩ := exists_quadForm_le Sys.lq.Qs
  have hane : ‖a‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro ha0
    apply hwne
    have h1 : blk₂ a = w := rfl
    rw [ha0] at h1
    exact h1.symm.trans rfl
  have hup : ∀ T, Sys.value a T
      ≤ cy * ‖a‖ ^ 2 * ∑ k ∈ Finset.range T, σ k ^ 2 := by
    intro T
    refine le_trans (Sys.value_le_sum_optTerm a T) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 := hyb (Sys.optTerm a k)
    have h2 := hσb k a
    have h3 : ‖Sys.optTerm a k‖ ^ 2 ≤ (σ k * ‖a‖) ^ 2 := by
      have h0 : 0 ≤ ‖Sys.optTerm a k‖ := norm_nonneg _
      nlinarith
    calc quadForm Sys.lq.Qs (Sys.optTerm a k)
        ≤ cy * ‖Sys.optTerm a k‖ ^ 2 := h1
    _ ≤ cy * (σ k * ‖a‖) ^ 2 := mul_le_mul_of_nonneg_left h3 hcy.le
    _ = cy * ‖a‖ ^ 2 * σ k ^ 2 := by ring
  -- Cesàro convergence of the GAS rates kills the upper bound
  have hσ2 : Tendsto (fun k => σ k ^ 2) atTop (nhds 0) := by
    have h1 := hσ0.pow 2
    simpa using h1
  have hces := hσ2.cesaro
  have hMJ : Tendsto (fun J : ℕ => M * J) atTop atTop := by
    refine tendsto_atTop_mono (fun J => ?_) tendsto_id
    calc (J:ℕ) = 1 * J := (one_mul J).symm
    _ ≤ M * J := Nat.mul_le_mul_right J hM1
  have hsub := hces.comp hMJ
  have hcyA : (0:ℝ) < cy * ‖a‖ ^ 2 := by
    have h1 : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg a) (Ne.symm hane)
    positivity
  set δ := β * c₀ / (cy * ‖a‖ ^ 2 * M) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    have : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
    positivity
  have hδle : ∀ J : ℕ, 1 ≤ J →
      δ ≤ ((M * J : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (M * J), σ k ^ 2 := by
    intro J hJ
    have h1 := hlin J hJ
    have h2 := hup (M * J)
    have hMJpos : (0:ℝ) < ((M * J : ℕ) : ℝ) := by
      have h3 : 0 < M * J := Nat.mul_pos (by omega) (by omega)
      exact_mod_cast h3
    rw [smul_eq_mul, inv_mul_eq_div, le_div_iff₀ hMJpos, hδ]
    have hcast : ((M * J : ℕ) : ℝ) = (M:ℝ) * (J:ℝ) := by push_cast; ring
    rw [hcast, div_mul_eq_mul_div, div_le_iff₀ (by positivity :
      (0:ℝ) < cy * ‖a‖ ^ 2 * (M:ℝ))]
    have h4 : β * c₀ * J ≤ cy * ‖a‖ ^ 2
        * ∑ k ∈ Finset.range (M * J), σ k ^ 2 := le_trans h1 h2
    have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
    nlinarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (M * J)) =>
      sq_nonneg (σ k))]
  obtain ⟨J, hJlt, hJ1⟩ :=
    ((hsub.eventually_lt_const hδpos).and (eventually_ge_atTop 1)).exists
  exact absurd (hδle J hJ1) (not_le.mpr hJlt)

end FIESystem

end Estimation

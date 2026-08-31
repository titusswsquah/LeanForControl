import LeanForControl.Estimation.Reduction
import LeanForControl.Estimation.Coercive
import LeanForControl.LinearSystems.IOSS
import Architect

/-!
# Necessity of C1 and C2 at the general level

The necessity halves of the headline theorem cannot be routed through
the reduction of `Estimation.Reduction`, because the correspondence of
prior penalties itself requires C2. This file replays the two necessity
arguments directly on a `GeneralSystem`: the unobservable-direction
argument for C1, and the patched pinned-kernel argument for C2 (linear
window growth against the sublinear GAS cap). The growth is produced
by the paper's `eq:iosssum` chain — the IOSS Lyapunov summation along
the optimal trajectories, dominated by the optimal cost, against the
antistable gramian — with no penalty correspondence needed.
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

/-! ### The measured-energy cap (`eq:Venergy`) -/

lemma value_zero (a : Fin n → ℝ) : S.value a 0 = 0 := by
  refine le_antisymm ?_ (S.value_nonneg a 0)
  refine le_trans (S.value_le_gCost (S.feasible_self a)
    (fun _ => 0) 0) ?_
  unfold gCost priorPen
  rw [sub_self, LQSystem.cost_zero]
  simp [quadForm]

/-- One more stage costs at most the measured output energy of the
current terminal error. -/
theorem value_succ_le (a : Fin n → ℝ) (T : ℕ) :
    S.value a (T + 1)
      ≤ S.value a T + quadForm S.glq.Qs (S.optTerm a T) := by
  classical
  set e₀ := S.optInit a T with he₀
  set u : ℕ → Fin m → ℝ := S.glq.optCtrl e₀ T with hu
  set u' : ℕ → Fin m → ℝ := fun j => if j < T then u j else 0 with hu'
  have h1 := S.value_le_gCost (S.optInit_feasible a T) u' (T + 1)
  rw [← he₀] at h1
  have hc : S.glq.cost e₀ u' (T + 1)
      = S.glq.cost e₀ u' T
        + (quadForm S.glq.Qs (S.glq.traj e₀ u' T)
          + quadForm S.glq.Ru (u' T)) := by
    unfold LQSystem.cost
    rw [Finset.sum_range_succ]
  have hagree : ∀ j < T, u' j = u j := by
    intro j hj
    rw [hu']
    simp [hj]
  have hcostT : S.glq.cost e₀ u' T = S.glq.cost e₀ u T := by
    unfold LQSystem.cost
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [S.glq.traj_congr e₀ fun j hj =>
        hagree j (lt_of_lt_of_le hj (Finset.mem_range.mp hk).le),
      hagree k (Finset.mem_range.mp hk)]
  have huT : u' T = 0 := by
    rw [hu']
    simp
  have hterm : S.glq.traj e₀ u' T = S.optTerm a T := by
    rw [S.glq.traj_congr e₀ fun j hj => hagree j hj, hu,
      S.glq.traj_optCtrl]
    rfl
  have h4 : S.priorPen a e₀ + S.glq.cost e₀ u T = S.value a T := by
    have h5 := S.gCost_optCtrl a T
    unfold gCost at h5
    rw [← he₀, ← hu] at h5
    exact h5
  have h2 : S.gCost a e₀ u' (T + 1)
      = S.value a T + quadForm S.glq.Qs (S.optTerm a T) := by
    unfold gCost
    rw [hc, hcostT, huT, hterm]
    have h3 : quadForm S.glq.Ru (0 : Fin m → ℝ) = 0 := by
      simp [quadForm]
    rw [h3]
    linarith
  linarith [h2 ▸ h1]

/-- The value is capped by the cumulative measured energy of the
terminal errors. -/
theorem value_le_sum_optTerm (a : Fin n → ℝ) : ∀ T : ℕ,
    S.value a T
      ≤ ∑ k ∈ Finset.range T, quadForm S.glq.Qs (S.optTerm a k)
  | 0 => by
    rw [S.value_zero]
    simp
  | T + 1 => by
    rw [Finset.sum_range_succ]
    have h1 := S.value_succ_le a T
    have h2 := value_le_sum_optTerm a T
    linarith

/-- Second-block coordinates through `redT` agree with the staircase
coordinates. -/
lemma redT_mulVec_inr (x : Fin n → ℝ) (i : Fin S.rk2) :
    (S.redT *ᵥ x) (Sum.inr i) = (S.stairW *ᵥ x) (Sum.inr i) := by
  unfold redT decT
  rw [← Matrix.mulVec_mulVec, Matrix.fromBlocks_mulVec]
  simp

/-! ### C2 is necessary (patched argument, general coordinates) -/

/-- **C2 is necessary for GAS given C1** (general coordinates). -/
theorem C2_of_isGAS (hC1 : S.C1) (hgas : S.IsGAS) : S.C2 := by
  classical
  by_contra hnc2
  -- a kernel witness of the antistable staircase prior block
  obtain ⟨w, hwne, hwker⟩ : ∃ w : Fin S.rk2 → ℝ, w ≠ 0 ∧
      S.stairSig.toBlocks₂₂ *ᵥ w = 0 := by
    by_contra hno
    push Not at hno
    have hPSD : S.stairSig.toBlocks₂₂.PosSemidef :=
      S.stairSig_posSemidef.submatrix Sum.inr
    refine hnc2 ((S.C2_iff_stairSig₂_posDef).mpr
      (Matrix.PosDef.of_dotProduct_mulVec_pos hPSD.1 fun x hx => ?_))
    have h1 : 0 ≤ quadForm S.stairSig.toBlocks₂₂ x :=
      hPSD.quadForm_nonneg x
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (hPSD.mulVec_eq_zero_of_quadForm_eq_zero h.symm)
        (hno x hx)
  -- the pulled-back kernel direction
  set ξ : Fin n → ℝ :=
    S.stairWᵀ *ᵥ Sum.elim (0 : Fin S.rk1 → ℝ) w with hξ
  have hξker : S.Sig0 *ᵥ ξ = 0 := by
    refine S.hSig0.mulVec_eq_zero_of_quadForm_eq_zero ?_
    rw [hξ, ← stairSig₂_quadForm]
    show w ⬝ᵥ (S.stairSig.toBlocks₂₂ *ᵥ w) = 0
    rw [hwker, dotProduct_zero]
  have hξne : ξ ≠ 0 := by
    intro h0
    exact hwne (S.transposeW_elim_eq_zero (hξ ▸ h0))
  -- the pinned component of every optimizer
  have hpair : ∀ x : Fin n → ℝ,
      w ⬝ᵥ (fun i => (S.stairW *ᵥ x) (Sum.inr i)) = ξ ⬝ᵥ x := by
    intro x
    rw [hξ, mulVec_dotProduct_eq, Matrix.transpose_transpose]
    simp [dotProduct, Fintype.sum_sum_type]
  have hpin : ∀ T, ξ ⬝ᵥ S.optInit ξ T = ξ ⬝ᵥ ξ := by
    intro T
    obtain ⟨z, hz⟩ := S.optInit_feasible ξ T
    have h1 : ξ ⬝ᵥ (S.optInit ξ T - ξ) = 0 := by
      rw [hz, dotProduct_mulVec_eq,
        S.hSig0.1.transpose_eq_self, hξker, zero_dotProduct]
    rw [dotProduct_sub] at h1
    linarith
  have hξξ : 0 < ξ ⬝ᵥ ξ := by
    obtain ⟨j, hj⟩ : ∃ j, ξ j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hξne (funext hall)
    have h1 : (0:ℝ) < ξ j * ξ j := mul_self_pos.mpr hj
    have h2 : ∀ i ∈ Finset.univ, (0:ℝ) ≤ ξ i * ξ i :=
      fun i _ => mul_self_nonneg _
    exact Finset.sum_pos' h2 ⟨j, Finset.mem_univ j, h1⟩
  have hww : 0 < w ⬝ᵥ w := by
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hwne (funext hall)
    have h1 : (0:ℝ) < w j * w j := mul_self_pos.mpr hj
    have h2 : ∀ i ∈ Finset.univ, (0:ℝ) ≤ w i * w i :=
      fun i _ => mul_self_nonneg _
    exact Finset.sum_pos' h2 ⟨j, Finset.mem_univ j, h1⟩
  have hne2 : Nonempty (Fin S.rk2) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact hwne (funext fun i => (hemp.false i).elim)
  have hcard : (0:ℝ) < (Fintype.card (Fin S.rk2) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  -- lower bound on the antistable coordinates of the optimizer
  set c₀ := (ξ ⬝ᵥ ξ) ^ 2
    / ((w ⬝ᵥ w) * (Fintype.card (Fin S.rk2) : ℝ)) with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    positivity
  have hlow : ∀ T, c₀
      ≤ ‖FIESystem.blk₂ (S.redT *ᵥ S.optInit ξ T)‖ ^ 2 := by
    intro T
    set x : Fin S.rk2 → ℝ :=
      FIESystem.blk₂ (S.redT *ᵥ S.optInit ξ T) with hx
    have hxW : x = fun i => (S.stairW *ᵥ S.optInit ξ T) (Sum.inr i) := by
      funext i
      rw [hx]
      exact S.redT_mulVec_inr _ i
    have hwx : w ⬝ᵥ x = ξ ⬝ᵥ ξ := by
      rw [hxW, hpair, hpin]
    have hCS : (w ⬝ᵥ x) ^ 2 ≤ (w ⬝ᵥ w) * (x ⬝ᵥ x) := by
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w x
      simpa [dotProduct, sq] using h1
    rw [hwx] at hCS
    have h3 : x ⬝ᵥ x ≤ (Fintype.card (Fin S.rk2) : ℝ) * ‖x‖ ^ 2 :=
      dotProduct_le_card_mul_sq_norm x
    rw [hc₀, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (ξ ⬝ᵥ ξ), hww, hcard]
  -- linear growth of the value along full windows
  -- IOSS data along the optimal trajectories (`eq:iosssum` route)
  obtain ⟨P, a₁, a₂, a₃, c₁, c₂, hPD, ha₁, ha₂, ha₃, hc₁, hc₂,
    hbounds, hdiss⟩ := exists_ioss_lyapunov S.A S.C (-S.G) hC1
  obtain ⟨αQ, hαQ, hbQ⟩ := S.hQi.exists_le_quadForm
  obtain ⟨αR, hαR, hbR⟩ := S.hRi.exists_le_quadForm
  obtain ⟨cr, hcr, hbr⟩ := S.hSig0.exists_sq_norm_mulVec_le
  obtain ⟨cB, hcB, hgram⟩ := gramian_growth S.redSys.A₂ S.redSys.hAnti
  set eT : ℕ → ℕ → Fin n → ℝ := fun T k =>
    S.glq.traj (S.optInit ξ T) (S.glq.optCtrl (S.optInit ξ T) T) k
    with heT
  have hrec : ∀ T k, eT T (k + 1)
      = S.A *ᵥ eT T k + (-S.G) *ᵥ S.glq.optCtrl (S.optInit ξ T) T k := by
    intro T k
    rw [heT]
    simp only
    rw [LQSystem.traj_succ]
    rfl
  -- `eq:iosssum` along the optimum
  have hsum : ∀ T, a₃ * ∑ k ∈ Finset.range T, ‖eT T k‖ ^ 2
      ≤ quadForm P (eT T 0)
        + c₁ * ∑ k ∈ Finset.range T,
            ‖S.glq.optCtrl (S.optInit ξ T) T k‖ ^ 2
        + c₂ * ∑ k ∈ Finset.range T, ‖S.C *ᵥ eT T k‖ ^ 2 :=
    fun T => sum_sq_bound_of_ioss
      (fun x => hPD.posSemidef.quadForm_nonneg x) hdiss
      (eT T) (S.glq.optCtrl (S.optInit ξ T) T) (hrec T) T
  -- `eq:rhs-bound`: the right side is dominated by the optimal cost
  set cV : ℝ := max (2 * a₂ * cr) (max (c₁ / αQ) (c₂ / αR)) + 1
    with hcV
  have hcV0 : 0 < cV := by
    have h1 : (0:ℝ) ≤ 2 * a₂ * cr := by positivity
    have h2 := le_max_left (2 * a₂ * cr) (max (c₁ / αQ) (c₂ / αR))
    rw [hcV]
    linarith
  have hrhs : ∀ T, quadForm P (eT T 0)
      + c₁ * ∑ k ∈ Finset.range T,
          ‖S.glq.optCtrl (S.optInit ξ T) T k‖ ^ 2
      + c₂ * ∑ k ∈ Finset.range T, ‖S.C *ᵥ eT T k‖ ^ 2
      ≤ 2 * a₂ * ‖ξ‖ ^ 2 + cV * S.value ξ T := by
    intro T
    -- initial-state energy against the prior term
    have h1 : eT T 0 = S.optInit ξ T := rfl
    have h2 : quadForm P (eT T 0)
        ≤ 2 * a₂ * (cr * S.priorPen ξ (S.optInit ξ T))
          + 2 * a₂ * ‖ξ‖ ^ 2 := by
      rw [h1]
      have h3 := (hbounds (S.optInit ξ T)).2
      have h4 : ‖S.optInit ξ T‖ ^ 2
          ≤ 2 * ‖S.optInit ξ T - ξ‖ ^ 2 + 2 * ‖ξ‖ ^ 2 := by
        have h5 := norm_add_le (S.optInit ξ T - ξ) ξ
        have h6 : S.optInit ξ T - ξ + ξ = S.optInit ξ T := by module
        rw [h6] at h5
        nlinarith [norm_nonneg (S.optInit ξ T - ξ), norm_nonneg ξ,
          sq_nonneg (‖S.optInit ξ T - ξ‖ - ‖ξ‖),
          mul_le_mul h5 h5 (norm_nonneg _) (by positivity :
            (0:ℝ) ≤ ‖S.optInit ξ T - ξ‖ + ‖ξ‖)]
      have h7 : ‖S.optInit ξ T - ξ‖ ^ 2
          ≤ cr * S.priorPen ξ (S.optInit ξ T) := by
        obtain ⟨z, hz⟩ := S.optInit_feasible ξ T
        unfold priorPen
        rw [hz, quadForm_symmPinv_image S.hSig0]
        exact hbr z
      nlinarith
    -- stage energies against the stage costs
    have h8 : c₁ * ∑ k ∈ Finset.range T,
        ‖S.glq.optCtrl (S.optInit ξ T) T k‖ ^ 2
        ≤ (c₁ / αQ) * ∑ k ∈ Finset.range T,
            quadForm S.Qi (S.glq.optCtrl (S.optInit ξ T) T k) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h9 := hbQ (S.glq.optCtrl (S.optInit ξ T) T k)
      rw [div_mul_eq_mul_div, le_div_iff₀ hαQ]
      nlinarith [sq_nonneg ‖S.glq.optCtrl (S.optInit ξ T) T k‖]
    have h10 : c₂ * ∑ k ∈ Finset.range T, ‖S.C *ᵥ eT T k‖ ^ 2
        ≤ (c₂ / αR) * ∑ k ∈ Finset.range T,
            quadForm S.Ri (S.C *ᵥ eT T k) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h9 := hbR (S.C *ᵥ eT T k)
      rw [div_mul_eq_mul_div, le_div_iff₀ hαR]
      nlinarith [sq_nonneg ‖S.C *ᵥ eT T k‖]
    -- the optimal cost splits into exactly these stage costs
    have h11 : S.priorPen ξ (S.optInit ξ T)
        + ∑ k ∈ Finset.range T,
            (quadForm S.Qi (S.glq.optCtrl (S.optInit ξ T) T k)
              + quadForm S.Ri (S.C *ᵥ eT T k))
        = S.value ξ T := by
      have h12 := S.gCost_optCtrl ξ T
      unfold gCost at h12
      rw [← h12]
      congr 1
      unfold LQSystem.cost
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [S.quadForm_glq_Qs]
      have h13 : quadForm S.glq.Ru (S.glq.optCtrl (S.optInit ξ T) T k)
          = quadForm S.Qi (S.glq.optCtrl (S.optInit ξ T) T k) := rfl
      rw [h13, heT]
      simp only
      ring
    have h14 : (0:ℝ) ≤ S.priorPen ξ (S.optInit ξ T) :=
      S.priorPen_nonneg _ _
    have h15 : ∀ k ∈ Finset.range T, (0:ℝ)
        ≤ quadForm S.Qi (S.glq.optCtrl (S.optInit ξ T) T k) :=
      fun k _ => S.hQi.posSemidef.quadForm_nonneg _
    have h16 : ∀ k ∈ Finset.range T, (0:ℝ)
        ≤ quadForm S.Ri (S.C *ᵥ eT T k) :=
      fun k _ => S.hRi.posSemidef.quadForm_nonneg _
    have h17 : (2 * a₂ * cr) * S.priorPen ξ (S.optInit ξ T)
        + (c₁ / αQ) * ∑ k ∈ Finset.range T,
            quadForm S.Qi (S.glq.optCtrl (S.optInit ξ T) T k)
        + (c₂ / αR) * ∑ k ∈ Finset.range T,
            quadForm S.Ri (S.C *ᵥ eT T k)
        ≤ cV * S.value ξ T := by
      have hm1 : 2 * a₂ * cr ≤ cV := by
        have := le_max_left (2 * a₂ * cr) (max (c₁ / αQ) (c₂ / αR))
        rw [hcV]
        linarith
      have hm2 : c₁ / αQ ≤ cV := by
        have h18 := le_trans (le_max_left (c₁ / αQ) (c₂ / αR))
          (le_max_right (2 * a₂ * cr) _)
        rw [hcV]
        linarith
      have hm3 : c₂ / αR ≤ cV := by
        have h18 := le_trans (le_max_right (c₁ / αQ) (c₂ / αR))
          (le_max_right (2 * a₂ * cr) _)
        rw [hcV]
        linarith
      have hs1 : (0:ℝ) ≤ ∑ k ∈ Finset.range T,
          quadForm S.Qi (S.glq.optCtrl (S.optInit ξ T) T k) :=
        Finset.sum_nonneg h15
      have hs2 : (0:ℝ) ≤ ∑ k ∈ Finset.range T,
          quadForm S.Ri (S.C *ᵥ eT T k) := Finset.sum_nonneg h16
      have h19 : (2 * a₂ * cr) * S.priorPen ξ (S.optInit ξ T)
          ≤ cV * S.priorPen ξ (S.optInit ξ T) :=
        mul_le_mul_of_nonneg_right hm1 h14
      have h20 : (c₁ / αQ) * ∑ k ∈ Finset.range T,
          quadForm S.Qi (S.glq.optCtrl (S.optInit ξ T) T k)
          ≤ cV * ∑ k ∈ Finset.range T,
            quadForm S.Qi (S.glq.optCtrl (S.optInit ξ T) T k) :=
        mul_le_mul_of_nonneg_right hm2 hs1
      have h21 : (c₂ / αR) * ∑ k ∈ Finset.range T,
          quadForm S.Ri (S.C *ᵥ eT T k)
          ≤ cV * ∑ k ∈ Finset.range T,
            quadForm S.Ri (S.C *ᵥ eT T k) :=
        mul_le_mul_of_nonneg_right hm3 hs2
      have h22 : cV * S.priorPen ξ (S.optInit ξ T)
          + cV * (∑ k ∈ Finset.range T,
              quadForm S.Qi (S.glq.optCtrl (S.optInit ξ T) T k))
          + cV * ∑ k ∈ Finset.range T,
              quadForm S.Ri (S.C *ᵥ eT T k)
          = cV * S.value ξ T := by
        rw [← h11, Finset.sum_add_distrib]
        ring
      linarith
    linarith
  -- `eq:lhs-bound`: the antistable coordinates force linear growth
  set bm : ℝ := ‖S.blkTwoMat‖ + 1 with hbm
  have hbm0 : 0 < bm := by
    have := norm_nonneg S.blkTwoMat
    rw [hbm]
    linarith
  have hcoords : ∀ T k, FIESystem.blk₂ (S.redT *ᵥ eT T k)
      = S.redSys.A₂ ^ k
        *ᵥ FIESystem.blk₂ (S.redT *ᵥ S.optInit ξ T) := by
    intro T k
    rw [heT]
    simp only
    rw [← S.red_traj (S.optInit ξ T) (S.glq.optCtrl (S.optInit ξ T) T) k]
    exact S.redSys.blk₂_traj _ _ k
  have hlhs : ∀ T : ℕ, 1 ≤ T →
      cB * T * c₀ ≤ bm ^ 2 * ∑ k ∈ Finset.range T, ‖eT T k‖ ^ 2 := by
    intro T hT
    have h1 := hgram (FIESystem.blk₂ (S.redT *ᵥ S.optInit ξ T)) T hT
    have h2 := hlow T
    have h3 : ∀ k, ‖FIESystem.blk₂ (S.redT *ᵥ eT T k)‖
        ≤ bm * ‖eT T k‖ := by
      intro k
      have h4 : FIESystem.blk₂ (S.redT *ᵥ eT T k)
          = S.blkTwoMat *ᵥ eT T k := by
        funext i
        rw [FIESystem.blk₂_apply, S.redT_mulVec_inr]
        rfl
      rw [h4]
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      have h5 : ‖S.blkTwoMat‖ ≤ bm := by
        rw [hbm]
        linarith
      exact mul_le_mul_of_nonneg_right h5 (norm_nonneg _)
    have h6 : ∑ k ∈ Finset.range T,
        ‖S.redSys.A₂ ^ k
          *ᵥ FIESystem.blk₂ (S.redT *ᵥ S.optInit ξ T)‖ ^ 2
        ≤ bm ^ 2 * ∑ k ∈ Finset.range T, ‖eT T k‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← hcoords T k]
      have h7 := h3 k
      have h8 := norm_nonneg (FIESystem.blk₂ (S.redT *ᵥ eT T k))
      nlinarith [norm_nonneg (eT T k), hbm0.le]
    have h9 : cB * T * c₀
        ≤ cB * T * ‖FIESystem.blk₂ (S.redT *ᵥ S.optInit ξ T)‖ ^ 2 := by
      have h10 : (0:ℝ) ≤ cB * T := by positivity
      exact mul_le_mul_of_nonneg_left h2 h10
    linarith
  -- `eq:Vlinear`: the value grows at least linearly
  set β : ℝ := a₃ * cB * c₀ / bm ^ 2 with hβ
  have hβ0 : 0 < β := by
    rw [hβ]
    positivity
  have hVlin : ∀ T : ℕ, 1 ≤ T →
      β * T ≤ 2 * a₂ * ‖ξ‖ ^ 2 + cV * S.value ξ T := by
    intro T hT
    have h1 := hsum T
    have h2 := hrhs T
    have h3 := hlhs T hT
    have h4 : a₃ * (cB * T * c₀ / bm ^ 2)
        ≤ a₃ * ∑ k ∈ Finset.range T, ‖eT T k‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ ha₃.le
      rw [div_le_iff₀ (by positivity : (0:ℝ) < bm ^ 2)]
      linarith [hlhs T hT]
    have h5 : β * T = a₃ * (cB * T * c₀ / bm ^ 2) := by
      rw [hβ]
      ring
    rw [h5]
    linarith
  -- `eq:Venergy` cap and the Cesàro contradiction
  obtain ⟨σ, hσ0, hσb⟩ := hgas
  obtain ⟨cy, hcy, hyb⟩ := exists_quadForm_le S.glq.Qs
  have hξnorm : (0:ℝ) < ‖ξ‖ ^ 2 := by
    have h1 : 0 < ‖ξ‖ := norm_pos_iff.mpr hξne
    positivity
  have hup : ∀ T, S.value ξ T
      ≤ cy * ‖ξ‖ ^ 2 * ∑ k ∈ Finset.range T, σ k ^ 2 := by
    intro T
    refine le_trans (S.value_le_sum_optTerm ξ T) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 := hyb (S.optTerm ξ k)
    have h2 := hσb k ξ
    have h3 : ‖S.optTerm ξ k‖ ^ 2 ≤ (σ k * ‖ξ‖) ^ 2 := by
      have h0 : 0 ≤ ‖S.optTerm ξ k‖ := norm_nonneg _
      nlinarith
    calc quadForm S.glq.Qs (S.optTerm ξ k)
        ≤ cy * ‖S.optTerm ξ k‖ ^ 2 := h1
    _ ≤ cy * (σ k * ‖ξ‖) ^ 2 := mul_le_mul_of_nonneg_left h3 hcy.le
    _ = cy * ‖ξ‖ ^ 2 * σ k ^ 2 := by ring
  have hσ2 : Tendsto (fun k => σ k ^ 2) atTop (nhds 0) := by
    have h1 := hσ0.pow 2
    simpa using h1
  have hces := hσ2.cesaro
  set δ : ℝ := β / (cV * (cy * ‖ξ‖ ^ 2)) with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]
    positivity
  set cA : ℝ := 2 * a₂ * ‖ξ‖ ^ 2 / (cV * (cy * ‖ξ‖ ^ 2)) with hcA
  have hcA0 : 0 ≤ cA := by
    rw [hcA]
    positivity
  have hδle : ∀ T : ℕ, 1 ≤ T →
      δ - cA / T ≤ (T:ℝ)⁻¹ • ∑ k ∈ Finset.range T, σ k ^ 2 := by
    intro T hT
    have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
    have h1 := hVlin T hT
    have h2 := hup T
    have hden : (0:ℝ) < cV * (cy * ‖ξ‖ ^ 2) := by positivity
    have h3 : β * T ≤ 2 * a₂ * ‖ξ‖ ^ 2
        + cV * (cy * ‖ξ‖ ^ 2 * ∑ k ∈ Finset.range T, σ k ^ 2) := by
      have h4 : cV * S.value ξ T
          ≤ cV * (cy * ‖ξ‖ ^ 2 * ∑ k ∈ Finset.range T, σ k ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hcV0.le
      linarith
    rw [smul_eq_mul, hδ, hcA, inv_mul_eq_div, le_div_iff₀ hTpos]
    have hexp : (β / (cV * (cy * ‖ξ‖ ^ 2))
        - 2 * a₂ * ‖ξ‖ ^ 2 / (cV * (cy * ‖ξ‖ ^ 2)) / T) * T
        = (β * T - 2 * a₂ * ‖ξ‖ ^ 2) / (cV * (cy * ‖ξ‖ ^ 2)) := by
      field_simp
    rw [hexp, div_le_iff₀ hden]
    calc β * T - 2 * a₂ * ‖ξ‖ ^ 2
        ≤ cV * (cy * ‖ξ‖ ^ 2 * ∑ k ∈ Finset.range T, σ k ^ 2) := by
          linarith
      _ = (∑ k ∈ Finset.range T, σ k ^ 2) * (cV * (cy * ‖ξ‖ ^ 2)) := by
          ring
  -- eventual contradiction
  have hev1 := hces.eventually_lt_const (by linarith : (0:ℝ) < δ / 2)
  have hev2 : ∀ᶠ T : ℕ in atTop, cA / T < δ / 2 := by
    have h1 : Tendsto (fun T : ℕ => cA / (T:ℝ)) atTop (nhds 0) := by
      have h2 := tendsto_natCast_atTop_atTop (R := ℝ)
      exact Tendsto.div_atTop tendsto_const_nhds h2
    exact h1.eventually_lt_const (by linarith)
  obtain ⟨T, hT⟩ := ((hev1.and hev2).and (eventually_ge_atTop 1)).exists
  obtain ⟨⟨hT1, hT2⟩, hT3⟩ := hT
  have h1 := hδle T hT3
  have h2 : δ - cA / T > δ / 2 := by linarith
  have h3 : ((T:ℝ)⁻¹ • ∑ k ∈ Finset.range T, σ k ^ 2) < δ / 2 := hT1
  linarith
end GeneralSystem

end Estimation

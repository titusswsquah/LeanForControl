import LeanForControl.Estimation.ChiProblem
import LeanForControl.LinearSystems.IOSS
import Architect

/-!
# The modified Q-function route (`prop:tvkfQuns`, `prop:modQgas`)

The paper's Lyapunov-like argument for GAS of the optimal estimator:
flip the partial optimal costs against the limiting value
(`Z(j|k) = V∞⁰ − V⁰(j|k)`), add the IOSS-Lyapunov energy of the running
error, and read off the three modified-Q-function properties with
quadratic bounds (`prop:tvkfQuns`). A modified Q-function forces the
error along the limit trajectory to die; `it:xTT` transfers this to the
terminal error, and linearity of the optimizer in the prior mismatch
upgrades pointwise attraction to the uniform `σ_T`-form of GAS
(`prop:modQgas`).
-/

namespace Estimation

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

namespace GeneralSystem

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-! ### Linearity of the optimizer in the prior mismatch -/

lemma isStationary_add {a a' e₀ e₀' : Fin n → ℝ} {T : ℕ}
    (h : S.IsStationary a e₀ T) (h' : S.IsStationary a' e₀' T) :
    S.IsStationary (a + a') (e₀ + e₀') T := by
  obtain ⟨⟨z, hz⟩, hstat⟩ := h
  obtain ⟨⟨z', hz'⟩, hstat'⟩ := h'
  refine ⟨⟨z + z', ?_⟩, ?_⟩
  · rw [Matrix.mulVec_add, ← hz, ← hz']
    module
  · intro d hd
    have h1 := hstat d hd
    have h2 := hstat' d hd
    have h3 : e₀ + e₀' - (a + a') = (e₀ - a) + (e₀' - a') := by
      module
    rw [h3, Matrix.mulVec_add, Matrix.mulVec_add, add_dotProduct,
      add_dotProduct]
    linarith

lemma isStationary_smul {a e₀ : Fin n → ℝ} {T : ℕ} (c : ℝ)
    (h : S.IsStationary a e₀ T) :
    S.IsStationary (c • a) (c • e₀) T := by
  obtain ⟨⟨z, hz⟩, hstat⟩ := h
  refine ⟨⟨c • z, ?_⟩, ?_⟩
  · rw [Matrix.mulVec_smul, ← hz]
    module
  · intro d hd
    have h1 := hstat d hd
    have h3 : c • e₀ - c • a = c • (e₀ - a) := by
      module
    rw [h3, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct,
      smul_dotProduct]
    have h4 : c • ((symmPinv S.hSig0.1 *ᵥ (e₀ - a)) ⬝ᵥ d)
        + c • ((S.glq.ric T *ᵥ e₀) ⬝ᵥ d)
        = c * ((symmPinv S.hSig0.1 *ᵥ (e₀ - a)) ⬝ᵥ d
          + (S.glq.ric T *ᵥ e₀) ⬝ᵥ d) := by
      simp [smul_eq_mul]
      ring
    rw [h4, h1, mul_zero]

/-- The optimal initial error is additive in the prior mismatch. -/
lemma optInit_add (a a' : Fin n → ℝ) (T : ℕ) :
    S.optInit (a + a') T = S.optInit a T + S.optInit a' T :=
  (S.isStationary_unique (S.optInit_isStationary (a + a') T)
    (S.isStationary_add (S.optInit_isStationary a T)
      (S.optInit_isStationary a' T)))

/-- The optimal initial error is homogeneous in the prior mismatch. -/
lemma optInit_smul (c : ℝ) (a : Fin n → ℝ) (T : ℕ) :
    S.optInit (c • a) T = c • S.optInit a T :=
  (S.isStationary_unique (S.optInit_isStationary (c • a) T)
    (S.isStationary_smul c (S.optInit_isStationary a T)))

/-- The optimal closed-loop trajectory is additive in the initial
state. -/
lemma optTraj_add (x x' : Fin n → ℝ) (T : ℕ) : ∀ k,
    S.glq.optTraj (x + x') T k
      = S.glq.optTraj x T k + S.glq.optTraj x' T k
  | 0 => rfl
  | k + 1 => by
    show S.glq.Acl (S.glq.ric (T - 1 - k)) *ᵥ S.glq.optTraj (x + x') T k
      = _
    rw [optTraj_add x x' T k, Matrix.mulVec_add]
    rfl

lemma optTraj_smul (c : ℝ) (x : Fin n → ℝ) (T : ℕ) : ∀ k,
    S.glq.optTraj (c • x) T k = c • S.glq.optTraj x T k
  | 0 => rfl
  | k + 1 => by
    show S.glq.Acl (S.glq.ric (T - 1 - k)) *ᵥ S.glq.optTraj (c • x) T k
      = _
    rw [optTraj_smul c x T k, Matrix.mulVec_smul]
    rfl

/-- The optimal terminal error is additive in the prior mismatch. -/
lemma optTerm_add (a a' : Fin n → ℝ) (T : ℕ) :
    S.optTerm (a + a') T = S.optTerm a T + S.optTerm a' T := by
  unfold optTerm
  rw [S.optInit_add, S.optTraj_add]

lemma optTerm_smul (c : ℝ) (a : Fin n → ℝ) (T : ℕ) :
    S.optTerm (c • a) T = c • S.optTerm a T := by
  unfold optTerm
  rw [S.optInit_smul, S.optTraj_smul]

/-- **Pointwise attraction is uniform for a linear estimator**: if every
terminal error dies, they die at a mismatch-free rate. -/
theorem isGAS_of_pointwise
    (h : ∀ a : Fin n → ℝ, Tendsto (fun T => ‖S.optTerm a T‖) atTop
      (nhds 0)) : S.IsGAS := by
  classical
  refine ⟨fun T => ∑ i : Fin n, ‖S.optTerm (Pi.single i 1) T‖, ?_, ?_⟩
  · have h1 := tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (fun i _ => h (Pi.single i 1))
    simpa using h1
  · intro T a
    -- decompose `a` over the standard basis
    have hdec : a = ∑ i : Fin n, a i • (Pi.single i 1 : Fin n → ℝ) := by
      funext j
      rw [Finset.sum_apply]
      simp [Pi.single_apply]
    have hlin : S.optTerm a T
        = ∑ i : Fin n, a i • S.optTerm (Pi.single i 1) T := by
      conv_lhs => rw [hdec]
      -- push optTerm through the finite sum
      have hsum : ∀ (s : Finset (Fin n)),
          S.optTerm (∑ i ∈ s, a i • (Pi.single i 1 : Fin n → ℝ)) T
            = ∑ i ∈ s, a i • S.optTerm (Pi.single i 1) T := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          have h0 : S.optTerm (0 : Fin n → ℝ) T = 0 := by
            have h2 := S.optTerm_smul 0 0 T
            simpa using h2
          exact h0
        | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi,
            S.optTerm_add, ih, S.optTerm_smul]
      exact hsum Finset.univ
    rw [hlin]
    calc ‖∑ i : Fin n, a i • S.optTerm (Pi.single i 1) T‖
        ≤ ∑ i : Fin n, ‖a i • S.optTerm (Pi.single i 1) T‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ‖a‖ * ‖S.optTerm (Pi.single i 1) T‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
          exact norm_le_pi_norm a i
      _ = (∑ i : Fin n, ‖S.optTerm (Pi.single i 1) T‖) * ‖a‖ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ### Partial costs and the flipped cost `Z` (`prop:tvkfQuns` data) -/

/-- The optimal error trajectory of the horizon-`k` problem,
`x(j) − x̂(j|k)` in the paper's variables. -/
noncomputable def eTraj (a : Fin n → ℝ) (k j : ℕ) : Fin n → ℝ :=
  S.glq.traj (S.optInit a k) (S.glq.optCtrl (S.optInit a k) k) j

/-- The partial optimal cost `V⁰(j|k)`. -/
noncomputable def partialCost (a : Fin n → ℝ) (j k : ℕ) : ℝ :=
  S.priorPen a (S.optInit a k)
    + ∑ i ∈ Finset.range j,
        S.gStage (S.optInit a k) (S.glq.optCtrl (S.optInit a k) k) i

lemma partialCost_succ (a : Fin n → ℝ) (j k : ℕ) :
    S.partialCost a (j + 1) k
      = S.partialCost a j k
        + S.gStage (S.optInit a k) (S.glq.optCtrl (S.optInit a k) k) j := by
  unfold partialCost
  rw [Finset.sum_range_succ]
  ring

lemma partialCost_le_valueLim (hC2 : S.C2) (a : Fin n → ℝ) {j k : ℕ}
    (hjk : j ≤ k) : S.partialCost a j k ≤ S.valueLim a := by
  have h1 : S.partialCost a j k ≤ S.value a k := by
    have h2 := S.gCost_optCtrl a k
    unfold gCost at h2
    rw [cost_eq_sum_gStage] at h2
    unfold partialCost
    have h3 : ∑ i ∈ Finset.range j,
        S.gStage (S.optInit a k) (S.glq.optCtrl (S.optInit a k) k) i
        ≤ ∑ i ∈ Finset.range k,
          S.gStage (S.optInit a k) (S.glq.optCtrl (S.optInit a k) k) i :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hjk)
        fun i _ _ => S.gStage_nonneg _ _ _
    linarith
  exact h1.trans (S.value_le_valueLim hC2 a k)

/-- The limiting value inherits the C2 quadratic bound. -/
lemma valueLim_le_bound (hC2 : S.C2) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Fin n → ℝ, S.valueLim a ≤ c * ‖a‖ ^ 2 := by
  obtain ⟨c, hc, hb⟩ := S.exists_value_bound_C2 hC2
  exact ⟨c, hc, fun a => ciSup_le fun T => hb a T⟩

/-- **`prop:tvkfQuns`** (general coordinates): under C1 ∧ C2 the
optimal estimator admits a modified Q-function with quadratic
`K∞`-bounds. -/
theorem exists_modQ (hC1 : S.C1) (hC2 : S.C2) :
    ∃ (Q : (Fin n → ℝ) → ℕ → ℕ → ℝ) (c₀ cl cd : ℝ),
      0 < c₀ ∧ 0 < cl ∧ 0 < cd ∧
      (∀ a k, Q a 0 k ≤ c₀ * ‖a‖ ^ 2) ∧
      (∀ a k j, j ≤ k → cl * ‖S.eTraj a k j‖ ^ 2 ≤ Q a j k) ∧
      (∀ a k j, Q a (j + 1) k ≤ Q a j k - cd * ‖S.eTraj a k j‖ ^ 2) ∧
      (∀ a j, ∃ L, Tendsto (fun k => Q a j k) atTop (nhds L)) := by
  classical
  obtain ⟨P, a₁, a₂, a₃, c₁, c₂, hPD, ha₁, ha₂, ha₃, hc₁, hc₂,
    hbounds, hdiss⟩ := exists_ioss_lyapunov S.A S.C (-S.G) hC1
  obtain ⟨αQ, hαQ, hbQ⟩ := S.hQi.exists_le_quadForm
  obtain ⟨αR, hαR, hbR⟩ := S.hRi.exists_le_quadForm
  obtain ⟨cr, hcr, hbr⟩ := S.hSig0.exists_sq_norm_mulVec_le
  obtain ⟨cv, hcv, hbv⟩ := S.valueLim_le_bound hC2
  set ρ : ℝ := min (min (αQ / (2 * c₁)) (αR / (2 * c₂)))
    (1 / (2 * a₂ * cr + 1)) with hρ
  have hρ0 : 0 < ρ := by
    rw [hρ]
    have h1 : (0:ℝ) < αQ / (2 * c₁) := by positivity
    have h2 : (0:ℝ) < αR / (2 * c₂) := by positivity
    have h3 : (0:ℝ) < 1 / (2 * a₂ * cr + 1) := by positivity
    exact lt_min (lt_min h1 h2) h3
  have hρQ : ρ * c₁ ≤ αQ / 2 := by
    have h1 : ρ ≤ αQ / (2 * c₁) :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    calc ρ * c₁ ≤ αQ / (2 * c₁) * c₁ :=
          mul_le_mul_of_nonneg_right h1 hc₁.le
      _ = αQ / 2 := by field_simp
  have hρR : ρ * c₂ ≤ αR / 2 := by
    have h1 : ρ ≤ αR / (2 * c₂) :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    calc ρ * c₂ ≤ αR / (2 * c₂) * c₂ :=
          mul_le_mul_of_nonneg_right h1 hc₂.le
      _ = αR / 2 := by field_simp
  have hρP : ρ * (2 * a₂ * cr) ≤ 1 := by
    have h1 : ρ ≤ 1 / (2 * a₂ * cr + 1) := min_le_right _ _
    have h2 : (0:ℝ) < 2 * a₂ * cr + 1 := by positivity
    calc ρ * (2 * a₂ * cr) ≤ 1 / (2 * a₂ * cr + 1) * (2 * a₂ * cr) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 1 := by
          rw [div_mul_eq_mul_div, div_le_one h2]
          linarith
  refine ⟨fun a j k => S.valueLim a - S.partialCost a j k
      + ρ * quadForm P (S.eTraj a k j),
    cv + 2 * ρ * a₂, ρ * a₁, ρ * a₃,
    by positivity, by positivity, by positivity, ?_, ?_, ?_, ?_⟩
  · -- `eq:QunsInitUB`
    intro a k
    dsimp only
    have h1 : S.eTraj a k 0 = S.optInit a k := rfl
    rw [h1]
    have h2 : quadForm P (S.optInit a k)
        ≤ a₂ * ‖S.optInit a k‖ ^ 2 := (hbounds _).2
    have h3 : ‖S.optInit a k‖ ^ 2
        ≤ 2 * ‖S.optInit a k - a‖ ^ 2 + 2 * ‖a‖ ^ 2 := by
      have h4 := norm_add_le (S.optInit a k - a) a
      have h5 : S.optInit a k - a + a = S.optInit a k := by module
      rw [h5] at h4
      nlinarith [norm_nonneg (S.optInit a k - a), norm_nonneg a,
        sq_nonneg (‖S.optInit a k - a‖ - ‖a‖),
        mul_le_mul h4 h4 (norm_nonneg _) (by positivity :
          (0:ℝ) ≤ ‖S.optInit a k - a‖ + ‖a‖)]
    have h6 : ‖S.optInit a k - a‖ ^ 2
        ≤ cr * S.priorPen a (S.optInit a k) := by
      obtain ⟨z, hz⟩ := S.optInit_feasible a k
      unfold priorPen
      rw [hz, quadForm_symmPinv_image S.hSig0]
      exact hbr z
    have h7 : S.partialCost a 0 k = S.priorPen a (S.optInit a k) := by
      unfold partialCost
      simp
    have h8 := hbv a
    have hpen := S.priorPen_nonneg a (S.optInit a k)
    -- assemble: the prior term absorbs the mismatch part of `V_io`
    have h9 : ρ * quadForm P (S.optInit a k)
        ≤ ρ * (2 * a₂) * (cr * S.priorPen a (S.optInit a k))
          + 2 * ρ * a₂ * ‖a‖ ^ 2 := by
      have h10 : quadForm P (S.optInit a k)
          ≤ 2 * a₂ * (cr * S.priorPen a (S.optInit a k))
            + 2 * a₂ * ‖a‖ ^ 2 := by
        nlinarith
      nlinarith
    have h11 : ρ * (2 * a₂) * (cr * S.priorPen a (S.optInit a k))
        ≤ S.priorPen a (S.optInit a k) := by
      have h12 : ρ * (2 * a₂) * cr = ρ * (2 * a₂ * cr) := by ring
      calc ρ * (2 * a₂) * (cr * S.priorPen a (S.optInit a k))
          = (ρ * (2 * a₂ * cr)) * S.priorPen a (S.optInit a k) := by
            ring
        _ ≤ 1 * S.priorPen a (S.optInit a k) :=
            mul_le_mul_of_nonneg_right hρP hpen
        _ = S.priorPen a (S.optInit a k) := one_mul _
    rw [h7]
    nlinarith
  · -- lower bound in `eq:QunsLBUB`
    intro a k j hjk
    dsimp only
    have h1 := S.partialCost_le_valueLim hC2 a hjk
    have h2 := (hbounds (S.eTraj a k j)).1
    nlinarith
  · -- `eq:QunsDecrease`
    intro a k j
    dsimp only
    have hstep : S.eTraj a k (j + 1)
        = S.A *ᵥ S.eTraj a k j
          + (-S.G) *ᵥ S.glq.optCtrl (S.optInit a k) k j := by
      unfold eTraj
      rw [LQSystem.traj_succ]
      rfl
    have hd := hdiss (S.eTraj a k j) (S.glq.optCtrl (S.optInit a k) k j)
    rw [← hstep] at hd
    have hZ := S.partialCost_succ a j k
    have hstage : S.gStage (S.optInit a k)
        (S.glq.optCtrl (S.optInit a k) k) j
        = quadForm S.Ri (S.C *ᵥ S.eTraj a k j)
          + quadForm S.Qi (S.glq.optCtrl (S.optInit a k) k j) := by
      unfold gStage eTraj
      rw [S.quadForm_glq_Qs]
      have h2 : quadForm S.glq.Ru (S.glq.optCtrl (S.optInit a k) k j)
          = quadForm S.Qi (S.glq.optCtrl (S.optInit a k) k j) := rfl
      rw [h2]
    have hQlb := hbQ (S.glq.optCtrl (S.optInit a k) k j)
    have hRlb := hbR (S.C *ᵥ S.eTraj a k j)
    -- Young-balanced dissipation
    have hω := sq_nonneg ‖S.glq.optCtrl (S.optInit a k) k j‖
    have hν := sq_nonneg ‖S.C *ᵥ S.eTraj a k j‖
    have hx := sq_nonneg ‖S.eTraj a k j‖
    have hc₁ω : ρ * (c₁ * ‖S.glq.optCtrl (S.optInit a k) k j‖ ^ 2)
        ≤ αQ / 2 * ‖S.glq.optCtrl (S.optInit a k) k j‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hρQ hω
      nlinarith
    have hc₂ν : ρ * (c₂ * ‖S.C *ᵥ S.eTraj a k j‖ ^ 2)
        ≤ αR / 2 * ‖S.C *ᵥ S.eTraj a k j‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hρR hν
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd hρ0.le]
  · -- convergence along horizons (via `it:zlim`)
    intro a j
    dsimp only
    have hquad : Continuous (fun v : Fin n → ℝ => quadForm P v) := by
      unfold quadForm
      exact continuous_id.dotProduct
        (P.mulVecLin.continuous_of_finiteDimensional.comp continuous_id)
    have htrajP : Tendsto (fun k => quadForm P (S.eTraj a k j)) atTop
        (nhds (quadForm P
          (S.glq.traj (S.optInitLim a) (S.optCtrlLim a) j))) := by
      exact ((hquad.tendsto _).comp (S.tendsto_traj hC2 a j))
    have hpartial : Tendsto (fun k => S.partialCost a j k) atTop
        (nhds (S.priorPen a (S.optInitLim a)
          + ∑ i ∈ Finset.range j,
              S.gStage (S.optInitLim a) (S.optCtrlLim a) i)) := by
      unfold partialCost
      exact (S.tendsto_priorPen hC2 a).add
        (tendsto_finset_sum _ fun i _ => S.tendsto_gStage hC2 a i)
    refine ⟨S.valueLim a - (S.priorPen a (S.optInitLim a)
      + ∑ i ∈ Finset.range j,
          S.gStage (S.optInitLim a) (S.optCtrlLim a) i)
      + ρ * quadForm P
          (S.glq.traj (S.optInitLim a) (S.optCtrlLim a) j), ?_⟩
    exact ((tendsto_const_nhds.sub hpartial).add (htrajP.const_mul ρ))

/-! ### `prop:modQgas`: a modified Q-function forces GAS -/

/-- **`prop:modQgas`** (general/optimizer form). One hypothesis is made
explicit that the paper leaves implicit: the horizon limits
`Q(j|∞) = lim_k Q(j|k)` must exist (the paper justifies this via
`prop:infhor` and continuity *for the constructed Q*; an arbitrary
modified Q-function need not converge along horizons). -/
theorem isGAS_of_modQ (hC1 : S.C1) (hC2 : S.C2)
    (Q : (Fin n → ℝ) → ℕ → ℕ → ℝ) (c₀ cl cd : ℝ)
    (_hc₀ : 0 < c₀) (hcl : 0 < cl) (hcd : 0 < cd)
    (_hinit : ∀ a k, Q a 0 k ≤ c₀ * ‖a‖ ^ 2)
    (hlb : ∀ a k j, j ≤ k → cl * ‖S.eTraj a k j‖ ^ 2 ≤ Q a j k)
    (hdec : ∀ a k j, Q a (j + 1) k ≤ Q a j k - cd * ‖S.eTraj a k j‖ ^ 2)
    (hconv : ∀ a j, ∃ L, Tendsto (fun k => Q a j k) atTop (nhds L)) :
    S.IsGAS := by
  classical
  refine S.isGAS_of_pointwise fun a => ?_
  -- the horizon-limit Q-function
  choose Qlim hQlim using hconv
  set eL : ℕ → Fin n → ℝ :=
    fun j => S.glq.traj (S.optInitLim a) (S.optCtrlLim a) j with heL
  have htraj := S.tendsto_traj hC2 a
  -- limit lower bound
  have hlbL : ∀ j, cl * ‖eL j‖ ^ 2 ≤ Qlim a j := by
    intro j
    have h1 : Tendsto (fun k => cl * ‖S.eTraj a k j‖ ^ 2) atTop
        (nhds (cl * ‖eL j‖ ^ 2)) := by
      have h2 : Tendsto (fun k => S.eTraj a k j) atTop (nhds (eL j)) :=
        htraj j
      have h3 : Continuous (fun v : Fin n → ℝ => cl * ‖v‖ ^ 2) := by
        continuity
      exact (h3.tendsto _).comp h2
    refine le_of_tendsto_of_tendsto h1 (hQlim a j) ?_
    filter_upwards [eventually_ge_atTop j] with k hk
    exact hlb a k j hk
  -- limit decrease
  have hdecL : ∀ j, Qlim a (j + 1) ≤ Qlim a j - cd * ‖eL j‖ ^ 2 := by
    intro j
    have h1 : Tendsto (fun k => Q a j k - cd * ‖S.eTraj a k j‖ ^ 2)
        atTop (nhds (Qlim a j - cd * ‖eL j‖ ^ 2)) := by
      have h3 : Continuous (fun v : Fin n → ℝ => cd * ‖v‖ ^ 2) := by
        continuity
      exact (hQlim a j).sub ((h3.tendsto _).comp (htraj j))
    exact le_of_tendsto_of_tendsto (hQlim a (j + 1)) h1
      (Eventually.of_forall fun k => hdec a k j)
  -- `Qlim` is antitone and bounded below, hence convergent
  have hanti : Antitone (Qlim a) := by
    refine antitone_nat_of_succ_le fun j => ?_
    have h1 := hdecL j
    have h2 : (0:ℝ) ≤ cd * ‖eL j‖ ^ 2 := by positivity
    linarith
  have hbdd : ∀ j, 0 ≤ Qlim a j := by
    intro j
    have h1 := hlbL j
    have h2 : (0:ℝ) ≤ cl * ‖eL j‖ ^ 2 := by positivity
    linarith
  have hQconv : Tendsto (Qlim a) atTop (nhds (⨅ j, Qlim a j)) :=
    tendsto_atTop_ciInf hanti ⟨0, fun x ⟨j, hj⟩ => hj ▸ hbdd j⟩
  -- the decrements vanish, so the limit trajectory dies
  have hdiff : Tendsto (fun j => Qlim a j - Qlim a (j + 1)) atTop
      (nhds 0) := by
    have h1 := hQconv.sub (hQconv.comp (tendsto_add_atTop_nat 1))
    simpa using h1
  have heL0 : Tendsto (fun j => ‖eL j‖) atTop (nhds 0) := by
    have h1 : Tendsto (fun j => cd * ‖eL j‖ ^ 2) atTop (nhds 0) := by
      refine squeeze_zero (fun j => by positivity) (fun j => ?_) hdiff
      have h2 := hdecL j
      linarith
    have h2 : Tendsto (fun j => ‖eL j‖ ^ 2) atTop (nhds 0) := by
      have h3 := h1.const_mul cd⁻¹
      have h4 : (fun j => cd⁻¹ * (cd * ‖eL j‖ ^ 2))
          = fun j => ‖eL j‖ ^ 2 := by
        funext j
        field_simp
      rw [h4] at h3
      simpa using h3
    have h5 := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at h5
    refine h5.congr fun j => ?_
    rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
  -- transfer to the diagonal by `it:xTT`
  have hxTT := S.tendsto_optTerm_sub_limTraj hC1 hC2 a
  have h6 : Tendsto (fun T => ‖S.optTerm a T‖) atTop (nhds 0) := by
    have h7 : ∀ T, ‖S.optTerm a T‖
        ≤ ‖S.optTerm a T - eL T‖ + ‖eL T‖ := by
      intro T
      calc ‖S.optTerm a T‖ = ‖S.optTerm a T - eL T + eL T‖ := by
            congr 1
            module
        _ ≤ ‖S.optTerm a T - eL T‖ + ‖eL T‖ := norm_add_le _ _
    have h8 : Tendsto (fun T => ‖S.optTerm a T - eL T‖ + ‖eL T‖)
        atTop (nhds 0) := by
      have h9 := (tendsto_zero_iff_norm_tendsto_zero.mp hxTT).add heL0
      simpa using h9
    exact squeeze_zero (fun T => norm_nonneg _) h7 h8
  exact h6

/-- **`prop:tvkf`, optimizer form, by the paper's Q-function route**:
the optimal estimator is GAS iff C1 ∧ C2 — sufficiency through
`prop:tvkfQuns` + `prop:modQgas`, necessity through the direct
arguments. -/
theorem prop_tvkf_optimizer : S.IsGAS ↔ S.C1 ∧ S.C2 := by
  constructor
  · intro h
    have hC1 := S.C1_of_isGAS h
    exact ⟨hC1, S.C2_of_isGAS hC1 h⟩
  · rintro ⟨hC1, hC2⟩
    obtain ⟨Q, c₀, cl, cd, hc₀, hcl, hcd, hinit, hlb, hdec, hconv⟩ :=
      S.exists_modQ hC1 hC2
    exact S.isGAS_of_modQ hC1 hC2 Q c₀ cl cd hc₀ hcl hcd hinit hlb
      hdec hconv

end GeneralSystem

end Estimation

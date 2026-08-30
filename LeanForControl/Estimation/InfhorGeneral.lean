import LeanForControl.Estimation.Reduction
import LeanForControl.Estimation.Infhor
import LeanForControl.Estimation.GeneralNecessity
import Architect

/-!
# `prop:infhor` at the general level (paper.tex, 2026a)

The infinite-horizon limit of the general full-information problem, with
the paper's hypothesis split: the optimizer and value limits (`it:zlim`,
`it:Vlim`) under C2 alone, and the terminal-error transfer (`it:xTT`)
under C1 ∧ C2. C2-only statements ride the reduction of
`Estimation.Reduction`; the value bound behind them is the C2-only
`exists_value_bound_C2` (`lem:unibounded` with the corrected hypothesis
bookkeeping).
-/

namespace Estimation

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

namespace GeneralSystem

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-! ### Value monotonicity and convergence (`lem:unibounded`) -/

/-- The value is nondecreasing in the horizon (no hypotheses). -/
theorem value_mono (a : Fin n → ℝ) {T τ : ℕ} (h : T ≤ τ) :
    S.value a T ≤ S.value a τ := by
  calc S.value a T
      ≤ S.gCost a (S.optInit a τ) (S.glq.optCtrl (S.optInit a τ) τ) T :=
        S.value_le_gCost (S.optInit_feasible a τ) _ T
  _ ≤ S.gCost a (S.optInit a τ) (S.glq.optCtrl (S.optInit a τ) τ) τ := by
      unfold gCost
      have := S.glq.cost_mono (S.optInit a τ)
        (S.glq.optCtrl (S.optInit a τ) τ) h
      linarith
  _ = S.value a τ := S.gCost_optCtrl a τ

/-- The limiting value `V∞⁰(a)` (finite under C2; junk otherwise). -/
noncomputable def valueLim (a : Fin n → ℝ) : ℝ :=
  ⨆ T, S.value a T

/-- The C2-only uniform value bound, general coordinates
(`lem:unibounded`). -/
theorem exists_value_bound_C2 (hC2 : S.C2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin n → ℝ) (T : ℕ),
      S.value a T ≤ c * ‖a‖ ^ 2 := by
  obtain ⟨c, hc, hb⟩ := S.redSys.exists_value_bound_C2
    (S.red_C2_iff.mpr hC2)
  refine ⟨c * (‖S.redT‖ ^ 2 + 1), by positivity, fun a T => ?_⟩
  have h1 : S.value a T = S.redSys.value (S.redT *ᵥ a) T :=
    (S.red_value hC2 a T).symm
  have h2 := hb (S.redT *ᵥ a) T
  have h3 : ‖S.redT *ᵥ a‖ ^ 2 ≤ ‖S.redT‖ ^ 2 * ‖a‖ ^ 2 := by
    have h4 := Matrix.linfty_opNorm_mulVec S.redT a
    have h5 : (0:ℝ) ≤ ‖S.redT *ᵥ a‖ := norm_nonneg _
    nlinarith [norm_nonneg (S.redT), norm_nonneg a]
  rw [h1]
  refine h2.trans ?_
  have h6 : (0:ℝ) ≤ ‖a‖ ^ 2 := sq_nonneg _
  nlinarith

/-- Under C2 the values converge to `valueLim` from below. -/
theorem tendsto_value (hC2 : S.C2) (a : Fin n → ℝ) :
    Tendsto (fun T => S.value a T) atTop (nhds (S.valueLim a)) := by
  obtain ⟨c, hc, hb⟩ := S.exists_value_bound_C2 hC2
  refine tendsto_atTop_ciSup (fun T τ h => S.value_mono a h)
    ⟨c * ‖a‖ ^ 2, ?_⟩
  rintro x ⟨T, rfl⟩
  exact hb a T

theorem value_le_valueLim (hC2 : S.C2) (a : Fin n → ℝ) (T : ℕ) :
    S.value a T ≤ S.valueLim a := by
  obtain ⟨c, hc, hb⟩ := S.exists_value_bound_C2 hC2
  refine le_ciSup ⟨c * ‖a‖ ^ 2, ?_⟩ T
  rintro x ⟨τ, rfl⟩
  exact hb a τ

/-- The limiting value transfers through the reduction. -/
lemma red_valueLim (hC2 : S.C2) (a : Fin n → ℝ) :
    S.valueLim a = S.redSys.valueLim (S.redT *ᵥ a) := by
  have h1 := S.tendsto_value hC2 a
  have h2 := S.redSys.tendsto_value (S.red_C2_iff.mpr hC2) (S.redT *ᵥ a)
  have h3 : (fun T => S.redSys.value (S.redT *ᵥ a) T)
      = fun T => S.value a T := by
    funext T
    exact S.red_value hC2 a T
  rw [h3] at h2
  exact tendsto_nhds_unique h1 h2

/-! ### `it:zlim`: the optimizer limits, under C2 alone -/

/-- The general optimizers as transformed reduced optimizers. -/
lemma optInit_eq_redTinv (hC2 : S.C2) (a : Fin n → ℝ) (T : ℕ) :
    S.optInit a T
      = S.redTinv *ᵥ (S.redSys.optInit (S.redT *ᵥ a) T) := by
  rw [S.red_optInit hC2, redTinv_redT_mulVec]

lemma optCtrl_eq_red (hC2 : S.C2) (a : Fin n → ℝ) (T k : ℕ) :
    S.glq.optCtrl (S.optInit a T) T k
      = S.redSys.lq.optCtrl (S.redSys.optInit (S.redT *ᵥ a) T) T k := by
  rw [S.red_optInit hC2, red_optCtrl]

/-- The limiting optimal initial error. -/
noncomputable def optInitLim (a : Fin n → ℝ) : Fin n → ℝ :=
  limUnder atTop (fun T => S.optInit a T)

/-- The limiting optimal noise sequence. -/
noncomputable def optCtrlLim (a : Fin n → ℝ) (k : ℕ) : Fin m → ℝ :=
  limUnder atTop (fun T => S.glq.optCtrl (S.optInit a T) T k)

private lemma continuous_mulVec {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ) :
    Continuous (fun v : β → ℝ => M *ᵥ v) :=
  M.mulVecLin.continuous_of_finiteDimensional

/-- **`it:zlim` (initial error)**: the optimal initial errors converge,
under C2 alone. -/
theorem tendsto_optInit (hC2 : S.C2) (a : Fin n → ℝ) :
    Tendsto (fun T => S.optInit a T) atTop (nhds (S.optInitLim a)) := by
  have h1 := S.redSys.tendsto_optInit (S.red_C2_iff.mpr hC2)
    (S.redT *ᵥ a)
  have h2 : Tendsto (fun T => S.optInit a T) atTop
      (nhds (S.redTinv *ᵥ S.redSys.optInitLim (S.redT *ᵥ a))) := by
    have h3 := ((continuous_mulVec S.redTinv).tendsto
      (S.redSys.optInitLim (S.redT *ᵥ a))).comp h1
    refine h3.congr fun T => ?_
    exact (S.optInit_eq_redTinv hC2 a T).symm
  have h4 : CauchySeq (fun T => S.optInit a T) := h2.cauchySeq
  have h5 := h4.tendsto_limUnder
  exact h5

lemma optInitLim_eq_redTinv (hC2 : S.C2) (a : Fin n → ℝ) :
    S.optInitLim a
      = S.redTinv *ᵥ S.redSys.optInitLim (S.redT *ᵥ a) := by
  have h1 := S.tendsto_optInit hC2 a
  have h2 := S.redSys.tendsto_optInit (S.red_C2_iff.mpr hC2)
    (S.redT *ᵥ a)
  have h3 : Tendsto (fun T => S.optInit a T) atTop
      (nhds (S.redTinv *ᵥ S.redSys.optInitLim (S.redT *ᵥ a))) := by
    have h4 := ((continuous_mulVec S.redTinv).tendsto
      (S.redSys.optInitLim (S.redT *ᵥ a))).comp h2
    refine h4.congr fun T => ?_
    exact (S.optInit_eq_redTinv hC2 a T).symm
  exact tendsto_nhds_unique h1 h3

/-- **`it:zlim` (noise)**: the optimal noises converge stagewise, under
C2 alone. -/
theorem tendsto_optCtrl (hC2 : S.C2) (a : Fin n → ℝ) (k : ℕ) :
    Tendsto (fun T => S.glq.optCtrl (S.optInit a T) T k) atTop
      (nhds (S.optCtrlLim a k)) := by
  have h1 := S.redSys.tendsto_optCtrl (S.red_C2_iff.mpr hC2)
    (S.redT *ᵥ a) k
  have h2 : Tendsto (fun T => S.glq.optCtrl (S.optInit a T) T k) atTop
      (nhds (S.redSys.optCtrlLim (S.redT *ᵥ a) k)) := by
    refine h1.congr fun T => ?_
    exact (S.optCtrl_eq_red hC2 a T k).symm
  exact h2.cauchySeq.tendsto_limUnder

lemma optCtrlLim_eq_red (hC2 : S.C2) (a : Fin n → ℝ) (k : ℕ) :
    S.optCtrlLim a k = S.redSys.optCtrlLim (S.redT *ᵥ a) k := by
  have h1 := S.tendsto_optCtrl hC2 a k
  have h2 := S.redSys.tendsto_optCtrl (S.red_C2_iff.mpr hC2)
    (S.redT *ᵥ a) k
  have h3 : Tendsto (fun T => S.glq.optCtrl (S.optInit a T) T k) atTop
      (nhds (S.redSys.optCtrlLim (S.redT *ᵥ a) k)) := by
    refine h2.congr fun T => ?_
    exact (S.optCtrl_eq_red hC2 a T k).symm
  exact tendsto_nhds_unique h1 h3

/-! ### The exact gap (`eq:gap`) and its energy corollary, under C2 -/

lemma feasible_sub {a e₀ e₀' : Fin n → ℝ} (h : S.Feasible a e₀)
    (h' : S.Feasible a e₀') : S.Feasible 0 (e₀ - e₀') := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨z', hz'⟩ := h'
  refine ⟨z - z', ?_⟩
  rw [sub_zero, Matrix.mulVec_sub, ← hz, ← hz']
  abel

/-- **`eq:gap`** at the general level: any feasible pair's excess cost
over the value is the zero-prior cost of the deviation pair. -/
theorem gCost_gap (hC2 : S.C2) {a e₀ : Fin n → ℝ}
    (hfeas : S.Feasible a e₀) (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    S.gCost a e₀ ω T
      = S.value a T
        + S.gCost 0 (e₀ - S.optInit a T)
            (fun j => ω j - S.glq.optCtrl (S.optInit a T) T j) T := by
  have h1 := (S.red_fieCost hC2 hfeas ω T).symm
  have h2 := S.redSys.fieCost_gap (S.red_feasible hC2 hfeas) ω T
  rw [S.red_optInit hC2] at h2
  have h3 : S.redT *ᵥ e₀ - S.redT *ᵥ S.optInit a T
      = S.redT *ᵥ (e₀ - S.optInit a T) := (Matrix.mulVec_sub _ _ _).symm
  have h4 : (fun j => ω j
        - S.redSys.lq.optCtrl (S.redT *ᵥ S.optInit a T) T j)
      = fun j => ω j - S.glq.optCtrl (S.optInit a T) T j := by
    funext j
    rw [red_optCtrl]
  rw [h3, h4] at h2
  have h5 := S.red_fieCost hC2
    (S.feasible_sub hfeas (S.optInit_feasible a T))
    (fun j => ω j - S.glq.optCtrl (S.optInit a T) T j) T
  rw [Matrix.mulVec_zero] at h5
  rw [h1, h2, S.red_value hC2, h5]

/-- The gap dominates the squared deviation energies (the
`eq:rangebound`/`eq:quadbound` mechanism). -/
theorem exists_gap_energy_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ {d : Fin n → ℝ}, S.Feasible 0 d →
      ∀ (δ : ℕ → Fin m → ℝ) (T : ℕ),
      ‖d‖ ^ 2 + (∑ k ∈ Finset.range T, ‖δ k‖ ^ 2)
        + ∑ k ∈ Finset.range T, ‖S.C *ᵥ S.glq.traj d δ k‖ ^ 2
      ≤ c * S.gCost 0 d δ T := by
  obtain ⟨cr, hcr, hbr⟩ := S.hSig0.exists_sq_norm_mulVec_le
  obtain ⟨cq, hcq, hbq⟩ := S.hQi.exists_le_quadForm
  obtain ⟨cR, hcR, hbR⟩ := S.hRi.exists_le_quadForm
  refine ⟨cr + cq⁻¹ + cR⁻¹, by positivity, fun {d} hd δ T => ?_⟩
  obtain ⟨z, hz⟩ := hd
  rw [sub_zero] at hz
  -- the prior part
  have h1 : ‖d‖ ^ 2 ≤ cr * S.priorPen 0 d := by
    have h2 : S.priorPen 0 d = quadForm S.Sig0 z := by
      unfold priorPen
      rw [sub_zero, hz, quadForm_symmPinv_image S.hSig0]
    rw [h2, hz]
    exact hbr z
  -- the stage parts
  have h3 : ∀ k, ‖δ k‖ ^ 2 ≤ cq⁻¹ * quadForm S.glq.Ru (δ k) := by
    intro k
    calc ‖δ k‖ ^ 2 = cq * ‖δ k‖ ^ 2 / cq := by
          field_simp
      _ ≤ quadForm S.Qi (δ k) / cq := by
          have h5 := hbq (δ k)
          gcongr
      _ = cq⁻¹ * quadForm S.glq.Ru (δ k) := by
          rw [div_eq_inv_mul]
          rfl
  have h6 : ∀ k, ‖S.C *ᵥ S.glq.traj d δ k‖ ^ 2
      ≤ cR⁻¹ * quadForm S.glq.Qs (S.glq.traj d δ k) := by
    intro k
    rw [S.quadForm_glq_Qs]
    have h7 := hbR (S.C *ᵥ S.glq.traj d δ k)
    calc ‖S.C *ᵥ S.glq.traj d δ k‖ ^ 2
        = cR * ‖S.C *ᵥ S.glq.traj d δ k‖ ^ 2 / cR := by
          field_simp
      _ ≤ quadForm S.Ri (S.C *ᵥ S.glq.traj d δ k) / cR := by
          gcongr
      _ = cR⁻¹ * quadForm S.Ri (S.C *ᵥ S.glq.traj d δ k) := by
          rw [div_eq_inv_mul]
  -- assemble
  have h8 : ∑ k ∈ Finset.range T, ‖δ k‖ ^ 2
      ≤ cq⁻¹ * S.glq.cost d δ T := by
    unfold LQSystem.cost
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h9 := h3 k
    have h10 : (0:ℝ) ≤ quadForm S.glq.Qs (S.glq.traj d δ k) :=
      S.glq.hQs.quadForm_nonneg _
    have h11 : (0:ℝ) ≤ cq⁻¹ := by positivity
    nlinarith
  have h12 : ∑ k ∈ Finset.range T, ‖S.C *ᵥ S.glq.traj d δ k‖ ^ 2
      ≤ cR⁻¹ * S.glq.cost d δ T := by
    unfold LQSystem.cost
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h9 := h6 k
    have h10 : (0:ℝ) ≤ quadForm S.glq.Ru (δ k) :=
      S.glq.hRu.posSemidef.quadForm_nonneg _
    have h11 : (0:ℝ) ≤ cR⁻¹ := by positivity
    nlinarith
  have hcost0 : (0:ℝ) ≤ S.glq.cost d δ T :=
    Finset.sum_nonneg fun k _ => S.glq.stage_nonneg _ _
  have hpen0 : (0:ℝ) ≤ S.priorPen 0 d := S.priorPen_nonneg _ _
  unfold gCost
  have h13 : cr * S.priorPen 0 d
      ≤ (cr + cq⁻¹ + cR⁻¹) * S.priorPen 0 d := by
    have : (0:ℝ) ≤ cq⁻¹ + cR⁻¹ := by positivity
    nlinarith
  have h14 : (cq⁻¹ + cR⁻¹) * S.glq.cost d δ T
      ≤ (cr + cq⁻¹ + cR⁻¹) * S.glq.cost d δ T := by
    nlinarith
  nlinarith [h1, h8, h12]

/-! ### `lem:exist`: joint uniqueness (hypothesis-free) -/

/-- Any cost-minimizing feasible pair has the optimal initial error. -/
theorem optimal_init_unique {a e₀ : Fin n → ℝ} {ω : ℕ → Fin m → ℝ}
    {T : ℕ} (hfeas : S.Feasible a e₀)
    (hmin : S.gCost a e₀ ω T = S.value a T) :
    e₀ = S.optInit a T := by
  -- the outer objective at `e₀` is at most the value
  have h1 : S.priorPen a e₀ + quadForm (S.glq.ric T) e₀
      ≤ S.value a T := by
    have h2 := S.glq.quadForm_ric_le_cost e₀ ω T
    unfold gCost at hmin
    linarith
  -- the outer gap forces the pinv- and ric-quadratics of the
  -- difference to vanish
  have h3 := S.outerObj_gap (S.optInit_isStationary a T) hfeas
  have hq1 := S.hSig0.symmPinv.quadForm_nonneg (e₀ - S.optInit a T)
  have hq2 := (S.glq.ric_posSemidef T).quadForm_nonneg
    (e₀ - S.optInit a T)
  have h4 : quadForm (symmPinv S.hSig0.1) (e₀ - S.optInit a T) = 0 := by
    unfold value at h1
    linarith
  obtain ⟨z, hz⟩ := hfeas
  obtain ⟨z', hz'⟩ := S.optInit_feasible a T
  have hd : e₀ - S.optInit a T = S.Sig0 *ᵥ (z - z') := by
    rw [Matrix.mulVec_sub, ← hz, ← hz']
    abel
  rw [hd, quadForm_symmPinv_image S.hSig0] at h4
  have h5 := S.hSig0.mulVec_eq_zero_of_quadForm_eq_zero h4
  rw [← hd] at h5
  have h6 : e₀ = S.optInit a T + 0 := by
    rw [← h5]
    abel
  simpa using h6

/-- **`lem:exist`** (uniqueness half, hypothesis-free): a minimizing
pair agrees with the canonical optimizer in both components. -/
theorem optimal_pair_unique {a e₀ : Fin n → ℝ} {ω : ℕ → Fin m → ℝ}
    {T : ℕ} (hfeas : S.Feasible a e₀)
    (hmin : S.gCost a e₀ ω T = S.value a T) :
    e₀ = S.optInit a T ∧
      ∀ k < T, ω k = S.glq.optCtrl (S.optInit a T) T k := by
  have h0 := S.optimal_init_unique hfeas hmin
  refine ⟨h0, ?_⟩
  -- the noise attains the LQ optimum from the optimal initial error
  have h1 : S.glq.cost (S.optInit a T) ω T
      = quadForm (S.glq.ric T) (S.optInit a T) := by
    have h2 := S.glq.quadForm_ric_le_cost (S.optInit a T) ω T
    have h3 : S.gCost a (S.optInit a T) ω T = S.value a T := by
      rw [← h0]
      exact hmin
    unfold gCost at h3
    unfold value at h3
    linarith
  have h4 := S.glq.optCtrl_unique (S.optInit a T) ω T h1
  rw [← h0] at h4 ⊢
  intro k hk
  rw [h0] at h4 ⊢
  exact h4 k hk

/-! ### `eq:ellT`: the last optimal stage cost vanishes -/

/-- Dropping the final stage of the `(T+1)`-optimum is `T`-feasible:
the value increments dominate the last stage cost. -/
theorem lastStage_le_value_diff (a : Fin n → ℝ) (T : ℕ) :
    quadForm S.glq.Qs (S.glq.traj (S.optInit a (T + 1))
        (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1)) T)
      + quadForm S.glq.Ru (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1) T)
    ≤ S.value a (T + 1) - S.value a T := by
  have h1 := S.value_le_gCost (S.optInit_feasible a (T + 1))
    (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1)) T
  have h2 := S.gCost_optCtrl a (T + 1)
  unfold gCost at h1 h2
  have h3 : S.glq.cost (S.optInit a (T + 1))
      (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1)) (T + 1)
      = S.glq.cost (S.optInit a (T + 1))
          (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1)) T
        + (quadForm S.glq.Qs (S.glq.traj (S.optInit a (T + 1))
            (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1)) T)
          + quadForm S.glq.Ru
            (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1) T)) := by
    unfold LQSystem.cost
    rw [Finset.sum_range_succ]
  linarith

/-- **`eq:ellT`** under C2: the final optimal stage cost tends to
zero. -/
theorem tendsto_lastStage (hC2 : S.C2) (a : Fin n → ℝ) :
    Tendsto (fun T => quadForm S.glq.Qs
        (S.glq.traj (S.optInit a (T + 1))
          (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1)) T)
      + quadForm S.glq.Ru (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1) T))
      atTop (nhds 0) := by
  have h1 := S.tendsto_value hC2 a
  have h2 : Tendsto (fun T => S.value a (T + 1) - S.value a T) atTop
      (nhds 0) := by
    have h3 := (h1.comp (tendsto_add_atTop_nat 1)).sub h1
    simpa using h3
  refine squeeze_zero (fun T => ?_)
    (fun T => S.lastStage_le_value_diff a T) h2
  exact add_nonneg (S.glq.hQs.quadForm_nonneg _)
    (S.glq.hRu.posSemidef.quadForm_nonneg _)

end GeneralSystem

end Estimation

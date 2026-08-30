import LeanForControl.Estimation.Reduction
import LeanForControl.Estimation.Infhor
import LeanForControl.Estimation.GeneralNecessity
import LeanForControl.LinearSystems.OutputInjection
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

/-- **The variational front door** (F6): the value is the least cost
over feasible decision pairs — the Riccati recursion behind
`optInit`/`optCtrl` is a construction witness, not part of any
statement. -/
theorem value_isLeast (a : Fin n → ℝ) (T : ℕ) :
    IsLeast {c : ℝ | ∃ e₀ ω, S.Feasible a e₀ ∧ c = S.gCost a e₀ ω T}
      (S.value a T) := by
  constructor
  · exact ⟨S.optInit a T, S.glq.optCtrl (S.optInit a T) T,
      S.optInit_feasible a T, (S.gCost_optCtrl a T).symm⟩
  · rintro c ⟨e₀, ω, hfeas, rfl⟩
    exact S.value_le_gCost hfeas ω T

/-! ### The exact gap (`eq:gap`) and its energy corollary (C2-free) -/

lemma feasible_sub {a e₀ e₀' : Fin n → ℝ} (h : S.Feasible a e₀)
    (h' : S.Feasible a e₀') : S.Feasible 0 (e₀ - e₀') := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨z', hz'⟩ := h'
  refine ⟨z - z', ?_⟩
  rw [sub_zero, Matrix.mulVec_sub, ← hz, ← hz']
  abel

/-- Quadratic expansion of the prior penalty along an affine line. -/
lemma priorPen_add_smul (a e₀ d : Fin n → ℝ) (t : ℝ) :
    S.priorPen a (e₀ + t • d)
      = S.priorPen a e₀
        + 2 * t * ((e₀ - a) ⬝ᵥ (symmPinv S.hSig0.1 *ᵥ d))
        + t ^ 2 * S.priorPen 0 d := by
  unfold priorPen
  have h1 : e₀ + t • d - a = (e₀ - a) + t • d := by abel
  rw [h1, quadForm_add_of_isHermitian (symmPinv_isHermitian S.hSig0.1),
    quadForm_smul]
  have h2 : d - 0 = d := sub_zero d
  rw [h2]
  have h3 : (e₀ - a) ⬝ᵥ (symmPinv S.hSig0.1 *ᵥ (t • d))
      = t * ((e₀ - a) ⬝ᵥ (symmPinv S.hSig0.1 *ᵥ d)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [h3]
  ring

/-- Feasibility is stable along feasible directions. -/
lemma feasible_add_smul {a e₀ d : Fin n → ℝ} (h : S.Feasible a e₀)
    (hd : S.Feasible 0 d) (t : ℝ) : S.Feasible a (e₀ + t • d) := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨w, hw⟩ := hd
  rw [sub_zero] at hw
  refine ⟨z + t • w, ?_⟩
  rw [Matrix.mulVec_add, ← hz, Matrix.mulVec_smul, ← hw]
  abel

private lemma cross_eq_zero_of_nonneg' {c D : ℝ} (hD : 0 ≤ D)
    (h : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * D) : c = 0 := by
  have hD1 : (0:ℝ) < D + 1 := by linarith
  have h1 := h (-c / (D + 1))
  have h2 : 2 * (-c / (D + 1)) * c + (-c / (D + 1)) ^ 2 * D
      = c ^ 2 / (D + 1) * (D / (D + 1) - 2) := by
    field_simp
    ring
  rw [h2] at h1
  have h3 : D / (D + 1) - 2 < 0 := by
    have h4 : D / (D + 1) < 1 := by
      rw [div_lt_one hD1]
      linarith
    linarith
  have h7 : (0:ℝ) ≤ c ^ 2 / (D + 1) := by positivity
  have h8 : c ^ 2 = 0 := by
    have h5 : c ^ 2 / (D + 1) = 0 := by nlinarith
    field_simp at h5
    linarith
  exact pow_eq_zero_iff (by norm_num) |>.mp h8

lemma gCost_nonneg (a e₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    0 ≤ S.gCost a e₀ ω T := by
  unfold gCost
  have h1 := S.priorPen_nonneg a e₀
  have h2 : (0:ℝ) ≤ S.glq.cost e₀ ω T :=
    Finset.sum_nonneg fun k _ => S.glq.stage_nonneg _ _
  linarith

/-- **`eq:gap`** at the general level, C2-free and by the paper's own
route (quadratic refactoring about the optimizer, `eq:quadmin` style):
any feasible pair's excess cost over the value is the zero-prior cost
of the deviation pair. -/
theorem gCost_gap {a e₀ : Fin n → ℝ}
    (hfeas : S.Feasible a e₀) (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    S.gCost a e₀ ω T
      = S.value a T
        + S.gCost 0 (e₀ - S.optInit a T)
            (fun j => ω j - S.glq.optCtrl (S.optInit a T) T j) T := by
  set es := S.optInit a T with hes
  set ωs := S.glq.optCtrl es T with hωs
  set d := e₀ - es with hd
  set δ : ℕ → Fin m → ℝ := fun j => ω j - ωs j with hδ
  have hdfeas : S.Feasible 0 d :=
    S.feasible_sub hfeas (S.optInit_feasible a T)
  set CR : ℝ := (es - a) ⬝ᵥ (symmPinv S.hSig0.1 *ᵥ d)
      + S.glq.costCross es d ωs δ T with hCRdef
  -- the cost along the line through the optimizer
  have hg : ∀ t : ℝ,
      S.gCost a (es + t • d) (fun j => ωs j + t • δ j) T
        = S.value a T + 2 * t * CR + t ^ 2 * S.gCost 0 d δ T := by
    intro t
    unfold gCost
    rw [S.priorPen_add_smul a es d t, S.glq.cost_add_smul es d ωs δ T t]
    have hval : S.priorPen a es + S.glq.cost es ωs T = S.value a T := by
      have h := S.gCost_optCtrl a T
      unfold gCost at h
      rw [← hes, ← hωs] at h
      exact h
    rw [hCRdef]
    linarith [hval]
  -- optimality along the line kills the cross term
  have hDpos : 0 ≤ S.gCost 0 d δ T := S.gCost_nonneg 0 d δ T
  have hCR : CR = 0 := by
    refine cross_eq_zero_of_nonneg' hDpos fun t => ?_
    have hfeas' : S.Feasible a (es + t • d) :=
      S.feasible_add_smul (S.optInit_feasible a T) hdfeas t
    have h1 := S.value_le_gCost hfeas' (fun j => ωs j + t • δ j) T
    rw [hg t] at h1
    linarith
  -- evaluate at `t = 1`
  have h1 := hg 1
  rw [hCR] at h1
  have h2 : es + (1 : ℝ) • d = e₀ := by
    rw [hd, one_smul]
    abel
  have h3 : (fun j => ωs j + (1 : ℝ) • δ j) = ω := by
    funext j
    rw [hδ]
    simp
  rw [h2, h3] at h1
  rw [h1]
  ring

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

/-- **Truncation gap** (the direct `eq:gapopt` mechanism): for
`T ≤ τ`, the `τ`-optimal pair at horizon `T` deviates from the
`T`-optimum by at most the value increment, in the gap metric. -/
theorem truncation_gap (a : Fin n → ℝ) {T τ : ℕ} (h : T ≤ τ) :
    S.gCost 0 (S.optInit a τ - S.optInit a T)
      (fun j => S.glq.optCtrl (S.optInit a τ) τ j
        - S.glq.optCtrl (S.optInit a T) T j) T
      ≤ S.value a τ - S.value a T := by
  have hgap := S.gCost_gap (S.optInit_feasible a τ)
    (S.glq.optCtrl (S.optInit a τ) τ) T
  have h1 : S.gCost a (S.optInit a τ)
      (S.glq.optCtrl (S.optInit a τ) τ) T ≤ S.value a τ := by
    unfold gCost
    have h2 := S.glq.cost_mono (S.optInit a τ)
      (S.glq.optCtrl (S.optInit a τ) τ) h
    have h3 := S.gCost_optCtrl a τ
    unfold gCost at h3
    linarith
  linarith

/-- **`it:zlim` (initial error)**: the optimal initial errors converge,
under C2 alone — direct proof by the truncation gap and the energy
corollary. -/
theorem tendsto_optInit (hC2 : S.C2) (a : Fin n → ℝ) :
    Tendsto (fun T => S.optInit a T) atTop (nhds (S.optInitLim a)) := by
  obtain ⟨cE, hcE, hbE⟩ := S.exists_gap_energy_bound
  have hcauchy : CauchySeq (fun T => S.optInit a T) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have htend := S.tendsto_value hC2 a
    have h1 : Tendsto (fun T => cE * (S.valueLim a - S.value a T))
        atTop (nhds 0) := by
      have h2 := (htend.const_sub (S.valueLim a)).const_mul cE
      simpa using h2
    obtain ⟨N, hN⟩ := (h1.eventually_lt_const
      (by positivity : (0:ℝ) < ε ^ 2)).exists
    refine ⟨N, fun τ hτ => ?_⟩
    have hdfeas : S.Feasible 0 (S.optInit a τ - S.optInit a N) :=
      S.feasible_sub (S.optInit_feasible a τ) (S.optInit_feasible a N)
    have h3 := hbE hdfeas
      (fun j => S.glq.optCtrl (S.optInit a τ) τ j
        - S.glq.optCtrl (S.optInit a N) N j) N
    have h4 := S.truncation_gap a hτ
    have h5 := S.value_le_valueLim hC2 a τ
    have h6 : ‖S.optInit a τ - S.optInit a N‖ ^ 2
        ≤ cE * (S.valueLim a - S.value a N) := by
      have h7 : (0:ℝ) ≤ ∑ k ∈ Finset.range N,
          ‖S.glq.optCtrl (S.optInit a τ) τ k
            - S.glq.optCtrl (S.optInit a N) N k‖ ^ 2 :=
        Finset.sum_nonneg fun k _ => sq_nonneg _
      have h8 : (0:ℝ) ≤ ∑ k ∈ Finset.range N,
          ‖S.C *ᵥ S.glq.traj (S.optInit a τ - S.optInit a N)
            (fun j => S.glq.optCtrl (S.optInit a τ) τ j
              - S.glq.optCtrl (S.optInit a N) N j) k‖ ^ 2 :=
        Finset.sum_nonneg fun k _ => sq_nonneg _
      nlinarith
    rw [dist_eq_norm]
    have h9 : ‖S.optInit a τ - S.optInit a N‖ ^ 2 < ε ^ 2 :=
      lt_of_le_of_lt h6 hN
    nlinarith [norm_nonneg (S.optInit a τ - S.optInit a N), hε]
  exact hcauchy.tendsto_limUnder

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
C2 alone — direct proof. -/
theorem tendsto_optCtrl (hC2 : S.C2) (a : Fin n → ℝ) (k : ℕ) :
    Tendsto (fun T => S.glq.optCtrl (S.optInit a T) T k) atTop
      (nhds (S.optCtrlLim a k)) := by
  obtain ⟨cE, hcE, hbE⟩ := S.exists_gap_energy_bound
  have hcauchy : CauchySeq
      (fun T => S.glq.optCtrl (S.optInit a T) T k) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have htend := S.tendsto_value hC2 a
    have h1 : Tendsto (fun T => cE * (S.valueLim a - S.value a T))
        atTop (nhds 0) := by
      have h2 := (htend.const_sub (S.valueLim a)).const_mul cE
      simpa using h2
    obtain ⟨N, hN, hNk⟩ := ((h1.eventually_lt_const
      (by positivity : (0:ℝ) < ε ^ 2)).and
      (eventually_gt_atTop k)).exists
    refine ⟨N, fun τ hτ => ?_⟩
    have hdfeas : S.Feasible 0 (S.optInit a τ - S.optInit a N) :=
      S.feasible_sub (S.optInit_feasible a τ) (S.optInit_feasible a N)
    have h3 := hbE hdfeas
      (fun j => S.glq.optCtrl (S.optInit a τ) τ j
        - S.glq.optCtrl (S.optInit a N) N j) N
    have h4 := S.truncation_gap a hτ
    have h5 := S.value_le_valueLim hC2 a τ
    have h6 : ‖S.glq.optCtrl (S.optInit a τ) τ k
        - S.glq.optCtrl (S.optInit a N) N k‖ ^ 2
        ≤ cE * (S.valueLim a - S.value a N) := by
      have hsingle : ‖S.glq.optCtrl (S.optInit a τ) τ k
          - S.glq.optCtrl (S.optInit a N) N k‖ ^ 2
          ≤ ∑ j ∈ Finset.range N,
            ‖S.glq.optCtrl (S.optInit a τ) τ j
              - S.glq.optCtrl (S.optInit a N) N j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j =>
            ‖S.glq.optCtrl (S.optInit a τ) τ j
              - S.glq.optCtrl (S.optInit a N) N j‖ ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_range.mpr hNk)
      have h8 : (0:ℝ) ≤ ∑ j ∈ Finset.range N,
          ‖S.C *ᵥ S.glq.traj (S.optInit a τ - S.optInit a N)
            (fun i => S.glq.optCtrl (S.optInit a τ) τ i
              - S.glq.optCtrl (S.optInit a N) N i) j‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have h9 : (0:ℝ) ≤ ‖S.optInit a τ - S.optInit a N‖ ^ 2 :=
        sq_nonneg _
      nlinarith
    rw [dist_eq_norm]
    have h9 : ‖S.glq.optCtrl (S.optInit a τ) τ k
        - S.glq.optCtrl (S.optInit a N) N k‖ ^ 2 < ε ^ 2 :=
      lt_of_le_of_lt h6 hN
    nlinarith [norm_nonneg (S.glq.optCtrl (S.optInit a τ) τ k
      - S.glq.optCtrl (S.optInit a N) N k), hε]
  exact hcauchy.tendsto_limUnder

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

/-! ### `it:Vlim`: the infinite-horizon cost of the limit pair -/

/-- One stage cost of the general LQ layer. -/
noncomputable def gStage (e₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ)
    (k : ℕ) : ℝ :=
  quadForm S.glq.Qs (S.glq.traj e₀ ω k) + quadForm S.glq.Ru (ω k)

lemma gStage_nonneg (e₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ) (k : ℕ) :
    0 ≤ S.gStage e₀ ω k :=
  S.glq.stage_nonneg _ _

lemma cost_eq_sum_gStage (e₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    S.glq.cost e₀ ω T = ∑ k ∈ Finset.range T, S.gStage e₀ ω k :=
  rfl

/-- The infinite-horizon cost `V_∞` of a decision pair: prior penalty
plus the series of stage costs. -/
noncomputable def gInfCost (a e₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ) : ℝ :=
  S.priorPen a e₀ + ∑' k, S.gStage e₀ ω k

/-- Trajectories converge stagewise along the optimizer limits. -/
theorem tendsto_traj (hC2 : S.C2) (a : Fin n → ℝ) : ∀ k,
    Tendsto (fun T => S.glq.traj (S.optInit a T)
        (S.glq.optCtrl (S.optInit a T) T) k) atTop
      (nhds (S.glq.traj (S.optInitLim a) (S.optCtrlLim a) k))
  | 0 => by
    simpa only [LQSystem.traj_zero] using S.tendsto_optInit hC2 a
  | k + 1 => by
    simp only [LQSystem.traj_succ]
    exact (((continuous_mulVec S.glq.A).tendsto _).comp
        (tendsto_traj hC2 a k)).add
      (((continuous_mulVec S.glq.B).tendsto _).comp
        (S.tendsto_optCtrl hC2 a k))

/-- Stage costs converge along the optimizer limits. -/
theorem tendsto_gStage (hC2 : S.C2) (a : Fin n → ℝ) (k : ℕ) :
    Tendsto (fun T => S.gStage (S.optInit a T)
        (S.glq.optCtrl (S.optInit a T) T) k) atTop
      (nhds (S.gStage (S.optInitLim a) (S.optCtrlLim a) k)) := by
  unfold gStage
  have hq : ∀ (M : Matrix (Fin n) (Fin n) ℝ),
      Continuous (fun v : Fin n → ℝ => quadForm M v) := by
    intro M
    unfold quadForm
    exact continuous_id.dotProduct (continuous_mulVec M)
  have hqm : ∀ (M : Matrix (Fin m) (Fin m) ℝ),
      Continuous (fun v : Fin m → ℝ => quadForm M v) := by
    intro M
    unfold quadForm
    exact continuous_id.dotProduct (continuous_mulVec M)
  exact (((hq S.glq.Qs).tendsto _).comp (S.tendsto_traj hC2 a k)).add
    (((hqm S.glq.Ru).tendsto _).comp (S.tendsto_optCtrl hC2 a k))

/-- The prior penalty converges along the optimizer limits. -/
theorem tendsto_priorPen (hC2 : S.C2) (a : Fin n → ℝ) :
    Tendsto (fun T => S.priorPen a (S.optInit a T)) atTop
      (nhds (S.priorPen a (S.optInitLim a))) := by
  unfold priorPen quadForm
  have hcont : Continuous (fun v : Fin n → ℝ =>
      (v - a) ⬝ᵥ (symmPinv S.hSig0.1 *ᵥ (v - a))) := by
    have h1 : Continuous (fun v : Fin n → ℝ => v - a) :=
      continuous_id.sub continuous_const
    exact (h1.dotProduct ((continuous_mulVec _).comp h1))
  exact (hcont.tendsto _).comp (S.tendsto_optInit hC2 a)

/-- Partial limit costs stay below the limiting value. -/
theorem partial_le_valueLim (hC2 : S.C2) (a : Fin n → ℝ) (N : ℕ) :
    S.priorPen a (S.optInitLim a)
      + ∑ k ∈ Finset.range N, S.gStage (S.optInitLim a) (S.optCtrlLim a) k
    ≤ S.valueLim a := by
  have hlim : Tendsto (fun T => S.priorPen a (S.optInit a T)
      + ∑ k ∈ Finset.range N, S.gStage (S.optInit a T)
          (S.glq.optCtrl (S.optInit a T) T) k) atTop
      (nhds (S.priorPen a (S.optInitLim a)
        + ∑ k ∈ Finset.range N,
            S.gStage (S.optInitLim a) (S.optCtrlLim a) k)) := by
    refine (S.tendsto_priorPen hC2 a).add ?_
    exact tendsto_finset_sum _ fun k _ => S.tendsto_gStage hC2 a k
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop N] with T hT
  have h1 : ∑ k ∈ Finset.range N, S.gStage (S.optInit a T)
      (S.glq.optCtrl (S.optInit a T) T) k
      ≤ S.glq.cost (S.optInit a T) (S.glq.optCtrl (S.optInit a T) T) T := by
    rw [cost_eq_sum_gStage]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hT) fun k _ _ => S.gStage_nonneg _ _ _
  have h2 : S.priorPen a (S.optInit a T)
      + S.glq.cost (S.optInit a T) (S.glq.optCtrl (S.optInit a T) T) T
      = S.value a T := S.gCost_optCtrl a T
  have h3 := S.value_le_valueLim hC2 a T
  linarith

/-- The limit stage costs are summable. -/
theorem summable_gStage_lim (hC2 : S.C2) (a : Fin n → ℝ) :
    Summable (fun k => S.gStage (S.optInitLim a) (S.optCtrlLim a) k) := by
  refine summable_of_sum_range_le (fun k => S.gStage_nonneg _ _ _)
    (c := S.valueLim a - S.priorPen a (S.optInitLim a)) fun N => ?_
  have h1 := S.partial_le_valueLim hC2 a N
  linarith

/-- The limit pair is feasible (closedness of the prior range). -/
theorem optInitLim_feasible (hC2 : S.C2) (a : Fin n → ℝ) :
    S.Feasible a (S.optInitLim a) := by
  have hclosed : IsClosed (LinearMap.range S.Sig0.mulVecLin : Set (Fin n → ℝ)) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : ∀ T, S.optInit a T - a ∈ LinearMap.range S.Sig0.mulVecLin := by
    intro T
    obtain ⟨z, hz⟩ := S.optInit_feasible a T
    exact ⟨z, hz.symm⟩
  have hlim : Tendsto (fun T => S.optInit a T - a) atTop
      (nhds (S.optInitLim a - a)) :=
    (S.tendsto_optInit hC2 a).sub_const a
  have h2 : S.optInitLim a - a ∈ LinearMap.range S.Sig0.mulVecLin :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
  obtain ⟨z, hz⟩ := h2
  exact ⟨z, hz.symm⟩

/-- **`it:Vlim`**: the infinite-horizon cost of the limit pair equals
the limiting value, under C2 alone. -/
theorem gInfCost_optLim (hC2 : S.C2) (a : Fin n → ℝ) :
    S.gInfCost a (S.optInitLim a) (S.optCtrlLim a) = S.valueLim a := by
  have hsummable := S.summable_gStage_lim hC2 a
  refine le_antisymm ?_ ?_
  · -- `≤`: partial sums are dominated, then pass to the series
    unfold gInfCost
    have h1 := Real.tsum_le_of_sum_range_le
      (f := fun k => S.gStage (S.optInitLim a) (S.optCtrlLim a) k)
      (c := S.valueLim a - S.priorPen a (S.optInitLim a))
      (fun k => S.gStage_nonneg _ _ _) (fun N => by
        have h2 := S.partial_le_valueLim hC2 a N
        linarith)
    linarith
  · -- `≥`: every prefix of the limit pair is feasible at every horizon
    have hval : ∀ T, S.value a T
        ≤ S.gInfCost a (S.optInitLim a) (S.optCtrlLim a) := by
      intro T
      have h2 := S.value_le_gCost (S.optInitLim_feasible hC2 a)
        (S.optCtrlLim a) T
      refine h2.trans ?_
      unfold gCost gInfCost
      have h3 : S.glq.cost (S.optInitLim a) (S.optCtrlLim a) T
          ≤ ∑' k, S.gStage (S.optInitLim a) (S.optCtrlLim a) k := by
        rw [cost_eq_sum_gStage]
        exact hsummable.sum_le_tsum _ fun k _ => S.gStage_nonneg _ _ _
      linarith
    exact ciSup_le hval

/-! ### `it:xTT`: terminal errors track the limit rollout, under C1 ∧ C2 -/

/-- Every prefix cost of the limit pair is dominated by the limiting
value. -/
lemma gCost_optLim_le (hC2 : S.C2) (a : Fin n → ℝ) (T : ℕ) :
    S.gCost a (S.optInitLim a) (S.optCtrlLim a) T ≤ S.valueLim a := by
  have h1 : S.glq.cost (S.optInitLim a) (S.optCtrlLim a) T
      ≤ ∑' k, S.gStage (S.optInitLim a) (S.optCtrlLim a) k := by
    rw [cost_eq_sum_gStage]
    exact (S.summable_gStage_lim hC2 a).sum_le_tsum _
      fun k _ => S.gStage_nonneg _ _ _
  have h2 := S.gInfCost_optLim hC2 a
  unfold gCost
  unfold gInfCost at h2
  linarith

/-- The optimal terminal error is the trajectory endpoint of the
optimal pair. -/
lemma optTerm_eq_traj (a : Fin n → ℝ) (T : ℕ) :
    S.optTerm a T = S.glq.traj (S.optInit a T)
      (S.glq.optCtrl (S.optInit a T) T) T := by
  unfold optTerm
  rw [S.glq.traj_optCtrl]

/-- **`it:xTT`**: under C1 ∧ C2 the horizon-`T` terminal error tracks
the endpoint of the limit rollout. -/
theorem tendsto_optTerm_sub_limTraj (hC1 : S.C1) (hC2 : S.C2)
    (a : Fin n → ℝ) :
    Tendsto (fun T => S.optTerm a T
        - S.glq.traj (S.optInitLim a) (S.optCtrlLim a) T) atTop
      (nhds 0) := by
  classical
  -- the deviation pair at horizon `T`
  set d : ℕ → Fin n → ℝ :=
    fun T => S.optInitLim a - S.optInit a T with hd
  set δ : ℕ → ℕ → Fin m → ℝ :=
    fun T j => S.optCtrlLim a j - S.glq.optCtrl (S.optInit a T) T j
    with hδ
  -- gap of the limit pair at horizon T
  have hgap : ∀ T, S.gCost 0 (d T) (δ T) T
      ≤ S.valueLim a - S.value a T := by
    intro T
    have h1 := S.gCost_gap (S.optInitLim_feasible hC2 a)
      (S.optCtrlLim a) T
    have h2 := S.gCost_optLim_le hC2 a T
    rw [hd, hδ]
    simp only
    linarith
  -- deviation feasibility
  have hdfeas : ∀ T, S.Feasible 0 (d T) :=
    fun T => S.feasible_sub (S.optInitLim_feasible hC2 a)
      (S.optInit_feasible a T)
  -- energy bound
  obtain ⟨cE, hcE, hbE⟩ := S.exists_gap_energy_bound
  -- output injection for the deviation dynamics
  obtain ⟨L, hL⟩ := detect_inj S.A S.C hC1
  obtain ⟨cT, hcT, hbT⟩ :=
    exists_terminal_sq_bound_of_injection S.A S.C (-S.G) hL
  -- the deviation trajectory is a trajectory of the error dynamics
  have hrec : ∀ T k, S.glq.traj (d T) (δ T) (k + 1)
      = S.A *ᵥ S.glq.traj (d T) (δ T) k + (-S.G) *ᵥ δ T k := by
    intro T k
    rw [LQSystem.traj_succ]
    rfl
  -- terminal deviation controlled by the gap
  have hterm : ∀ T, ‖S.glq.traj (d T) (δ T) T‖ ^ 2
      ≤ cT * (1 + cE) * (S.valueLim a - S.value a T) := by
    intro T
    have h3 := hbT (fun k => S.glq.traj (d T) (δ T) k) (δ T)
      (hrec T) T
    have h4 := hbE (hdfeas T) (δ T) T
    have h5 := hgap T
    have hgap0 : 0 ≤ S.gCost 0 (d T) (δ T) T := by
      unfold gCost
      have h20 := S.priorPen_nonneg 0 (d T)
      have h21 : (0:ℝ) ≤ S.glq.cost (d T) (δ T) T :=
        Finset.sum_nonneg fun k _ => S.glq.stage_nonneg _ _
      linarith
    have h6 : ‖(fun k => S.glq.traj (d T) (δ T) k) 0‖ ^ 2
        + ∑ k ∈ Finset.range T,
          (‖S.C *ᵥ (fun k => S.glq.traj (d T) (δ T) k) k‖ ^ 2
            + ‖δ T k‖ ^ 2)
        ≤ (1 + cE) * (S.valueLim a - S.value a T) := by
      have h7 : (fun k => S.glq.traj (d T) (δ T) k) 0 = d T := rfl
      rw [h7]
      have h8 : ∑ k ∈ Finset.range T,
          (‖S.C *ᵥ S.glq.traj (d T) (δ T) k‖ ^ 2 + ‖δ T k‖ ^ 2)
          = (∑ k ∈ Finset.range T, ‖δ T k‖ ^ 2)
            + ∑ k ∈ Finset.range T,
              ‖S.C *ᵥ S.glq.traj (d T) (δ T) k‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h8]
      have h9 : cE * S.gCost 0 (d T) (δ T) T
          ≤ cE * (S.valueLim a - S.value a T) :=
        mul_le_mul_of_nonneg_left h5 hcE.le
      have h10 : (0:ℝ) ≤ S.valueLim a - S.value a T :=
        le_trans hgap0 h5
      linarith
    calc ‖S.glq.traj (d T) (δ T) T‖ ^ 2
        ≤ cT * (‖(fun k => S.glq.traj (d T) (δ T) k) 0‖ ^ 2
          + ∑ k ∈ Finset.range T,
            (‖S.C *ᵥ (fun k => S.glq.traj (d T) (δ T) k) k‖ ^ 2
              + ‖δ T k‖ ^ 2)) := h3
      _ ≤ cT * ((1 + cE) * (S.valueLim a - S.value a T)) :=
          mul_le_mul_of_nonneg_left h6 hcT.le
      _ = cT * (1 + cE) * (S.valueLim a - S.value a T) := by ring
  -- the deviation trajectory is the difference of trajectories
  have hdiff : ∀ T, S.glq.traj (d T) (δ T) T
      = S.glq.traj (S.optInitLim a) (S.optCtrlLim a) T
        - S.glq.traj (S.optInit a T)
            (S.glq.optCtrl (S.optInit a T) T) T := by
    intro T
    have h11 := S.glq.traj_add (S.optInit a T) (d T)
      (S.glq.optCtrl (S.optInit a T) T) (δ T) T
    have h12 : S.optInit a T + d T = S.optInitLim a := by
      rw [hd]
      module
    have h13 : (fun j => S.glq.optCtrl (S.optInit a T) T j + δ T j)
        = S.optCtrlLim a := by
      funext j
      rw [hδ]
      module
    rw [h12, h13] at h11
    rw [h11]
    module
  -- squeeze
  have hnorm : ∀ T, ‖S.optTerm a T
      - S.glq.traj (S.optInitLim a) (S.optCtrlLim a) T‖ ^ 2
      ≤ cT * (1 + cE) * (S.valueLim a - S.value a T) := by
    intro T
    have h14 := hterm T
    rw [hdiff T] at h14
    have h15 : S.optTerm a T
        - S.glq.traj (S.optInitLim a) (S.optCtrlLim a) T
        = -(S.glq.traj (S.optInitLim a) (S.optCtrlLim a) T
          - S.glq.traj (S.optInit a T)
              (S.glq.optCtrl (S.optInit a T) T) T) := by
      rw [S.optTerm_eq_traj]
      module
    rw [h15, norm_neg]
    exact h14
  have hε : Tendsto (fun T => cT * (1 + cE)
      * (S.valueLim a - S.value a T)) atTop (nhds 0) := by
    have h16 := (S.tendsto_value hC2 a).const_sub (S.valueLim a)
    have h17 := h16.const_mul (cT * (1 + cE))
    simpa using h17
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun T => ‖S.optTerm a T
      - S.glq.traj (S.optInitLim a) (S.optCtrlLim a) T‖ ^ 2) atTop
      (nhds 0) :=
    squeeze_zero (fun T => sq_nonneg _) hnorm hε
  have h18 : Tendsto (fun T => Real.sqrt (‖S.optTerm a T
      - S.glq.traj (S.optInitLim a) (S.optCtrlLim a) T‖ ^ 2)) atTop
      (nhds 0) := by
    have h19 := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at h19
    exact h19
  refine h18.congr fun T => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

end GeneralSystem

end Estimation

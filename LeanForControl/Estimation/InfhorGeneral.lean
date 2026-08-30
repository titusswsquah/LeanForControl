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

end GeneralSystem

end Estimation

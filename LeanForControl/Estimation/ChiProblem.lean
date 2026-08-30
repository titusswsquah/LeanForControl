import LeanForControl.Estimation.InfhorGeneral
import Architect

/-!
# The `ℙ_T` problem in original coordinates and `prop:infhor`

The paper's estimation problem `ℙ_T` (`lem:semiPT` form): decisions
`(χ(0), ω)`, dynamics `χ⁺ = Aχ + Gω`, nominal data `y(k) = CA^k x(0)`,
residuals `ν = y − Cχ`, cost `ℓ_x(χ(0) − x̄₀) + Σ ℓ(ω, ν)`, support
constraint `χ(0) − x̄₀ ∈ range Σ₀` (equivalently `U₂'(χ(0) − x̄₀) = 0`,
by `LinearSystems.mem_range_iff_forall_ker`). Everything transports to
the error-coordinate `GeneralSystem` problem through the affine
bijection `e = A^k x(0) − χ`, and `prop:infhor` is assembled here in
the paper's variables with the paper's hypothesis split.
-/

namespace Estimation

open Matrix LinearSystems Filter

namespace GeneralSystem

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-! ### The `ℙ_T` objects -/

/-- The estimate trajectory `χ`. -/
noncomputable def chiTraj (χ₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => χ₀
  | k + 1 => S.A *ᵥ chiTraj χ₀ ω k + S.G *ᵥ ω k

/-- Nominal measurements `y(k) = CA^k x(0)` (`eq:nommeas`). -/
noncomputable def nominalY (x₀ : Fin n → ℝ) (k : ℕ) : Fin p → ℝ :=
  S.C *ᵥ (S.A ^ k *ᵥ x₀)

/-- The measurement residual `ν(k) = y(k) − Cχ(k)`. -/
noncomputable def chiResid (x₀ χ₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ)
    (k : ℕ) : Fin p → ℝ :=
  S.nominalY x₀ k - S.C *ᵥ S.chiTraj χ₀ ω k

/-- The `ℙ_T` objective. -/
noncomputable def chiCost (x₀ xbar χ₀ : Fin n → ℝ)
    (ω : ℕ → Fin m → ℝ) (T : ℕ) : ℝ :=
  quadForm (symmPinv S.hSig0.1) (χ₀ - xbar)
    + ∑ k ∈ Finset.range T,
        (quadForm S.Qi (ω k) + quadForm S.Ri (S.chiResid x₀ χ₀ ω k))

/-- The `ℙ_T` support constraint, in range form. -/
def ChiFeasible (xbar χ₀ : Fin n → ℝ) : Prop :=
  ∃ z, χ₀ - xbar = S.Sig0 *ᵥ z

/-- The support constraint in the paper's `U₂'`-form: orthogonality to
the kernel of the prior. -/
lemma chiFeasible_iff_ker (xbar χ₀ : Fin n → ℝ) :
    S.ChiFeasible xbar χ₀
      ↔ ∀ u, S.Sig0 *ᵥ u = 0 → u ⬝ᵥ (χ₀ - xbar) = 0 := by
  unfold ChiFeasible
  constructor
  · rintro ⟨z, hz⟩
    rw [hz]
    exact fun u hu =>
      ((mem_range_iff_forall_ker S.hSig0 (S.Sig0 *ᵥ z)).mp
        ⟨z, rfl⟩) u hu
  · intro h
    obtain ⟨z, hz⟩ := (mem_range_iff_forall_ker S.hSig0 (χ₀ - xbar)).mpr h
    exact ⟨z, hz⟩

/-! ### The affine bijection to error coordinates -/

/-- The error along a `χ`-trajectory is the error-system trajectory of
the mismatched initial error, with the same noise. -/
lemma error_traj (x₀ χ₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ) : ∀ k,
    S.A ^ k *ᵥ x₀ - S.chiTraj χ₀ ω k
      = S.glq.traj (x₀ - χ₀) ω k
  | 0 => by
    simp [chiTraj, LQSystem.traj_zero]
  | k + 1 => by
    rw [LQSystem.traj_succ, ← error_traj x₀ χ₀ ω k]
    show S.A ^ (k + 1) *ᵥ x₀ - S.chiTraj χ₀ ω (k + 1) = _
    rw [show S.chiTraj χ₀ ω (k + 1)
        = S.A *ᵥ S.chiTraj χ₀ ω k + S.G *ᵥ ω k from rfl, glq_A_eq,
      glq_B_eq, show S.A ^ (k + 1) *ᵥ x₀
        = S.A *ᵥ (S.A ^ k *ᵥ x₀) from by
        rw [Matrix.mulVec_mulVec, ← pow_succ'],
      Matrix.mulVec_sub, Matrix.neg_mulVec]
    module

/-- Residuals are outputs of the error trajectory. -/
lemma chiResid_eq (x₀ χ₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ) (k : ℕ) :
    S.chiResid x₀ χ₀ ω k = S.C *ᵥ S.glq.traj (x₀ - χ₀) ω k := by
  unfold chiResid nominalY
  rw [← S.error_traj x₀ χ₀ ω k, Matrix.mulVec_sub]

/-- The `ℙ_T` cost is the error-coordinate cost. -/
theorem chiCost_eq_gCost (x₀ xbar χ₀ : Fin n → ℝ)
    (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    S.chiCost x₀ xbar χ₀ ω T
      = S.gCost (x₀ - xbar) (x₀ - χ₀) ω T := by
  unfold chiCost gCost priorPen
  have h1 : χ₀ - xbar = -((x₀ - χ₀) - (x₀ - xbar)) := by
    module
  rw [h1, quadForm_neg]
  congr 1
  unfold LQSystem.cost
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [S.chiResid_eq, S.quadForm_glq_Qs]
  have h2 : quadForm S.glq.Ru (ω k) = quadForm S.Qi (ω k) := rfl
  rw [h2]
  ring

/-- Feasibility corresponds. -/
lemma chiFeasible_iff (x₀ xbar χ₀ : Fin n → ℝ) :
    S.ChiFeasible xbar χ₀ ↔ S.Feasible (x₀ - xbar) (x₀ - χ₀) := by
  unfold ChiFeasible Feasible
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    rw [Matrix.mulVec_neg, ← hz]
    module
  · rintro ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    rw [Matrix.mulVec_neg, ← hz]
    module

/-! ### The `ℙ_T` optimizer -/

/-- The optimal `ℙ_T` initial estimate `x̂(0|T)`. -/
noncomputable def chiOpt (x₀ xbar : Fin n → ℝ) (T : ℕ) : Fin n → ℝ :=
  x₀ - S.optInit (x₀ - xbar) T

/-- The optimal `ℙ_T` noise `ŵ(·|T)`. -/
noncomputable def chiOptCtrl (x₀ xbar : Fin n → ℝ) (T k : ℕ) :
    Fin m → ℝ :=
  S.glq.optCtrl (S.optInit (x₀ - xbar) T) T k

/-- The optimal `ℙ_T` estimate trajectory `x̂(k|T)`. -/
noncomputable def chiOptTraj (x₀ xbar : Fin n → ℝ) (T k : ℕ) :
    Fin n → ℝ :=
  S.A ^ k *ᵥ x₀
    - S.glq.traj (S.optInit (x₀ - xbar) T) (S.chiOptCtrl x₀ xbar T) k

/-- The optimizer attains the value. -/
theorem chiCost_chiOpt (x₀ xbar : Fin n → ℝ) (T : ℕ) :
    S.chiCost x₀ xbar (S.chiOpt x₀ xbar T) (S.chiOptCtrl x₀ xbar T) T
      = S.value (x₀ - xbar) T := by
  rw [chiCost_eq_gCost]
  have h1 : x₀ - S.chiOpt x₀ xbar T = S.optInit (x₀ - xbar) T := by
    unfold chiOpt
    module
  rw [h1]
  exact S.gCost_optCtrl (x₀ - xbar) T

/-- Joint optimality: no feasible `ℙ_T` decision does better. -/
theorem value_le_chiCost {x₀ xbar χ₀ : Fin n → ℝ}
    (hfeas : S.ChiFeasible xbar χ₀) (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    S.value (x₀ - xbar) T ≤ S.chiCost x₀ xbar χ₀ ω T := by
  rw [chiCost_eq_gCost]
  exact S.value_le_gCost ((S.chiFeasible_iff x₀ xbar χ₀).mp hfeas) ω T

/-- **`lem:exist` in `ℙ_T` form**: minimizers are unique in both
components. -/
theorem chiOpt_unique {x₀ xbar χ₀ : Fin n → ℝ} {ω : ℕ → Fin m → ℝ}
    {T : ℕ} (hfeas : S.ChiFeasible xbar χ₀)
    (hmin : S.chiCost x₀ xbar χ₀ ω T = S.value (x₀ - xbar) T) :
    χ₀ = S.chiOpt x₀ xbar T ∧ ∀ k < T, ω k = S.chiOptCtrl x₀ xbar T k := by
  rw [chiCost_eq_gCost] at hmin
  obtain ⟨h1, h2⟩ := S.optimal_pair_unique
    ((S.chiFeasible_iff x₀ xbar χ₀).mp hfeas) hmin
  constructor
  · unfold chiOpt
    rw [← h1]
    module
  · intro k hk
    exact h2 k hk

/-! ### `prop:infhor` in the paper's variables -/

/-- The limiting initial estimate `x̂(0|∞)`. -/
noncomputable def chiOptLim (x₀ xbar : Fin n → ℝ) : Fin n → ℝ :=
  x₀ - S.optInitLim (x₀ - xbar)

/-- The limiting noise sequence `ŵ(·|∞)`. -/
noncomputable def chiOptCtrlLim (x₀ xbar : Fin n → ℝ) (k : ℕ) :
    Fin m → ℝ :=
  S.optCtrlLim (x₀ - xbar) k

/-- The limit estimate trajectory `x̂(k|∞)`: the rollout of
`(x̂(0|∞), ŵ_∞)`. -/
noncomputable def chiOptTrajLim (x₀ xbar : Fin n → ℝ) (k : ℕ) :
    Fin n → ℝ :=
  S.A ^ k *ᵥ x₀
    - S.glq.traj (S.optInitLim (x₀ - xbar)) (S.optCtrlLim (x₀ - xbar)) k

/-- `x̂(·|∞)` is indeed the `χ`-rollout of the limit pair. -/
lemma chiOptTrajLim_eq_chiTraj (x₀ xbar : Fin n → ℝ) (k : ℕ) :
    S.chiOptTrajLim x₀ xbar k
      = S.chiTraj (S.chiOptLim x₀ xbar) (S.chiOptCtrlLim x₀ xbar) k := by
  unfold chiOptTrajLim chiOptCtrlLim
  have h1 := S.error_traj x₀ (S.chiOptLim x₀ xbar)
    (S.optCtrlLim (x₀ - xbar)) k
  have h2 : x₀ - S.chiOptLim x₀ xbar = S.optInitLim (x₀ - xbar) := by
    unfold chiOptLim
    module
  rw [h2] at h1
  rw [← h1]
  module

/-- The `ℙ_T` infinite-horizon cost `V_∞`. -/
noncomputable def chiInfCost (x₀ xbar χ₀ : Fin n → ℝ)
    (ω : ℕ → Fin m → ℝ) : ℝ :=
  quadForm (symmPinv S.hSig0.1) (χ₀ - xbar)
    + ∑' k, (quadForm S.Qi (ω k) + quadForm S.Ri (S.chiResid x₀ χ₀ ω k))

lemma chiInfCost_eq_gInfCost (x₀ xbar χ₀ : Fin n → ℝ)
    (ω : ℕ → Fin m → ℝ) :
    S.chiInfCost x₀ xbar χ₀ ω
      = S.gInfCost (x₀ - xbar) (x₀ - χ₀) ω := by
  unfold chiInfCost gInfCost priorPen
  have h1 : χ₀ - xbar = -((x₀ - χ₀) - (x₀ - xbar)) := by
    module
  rw [h1, quadForm_neg]
  congr 1
  refine tsum_congr fun k => ?_
  unfold gStage
  rw [S.chiResid_eq, S.quadForm_glq_Qs]
  have h2 : quadForm S.glq.Ru (ω k) = quadForm S.Qi (ω k) := rfl
  rw [h2]
  ring

/-- **`prop:infhor`, `it:zlim`** (C2 alone): the optimal initial
estimates and noises converge. -/
theorem prop_infhor_zlim (hC2 : S.C2) (x₀ xbar : Fin n → ℝ) :
    Tendsto (fun T => S.chiOpt x₀ xbar T) atTop
        (nhds (S.chiOptLim x₀ xbar))
      ∧ ∀ k, Tendsto (fun T => S.chiOptCtrl x₀ xbar T k) atTop
        (nhds (S.chiOptCtrlLim x₀ xbar k)) := by
  constructor
  · have h1 := S.tendsto_optInit hC2 (x₀ - xbar)
    have h2 := (tendsto_const_nhds (x := x₀)
      (f := atTop (α := ℕ))).sub h1
    exact h2
  · intro k
    exact S.tendsto_optCtrl hC2 (x₀ - xbar) k

/-- **`prop:infhor`, `it:xTT`** (C1 ∧ C2): the terminal estimate tracks
the limit trajectory. -/
theorem prop_infhor_xTT (hC1 : S.C1) (hC2 : S.C2)
    (x₀ xbar : Fin n → ℝ) :
    Tendsto (fun T => S.chiOptTraj x₀ xbar T T
        - S.chiOptTrajLim x₀ xbar T) atTop (nhds 0) := by
  have h1 := S.tendsto_optTerm_sub_limTraj hC1 hC2 (x₀ - xbar)
  have h2 : (fun T => S.chiOptTraj x₀ xbar T T
      - S.chiOptTrajLim x₀ xbar T)
      = fun T => -(S.optTerm (x₀ - xbar) T
        - S.glq.traj (S.optInitLim (x₀ - xbar))
            (S.optCtrlLim (x₀ - xbar)) T) := by
    funext T
    unfold chiOptTraj chiOptTrajLim chiOptCtrl
    rw [S.optTerm_eq_traj]
    module
  rw [h2]
  have h3 := h1.neg
  simpa using h3

/-- **`prop:infhor`, `it:Vlim`** (C2 alone): the infinite-horizon cost
of the limit pair is the limiting optimal value. -/
theorem prop_infhor_Vlim (hC2 : S.C2) (x₀ xbar : Fin n → ℝ) :
    S.chiInfCost x₀ xbar (S.chiOptLim x₀ xbar)
        (S.chiOptCtrlLim x₀ xbar)
      = S.valueLim (x₀ - xbar) := by
  rw [chiInfCost_eq_gInfCost]
  have h1 : x₀ - S.chiOptLim x₀ xbar = S.optInitLim (x₀ - xbar) := by
    unfold chiOptLim
    module
  rw [h1]
  exact S.gInfCost_optLim hC2 (x₀ - xbar)

end GeneralSystem

end Estimation

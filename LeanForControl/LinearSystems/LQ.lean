import LeanForControl.LinearSystems.QuadForm
import Architect

/-!
# Finite-horizon linear-quadratic control: the Riccati value iteration

The dynamic-programming core of the `costogo` formalization. For the system
`x⁺ = A x + B u` with stage cost `x'Qs x + u'Ru u` (`Qs ⪰ 0`, `Ru ≻ 0`), the
horizon-`T` value function is the quadratic form of the `T`-th Riccati
iterate, and every control sequence satisfies the **exact sum-of-squares
identity**

`cost x₀ u T = x₀' (ric T) x₀ + ∑_{k<T} ‖u k + K_(T-1-k) x k‖²_{Γ(T-1-k)}`

(`LQSystem.cost_eq_quadForm_add_sum`), from which optimality of the
time-varying closed loop, the exact optimality gap, and monotonicity of the
iterates all read off. The estimation layer instantiates this over the block
index `Fin n₁ ⊕ Fin n₂`; the staged `fact:lqr` (infinite-horizon
convergence) will live on top of the same definitions.

No `½` is carried in the cost: values here are twice the paper's, which
affects no statement of interest.
-/

namespace LinearSystems

open Matrix

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A finite-horizon linear-quadratic problem: dynamics `x⁺ = A x + B u`,
stage cost `x'Qs x + u'Ru u` with `Qs ⪰ 0` and `Ru ≻ 0`. -/
structure LQSystem (ι κ : Type*) [Fintype ι] [Fintype κ] where
  /-- State matrix. -/
  A : Matrix ι ι ℝ
  /-- Input matrix. -/
  B : Matrix ι κ ℝ
  /-- State penalty (positive semidefinite). -/
  Qs : Matrix ι ι ℝ
  /-- Input penalty (positive definite). -/
  Ru : Matrix κ κ ℝ
  /-- The state penalty is positive semidefinite. -/
  hQs : Qs.PosSemidef
  /-- The input penalty is positive definite. -/
  hRu : Ru.PosDef

namespace LQSystem

variable (S : LQSystem ι κ)

/-- The information/curvature matrix `Γ(P) = Ru + BᵀPB`. -/
noncomputable def gainΓ (P : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  S.Ru + S.Bᵀ * P * S.B

/-- The optimal feedback gain `K(P) = Γ(P)⁻¹ BᵀPA` (the optimal input is
`u = -K(P) x`). -/
noncomputable def gainK (P : Matrix ι ι ℝ) : Matrix κ ι ℝ :=
  (S.gainΓ P)⁻¹ * S.Bᵀ * P * S.A

/-- The closed-loop matrix `A - B K(P)`. -/
noncomputable def Acl (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  S.A - S.B * S.gainK P

/-- One step of the Riccati value iteration. -/
noncomputable def step (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  S.Qs + S.Aᵀ * P * S.A -
    S.Aᵀ * P * S.B * (S.gainΓ P)⁻¹ * S.Bᵀ * P * S.A

/-- The Riccati value iterates from zero terminal cost: `ric T` is the value
matrix of the horizon-`T` problem. -/
noncomputable def ric : ℕ → Matrix ι ι ℝ
  | 0 => 0
  | T + 1 => S.step (ric T)

@[simp]
lemma ric_zero : S.ric 0 = 0 := rfl

lemma ric_succ (T : ℕ) : S.ric (T + 1) = S.step (S.ric T) := rfl

section GainAlgebra

variable {P : Matrix ι ι ℝ}

/-- `Γ(P) ≻ 0` for `P ⪰ 0`. -/
lemma gainΓ_posDef (hP : P.PosSemidef) : (S.gainΓ P).PosDef := by
  have h1 : (S.Bᵀ * P * S.B).PosSemidef := by
    have h := hP.mul_mul_conjTranspose_same S.Bᵀ
    rwa [show (S.Bᵀ)ᴴ = S.B from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]] at h
  exact S.hRu.add_posSemidef h1

lemma gainΓ_isHermitian (hP : P.PosSemidef) : (S.gainΓ P).IsHermitian :=
  (S.gainΓ_posDef hP).1

lemma gainΓ_isUnit (hP : P.PosSemidef) : IsUnit (S.gainΓ P) :=
  (S.gainΓ_posDef hP).isUnit

lemma gainΓ_isUnit_det (hP : P.PosSemidef) : IsUnit (S.gainΓ P).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (S.gainΓ_isUnit hP)

lemma gainΓ_mul_inv (hP : P.PosSemidef) :
    S.gainΓ P * (S.gainΓ P)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (S.gainΓ_isUnit_det hP)

lemma gainΓ_inv_mul (hP : P.PosSemidef) :
    (S.gainΓ P)⁻¹ * S.gainΓ P = 1 :=
  Matrix.nonsing_inv_mul _ (S.gainΓ_isUnit_det hP)

/-- The gain equation `Γ(P) K(P) = BᵀPA`. -/
lemma gainΓ_mul_gainK (hP : P.PosSemidef) :
    S.gainΓ P * S.gainK P = S.Bᵀ * P * S.A := by
  unfold gainK
  rw [show (S.gainΓ P)⁻¹ * S.Bᵀ * P * S.A
      = (S.gainΓ P)⁻¹ * (S.Bᵀ * P * S.A) by
    simp only [Matrix.mul_assoc],
    ← Matrix.mul_assoc, S.gainΓ_mul_inv hP, Matrix.one_mul]

/-- Transposed gain equation `K(P)ᵀ Γ(P) = AᵀPB` (for symmetric `P`). -/
lemma gainK_transpose_mul_gainΓ (hP : P.PosSemidef) :
    (S.gainK P)ᵀ * S.gainΓ P = S.Aᵀ * P * S.B := by
  have h := congrArg Matrix.transpose (S.gainΓ_mul_gainK hP)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose] at h
  have hΓ : (S.gainΓ P)ᵀ = S.gainΓ P := by
    have := S.gainΓ_isHermitian hP
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hPt : Pᵀ = P := by
    have := hP.1
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  rw [hΓ] at h
  rw [h, hPt]
  simp [Matrix.mul_assoc]

/-- The Riccati step in closed (completed-square) form:
`step P = Qs + AᵀPA - K(P)ᵀ Γ(P) K(P)`. -/
lemma step_eq_closed (hP : P.PosSemidef) :
    S.step P = S.Qs + S.Aᵀ * P * S.A -
      (S.gainK P)ᵀ * S.gainΓ P * S.gainK P := by
  have hPt : Pᵀ = P := by
    have := hP.1
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hΓinv : ((S.gainΓ P)⁻¹)ᵀ = (S.gainΓ P)⁻¹ := by
    have h1 : ((S.gainΓ P)⁻¹).IsHermitian := (S.gainΓ_isHermitian hP).inv
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at h1
  have hK : (S.gainK P)ᵀ * S.gainΓ P * S.gainK P
      = S.Aᵀ * P * S.B * (S.gainΓ P)⁻¹ * S.Bᵀ * P * S.A := by
    rw [Matrix.mul_assoc, S.gainΓ_mul_gainK hP]
    unfold gainK
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hΓinv, hPt]
    simp [Matrix.mul_assoc]
  unfold step
  rw [hK]

/-- The Riccati step in Joseph form:
`step P = Acl(P)ᵀ P Acl(P) + Qs + K(P)ᵀ Ru K(P)`. -/
lemma step_eq_joseph (hP : P.PosSemidef) :
    S.step P = (S.Acl P)ᵀ * P * S.Acl P + S.Qs +
      (S.gainK P)ᵀ * S.Ru * S.gainK P := by
  have hPt : Pᵀ = P := by
    have := hP.1
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hexp : (S.Acl P)ᵀ * P * S.Acl P
      = S.Aᵀ * P * S.A - S.Aᵀ * P * S.B * S.gainK P
        - (S.gainK P)ᵀ * (S.Bᵀ * P * S.A)
        + (S.gainK P)ᵀ * (S.Bᵀ * P * S.B) * S.gainK P := by
    unfold Acl
    rw [Matrix.transpose_sub, Matrix.transpose_mul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [hexp, ← S.gainΓ_mul_gainK hP]
  have hABK : S.Aᵀ * P * S.B * S.gainK P
      = (S.gainK P)ᵀ * S.gainΓ P * S.gainK P := by
    rw [← S.gainK_transpose_mul_gainΓ hP]
  rw [hABK, S.step_eq_closed hP]
  unfold gainΓ
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- One Riccati step preserves positive semidefiniteness. -/
lemma step_posSemidef (hP : P.PosSemidef) : (S.step P).PosSemidef := by
  rw [S.step_eq_joseph hP]
  have h1 : ((S.Acl P)ᵀ * P * S.Acl P).PosSemidef := by
    have h := hP.mul_mul_conjTranspose_same (S.Acl P)ᵀ
    rwa [show ((S.Acl P)ᵀ)ᴴ = S.Acl P from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]] at h
  have h2 : ((S.gainK P)ᵀ * S.Ru * S.gainK P).PosSemidef := by
    have h := S.hRu.posSemidef.mul_mul_conjTranspose_same (S.gainK P)ᵀ
    rwa [show ((S.gainK P)ᵀ)ᴴ = S.gainK P from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]] at h
  exact (h1.add S.hQs).add h2

/-- All Riccati iterates are positive semidefinite. -/
lemma ric_posSemidef : ∀ T, (S.ric T).PosSemidef
  | 0 => Matrix.PosSemidef.zero
  | T + 1 => S.step_posSemidef (ric_posSemidef T)

lemma ric_isHermitian (T : ℕ) : (S.ric T).IsHermitian :=
  (S.ric_posSemidef T).1

end GainAlgebra

section Bellman

variable {P : Matrix ι ι ℝ}

/-- **One-step completion of squares**: the Bellman identity for one Riccati
step. For `P ⪰ 0` and every state `x` and input `u`,
`x'Qs x + u'Ru u + (Ax+Bu)'P(Ax+Bu) = x'(step P)x + ‖u + K(P)x‖²_{Γ(P)}`. -/
lemma bellman_step (hP : P.PosSemidef) (x : ι → ℝ) (u : κ → ℝ) :
    quadForm S.Qs x + quadForm S.Ru u + quadForm P (S.A *ᵥ x + S.B *ᵥ u)
      = quadForm (S.step P) x + quadForm (S.gainΓ P) (u + S.gainK P *ᵥ x) := by
  have h3 : quadForm P (S.A *ᵥ x + S.B *ᵥ u)
      = quadForm (S.Aᵀ * P * S.A) x + x ⬝ᵥ ((S.Aᵀ * P * S.B) *ᵥ u)
        + u ⬝ᵥ ((S.Bᵀ * P * S.A) *ᵥ x) + quadForm (S.Bᵀ * P * S.B) u := by
    rw [quadForm_add, quadForm_mulVec, quadForm_mulVec,
      mulVec_dotProduct_mulVec_mulVec, mulVec_dotProduct_mulVec_mulVec]
  have h4 : quadForm (S.gainΓ P) (u + S.gainK P *ᵥ x)
      = quadForm (S.gainΓ P) u + u ⬝ᵥ ((S.Bᵀ * P * S.A) *ᵥ x)
        + x ⬝ᵥ ((S.Aᵀ * P * S.B) *ᵥ u)
        + quadForm ((S.gainK P)ᵀ * S.gainΓ P * S.gainK P) x := by
    rw [quadForm_add, quadForm_mulVec, Matrix.mulVec_mulVec,
      S.gainΓ_mul_gainK hP, mulVec_dotProduct_eq (S.gainK P),
      Matrix.mulVec_mulVec, S.gainK_transpose_mul_gainΓ hP]
  have h5 : quadForm S.Ru u + quadForm (S.Bᵀ * P * S.B) u
      = quadForm (S.gainΓ P) u := by
    rw [← quadForm_add_matrix]
    rfl
  have h6 : quadForm S.Qs x + quadForm (S.Aᵀ * P * S.A) x
      = quadForm (S.step P) x
        + quadForm ((S.gainK P)ᵀ * S.gainΓ P * S.gainK P) x := by
    rw [← quadForm_add_matrix, ← quadForm_add_matrix]
    congr 1
    rw [S.step_eq_closed hP]
    abel
  linarith [h3, h4, h5, h6]

end Bellman

section Trajectories

/-- The controlled trajectory of `x⁺ = A x + B u` from `x₀`. -/
def traj (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) : ℕ → ι → ℝ
  | 0 => x₀
  | k + 1 => S.A *ᵥ traj x₀ u k + S.B *ᵥ u k

@[simp]
lemma traj_zero (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) : S.traj x₀ u 0 = x₀ :=
  rfl

lemma traj_succ (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) (k : ℕ) :
    S.traj x₀ u (k + 1) = S.A *ᵥ S.traj x₀ u k + S.B *ᵥ u k :=
  rfl

/-- Shifting time by one step. -/
lemma traj_shift (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) (k : ℕ) :
    S.traj x₀ u (k + 1)
      = S.traj (S.A *ᵥ x₀ + S.B *ᵥ u 0) (fun j => u (j + 1)) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [traj_succ, ih, traj_succ]

/-- The horizon-`T` cost of a control sequence. -/
noncomputable def cost (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) (T : ℕ) : ℝ :=
  ∑ k ∈ Finset.range T,
    (quadForm S.Qs (S.traj x₀ u k) + quadForm S.Ru (u k))

@[simp]
lemma cost_zero (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) : S.cost x₀ u 0 = 0 := by
  simp [cost]

/-- Peel the first stage off the cost. -/
lemma cost_succ_first (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) (T : ℕ) :
    S.cost x₀ u (T + 1)
      = quadForm S.Qs x₀ + quadForm S.Ru (u 0)
        + S.cost (S.A *ᵥ x₀ + S.B *ᵥ u 0) (fun j => u (j + 1)) T := by
  rw [cost, Finset.sum_range_succ']
  rw [cost]
  have h1 : ∀ k ∈ Finset.range T,
      quadForm S.Qs (S.traj x₀ u (k + 1)) + quadForm S.Ru (u (k + 1))
        = quadForm S.Qs
            (S.traj (S.A *ᵥ x₀ + S.B *ᵥ u 0) (fun j => u (j + 1)) k)
          + quadForm S.Ru (u (k + 1)) := by
    intro k _
    rw [S.traj_shift]
  rw [Finset.sum_congr rfl h1]
  simp [traj_zero]
  ring

/-- Every stage cost is nonnegative. -/
lemma stage_nonneg (x : ι → ℝ) (u : κ → ℝ) :
    0 ≤ quadForm S.Qs x + quadForm S.Ru u :=
  add_nonneg (S.hQs.quadForm_nonneg x) (S.hRu.posSemidef.quadForm_nonneg u)

/-- The cost is monotone in the horizon. -/
lemma cost_mono (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) {T T' : ℕ} (h : T ≤ T') :
    S.cost x₀ u T ≤ S.cost x₀ u T' := by
  unfold cost
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => S.stage_nonneg _ _
  exact fun k hk => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hk) h)

/-- **The exact sum-of-squares identity**: the cost of any control sequence
is the optimal value `x₀'(ric T)x₀` plus the `Γ`-weighted squares of the
deviations from the optimal feedback. Everything else — the value lower
bound, optimality of the closed loop, the exact optimality gap — reads off
this identity. -/
theorem cost_eq_quadForm_add_sum : ∀ (T : ℕ) (x₀ : ι → ℝ) (u : ℕ → κ → ℝ),
    S.cost x₀ u T = quadForm (S.ric T) x₀
      + ∑ k ∈ Finset.range T,
          quadForm (S.gainΓ (S.ric (T - 1 - k)))
            (u k + S.gainK (S.ric (T - 1 - k)) *ᵥ S.traj x₀ u k) := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
    intro x₀ u
    rw [S.cost_succ_first, ih]
    have hb := S.bellman_step (S.ric_posSemidef T) x₀ (u 0)
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ']
    have hsum : ∀ k ∈ Finset.range T,
        quadForm (S.gainΓ (S.ric (T - (k + 1))))
          (u (k + 1) + S.gainK (S.ric (T - (k + 1))) *ᵥ S.traj x₀ u (k + 1))
        = quadForm (S.gainΓ (S.ric (T - 1 - k)))
            ((fun j => u (j + 1)) k + S.gainK (S.ric (T - 1 - k)) *ᵥ
              S.traj (S.A *ᵥ x₀ + S.B *ᵥ u 0) (fun j => u (j + 1)) k) := by
      intro k _
      rw [S.traj_shift]
      have hidx : T - (k + 1) = T - 1 - k := by omega
      rw [hidx]
    rw [Finset.sum_congr rfl hsum]
    simp only [Nat.sub_zero, traj_zero]
    rw [S.ric_succ] at *
    linarith [hb]

/-- The value lower bound: `x₀'(ric T)x₀ ≤ cost x₀ u T` for every control. -/
theorem quadForm_ric_le_cost (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) (T : ℕ) :
    quadForm (S.ric T) x₀ ≤ S.cost x₀ u T := by
  rw [S.cost_eq_quadForm_add_sum T x₀ u]
  have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range T,
      quadForm (S.gainΓ (S.ric (T - 1 - k)))
        (u k + S.gainK (S.ric (T - 1 - k)) *ᵥ S.traj x₀ u k) :=
    Finset.sum_nonneg fun k _ =>
      (S.gainΓ_posDef (S.ric_posSemidef _)).posSemidef.quadForm_nonneg _
  linarith

/-- The optimal closed-loop trajectory for horizon `T` (time-varying gains
`K (ric (T-1-k))`). -/
noncomputable def optTraj (x₀ : ι → ℝ) (T : ℕ) : ℕ → ι → ℝ
  | 0 => x₀
  | k + 1 => S.Acl (S.ric (T - 1 - k)) *ᵥ optTraj x₀ T k

/-- The optimal control for horizon `T`: `u k = -K (ric (T-1-k)) x k`. -/
noncomputable def optCtrl (x₀ : ι → ℝ) (T : ℕ) (k : ℕ) : κ → ℝ :=
  -(S.gainK (S.ric (T - 1 - k)) *ᵥ S.optTraj x₀ T k)

/-- The trajectory under the optimal control is the closed-loop rollout. -/
lemma traj_optCtrl (x₀ : ι → ℝ) (T : ℕ) : ∀ k,
    S.traj x₀ (S.optCtrl x₀ T) k = S.optTraj x₀ T k
  | 0 => rfl
  | k + 1 => by
    rw [traj_succ, traj_optCtrl x₀ T k, optCtrl, optTraj, Acl,
      Matrix.sub_mulVec, Matrix.mulVec_neg, ← Matrix.mulVec_mulVec]
    abel

/-- The optimal control attains the value: `cost x₀ u* T = x₀'(ric T)x₀`. -/
theorem cost_optCtrl (x₀ : ι → ℝ) (T : ℕ) :
    S.cost x₀ (S.optCtrl x₀ T) T = quadForm (S.ric T) x₀ := by
  rw [S.cost_eq_quadForm_add_sum T]
  have h1 : ∀ k ∈ Finset.range T,
      quadForm (S.gainΓ (S.ric (T - 1 - k)))
        (S.optCtrl x₀ T k + S.gainK (S.ric (T - 1 - k)) *ᵥ
          S.traj x₀ (S.optCtrl x₀ T) k) = 0 := by
    intro k _
    rw [S.traj_optCtrl, optCtrl]
    simp
  rw [Finset.sum_congr rfl h1]
  simp

/-- Monotonicity of the value in the horizon, pointwise. -/
lemma quadForm_ric_mono (x₀ : ι → ℝ) (T : ℕ) :
    quadForm (S.ric T) x₀ ≤ quadForm (S.ric (T + 1)) x₀ := by
  calc quadForm (S.ric T) x₀
      ≤ S.cost x₀ (S.optCtrl x₀ (T + 1)) T := S.quadForm_ric_le_cost _ _ _
  _ ≤ S.cost x₀ (S.optCtrl x₀ (T + 1)) (T + 1) :=
      S.cost_mono _ _ (Nat.le_succ T)
  _ = quadForm (S.ric (T + 1)) x₀ := S.cost_optCtrl x₀ (T + 1)

/-- Monotonicity of the Riccati iterates in the Loewner order. -/
lemma ric_succ_sub_posSemidef (T : ℕ) :
    (S.ric (T + 1) - S.ric T).PosSemidef :=
  posSemidef_sub_of_quadForm_le (S.ric_isHermitian T)
    (S.ric_isHermitian (T + 1)) (S.quadForm_ric_mono · T)

/-- Monotonicity of the Riccati iterates, general horizons. -/
lemma ric_sub_posSemidef {T T' : ℕ} (h : T ≤ T') :
    (S.ric T' - S.ric T).PosSemidef := by
  induction T' with
  | zero =>
    have hT : T = 0 := by omega
    subst hT
    simpa using Matrix.PosSemidef.zero
  | succ T' ih =>
    rcases Nat.lt_or_ge T (T' + 1) with h1 | h1
    · have h2 := ih (by omega)
      have h3 := S.ric_succ_sub_posSemidef T'
      have h4 := h2.add h3
      have h5 : S.ric T' - S.ric T + (S.ric (T' + 1) - S.ric T')
          = S.ric (T' + 1) - S.ric T := by abel
      rwa [h5] at h4
    · have hT : T = T' + 1 := by omega
      subst hT
      simpa using Matrix.PosSemidef.zero

/-- Pointwise value monotonicity for general horizons. -/
lemma quadForm_ric_mono_le (x₀ : ι → ℝ) {T T' : ℕ} (h : T ≤ T') :
    quadForm (S.ric T) x₀ ≤ quadForm (S.ric T') x₀ :=
  quadForm_le_quadForm_of_posSemidef_sub (S.ric_sub_posSemidef h) x₀

end Trajectories

end LQSystem

end LinearSystems

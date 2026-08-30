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

/-- The trajectory at time `k` depends only on the inputs before `k`. -/
lemma traj_congr (x₀ : ι → ℝ) {u u' : ℕ → κ → ℝ} {k : ℕ}
    (h : ∀ j < k, u j = u' j) : S.traj x₀ u k = S.traj x₀ u' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [traj_succ, traj_succ, ih fun j hj => h j (by omega),
      h k (by omega)]

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

/-- The horizon-`T` cost depends only on the inputs before `T`. -/
lemma cost_congr (x₀ : ι → ℝ) {u u' : ℕ → κ → ℝ} {T : ℕ}
    (h : ∀ j < T, u j = u' j) : S.cost x₀ u T = S.cost x₀ u' T := by
  unfold cost
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [S.traj_congr x₀ fun j hj =>
      h j (lt_of_lt_of_le hj (Finset.mem_range.mp hk).le),
    h k (Finset.mem_range.mp hk)]

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

section FixedPoint

variable {P : Matrix ι ι ℝ}

/-- At a Riccati fixed point, one closed-loop step pays exactly the drop of
the value function (`eq:are-cl` in energy form). -/
lemma stage_closed_loop_eq (hP : P.PosSemidef) (hfix : S.step P = P)
    (x : ι → ℝ) :
    quadForm S.Qs x + quadForm S.Ru (-(S.gainK P *ᵥ x))
      = quadForm P x - quadForm P (S.Acl P *ᵥ x) := by
  have hb := S.bellman_step hP x (-(S.gainK P *ᵥ x))
  rw [hfix] at hb
  have h1 : S.A *ᵥ x + S.B *ᵥ (-(S.gainK P *ᵥ x)) = S.Acl P *ᵥ x := by
    rw [Matrix.mulVec_neg, Acl, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have h2 : (-(S.gainK P *ᵥ x)) + S.gainK P *ᵥ x = 0 := by abel
  rw [h1, h2, quadForm_zero] at hb
  linarith

/-- The trajectory under the frozen optimal gain is the closed-loop power
rollout. -/
lemma traj_fixedGain (x₀ : ι → ℝ) : ∀ k,
    S.traj x₀ (fun j => -(S.gainK P *ᵥ (S.Acl P ^ j *ᵥ x₀))) k
      = S.Acl P ^ k *ᵥ x₀
  | 0 => by simp
  | k + 1 => by
    rw [traj_succ, traj_fixedGain x₀ k]
    have hstep : S.Acl P ^ (k + 1) *ᵥ x₀ = S.Acl P *ᵥ (S.Acl P ^ k *ᵥ x₀) := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hstep, Acl, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_neg]
    abel

/-- **Telescoped closed-loop cost** (`eq:tele`): rolling out the frozen
optimal gain from a Riccati fixed point costs exactly the drop of the
value function over the horizon. -/
theorem cost_fixedGain (hP : P.PosSemidef) (hfix : S.step P = P)
    (x₀ : ι → ℝ) (T : ℕ) :
    S.cost x₀ (fun j => -(S.gainK P *ᵥ (S.Acl P ^ j *ᵥ x₀))) T
      = quadForm P x₀ - quadForm P (S.Acl P ^ T *ᵥ x₀) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [cost, Finset.sum_range_succ, ← cost, ih, S.traj_fixedGain x₀ T,
      S.stage_closed_loop_eq hP hfix]
    have h1 : S.Acl P *ᵥ (S.Acl P ^ T *ᵥ x₀) = S.Acl P ^ (T + 1) *ᵥ x₀ := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [h1]
    ring

end FixedPoint


section Linearity

/-- Trajectories are additive in (initial state, input sequence). -/
lemma traj_add (x x' : ι → ℝ) (u u' : ℕ → κ → ℝ) : ∀ k,
    S.traj (x + x') (fun j => u j + u' j) k = S.traj x u k + S.traj x' u' k
  | 0 => rfl
  | k + 1 => by
    rw [traj_succ, traj_add x x' u u' k, traj_succ, traj_succ,
      Matrix.mulVec_add, Matrix.mulVec_add]
    abel

/-- Trajectories are homogeneous in (initial state, input sequence). -/
lemma traj_smul (c : ℝ) (x : ι → ℝ) (u : ℕ → κ → ℝ) : ∀ k,
    S.traj (c • x) (fun j => c • u j) k = c • S.traj x u k
  | 0 => rfl
  | k + 1 => by
    rw [traj_succ, traj_smul c x u k, traj_succ, Matrix.mulVec_smul,
      Matrix.mulVec_smul, smul_add]

/-- Trajectory along an affine line of decisions. -/
lemma traj_add_smul (x d : ι → ℝ) (u δ : ℕ → κ → ℝ) (t : ℝ) (k : ℕ) :
    S.traj (x + t • d) (fun j => u j + t • δ j) k
      = S.traj x u k + t • S.traj d δ k := by
  rw [S.traj_add x (t • d) u (fun j => t • δ j) k, S.traj_smul t d δ k]

/-- The cross term of the cost along a line of decisions. -/
noncomputable def costCross (x d : ι → ℝ) (u δ : ℕ → κ → ℝ) (T : ℕ) : ℝ :=
  ∑ k ∈ Finset.range T,
    ((S.traj x u k) ⬝ᵥ (S.Qs *ᵥ S.traj d δ k) + (u k) ⬝ᵥ (S.Ru *ᵥ δ k))

/-- **Quadratic expansion of the cost** along an affine line of decisions. -/
theorem cost_add_smul (x d : ι → ℝ) (u δ : ℕ → κ → ℝ) (T : ℕ) (t : ℝ) :
    S.cost (x + t • d) (fun j => u j + t • δ j) T
      = S.cost x u T + 2 * t * S.costCross x d u δ T
        + t ^ 2 * S.cost d δ T := by
  unfold cost costCross
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [S.traj_add_smul x d u δ t k]
  rw [quadForm_add_of_isHermitian S.hQs.1, quadForm_add_of_isHermitian S.hRu.1]
  rw [quadForm_smul, quadForm_smul]
  have h1 : S.traj x u k ⬝ᵥ (S.Qs *ᵥ (t • S.traj d δ k))
      = t * (S.traj x u k ⬝ᵥ (S.Qs *ᵥ S.traj d δ k)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : u k ⬝ᵥ (S.Ru *ᵥ (t • δ k))
      = t * (u k ⬝ᵥ (S.Ru *ᵥ δ k)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [h1, h2]
  ring

end Linearity


section Restart

/-- The tail of a trajectory is the trajectory of the restarted problem. -/
lemma traj_restart (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) (s : ℕ) : ∀ k,
    S.traj x₀ u (s + k) = S.traj (S.traj x₀ u s) (fun j => u (s + j)) k
  | 0 => rfl
  | k + 1 => by
    rw [show s + (k + 1) = (s + k) + 1 from rfl, traj_succ,
      traj_restart x₀ u s k, traj_succ]

/-- Splitting a cost at an intermediate time. -/
lemma cost_add (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) (s M : ℕ) :
    S.cost x₀ u (s + M)
      = S.cost x₀ u s
        + S.cost (S.traj x₀ u s) (fun j => u (s + j)) M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hsucc : S.cost (S.traj x₀ u s) (fun j => u (s + j)) (M + 1)
        = S.cost (S.traj x₀ u s) (fun j => u (s + j)) M
          + (quadForm S.Qs (S.traj (S.traj x₀ u s) (fun j => u (s + j)) M)
            + quadForm S.Ru (u (s + M))) := by
      rw [cost, Finset.sum_range_succ, ← cost]
    rw [show s + (M + 1) = (s + M) + 1 from rfl, cost, Finset.sum_range_succ,
      ← cost, ih, hsucc, S.traj_restart x₀ u s M]
    ring

/-- Every window of a cost dominates the windowed value. -/
lemma quadForm_ric_traj_le_cost (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) {s M T : ℕ}
    (h : s + M ≤ T) :
    quadForm (S.ric M) (S.traj x₀ u s) ≤ S.cost x₀ u T := by
  have h1 : quadForm (S.ric M) (S.traj x₀ u s)
      ≤ S.cost (S.traj x₀ u s) (fun j => u (s + j)) M :=
    S.quadForm_ric_le_cost _ _ M
  have h2 : S.cost x₀ u (s + M) ≤ S.cost x₀ u T := S.cost_mono x₀ u h
  have h3 := S.cost_add x₀ u s M
  have h4 : 0 ≤ S.cost x₀ u s :=
    Finset.sum_nonneg fun k _ => S.stage_nonneg _ _
  linarith

/-- A cost over `J` windows of length `M` is the sum of the windowed
restarted costs. -/
lemma cost_eq_sum_windows (x₀ : ι → ℝ) (u : ℕ → κ → ℝ) (M : ℕ) : ∀ J,
    S.cost x₀ u (J * M)
      = ∑ j ∈ Finset.range J,
          S.cost (S.traj x₀ u (j * M)) (fun r => u (j * M + r)) M
  | 0 => by simp
  | J + 1 => by
    rw [show (J + 1) * M = J * M + M from by ring, S.cost_add x₀ u (J * M) M,
      cost_eq_sum_windows x₀ u M J, Finset.sum_range_succ]

end Restart


/-! ### Cost of an arbitrary geometrically stable feedback rollout

Unlike `cost_fixedGain`, no Riccati fixed point (hence no detectability)
is needed: any feedback whose closed loop decays geometrically gives a
horizon-uniform quadratic cost bound. This is the engine behind the
C2-only uniform value bound (`lem:unibounded`). -/

section FeedbackRollout

open scoped Matrix.Norms.Operator

private lemma sum_pow_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (T : ℕ) : ∑ k ∈ Finset.range T, q ^ k ≤ (1 - q)⁻¹ := by
  have hpos : 0 < 1 - q := by linarith
  have hgs := geom_sum_eq (ne_of_lt hq1) T
  have heq : (q ^ T - 1) / (q - 1) = (1 - q ^ T) / (1 - q) := by
    rw [show (1 - q ^ T) = -(q ^ T - 1) from by ring,
      show (1 - q) = -(q - 1) from by ring, neg_div_neg_eq]
  rw [hgs, heq, div_le_iff₀ hpos, inv_mul_cancel₀ (ne_of_gt hpos)]
  nlinarith [pow_nonneg hq0 T]

/-- The trajectory driven by a fixed feedback along the closed-loop
powers is the closed-loop rollout. -/
lemma traj_feedback (K : Matrix κ ι ℝ) (x₀ : ι → ℝ) : ∀ k,
    S.traj x₀ (fun j => K *ᵥ ((S.A + S.B * K) ^ j *ᵥ x₀)) k
      = (S.A + S.B * K) ^ k *ᵥ x₀
  | 0 => by simp
  | k + 1 => by
    rw [traj_succ, traj_feedback K x₀ k,
      show (S.A + S.B * K) ^ (k + 1) *ᵥ x₀
          = (S.A + S.B * K) *ᵥ ((S.A + S.B * K) ^ k *ᵥ x₀) from by
        rw [Matrix.mulVec_mulVec, ← pow_succ'],
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec]

/-- **Feedback-rollout cost bound**: a geometrically stable closed loop
gives a horizon-uniform quadratic bound on the rollout cost. -/
theorem exists_cost_feedback_bound (K : Matrix κ ι ℝ) {c ρ : ℝ}
    (hc : 0 < c) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hpow : ∀ k : ℕ, ‖(S.A + S.B * K) ^ k‖ ≤ c * ρ ^ k) :
    ∃ cb : ℝ, 0 < cb ∧ ∀ (x₀ : ι → ℝ) (T : ℕ),
      S.cost x₀ (fun j => K *ᵥ ((S.A + S.B * K) ^ j *ᵥ x₀)) T
        ≤ cb * ‖x₀‖ ^ 2 := by
  obtain ⟨cQ, hcQ, hbQ⟩ := exists_quadForm_le S.Qs
  obtain ⟨cR, hcR, hbR⟩ := exists_quadForm_le S.Ru
  have hq0 : (0:ℝ) ≤ ρ ^ 2 := by positivity
  have hq1 : ρ ^ 2 < 1 := by nlinarith
  have hinv : 0 < (1 - ρ ^ 2)⁻¹ := by
    rw [inv_pos]
    linarith
  set cb := (cQ + cR * (‖K‖ + 1) ^ 2) * c ^ 2 * (1 - ρ ^ 2)⁻¹ + 1
    with hcb
  have hKpos : 0 < ‖K‖ + 1 := by
    have := norm_nonneg K
    linarith
  refine ⟨cb, by positivity, fun x₀ T => ?_⟩
  have hstate : ∀ k : ℕ, ‖(S.A + S.B * K) ^ k *ᵥ x₀‖ ≤ c * ρ ^ k * ‖x₀‖ := by
    intro k
    refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hpow k) (norm_nonneg _)
  have hstage : ∀ k : ℕ,
      quadForm S.Qs (S.traj x₀
          (fun j => K *ᵥ ((S.A + S.B * K) ^ j *ᵥ x₀)) k)
        + quadForm S.Ru (K *ᵥ ((S.A + S.B * K) ^ k *ᵥ x₀))
      ≤ (cQ + cR * (‖K‖ + 1) ^ 2) * c ^ 2 * (ρ ^ 2) ^ k * ‖x₀‖ ^ 2 := by
    intro k
    rw [S.traj_feedback K x₀ k]
    set v := (S.A + S.B * K) ^ k *ᵥ x₀ with hv
    set X := c * ρ ^ k * ‖x₀‖ with hX
    have hX0 : (0:ℝ) ≤ X := by
      rw [hX]
      positivity
    have h2 : ‖v‖ ≤ X := hstate k
    have hv2 : ‖v‖ ^ 2 ≤ X ^ 2 := by
      have h0 := norm_nonneg v
      nlinarith
    have h1 : quadForm S.Qs v ≤ cQ * X ^ 2 :=
      (hbQ v).trans (mul_le_mul_of_nonneg_left hv2 hcQ.le)
    have h4 : ‖K *ᵥ v‖ ≤ (‖K‖ + 1) * X := by
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      have h8 : ‖K‖ ≤ ‖K‖ + 1 := by linarith
      calc ‖K‖ * ‖v‖
          ≤ ‖K‖ * X := mul_le_mul_of_nonneg_left h2 (norm_nonneg K)
        _ ≤ (‖K‖ + 1) * X := mul_le_mul_of_nonneg_right h8 hX0
    have hu2 : ‖K *ᵥ v‖ ^ 2 ≤ ((‖K‖ + 1) * X) ^ 2 := by
      have h0 := norm_nonneg (K *ᵥ v)
      nlinarith
    have h5 : quadForm S.Ru (K *ᵥ v) ≤ cR * ((‖K‖ + 1) * X) ^ 2 :=
      (hbR _).trans (mul_le_mul_of_nonneg_left hu2 hcR.le)
    have hXsq : X ^ 2 = c ^ 2 * (ρ ^ 2) ^ k * ‖x₀‖ ^ 2 := by
      rw [hX]
      ring
    calc quadForm S.Qs v + quadForm S.Ru (K *ᵥ v)
        ≤ cQ * X ^ 2 + cR * ((‖K‖ + 1) * X) ^ 2 := by linarith
      _ = (cQ + cR * (‖K‖ + 1) ^ 2) * X ^ 2 := by ring
      _ = (cQ + cR * (‖K‖ + 1) ^ 2) * c ^ 2 * (ρ ^ 2) ^ k
          * ‖x₀‖ ^ 2 := by
          rw [hXsq]
          ring
  unfold cost
  calc ∑ k ∈ Finset.range T,
        (quadForm S.Qs (S.traj x₀
            (fun j => K *ᵥ ((S.A + S.B * K) ^ j *ᵥ x₀)) k)
          + quadForm S.Ru (K *ᵥ ((S.A + S.B * K) ^ k *ᵥ x₀)))
      ≤ ∑ k ∈ Finset.range T,
        (cQ + cR * (‖K‖ + 1) ^ 2) * c ^ 2 * (ρ ^ 2) ^ k * ‖x₀‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => hstage k
    _ = (cQ + cR * (‖K‖ + 1) ^ 2) * c ^ 2 * ‖x₀‖ ^ 2
        * ∑ k ∈ Finset.range T, (ρ ^ 2) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (cQ + cR * (‖K‖ + 1) ^ 2) * c ^ 2 * ‖x₀‖ ^ 2
        * (1 - ρ ^ 2)⁻¹ := by
        refine mul_le_mul_of_nonneg_left
          (sum_pow_le_inv_one_sub hq0 hq1 T) ?_
        positivity
    _ ≤ cb * ‖x₀‖ ^ 2 := by
        rw [hcb]
        nlinarith [sq_nonneg ‖x₀‖]

end FeedbackRollout

end LQSystem

end LinearSystems

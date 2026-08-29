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

end LQSystem

end LinearSystems

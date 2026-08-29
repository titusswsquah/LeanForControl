import LeanForControl.Estimation.Basic
import LeanForControl.LinearSystems.LQ
import LeanForControl.LinearSystems.SymmPinv
import LeanForControl.LinearSystems.Detectability
import Architect

/-!
# The full-information estimator in reduced coordinates

The estimation problem of `costogo.tex` §2, in the reduced block coordinates
fixed by the scope note (stabilizability canonical form, block-diagonal
prior): the error system

`e₁⁺ = A₁ e₁ + A₁₂ e₂ - G₁ ω`, `e₂⁺ = A₂ e₂`, `ν = C₁ e₁ + C₂ e₂`

with `(A₁, G₁)` stabilizable and `A₂` antistable, prior
`Σ₀ = diag(Σ₁, Σ₂) ⪰ 0`, and penalties `Qi = Q⁻¹ ≻ 0`, `Ri = R⁻¹ ≻ 0`.

* `Estimation.FIESystem` bundles the data and the canonical-form
  hypotheses.
* `FIESystem.lq` is the tail linear-quadratic problem over the sum index
  `Fin n₁ ⊕ Fin n₂` (state `e`, input `ω`, dynamics through
  `LinearSystems.LQSystem`).
* `FIESystem.C1`/`C2`/`C3w` are the standing conditions of the papers; in
  these coordinates C2 is exactly `Σ₂ ≻ 0` (`lem:Sigma2-pd` is absorbed
  into the coordinates).
* `FIESystem.fieCost` is the horizon-`T` objective `𝕡_Te` (with the prior
  as a pseudoinverse penalty plus support constraints on **both** blocks, so
  the problem is well-posed for every PSD prior and C2-necessity is
  statable); `FIESystem.Feasible` is the support constraint.

Costs carry no `½` (they are twice the paper's values).
-/

namespace Estimation

open Matrix LinearSystems

variable {n₁ n₂ m p : ℕ}

/-- The reduced-coordinate estimation system of the `costogo` papers: the
stabilizability canonical form with block-diagonal PSD prior, penalties
`Qi = Q⁻¹`, `Ri = R⁻¹`, a stabilizable `(A₁, G₁)` block and an antistable
`A₂` block. -/
structure FIESystem (n₁ n₂ m p : ℕ) where
  /-- Stabilizable-block state matrix. -/
  A₁ : Matrix (Fin n₁) (Fin n₁) ℝ
  /-- Cross-coupling from the antistable block. -/
  A₁₂ : Matrix (Fin n₁) (Fin n₂) ℝ
  /-- Antistable (uncontrollable) block state matrix. -/
  A₂ : Matrix (Fin n₂) (Fin n₂) ℝ
  /-- Noise input matrix (the antistable block is unforced). -/
  G₁ : Matrix (Fin n₁) (Fin m) ℝ
  /-- Output matrix, stabilizable block. -/
  C₁ : Matrix (Fin p) (Fin n₁) ℝ
  /-- Output matrix, antistable block. -/
  C₂ : Matrix (Fin p) (Fin n₂) ℝ
  /-- Process-noise penalty `Q⁻¹`. -/
  Qi : Matrix (Fin m) (Fin m) ℝ
  /-- Measurement-noise penalty `R⁻¹`. -/
  Ri : Matrix (Fin p) (Fin p) ℝ
  /-- Prior covariance, stabilizable block. -/
  Sig₁ : Matrix (Fin n₁) (Fin n₁) ℝ
  /-- Prior covariance, antistable block. -/
  Sig₂ : Matrix (Fin n₂) (Fin n₂) ℝ
  /-- `Q ≻ 0`. -/
  hQi : Qi.PosDef
  /-- `R ≻ 0`. -/
  hRi : Ri.PosDef
  /-- `Σ₁ ⪰ 0`. -/
  hSig₁ : Sig₁.PosSemidef
  /-- `Σ₂ ⪰ 0`. -/
  hSig₂ : Sig₂.PosSemidef
  /-- `(A₁, G₁)` is stabilizable (canonical-form hypothesis). -/
  hStab : IsStabilizable (complexify A₁) (complexify G₁)
  /-- `A₂` is antistable: every eigenvalue on or outside the unit circle
  (canonical-form hypothesis). -/
  hAnti : ∀ μ ∈ spectrum ℂ (complexify A₂), 1 ≤ ‖μ‖

namespace FIESystem

variable (Sys : FIESystem n₁ n₂ m p)

/-! ### Block vectors -/

/-- First (stabilizable) block of a state vector. -/
def blk₁ (e : Fin n₁ ⊕ Fin n₂ → ℝ) : Fin n₁ → ℝ := e ∘ Sum.inl

/-- Second (antistable) block of a state vector. -/
def blk₂ (e : Fin n₁ ⊕ Fin n₂ → ℝ) : Fin n₂ → ℝ := e ∘ Sum.inr

@[simp] lemma blk₁_apply (e : Fin n₁ ⊕ Fin n₂ → ℝ) (i : Fin n₁) :
    blk₁ e i = e (Sum.inl i) := rfl

@[simp] lemma blk₂_apply (e : Fin n₁ ⊕ Fin n₂ → ℝ) (i : Fin n₂) :
    blk₂ e i = e (Sum.inr i) := rfl

@[simp] lemma blk₁_add (e f : Fin n₁ ⊕ Fin n₂ → ℝ) :
    blk₁ (e + f) = blk₁ e + blk₁ f := rfl

@[simp] lemma blk₂_add (e f : Fin n₁ ⊕ Fin n₂ → ℝ) :
    blk₂ (e + f) = blk₂ e + blk₂ f := rfl

@[simp] lemma blk₁_sub (e f : Fin n₁ ⊕ Fin n₂ → ℝ) :
    blk₁ (e - f) = blk₁ e - blk₁ f := rfl

@[simp] lemma blk₂_sub (e f : Fin n₁ ⊕ Fin n₂ → ℝ) :
    blk₂ (e - f) = blk₂ e - blk₂ f := rfl

@[simp] lemma blk₁_smul (c : ℝ) (e : Fin n₁ ⊕ Fin n₂ → ℝ) :
    blk₁ (c • e) = c • blk₁ e := rfl

@[simp] lemma blk₂_smul (c : ℝ) (e : Fin n₁ ⊕ Fin n₂ → ℝ) :
    blk₂ (c • e) = c • blk₂ e := rfl

@[simp] lemma blk₁_zero : blk₁ (0 : Fin n₁ ⊕ Fin n₂ → ℝ) = 0 := rfl

@[simp] lemma blk₂_zero : blk₂ (0 : Fin n₁ ⊕ Fin n₂ → ℝ) = 0 := rfl

@[simp] lemma blk₁_sumElim (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) :
    blk₁ (Sum.elim x y) = x := rfl

@[simp] lemma blk₂_sumElim (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) :
    blk₂ (Sum.elim x y) = y := rfl

lemma sumElim_blk (e : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sum.elim (blk₁ e) (blk₂ e) = e := by
  funext i
  cases i <;> rfl

/-- A dot product over the sum index splits into blocks. -/
lemma dotProduct_blocks (e f : Fin n₁ ⊕ Fin n₂ → ℝ) :
    e ⬝ᵥ f = blk₁ e ⬝ᵥ blk₁ f + blk₂ e ⬝ᵥ blk₂ f := by
  simp [dotProduct, Fintype.sum_sum_type, blk₁, blk₂]

/-! ### Full-system matrices and the tail LQ problem -/

/-- The full error-state matrix `[[A₁, A₁₂], [0, A₂]]`. -/
def fullA : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ :=
  Matrix.fromBlocks Sys.A₁ Sys.A₁₂ 0 Sys.A₂

/-- The full noise-input matrix `col(G₁, 0)`. -/
def fullG : Matrix (Fin n₁ ⊕ Fin n₂) (Fin m) ℝ :=
  Matrix.fromRows Sys.G₁ 0

/-- The full output matrix `[C₁ C₂]`. -/
def fullC : Matrix (Fin p) (Fin n₁ ⊕ Fin n₂) ℝ :=
  Matrix.fromCols Sys.C₁ Sys.C₂

/-- The tail linear-quadratic problem behind `𝕡_Te`: state `e`, input `ω`,
dynamics `e⁺ = A e - G ω`, stage cost `‖Ce‖²_{Ri} + ‖ω‖²_{Qi}`. -/
noncomputable def lq : LQSystem (Fin n₁ ⊕ Fin n₂) (Fin m) where
  A := Sys.fullA
  B := -Sys.fullG
  Qs := Sys.fullCᵀ * Sys.Ri * Sys.fullC
  Ru := Sys.Qi
  hQs := by
    have h := Sys.hRi.posSemidef.mul_mul_conjTranspose_same Sys.fullCᵀ
    rwa [show (Sys.fullCᵀ)ᴴ = Sys.fullC from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]] at h
  hRu := Sys.hQi

/-- The stage state-cost is the `Ri`-weighted squared output. -/
lemma quadForm_Qs (e : Fin n₁ ⊕ Fin n₂ → ℝ) :
    quadForm Sys.lq.Qs e = quadForm Sys.Ri (Sys.fullC *ᵥ e) := by
  rw [quadForm_mulVec]
  rfl

/-! ### The standing conditions -/

/-- **C1**: the full pair `(A, C)` is detectable. -/
def C1 : Prop :=
  IsDetectable (complexify Sys.fullA) (complexify Sys.fullC)

/-- **C2**: the antistable prior block is positive definite. In reduced
coordinates this is exactly the paper's kernel condition
`ker Σ₀ ∩ 𝒳_{u,uc} = 0` (`lem:Sigma2-pd` is absorbed). -/
def C2 : Prop := Sys.Sig₂.PosDef

/-- **C3w**: no eigenvalue of `A₂` on the unit circle — with antistability,
every eigenvalue strictly outside. -/
def C3w : Prop := ∀ μ ∈ spectrum ℂ (complexify Sys.A₂), 1 < ‖μ‖

/-! ### The full-information objective -/

/-- The prior penalty
`‖e₀-a‖²_{Σ₁†} + ‖e₀-a‖²_{Σ₂†}` (blockwise pseudoinverse weights). -/
noncomputable def priorPenalty (a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) : ℝ :=
  quadForm (symmPinv Sys.hSig₁.1) (blk₁ (e₀ - a))
    + quadForm (symmPinv Sys.hSig₂.1) (blk₂ (e₀ - a))

/-- The support constraint: the initial-error deviation from the prior
mismatch lies in the range of the prior, blockwise. -/
def Feasible (a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) : Prop :=
  (∃ z, blk₁ (e₀ - a) = Sys.Sig₁ *ᵥ z) ∧
    (∃ w, blk₂ (e₀ - a) = Sys.Sig₂ *ᵥ w)

/-- The horizon-`T` full-information objective `𝕡_Te`: prior penalty plus
tail cost, as a function of the initial-error decision `e₀` and the noise
sequence `ω`. -/
noncomputable def fieCost (a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) (ω : ℕ → Fin m → ℝ)
    (T : ℕ) : ℝ :=
  Sys.priorPenalty a e₀ + Sys.lq.cost e₀ ω T

lemma priorPenalty_nonneg (a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) :
    0 ≤ Sys.priorPenalty a e₀ :=
  add_nonneg (Sys.hSig₁.symmPinv.quadForm_nonneg _)
    (Sys.hSig₂.symmPinv.quadForm_nonneg _)

lemma fieCost_nonneg (a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) (ω : ℕ → Fin m → ℝ)
    (T : ℕ) : 0 ≤ Sys.fieCost a e₀ ω T := by
  have h1 := Sys.priorPenalty_nonneg a e₀
  have h2 : 0 ≤ Sys.lq.cost e₀ ω T :=
    Finset.sum_nonneg fun k _ => Sys.lq.stage_nonneg _ _
  unfold fieCost
  linarith

/-- Taking the prior mismatch itself with zero noise is always feasible;
`a` itself is a feasible initial decision. -/
lemma feasible_self (a : Fin n₁ ⊕ Fin n₂ → ℝ) : Sys.Feasible a a := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> simp

end FIESystem

end Estimation

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

/-! ### The outer problem: optimal initial error

The inner (noise) minimization is solved exactly by the LQ layer, leaving
the outer problem `min φ_T(e₀) = priorPenalty a e₀ + e₀'(ric T)e₀` over the
feasible affine set. We characterize its solutions variationally
(`IsStationary`), construct one through the parameterization
`e₀ = a + J v`, `J = diag(Σ₁, Σ₂)` (which turns the constrained problem into
an unconstrained bounded-below quadratic), and prove the exact outer gap
formula. None of this requires C2. -/

/-- The reduced outer objective `φ_T`. -/
noncomputable def outerObj (a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) : ℝ :=
  Sys.priorPenalty a e₀ + quadForm (Sys.lq.ric T) e₀

/-- The block-diagonal prior matrix `J = diag(Σ₁, Σ₂)`, used to
parameterize the feasible set. -/
def Jmat : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ :=
  Matrix.fromBlocks Sys.Sig₁ 0 0 Sys.Sig₂

lemma Jmat_mulVec (v : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.Jmat *ᵥ v
      = Sum.elim (Sys.Sig₁ *ᵥ blk₁ v) (Sys.Sig₂ *ᵥ blk₂ v) := by
  rw [Jmat, Matrix.fromBlocks_mulVec]
  simp [blk₁, blk₂]

/-- Feasibility is surjectively parameterized by `e₀ = a + J v`. -/
lemma feasible_iff (a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.Feasible a e₀ ↔ ∃ v, e₀ - a = Sys.Jmat *ᵥ v := by
  constructor
  · rintro ⟨⟨z, hz⟩, ⟨w, hw⟩⟩
    refine ⟨Sum.elim z w, ?_⟩
    rw [Jmat_mulVec]
    rw [← sumElim_blk (e₀ - a), hz, hw]
    simp
  · rintro ⟨v, hv⟩
    constructor
    · exact ⟨blk₁ v, by rw [hv, Sys.Jmat_mulVec]; simp⟩
    · exact ⟨blk₂ v, by rw [hv, Sys.Jmat_mulVec]; simp⟩

/-- A feasible **direction**: a difference of feasible points. -/
def FeasibleDir (d : Fin n₁ ⊕ Fin n₂ → ℝ) : Prop :=
  ∃ v, d = Sys.Jmat *ᵥ v

lemma feasibleDir_sub {a e₀ e₀' : Fin n₁ ⊕ Fin n₂ → ℝ}
    (h : Sys.Feasible a e₀) (h' : Sys.Feasible a e₀') :
    Sys.FeasibleDir (e₀ - e₀') := by
  rw [feasible_iff] at h h'
  obtain ⟨v, hv⟩ := h
  obtain ⟨v', hv'⟩ := h'
  refine ⟨v - v', ?_⟩
  rw [Matrix.mulVec_sub, ← hv, ← hv']
  abel

/-- First-order (variational) optimality of an initial-error decision for
the outer problem: feasibility plus vanishing directional derivative along
every feasible direction. -/
def IsStationary (a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) : Prop :=
  Sys.Feasible a e₀ ∧ ∀ d : Fin n₁ ⊕ Fin n₂ → ℝ, Sys.FeasibleDir d →
    (symmPinv Sys.hSig₁.1 *ᵥ blk₁ (e₀ - a)) ⬝ᵥ blk₁ d
      + (symmPinv Sys.hSig₂.1 *ᵥ blk₂ (e₀ - a)) ⬝ᵥ blk₂ d
      + (Sys.lq.ric T *ᵥ e₀) ⬝ᵥ d = 0

/-- `Mᵀ = M` for a real symmetric matrix (transposed form of
`IsHermitian`). -/
lemma _root_.Matrix.IsHermitian.transpose_eq_self {k : ℕ}
    {M : Matrix (Fin k) (Fin k) ℝ} (hM : M.IsHermitian) : Mᵀ = M := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact hM

lemma ric_transpose_eq (T : ℕ) : (Sys.lq.ric T)ᵀ = Sys.lq.ric T := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact Sys.lq.ric_isHermitian T

/-- The prior energy of an image point: `(Wz)'W†(Wz) = z'Wz`. -/
lemma quadForm_symmPinv_mulVec {k : ℕ} {W : Matrix (Fin k) (Fin k) ℝ}
    (hW : W.PosSemidef) (z : Fin k → ℝ) :
    quadForm (symmPinv hW.1) (W *ᵥ z) = quadForm W z := by
  rw [quadForm_mulVec, hW.1.transpose_eq_self,
    self_mul_symmPinv_mul_self hW.1]

lemma Jmat_isHermitian : Sys.Jmat.IsHermitian := by
  unfold Jmat Matrix.IsHermitian
  rw [Matrix.fromBlocks_conjTranspose]
  rw [Sys.hSig₁.1, Sys.hSig₂.1]
  simp

lemma Jmat_transpose_eq : Sys.Jmatᵀ = Sys.Jmat := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact Sys.Jmat_isHermitian

/-- The quadratic form of `J` splits blockwise. -/
lemma quadForm_Jmat (v : Fin n₁ ⊕ Fin n₂ → ℝ) :
    quadForm Sys.Jmat v
      = quadForm Sys.Sig₁ (blk₁ v) + quadForm Sys.Sig₂ (blk₂ v) := by
  rw [quadForm, Sys.Jmat_mulVec, dotProduct_blocks]
  simp [quadForm]

lemma Jmat_posSemidef : Sys.Jmat.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg Sys.Jmat_isHermitian
    fun v => ?_
  have h : 0 ≤ quadForm Sys.Jmat v := by
    rw [Sys.quadForm_Jmat]
    exact add_nonneg (Sys.hSig₁.quadForm_nonneg _) (Sys.hSig₂.quadForm_nonneg _)
  simpa [quadForm] using h

/-- **Outer gap formula** (`eq:quad-gap`, initial-error part): at a
stationary point, every feasible competitor pays exactly the deviation
energy on top. -/
theorem outerObj_gap {a e₀s : Fin n₁ ⊕ Fin n₂ → ℝ} {T : ℕ}
    (hstat : Sys.IsStationary a e₀s T) {e₀ : Fin n₁ ⊕ Fin n₂ → ℝ}
    (hfeas : Sys.Feasible a e₀) :
    Sys.outerObj a e₀ T = Sys.outerObj a e₀s T
      + (quadForm (symmPinv Sys.hSig₁.1) (blk₁ (e₀ - e₀s))
        + quadForm (symmPinv Sys.hSig₂.1) (blk₂ (e₀ - e₀s))
        + quadForm (Sys.lq.ric T) (e₀ - e₀s)) := by
  obtain ⟨hfs, hvar⟩ := hstat
  have hdir : Sys.FeasibleDir (e₀ - e₀s) := Sys.feasibleDir_sub hfeas hfs
  have hvd := hvar (e₀ - e₀s) hdir
  have hsplit : e₀ - a = (e₀s - a) + (e₀ - e₀s) := by abel
  have hsplit' : e₀ = e₀s + (e₀ - e₀s) := by abel
  -- expand the three quadratic forms
  have hq1 : quadForm (symmPinv Sys.hSig₁.1) (blk₁ (e₀ - a))
      = quadForm (symmPinv Sys.hSig₁.1) (blk₁ (e₀s - a))
        + 2 * (blk₁ (e₀s - a) ⬝ᵥ (symmPinv Sys.hSig₁.1 *ᵥ blk₁ (e₀ - e₀s)))
        + quadForm (symmPinv Sys.hSig₁.1) (blk₁ (e₀ - e₀s)) := by
    rw [hsplit, blk₁_add,
      quadForm_add_of_isHermitian (symmPinv_isHermitian Sys.hSig₁.1)]
  have hq2 : quadForm (symmPinv Sys.hSig₂.1) (blk₂ (e₀ - a))
      = quadForm (symmPinv Sys.hSig₂.1) (blk₂ (e₀s - a))
        + 2 * (blk₂ (e₀s - a) ⬝ᵥ (symmPinv Sys.hSig₂.1 *ᵥ blk₂ (e₀ - e₀s)))
        + quadForm (symmPinv Sys.hSig₂.1) (blk₂ (e₀ - e₀s)) := by
    rw [hsplit, blk₂_add,
      quadForm_add_of_isHermitian (symmPinv_isHermitian Sys.hSig₂.1)]
  have hq3 : quadForm (Sys.lq.ric T) e₀
      = quadForm (Sys.lq.ric T) e₀s
        + 2 * (e₀s ⬝ᵥ (Sys.lq.ric T *ᵥ (e₀ - e₀s)))
        + quadForm (Sys.lq.ric T) (e₀ - e₀s) := by
    conv_lhs => rw [hsplit']
    rw [quadForm_add_of_isHermitian (Sys.lq.ric_isHermitian T)]
  -- convert the cross terms to the stationarity form
  have hc1 : blk₁ (e₀s - a) ⬝ᵥ (symmPinv Sys.hSig₁.1 *ᵥ blk₁ (e₀ - e₀s))
      = (symmPinv Sys.hSig₁.1 *ᵥ blk₁ (e₀s - a)) ⬝ᵥ blk₁ (e₀ - e₀s) := by
    rw [dotProduct_mulVec_eq,
      (symmPinv_isHermitian Sys.hSig₁.1).transpose_eq_self]
  have hc2 : blk₂ (e₀s - a) ⬝ᵥ (symmPinv Sys.hSig₂.1 *ᵥ blk₂ (e₀ - e₀s))
      = (symmPinv Sys.hSig₂.1 *ᵥ blk₂ (e₀s - a)) ⬝ᵥ blk₂ (e₀ - e₀s) := by
    rw [dotProduct_mulVec_eq,
      (symmPinv_isHermitian Sys.hSig₂.1).transpose_eq_self]
  have hc3 : e₀s ⬝ᵥ (Sys.lq.ric T *ᵥ (e₀ - e₀s))
      = (Sys.lq.ric T *ᵥ e₀s) ⬝ᵥ (e₀ - e₀s) := by
    rw [dotProduct_mulVec_eq, Sys.ric_transpose_eq]
  unfold outerObj priorPenalty
  rw [hq1, hq2, hq3, hc1, hc2, hc3]
  linarith [hvd]

/-- **Existence of a stationary point** (no C2 required): the objective is
a bounded-below quadratic in the parameterization `e₀ = a + J v`. -/
theorem exists_isStationary (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    ∃ e₀, Sys.IsStationary a e₀ T := by
  classical
  set L := Sys.Jmat + Sys.Jmatᵀ * Sys.lq.ric T * Sys.Jmat with hL
  set sv : Fin n₁ ⊕ Fin n₂ → ℝ
    := Sys.Jmatᵀ *ᵥ (Sys.lq.ric T *ᵥ a) with hsv
  have hLpsd : L.PosSemidef := by
    refine Sys.Jmat_posSemidef.add ?_
    have h := (Sys.lq.ric_posSemidef T).mul_mul_conjTranspose_same Sys.Jmatᵀ
    rwa [show (Sys.Jmatᵀ)ᴴ = Sys.Jmat from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]] at h
  -- the objective along the parameterization
  have hψ : ∀ v, Sys.outerObj a (a + Sys.Jmat *ᵥ v) T
      = quadForm L v + 2 * (sv ⬝ᵥ v) + quadForm (Sys.lq.ric T) a := by
    intro v
    have hd1 : blk₁ ((a + Sys.Jmat *ᵥ v) - a) = Sys.Sig₁ *ᵥ blk₁ v := by
      rw [add_sub_cancel_left, Sys.Jmat_mulVec]
      simp
    have hd2 : blk₂ ((a + Sys.Jmat *ᵥ v) - a) = Sys.Sig₂ *ᵥ blk₂ v := by
      rw [add_sub_cancel_left, Sys.Jmat_mulVec]
      simp
    have hprior : Sys.priorPenalty a (a + Sys.Jmat *ᵥ v)
        = quadForm Sys.Sig₁ (blk₁ v) + quadForm Sys.Sig₂ (blk₂ v) := by
      unfold priorPenalty
      rw [hd1, hd2, quadForm_symmPinv_mulVec Sys.hSig₁,
        quadForm_symmPinv_mulVec Sys.hSig₂]
    have hric : quadForm (Sys.lq.ric T) (a + Sys.Jmat *ᵥ v)
        = quadForm (Sys.lq.ric T) a + 2 * (sv ⬝ᵥ v)
          + quadForm (Sys.Jmatᵀ * Sys.lq.ric T * Sys.Jmat) v := by
      rw [quadForm_add_of_isHermitian (Sys.lq.ric_isHermitian T),
        quadForm_mulVec]
      congr 2
      rw [hsv, Matrix.mulVec_mulVec, dotProduct_mulVec_eq,
        Matrix.transpose_mul, Sys.ric_transpose_eq, ← Matrix.mulVec_mulVec]
    unfold outerObj
    rw [hprior, hric, hL, quadForm_add_matrix, ← Sys.quadForm_Jmat]
    ring
  -- boundedness below gives solvability of the stationarity system
  have hbdd : ∀ v, 2 * ((-sv) ⬝ᵥ v) ≤ quadForm L v
      + quadForm (Sys.lq.ric T) a := by
    intro v
    have h1 : 0 ≤ Sys.outerObj a (a + Sys.Jmat *ᵥ v) T := by
      unfold outerObj
      exact add_nonneg (Sys.priorPenalty_nonneg _ _)
        ((Sys.lq.ric_posSemidef T).quadForm_nonneg _)
    rw [hψ v] at h1
    have h2 : (-sv) ⬝ᵥ v = -(sv ⬝ᵥ v) := by simp
    rw [h2]
    linarith
  obtain ⟨v, hv⟩ := hLpsd.exists_mulVec_eq hbdd
  refine ⟨a + Sys.Jmat *ᵥ v, ⟨?_, ?_⟩⟩
  · rw [feasible_iff]
    exact ⟨v, by rw [add_sub_cancel_left]⟩
  · rintro d ⟨w, hw⟩
    have hd1 : blk₁ ((a + Sys.Jmat *ᵥ v) - a) = Sys.Sig₁ *ᵥ blk₁ v := by
      rw [add_sub_cancel_left, Sys.Jmat_mulVec]
      simp
    have hd2 : blk₂ ((a + Sys.Jmat *ᵥ v) - a) = Sys.Sig₂ *ᵥ blk₂ v := by
      rw [add_sub_cancel_left, Sys.Jmat_mulVec]
      simp
    have hw1 : blk₁ d = Sys.Sig₁ *ᵥ blk₁ w := by
      rw [hw, Sys.Jmat_mulVec]
      simp
    have hw2 : blk₂ d = Sys.Sig₂ *ᵥ blk₂ w := by
      rw [hw, Sys.Jmat_mulVec]
      simp
    -- first two terms collapse to `(J v) ⬝ᵥ w`
    have ht1 : (symmPinv Sys.hSig₁.1 *ᵥ blk₁ ((a + Sys.Jmat *ᵥ v) - a))
          ⬝ᵥ blk₁ d
        = (Sys.Sig₁ *ᵥ blk₁ v) ⬝ᵥ blk₁ w := by
      rw [hd1, hw1, dotProduct_mulVec_eq, Sys.hSig₁.1.transpose_eq_self,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        self_mul_symmPinv_mul_self Sys.hSig₁.1]
    have ht2 : (symmPinv Sys.hSig₂.1 *ᵥ blk₂ ((a + Sys.Jmat *ᵥ v) - a))
          ⬝ᵥ blk₂ d
        = (Sys.Sig₂ *ᵥ blk₂ v) ⬝ᵥ blk₂ w := by
      rw [hd2, hw2, dotProduct_mulVec_eq, Sys.hSig₂.1.transpose_eq_self,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        self_mul_symmPinv_mul_self Sys.hSig₂.1]
    have hJvw : (Sys.Jmat *ᵥ v) ⬝ᵥ w
        = (Sys.Sig₁ *ᵥ blk₁ v) ⬝ᵥ blk₁ w
          + (Sys.Sig₂ *ᵥ blk₂ v) ⬝ᵥ blk₂ w := by
      rw [Sys.Jmat_mulVec, dotProduct_blocks]
      simp
    -- third term: expand along `d = J w`
    have htA : (Sys.lq.ric T *ᵥ a) ⬝ᵥ (Sys.Jmat *ᵥ w) = sv ⬝ᵥ w := by
      rw [dotProduct_mulVec_eq, ← hsv]
    have hMsymm : (Sys.Jmatᵀ * Sys.lq.ric T * Sys.Jmat)ᵀ
        = Sys.Jmatᵀ * Sys.lq.ric T * Sys.Jmat := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Sys.ric_transpose_eq, ← Matrix.mul_assoc]
    have htB : (Sys.lq.ric T *ᵥ (Sys.Jmat *ᵥ v)) ⬝ᵥ (Sys.Jmat *ᵥ w)
        = ((Sys.Jmatᵀ * Sys.lq.ric T * Sys.Jmat) *ᵥ v) ⬝ᵥ w := by
      rw [Matrix.mulVec_mulVec, mulVec_dotProduct_eq, Matrix.mulVec_mulVec,
        Matrix.transpose_mul, Sys.ric_transpose_eq, dotProduct_mulVec_eq,
        hMsymm]
    rw [ht1, ht2, hw, Matrix.mulVec_add, add_dotProduct, htA, htB, ← hJvw]
    have hfin : (Sys.Jmat *ᵥ v) ⬝ᵥ w
          + ((Sys.Jmatᵀ * Sys.lq.ric T * Sys.Jmat) *ᵥ v) ⬝ᵥ w
        = (L *ᵥ v) ⬝ᵥ w := by
      rw [hL, Matrix.add_mulVec, add_dotProduct]
    have hneg : (L *ᵥ v) ⬝ᵥ w = -(sv ⬝ᵥ w) := by
      rw [hv, neg_dotProduct]
    linarith [hfin, hneg]

/-- **Uniqueness** of the stationary point (hence of the optimal initial
error), for every PSD prior. -/
theorem isStationary_unique {a e₀ e₀' : Fin n₁ ⊕ Fin n₂ → ℝ} {T : ℕ}
    (h : Sys.IsStationary a e₀ T) (h' : Sys.IsStationary a e₀' T) :
    e₀ = e₀' := by
  have hg := Sys.outerObj_gap h h'.1
  have hg' := Sys.outerObj_gap h' h.1
  set d := e₀' - e₀ with hd
  have hd' : e₀ - e₀' = -d := by rw [hd]; abel
  have hgap : quadForm (symmPinv Sys.hSig₁.1) (blk₁ d)
      + quadForm (symmPinv Sys.hSig₂.1) (blk₂ d)
      + quadForm (Sys.lq.ric T) d = 0 := by
    have e1 : quadForm (symmPinv Sys.hSig₁.1) (blk₁ (e₀ - e₀'))
        = quadForm (symmPinv Sys.hSig₁.1) (blk₁ d) := by
      rw [hd']
      have : blk₁ (-d) = -(blk₁ d) := rfl
      rw [this, quadForm_neg]
    have e2 : quadForm (symmPinv Sys.hSig₂.1) (blk₂ (e₀ - e₀'))
        = quadForm (symmPinv Sys.hSig₂.1) (blk₂ d) := by
      rw [hd']
      have : blk₂ (-d) = -(blk₂ d) := rfl
      rw [this, quadForm_neg]
    have e3 : quadForm (Sys.lq.ric T) (e₀ - e₀') = quadForm (Sys.lq.ric T) d := by
      rw [hd', quadForm_neg]
    rw [e1, e2, e3] at hg'
    linarith
  -- each summand is nonnegative, hence zero
  have h1 : 0 ≤ quadForm (symmPinv Sys.hSig₁.1) (blk₁ d) :=
    Sys.hSig₁.symmPinv.quadForm_nonneg _
  have h2 : 0 ≤ quadForm (symmPinv Sys.hSig₂.1) (blk₂ d) :=
    Sys.hSig₂.symmPinv.quadForm_nonneg _
  have h3 : 0 ≤ quadForm (Sys.lq.ric T) d :=
    (Sys.lq.ric_posSemidef T).quadForm_nonneg _
  have hz1 : quadForm (symmPinv Sys.hSig₁.1) (blk₁ d) = 0 := by linarith
  have hz2 : quadForm (symmPinv Sys.hSig₂.1) (blk₂ d) = 0 := by linarith
  -- the deviation is a feasible direction, so vanishing prior energy kills it
  obtain ⟨w, hwd⟩ := Sys.feasibleDir_sub h'.1 h.1
  rw [← hd] at hwd
  have hw1 : blk₁ d = Sys.Sig₁ *ᵥ blk₁ w := by
    rw [hwd, Sys.Jmat_mulVec]
    simp
  have hw2 : blk₂ d = Sys.Sig₂ *ᵥ blk₂ w := by
    rw [hwd, Sys.Jmat_mulVec]
    simp
  have hb1 : blk₁ d = 0 := by
    rw [hw1] at hz1 ⊢
    rw [quadForm_symmPinv_mulVec Sys.hSig₁] at hz1
    have := Sys.hSig₁.mulVec_eq_zero_of_quadForm_eq_zero hz1
    rw [this]
  have hb2 : blk₂ d = 0 := by
    rw [hw2] at hz2 ⊢
    rw [quadForm_symmPinv_mulVec Sys.hSig₂] at hz2
    have := Sys.hSig₂.mulVec_eq_zero_of_quadForm_eq_zero hz2
    rw [this]
  have hdz : d = 0 := by
    rw [← sumElim_blk d, hb1, hb2]
    funext i
    cases i <;> rfl
  have := hdz
  rw [hd] at this
  have : e₀' = e₀ := by
    have h0 := this
    rwa [sub_eq_zero] at h0
  exact this.symm

/-! ### The optimal initial error, value, and stability notions -/

/-- The optimal initial error `e*(0|T)` of the horizon-`T` problem (the
unique stationary point of the outer objective). -/
noncomputable def optInit (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Fin n₁ ⊕ Fin n₂ → ℝ :=
  Classical.choose (Sys.exists_isStationary a T)

lemma optInit_isStationary (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.IsStationary a (Sys.optInit a T) T :=
  Classical.choose_spec (Sys.exists_isStationary a T)

lemma optInit_feasible (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.Feasible a (Sys.optInit a T) :=
  (Sys.optInit_isStationary a T).1

/-- The optimal value `V_T⁰` of the horizon-`T` full-information problem. -/
noncomputable def value (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) : ℝ :=
  Sys.outerObj a (Sys.optInit a T) T

lemma value_nonneg (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    0 ≤ Sys.value a T :=
  add_nonneg (Sys.priorPenalty_nonneg _ _)
    ((Sys.lq.ric_posSemidef T).quadForm_nonneg _)

/-- **Joint optimality**: the value lower-bounds the cost of every feasible
decision pair. -/
theorem value_le_fieCost {a e₀ : Fin n₁ ⊕ Fin n₂ → ℝ}
    (hfeas : Sys.Feasible a e₀) (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    Sys.value a T ≤ Sys.fieCost a e₀ ω T := by
  have h1 : Sys.outerObj a e₀ T ≤ Sys.fieCost a e₀ ω T := by
    unfold outerObj fieCost
    have := Sys.lq.quadForm_ric_le_cost e₀ ω T
    linarith
  have h2 : Sys.value a T ≤ Sys.outerObj a e₀ T := by
    rw [Sys.outerObj_gap (Sys.optInit_isStationary a T) hfeas]
    have h3 : 0 ≤ quadForm (symmPinv Sys.hSig₁.1) (blk₁ (e₀ - Sys.optInit a T))
        + quadForm (symmPinv Sys.hSig₂.1) (blk₂ (e₀ - Sys.optInit a T))
        + quadForm (Sys.lq.ric T) (e₀ - Sys.optInit a T) := by
      have g1 := Sys.hSig₁.symmPinv.quadForm_nonneg
        (blk₁ (e₀ - Sys.optInit a T))
      have g2 := Sys.hSig₂.symmPinv.quadForm_nonneg
        (blk₂ (e₀ - Sys.optInit a T))
      have g3 := (Sys.lq.ric_posSemidef T).quadForm_nonneg
        (e₀ - Sys.optInit a T)
      linarith
    unfold value
    linarith
  linarith

/-- The value is attained by the optimal initial error and the optimal
noise sequence. -/
theorem fieCost_optCtrl (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.fieCost a (Sys.optInit a T)
      (Sys.lq.optCtrl (Sys.optInit a T) T) T = Sys.value a T := by
  unfold fieCost value outerObj
  rw [Sys.lq.cost_optCtrl]

/-- The optimal terminal error `e*(T|T)`: the endpoint of the optimal
trajectory of the horizon-`T` problem. -/
noncomputable def optTerm (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Fin n₁ ⊕ Fin n₂ → ℝ :=
  Sys.lq.optTraj (Sys.optInit a T) T T

/-- **Global asymptotic stability** of the full-information estimator
(`def:gas`): the optimal terminal error dies out, linearly in the prior
mismatch, uniformly over mismatches. -/
def IsGAS : Prop :=
  ∃ σ : ℕ → ℝ, Filter.Tendsto σ Filter.atTop (nhds 0) ∧
    ∀ (T : ℕ) (a : Fin n₁ ⊕ Fin n₂ → ℝ), ‖Sys.optTerm a T‖ ≤ σ T * ‖a‖

/-- **Global exponential stability** of the full-information estimator
(`def:ges-fi`). -/
def IsGES : Prop :=
  ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧
    ∀ (T : ℕ) (a : Fin n₁ ⊕ Fin n₂ → ℝ),
      ‖Sys.optTerm a T‖ ≤ c * ρ ^ T * ‖a‖

end FIESystem

end Estimation

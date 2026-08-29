import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Architect

/-!
# Complexification of real matrices and vectors

The estimator formalized by the `Estimation` track lives over `ℝ`, while the
eigenvalue arguments (Hautus tests, Schur stability, spectral growth bounds)
live over `ℂ`, following `LinearSystems.Hautus`. This file provides the
entrywise complexification maps

* `LinearSystems.complexify A = A.map Complex.ofReal` for matrices, and
* `LinearSystems.complexifyVec v = fun i => (v i : ℂ)` for vectors,

together with the compatibility lemmas the `ℝ`/`ℂ` boundary needs:
multiplicativity, powers, `mulVec`, injectivity, and preservation of the
`L∞` operator norm (`Matrix.Norms.Operator`) and of the sup norm on vectors.
-/

namespace LinearSystems

open Matrix

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ] [DecidableEq ι]

/-- Entrywise complexification of a real matrix. -/
def complexify (A : Matrix ι κ ℝ) : Matrix ι κ ℂ :=
  A.map Complex.ofReal

/-- Entrywise complexification of a real vector. -/
def complexifyVec (v : ι → ℝ) : ι → ℂ :=
  fun i => v i

@[simp]
lemma complexify_apply (A : Matrix ι κ ℝ) (i : ι) (j : κ) :
    complexify A i j = (A i j : ℂ) :=
  rfl

@[simp]
lemma complexifyVec_apply (v : ι → ℝ) (i : ι) :
    complexifyVec v i = (v i : ℂ) :=
  rfl

@[simp]
lemma complexify_zero : complexify (0 : Matrix ι κ ℝ) = 0 := by
  ext i j
  simp

@[simp]
lemma complexify_one : complexify (1 : Matrix ι ι ℝ) = 1 :=
  Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

@[simp]
lemma complexifyVec_zero : complexifyVec (0 : ι → ℝ) = 0 := by
  funext i
  simp

lemma complexify_injective :
    Function.Injective (complexify : Matrix ι κ ℝ → _) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

lemma complexifyVec_injective :
    Function.Injective (complexifyVec : (ι → ℝ) → _) := by
  intro v w h
  funext i
  exact Complex.ofReal_injective (congrFun h i)

@[simp]
lemma complexify_eq_zero_iff {A : Matrix ι κ ℝ} :
    complexify A = 0 ↔ A = 0 :=
  ⟨fun h => complexify_injective (h.trans complexify_zero.symm), fun h => by
    rw [h, complexify_zero]⟩

@[simp]
lemma complexifyVec_eq_zero_iff {v : ι → ℝ} :
    complexifyVec v = 0 ↔ v = 0 :=
  ⟨fun h => complexifyVec_injective (h.trans complexifyVec_zero.symm), fun h => by
    rw [h, complexifyVec_zero]⟩

lemma complexify_add (A B : Matrix ι κ ℝ) :
    complexify (A + B) = complexify A + complexify B := by
  ext i j
  simp

lemma complexify_mul (A : Matrix ι κ ℝ) (B : Matrix κ σ ℝ) :
    complexify (A * B) = complexify A * complexify B :=
  Matrix.map_mul (f := Complex.ofRealHom)

lemma complexify_pow (A : Matrix ι ι ℝ) (k : ℕ) :
    complexify (A ^ k) = complexify A ^ k := by
  simpa [complexify, RingHom.mapMatrix_apply] using
    map_pow Complex.ofRealHom.mapMatrix A k

lemma complexify_transpose (A : Matrix ι κ ℝ) :
    complexify Aᵀ = (complexify A)ᵀ :=
  rfl

@[simp]
lemma complexify_neg (A : Matrix ι κ ℝ) : complexify (-A) = -complexify A := by
  ext i j
  simp

lemma complexify_mulVec (A : Matrix ι κ ℝ) (v : κ → ℝ) :
    complexify A *ᵥ complexifyVec v = complexifyVec (A *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, complexify_apply, complexifyVec_apply]
  push_cast
  rfl

lemma complexifyVec_smul (r : ℝ) (v : ι → ℝ) :
    complexifyVec (r • v) = (r : ℂ) • complexifyVec v := by
  funext i
  simp

section Norms

open scoped Matrix.Norms.Operator

/-- Complexification preserves the `L∞` operator norm (`nnnorm` version). -/
lemma linfty_opNNNorm_complexify (A : Matrix ι κ ℝ) :
    ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

/-- Complexification preserves the `L∞` operator norm. -/
lemma linfty_opNorm_complexify (A : Matrix ι κ ℝ) :
    ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (linfty_opNNNorm_complexify A)

/-- Complexification preserves the sup norm on vectors (`nnnorm` version). -/
lemma nnnorm_complexifyVec (v : ι → ℝ) : ‖complexifyVec v‖₊ = ‖v‖₊ := by
  simp only [Pi.nnnorm_def, complexifyVec_apply, Complex.nnnorm_real]

/-- Complexification preserves the sup norm on vectors. -/
lemma norm_complexifyVec (v : ι → ℝ) : ‖complexifyVec v‖ = ‖v‖ :=
  congrArg NNReal.toReal (nnnorm_complexifyVec v)

end Norms

end LinearSystems

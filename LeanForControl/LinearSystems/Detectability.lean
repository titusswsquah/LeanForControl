import LeanForControl.LinearSystems.Hautus
import LeanForControl.LinearSystems.Schur

/-!
# Detectability and stabilizability

`(A, C)` is *detectable* when every eigenvector of `A` attached to an
eigenvalue on or outside the unit circle is seen by the output map `C`;
`(A, B)` is *stabilizable* when the transposed pair `(Aᵀ, Bᵀ)` is detectable.
These are the Hautus-style definitions, phrased directly in terms of
eigenpairs, matching the "unstable modes" reading used throughout the
`costogo` papers (conditions C1 and, dually, the stabilizability of the
`(A₁, G₁)` block).

Main results:

* `LinearSystems.IsDetectable`, `LinearSystems.IsStabilizable` — definitions.
* `LinearSystems.IsObservable.isDetectable`,
  `LinearSystems.IsControllable.isStabilizable` — the classical implications.
* `LinearSystems.isDetectable_iff_hautus`,
  `LinearSystems.isStabilizable_iff_hautus` — kernel/rank forms of the
  restricted Hautus tests.
* `LinearSystems.IsSchurStable.isDetectable_complexify` — a Schur-stable
  matrix is detectable through any output map (there are no unstable modes).

The `mem_spectrum_of_mulVec_eq_smul` helper bridges eigenpairs of a matrix to
membership in `spectrum ℂ`, which several later files also use.
-/

namespace LinearSystems

open Matrix

variable {n m p : ℕ}

section GeneralIndex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- An eigenpair of a complex matrix puts the eigenvalue in `spectrum ℂ`. -/
lemma mem_spectrum_of_mulVec_eq_smul {A : Matrix ι ι ℂ} {μ : ℂ}
    {v : ι → ℂ} (hv : v ≠ 0) (h : A *ᵥ v = μ • v) :
    μ ∈ spectrum ℂ A := by
  rw [← Matrix.spectrum_toLin']
  refine Module.End.hasEigenvalue_iff_mem_spectrum.mp ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact h

/-- **Detectability** (condition C1 of the `costogo` papers): every
eigenvector of `A` whose eigenvalue satisfies `1 ≤ ‖μ‖` is detected by `C`.
Equivalently, all unobservable modes are strictly stable. -/
@[blueprint "def:isDetectable"
  (statement := /-- A pair $(A, C)$ is \emph{detectable} if for every
    $\mu \in \mathbb{C}$ with $|\mu| \ge 1$, the only vector $v$ with
    $A v = \mu v$ and $C v = 0$ is $v = 0$: unstable modes are observable. -/)]
def IsDetectable
    (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ) : Prop :=
  ∀ (μ : ℂ) (v : ι → ℂ), 1 ≤ ‖μ‖ → A *ᵥ v = μ • v → C *ᵥ v = 0 → v = 0

/-- **Stabilizability**: the dual of detectability. `(A, B)` is stabilizable
when `(Aᵀ, Bᵀ)` is detectable, i.e. every left eigenvector of `A` attached to
an eigenvalue with `1 ≤ ‖μ‖` is excited by the input map `B`. -/
@[blueprint "def:isStabilizable"
  (statement := /-- A pair $(A, B)$ is \emph{stabilizable} if
    $(A^{\mathsf T}, B^{\mathsf T})$ is detectable: every left eigenvector of
    $A$ at an eigenvalue with $|\mu| \ge 1$ satisfies $w' B \neq 0$. -/)]
def IsStabilizable
    (A : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) : Prop :=
  IsDetectable Aᵀ Bᵀ

/-- Stabilizability is insensitive to the sign of the input matrix. -/
lemma IsStabilizable.neg {A : Matrix ι ι ℂ} {B : Matrix ι κ ℂ}
    (h : IsStabilizable A B) : IsStabilizable A (-B) := by
  intro μ v hμ hAv hBv
  refine h μ v hμ hAv ?_
  rw [Matrix.transpose_neg, Matrix.neg_mulVec, neg_eq_zero] at hBv
  exact hBv

end GeneralIndex

/-- Observability implies detectability. -/
@[blueprint "lem:isObservable-isDetectable"
  (statement := /-- Every observable pair is detectable. -/)
  (proof := /-- An eigenpair $A v = \mu v$ with $C v = 0$ gives
    $C A^{k} v = \mu^{k} C v = 0$ for every $k$, so $v$ is unobservable and
    hence zero. -/)]
theorem IsObservable.isDetectable
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    (h : IsObservable A C) : IsDetectable A C := by
  intro μ v _ hAv hCv
  refine h v fun k => ?_
  have hpow : A ^ (k : ℕ) *ᵥ v = μ ^ (k : ℕ) • v := by
    induction (k : ℕ) with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih,
        smul_smul]
      congr 1
      ring
  rw [← Matrix.mulVec_mulVec, hpow, Matrix.mulVec_smul, hCv, smul_zero]

/-- Controllability implies stabilizability. -/
@[blueprint "lem:isControllable-isStabilizable"
  (statement := /-- Every controllable pair is stabilizable. -/)
  (proof := /-- Controllability of $(A, B)$ is observability of
    $(A^{\mathsf T}, B^{\mathsf T})$, which is in particular detectability
    of the transposed pair. -/)]
theorem IsControllable.isStabilizable
    {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin m) ℂ}
    (h : IsControllable A B) : IsStabilizable A B :=
  ((isControllable_iff_isObservable_transpose A B).mp h).isDetectable

/-- Hautus test for detectability: the Hautus observability block
`[μI - A; C]` has trivial kernel at every `μ` on or outside the unit
circle. -/
@[blueprint "thm:isDetectable-iff-hautus"
  (statement := /-- $(A, C)$ is detectable if and only if for every
    $\mu \in \mathbb{C}$ with $|\mu| \ge 1$, the Hautus matrix
    $\begin{bmatrix} \mu I - A \\ C\end{bmatrix}$ has trivial kernel. -/)
  (proof := /-- Both sides quantify over the same eigenpair data via
    \cref{lem:hautus-mulVec-eq-zero-iff}. -/)]
theorem isDetectable_iff_hautus
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    IsDetectable A C
      ↔ ∀ μ : ℂ, 1 ≤ ‖μ‖ →
          LinearMap.ker (hautusObservabilityMatrix A C μ).mulVecLin = ⊥ := by
  constructor
  · intro h μ hμ
    rw [Matrix.ker_mulVecLin_eq_bot_iff]
    intro v hv
    rw [hautusObservabilityMatrix_mulVec_eq_zero_iff] at hv
    exact h μ v hμ hv.1 hv.2
  · intro h μ v hμ hAv hCv
    have hker := (Matrix.ker_mulVecLin_eq_bot_iff).mp (h μ hμ)
    exact hker v ((hautusObservabilityMatrix_mulVec_eq_zero_iff A C μ v).mpr
      ⟨hAv, hCv⟩)

/-- Hautus test for stabilizability: the Hautus controllability block
`[μI - A | B]` has full row rank at every `μ` on or outside the unit
circle. -/
@[blueprint "thm:isStabilizable-iff-hautus"
  (statement := /-- $(A, B)$ is stabilizable if and only if for every
    $\mu \in \mathbb{C}$ with $|\mu| \ge 1$, the Hautus matrix
    $\begin{bmatrix} \mu I - A & B\end{bmatrix}$ has full row rank $n$. -/)
  (proof := /-- Transpose \cref{thm:isDetectable-iff-hautus} and convert the
    kernel form to the rank form. -/)]
theorem isStabilizable_iff_hautus
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    IsStabilizable A B
      ↔ ∀ μ : ℂ, 1 ≤ ‖μ‖ →
          Matrix.rank (hautusControllabilityMatrix A B μ) = n := by
  rw [IsStabilizable, isDetectable_iff_hautus]
  refine forall_congr' fun μ => imp_congr_right fun _ => ?_
  rw [Matrix.ker_mulVecLin_eq_bot_iff,
    LinearSystems.MatrixLemmas.mulVec_kernel_trivial_iff_rank_eq_card_cols,
    Fintype.card_fin,
    ← hautusControllabilityMatrix_transpose,
    Matrix.rank_transpose]

/-- A Schur-stable real matrix is detectable through any output map: there
are no modes on or outside the unit circle to detect. -/
@[blueprint "lem:isSchurStable-isDetectable"
  (statement := /-- If $A$ is Schur stable, then $(A, C)$ is detectable for
    every $C$. -/)
  (proof := /-- An eigenpair at $|\mu| \ge 1$ would put $\mu$ in the
    spectrum, contradicting $\rho(A) < 1$. -/)]
theorem IsSchurStable.isDetectable_complexify
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSchurStable A)
    (C : Matrix (Fin p) (Fin n) ℝ) :
    IsDetectable (complexify A) (complexify C) := by
  intro μ v hμ hAv _
  by_contra hv
  exact absurd hμ (not_le.mpr (hA μ (mem_spectrum_of_mulVec_eq_smul hv hAv)))

end LinearSystems

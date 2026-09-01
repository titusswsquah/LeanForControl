import LeanForControl.Estimation.Dare.MainRate
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Architect

/-!
# The symplectic-pencil closed form (E4, `thm:formula`)

Arc 1's engine, verified by the deck's own induction — no pencil
theory is load-bearing:

* `innovWeight` is the symmetric innovation weight
  `Ω = CᵀS∞⁻¹C` with its two display forms;
* `fwdGram` is the forward `F∞`-gramian `𝒢_T`;
* `pushthrough_gram` / `slide_step` — the push-through
  `Γᵀ(S₀ + ΓXΓᵀ)⁻¹ = (I + ΓᵀS₀⁻¹ΓX)⁻¹ΓᵀS₀⁻¹` and the homographic
  slide of one Riccati step;
* `formula` — the joint induction: the denominator `N_T = I + 𝒢_T D`
  is nonsingular (Weinstein–Aronszajn against the innovation
  determinants) and
  `Σ_T = Σ∞ + F∞^T·D·N_T⁻¹·(F∞ᵀ)^T` (`eq:formula`), for **every**
  PSD seed and every finite `T` — Schur-ness enters only in the
  gramian limit and the rate corollary.

The identities `id1`, `id2` and the two-sided block-triangularization
`eq:pencil-block` are verified separately as matrix computations.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

/-! ### The push-through and the slide (general) -/

variable {n' p' : Type*} [Fintype n'] [DecidableEq n'] [Fintype p']
  [DecidableEq p']

/-- **The push-through**:
`Γᵀ(S₀ + ΓXΓᵀ)⁻¹ = (I + ΓᵀS₀⁻¹ΓX)⁻¹ · ΓᵀS₀⁻¹`. -/
lemma pushthrough_gram (Γ : Matrix p' n' ℝ) (S₀ : Matrix p' p' ℝ)
    (X : Matrix n' n' ℝ) (hS₀ : IsUnit S₀.det)
    (hSV : IsUnit (S₀ + Γ * X * Γᵀ).det)
    (hN : IsUnit (1 + Γᵀ * S₀⁻¹ * Γ * X).det) :
    Γᵀ * (S₀ + Γ * X * Γᵀ)⁻¹
      = (1 + Γᵀ * S₀⁻¹ * Γ * X)⁻¹ * (Γᵀ * S₀⁻¹) := by
  have hkey : (1 + Γᵀ * S₀⁻¹ * Γ * X) * Γᵀ
      = Γᵀ * S₀⁻¹ * (S₀ + Γ * X * Γᵀ) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_assoc Γᵀ S₀⁻¹ S₀, Matrix.nonsing_inv_mul _ hS₀,
      Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  calc Γᵀ * (S₀ + Γ * X * Γᵀ)⁻¹
      = (1 + Γᵀ * S₀⁻¹ * Γ * X)⁻¹
        * ((1 + Γᵀ * S₀⁻¹ * Γ * X) * Γᵀ)
        * (S₀ + Γ * X * Γᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hN,
          Matrix.one_mul]
  _ = (1 + Γᵀ * S₀⁻¹ * Γ * X)⁻¹ * (Γᵀ * S₀⁻¹)
        * ((S₀ + Γ * X * Γᵀ) * (S₀ + Γ * X * Γᵀ)⁻¹) := by
      rw [hkey]
      simp only [Matrix.mul_assoc]
  _ = (1 + Γᵀ * S₀⁻¹ * Γ * X)⁻¹ * (Γᵀ * S₀⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hSV, Matrix.mul_one]

/-- **The homographic slide of one Riccati step**: the gap bracket
collapses onto the next denominator. -/
lemma slide_step (Γ : Matrix p' n' ℝ) (S₀ : Matrix p' p' ℝ)
    (D N : Matrix n' n' ℝ) (hS₀ : IsUnit S₀.det)
    (hSV : IsUnit (S₀ + Γ * (D * N⁻¹) * Γᵀ).det)
    (hY : IsUnit (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹)).det) :
    D * N⁻¹ - D * N⁻¹ * Γᵀ * (S₀ + Γ * (D * N⁻¹) * Γᵀ)⁻¹
        * (Γ * (D * N⁻¹))
      = D * ((1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹)) * N)⁻¹ := by
  have hpush := pushthrough_gram Γ S₀ (D * N⁻¹) hS₀ hSV hY
  have h1 : D * N⁻¹ * Γᵀ * (S₀ + Γ * (D * N⁻¹) * Γᵀ)⁻¹
      * (Γ * (D * N⁻¹))
      = D * N⁻¹ * ((1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹
        * (Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))) := by
    rw [Matrix.mul_assoc (D * N⁻¹) Γᵀ _, hpush]
    simp only [Matrix.mul_assoc]
  rw [h1]
  have h4 : (1 : Matrix n' n' ℝ)
      - (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹
        * (Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))
      = (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹ := by
    calc (1 : Matrix n' n' ℝ)
        - (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹
          * (Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))
        = (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹
            * (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))
          - (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹
            * (Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹)) := by
          rw [Matrix.nonsing_inv_mul _ hY]
    _ = (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹
          * (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹)
            - Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹)) := by
        rw [Matrix.mul_sub]
    _ = (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹ := by
        rw [add_sub_cancel_right, Matrix.mul_one]
  calc D * N⁻¹
      - D * N⁻¹ * ((1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹
        * (Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹)))
      = D * N⁻¹ * ((1 : Matrix n' n' ℝ)
          - (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹
            * (Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))) := by
        rw [Matrix.mul_sub, Matrix.mul_one]
  _ = D * N⁻¹ * (1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹))⁻¹ := by
      rw [h4]
  _ = D * ((1 + Γᵀ * S₀⁻¹ * Γ * (D * N⁻¹)) * N)⁻¹ := by
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-! ### The innovation weight and the forward gramian -/

variable (Sinf) in
/-- The symmetric innovation weight `Ω = CᵀS∞⁻¹C` (`eq:gramian`). -/
noncomputable def innovWeight : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  S.fullCᵀ * (innov S.fullC S.R Sinf)⁻¹ * S.fullC

variable (Sinf) in
/-- The forward `F∞`-gramian `𝒢_T` (`eq:gramian`). -/
noncomputable def fwdGram (T : ℕ) : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  ∑ k ∈ Finset.range T,
    ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ k * S.innovWeight Sinf
      * (errMap S.fullC S.R S.fullA Sinf) ^ k

lemma innovWeight_posSemidef (hS : Sinf.PosSemidef) :
    (S.innovWeight Sinf).PosSemidef := by
  have h := (innov_posDef (C := S.fullC) S.hR
    hS).inv.posSemidef.conjTranspose_mul_mul_same S.fullC
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

lemma innovWeight_transpose (hS : Sinf.PosSemidef) :
    (S.innovWeight Sinf)ᵀ = S.innovWeight Sinf := by
  unfold innovWeight
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
    innov_transpose S.hR hS]
  simp only [Matrix.mul_assoc]

@[simp]
lemma fwdGram_zero : S.fwdGram Sinf 0 = 0 := by
  unfold fwdGram
  simp

lemma fwdGram_succ (T : ℕ) :
    S.fwdGram Sinf (T + 1)
      = S.fwdGram Sinf T
        + ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T
          * S.innovWeight Sinf
          * (errMap S.fullC S.R S.fullA Sinf) ^ T := by
  unfold fwdGram
  rw [Finset.sum_range_succ]

/-- The stepped weight in observation form:
`(F∞ᵀ)^T·Ω·F∞^T = Γ_TᵀS∞⁻¹Γ_T`, `Γ_T := C·F∞^T`. -/
lemma stepped_weight_eq (T : ℕ) :
    ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T * S.innovWeight Sinf
      * (errMap S.fullC S.R S.fullA Sinf) ^ T
      = (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ
        * (innov S.fullC S.R Sinf)⁻¹
        * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T) := by
  unfold innovWeight
  rw [Matrix.transpose_mul, ← Matrix.transpose_pow]
  simp only [Matrix.mul_assoc]

set_option maxHeartbeats 3200000 in
/-- **`thm:formula` (`eq:formula`)**: for every PSD seed and every
finite horizon, the denominator `N_T = I + 𝒢_T·D` is nonsingular and

`Σ_T = Σ∞ + F∞^T · D · N_T⁻¹ · (F∞ᵀ)^T`, `D := Σ₀ − Σ∞`.

The joint induction: nonsingularity by the Weinstein–Aronszajn
identity against the ratio of innovation determinants; the step by
`eq:gap-ric` and the push-through. No Schur-ness, no inverse of `A`,
no pencil. -/
theorem formula (hS : S.IsStrongSolution Sinf)
    {L₀ : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hL₀ : L₀.PosSemidef) :
    ∀ T, IsUnit (1 + S.fwdGram Sinf T * (L₀ - Sinf)).det
      ∧ S.dareFrom L₀ T
        = Sinf + (errMap S.fullC S.R S.fullA Sinf) ^ T * (L₀ - Sinf)
            * (1 + S.fwdGram Sinf T * (L₀ - Sinf))⁻¹
            * ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T := by
  have hSinfPD : (innov S.fullC S.R Sinf).PosDef :=
    innov_posDef S.hR hS.posSemidef
  have hSinfU : IsUnit (innov S.fullC S.R Sinf).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSinfPD.isUnit
  have hDdef : L₀ - Sinf = L₀ - Sinf := rfl
  generalize hD : L₀ - Sinf = D
  intro T
  induction T with
  | zero =>
    constructor
    · simp
    · show S.dareFrom L₀ 0 = _
      simp [dareFrom, ← hD]
  | succ T ih =>
    obtain ⟨hunit, heq⟩ := ih
    have hSigpsd : (S.dareFrom L₀ T).PosSemidef :=
      dareIter_posSemidef S.hR S.Qw_posSemidef hL₀ T
    have hGpsd : (Sinf + (errMap S.fullC S.R S.fullA Sinf) ^ T * D
        * (1 + S.fwdGram Sinf T * D)⁻¹
        * ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T).PosSemidef := by
      rw [← heq]
      exact hSigpsd
    have hSVPD : (innov S.fullC S.R (S.dareFrom L₀ T)).PosDef :=
      innov_posDef S.hR hSigpsd
    have hSVU : IsUnit (innov S.fullC S.R (S.dareFrom L₀ T)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hSVPD.isUnit
    -- the transpose bridge
    have hΓ : ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T * S.fullCᵀ
        = (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_pow]
    -- the innovation split
    have hST : innov S.fullC S.R (S.dareFrom L₀ T)
        = innov S.fullC S.R Sinf
          + (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
            * (D * (1 + S.fwdGram Sinf T * D)⁻¹)
            * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ := by
      conv_lhs => rw [heq]
      unfold innov
      rw [← hΓ]
      rw [Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
      abel
    -- Weinstein–Aronszajn: the slide factor is nonsingular
    have hYunit : IsUnit (1
        + (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ
          * (innov S.fullC S.R Sinf)⁻¹
          * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
          * (D * (1 + S.fwdGram Sinf T * D)⁻¹)).det := by
      have h1 : (1
          + (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ
            * (innov S.fullC S.R Sinf)⁻¹
            * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
            * (D * (1 + S.fwdGram Sinf T * D)⁻¹)).det
          = (1 + (innov S.fullC S.R Sinf)⁻¹
              * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
              * (D * (1 + S.fwdGram Sinf T * D)⁻¹)
              * (S.fullC
                * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ).det := by
        have h2 := Matrix.det_one_add_mul_comm
          ((S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ)
          ((innov S.fullC S.R Sinf)⁻¹
            * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
            * (D * (1 + S.fwdGram Sinf T * D)⁻¹))
        simp only [Matrix.mul_assoc] at h2 ⊢
        exact h2
      rw [h1]
      have h3 : (1 : Matrix (Fin p) (Fin p) ℝ)
          + (innov S.fullC S.R Sinf)⁻¹
            * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
            * (D * (1 + S.fwdGram Sinf T * D)⁻¹)
            * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ
          = (innov S.fullC S.R Sinf)⁻¹
            * innov S.fullC S.R (S.dareFrom L₀ T) := by
        rw [hST, Matrix.mul_add,
          Matrix.nonsing_inv_mul _ hSinfU]
        simp only [Matrix.mul_assoc]
      rw [h3, Matrix.det_mul]
      exact (hSinfPD.inv.isUnit.map (Matrix.detMonoidHom)).mul
        ((Matrix.isUnit_iff_isUnit_det _).mp hSVPD.isUnit)
    -- the next denominator factors
    have hNsucc : 1 + S.fwdGram Sinf (T + 1) * D
        = (1 + (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ
            * (innov S.fullC S.R Sinf)⁻¹
            * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
            * (D * (1 + S.fwdGram Sinf T * D)⁻¹))
          * (1 + S.fwdGram Sinf T * D) := by
      rw [S.fwdGram_succ, S.stepped_weight_eq, Matrix.add_mul,
        Matrix.add_mul, Matrix.one_mul]
      have h4 : (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ
          * (innov S.fullC S.R Sinf)⁻¹
          * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
          * (D * (1 + S.fwdGram Sinf T * D)⁻¹)
          * (1 + S.fwdGram Sinf T * D)
          = (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ
            * (innov S.fullC S.R Sinf)⁻¹
            * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
            * D := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
      rw [h4]
      abel
    have hNunit : IsUnit (1 + S.fwdGram Sinf (T + 1) * D).det := by
      rw [hNsucc, Matrix.det_mul]
      exact hYunit.mul hunit
    refine ⟨hNunit, ?_⟩
    -- one Riccati step through the gap identity
    have hgap := gapRic (C := S.fullC) (A := S.fullA) (Qw := S.Qw)
      S.hR hS.posSemidef hGpsd hS.fixed
    have hstep : S.dareFrom L₀ (T + 1)
        = dareStep S.fullC S.R S.fullA S.Qw (S.dareFrom L₀ T) := rfl
    rw [hstep]
    conv_lhs => rw [heq]
    rw [← sub_eq_iff_eq_add']
    rw [hgap]
    -- rewrite the running innovation
    have hSVrw : innov S.fullC S.R
        (Sinf + (errMap S.fullC S.R S.fullA Sinf) ^ T * D
          * (1 + S.fwdGram Sinf T * D)⁻¹
          * ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T)
        = innov S.fullC S.R Sinf
          + (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
            * (D * (1 + S.fwdGram Sinf T * D)⁻¹)
            * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ := by
      rw [← heq]
      exact hST
    rw [hSVrw]
    -- factor `F^T ⋯ (Fᵀ)^T` out of the bracket
    have hbracket : (errMap S.fullC S.R S.fullA Sinf) ^ T * D
          * (1 + S.fwdGram Sinf T * D)⁻¹
          * ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T
        - (errMap S.fullC S.R S.fullA Sinf) ^ T * D
            * (1 + S.fwdGram Sinf T * D)⁻¹
            * ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T
          * S.fullCᵀ
          * (innov S.fullC S.R Sinf
            + (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
              * (D * (1 + S.fwdGram Sinf T * D)⁻¹)
              * (S.fullC
                * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ)⁻¹
          * (S.fullC
            * ((errMap S.fullC S.R S.fullA Sinf) ^ T * D
              * (1 + S.fwdGram Sinf T * D)⁻¹
              * ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T))
        = (errMap S.fullC S.R S.fullA Sinf) ^ T
          * (D * (1 + S.fwdGram Sinf T * D)⁻¹
            - D * (1 + S.fwdGram Sinf T * D)⁻¹
              * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ
              * (innov S.fullC S.R Sinf
                + (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
                  * (D * (1 + S.fwdGram Sinf T * D)⁻¹)
                  * (S.fullC
                    * (errMap S.fullC S.R S.fullA Sinf) ^ T)ᵀ)⁻¹
              * (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T
                * (D * (1 + S.fwdGram Sinf T * D)⁻¹)))
          * ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T := by
      rw [← hΓ]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [hbracket]
    -- the slide collapses onto the next denominator
    have hslide := slide_step
      (S.fullC * (errMap S.fullC S.R S.fullA Sinf) ^ T)
      (innov S.fullC S.R Sinf) D
      (1 + S.fwdGram Sinf T * D) hSinfU
      (by rw [← hST]; exact hSVU) hYunit
    rw [hslide, ← hNsucc]
    -- reassemble the flanks
    rw [pow_succ (errMap S.fullC S.R S.fullA Sinf) T,
      pow_succ ((errMap S.fullC S.R S.fullA Sinf)ᵀ) T]
    have hcomm : (errMap S.fullC S.R S.fullA Sinf) ^ T
        * errMap S.fullC S.R S.fullA Sinf
        = errMap S.fullC S.R S.fullA Sinf
          * (errMap S.fullC S.R S.fullA Sinf) ^ T := by
      rw [← pow_succ, pow_succ']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((errMap S.fullC S.R S.fullA Sinf) ^ T)
      (errMap S.fullC S.R S.fullA Sinf)]
    rw [hcomm]
    simp only [Matrix.mul_assoc]

/-! ### The structural identities (`id1`, `id2`, the Ω forms) -/

/-- **id2**: `Σ∞ − Q_w = F∞·Σ∞·Aᵀ`. -/
lemma strong_id2 (hS : S.IsStrongSolution Sinf) :
    Sinf - S.Qw
      = errMap S.fullC S.R S.fullA Sinf * Sinf * S.fullAᵀ := by
  have hupd : updM S.fullC S.R Sinf
      = (1 - kGain S.fullC S.R Sinf * S.fullC) * Sinf := by
    unfold updM kGain
    rw [Matrix.sub_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  conv_lhs => rw [← hS.fixed]
  show S.fullA * updM S.fullC S.R Sinf * S.fullAᵀ + S.Qw - S.Qw = _
  rw [add_sub_cancel_right, hupd]
  unfold errMap
  simp only [Matrix.mul_assoc]

/-- The gain absorbs the innovation shear:
`K∞·C·(I + Σ∞H_C) = Σ∞·H_C`, `H_C := CᵀR⁻¹C`. -/
lemma kGain_shear (hSpsd : Sinf.PosSemidef) :
    kGain S.fullC S.R Sinf * S.fullC
        * (1 + Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC))
      = Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC) := by
  have hRdet : IsUnit S.R.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp S.hR.isUnit
  have hCS : S.fullC * (1 + Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC))
      = innov S.fullC S.R Sinf * (S.R⁻¹ * S.fullC) := by
    unfold innov
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
      ← Matrix.mul_assoc S.R S.R⁻¹ S.fullC,
      Matrix.mul_nonsing_inv _ hRdet, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    abel
  calc kGain S.fullC S.R Sinf * S.fullC
      * (1 + Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC))
      = kGain S.fullC S.R Sinf
        * (S.fullC * (1 + Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC))) := by
        rw [Matrix.mul_assoc]
  _ = kGain S.fullC S.R Sinf * innov S.fullC S.R Sinf
        * (S.R⁻¹ * S.fullC) := by
      rw [hCS, Matrix.mul_assoc]
  _ = Sinf * S.fullCᵀ * (S.R⁻¹ * S.fullC) := by
      rw [kGain_mul_innov S.hR hSpsd]
  _ = Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC) := by
      simp only [Matrix.mul_assoc]

/-- **id1**: `A = F∞·(I + Σ∞H_C)` — the shear inverts the gain. -/
lemma strong_id1 (hSpsd : Sinf.PosSemidef) :
    errMap S.fullC S.R S.fullA Sinf
        * (1 + Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC))
      = S.fullA := by
  have hkey : (1 - kGain S.fullC S.R Sinf * S.fullC)
      * (1 + Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC)) = 1 := by
    rw [Matrix.sub_mul, Matrix.one_mul, S.kGain_shear hSpsd,
      add_sub_cancel_right]
  unfold errMap
  rw [Matrix.mul_assoc, hkey, Matrix.mul_one]

/-- The innovation-form identity `Ω = (I − K∞C)ᵀ·H_C`
(`eq:gramian`'s display). -/
lemma innovWeight_eq_oneSubKC (hSpsd : Sinf.PosSemidef) :
    S.innovWeight Sinf
      = (1 - kGain S.fullC S.R Sinf * S.fullC)ᵀ
        * (S.fullCᵀ * S.R⁻¹ * S.fullC) := by
  have hRdet : IsUnit S.R.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp S.hR.isUnit
  have hSt : (innov S.fullC S.R Sinf).PosDef :=
    innov_posDef S.hR hSpsd
  have hStdet : IsUnit (innov S.fullC S.R Sinf).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSt.isUnit
  have hKt : (kGain S.fullC S.R Sinf * S.fullC)ᵀ
      = S.fullCᵀ * ((innov S.fullC S.R Sinf)⁻¹
        * (S.fullC * Sinf)) := by
    unfold kGain
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, innov_transpose S.hR hSpsd,
      hSpsd.1.transpose_eq_self]
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul,
    Matrix.one_mul, hKt]
  -- `Cᵀ·S⁻¹·(CΣ)·CᵀR⁻¹C = Cᵀ·(R⁻¹ − S⁻¹)·C`
  have hmid : (innov S.fullC S.R Sinf)⁻¹ * (S.fullC * Sinf)
      * (S.fullCᵀ * S.R⁻¹)
      = S.R⁻¹ - (innov S.fullC S.R Sinf)⁻¹ := by
    have h1 : S.fullC * Sinf * S.fullCᵀ
        = innov S.fullC S.R Sinf - S.R := by
      unfold innov
      abel
    calc (innov S.fullC S.R Sinf)⁻¹ * (S.fullC * Sinf)
        * (S.fullCᵀ * S.R⁻¹)
        = (innov S.fullC S.R Sinf)⁻¹
          * (S.fullC * Sinf * S.fullCᵀ) * S.R⁻¹ := by
          simp only [Matrix.mul_assoc]
    _ = (innov S.fullC S.R Sinf)⁻¹
          * (innov S.fullC S.R Sinf - S.R) * S.R⁻¹ := by rw [h1]
    _ = S.R⁻¹ - (innov S.fullC S.R Sinf)⁻¹ := by
        rw [Matrix.mul_sub, Matrix.sub_mul,
          Matrix.nonsing_inv_mul _ hStdet, Matrix.one_mul,
          Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hRdet,
          Matrix.mul_one]
  unfold innovWeight
  have h2 : S.fullCᵀ * ((innov S.fullC S.R Sinf)⁻¹
        * (S.fullC * Sinf)) * (S.fullCᵀ * S.R⁻¹ * S.fullC)
      = S.fullCᵀ * (S.R⁻¹ - (innov S.fullC S.R Sinf)⁻¹)
        * S.fullC := by
    rw [← hmid]
    simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  abel

/-- The shear form `(I + H_CΣ∞)·Ω = H_C` (so
`Ω = (I + H_CΣ∞)⁻¹H_C`, `sec:formula`-2's display). -/
lemma shear_mul_innovWeight (hSpsd : Sinf.PosSemidef) :
    (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf) * S.innovWeight Sinf
      = S.fullCᵀ * S.R⁻¹ * S.fullC := by
  have hRdet : IsUnit S.R.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp S.hR.isUnit
  have hSt : (innov S.fullC S.R Sinf).PosDef :=
    innov_posDef S.hR hSpsd
  have hStdet : IsUnit (innov S.fullC S.R Sinf).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSt.isUnit
  have h1 : S.fullC * Sinf * S.fullCᵀ
      = innov S.fullC S.R Sinf - S.R := by
    unfold innov
    abel
  unfold innovWeight
  rw [Matrix.add_mul, Matrix.one_mul]
  have h2 : S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf
      * (S.fullCᵀ * (innov S.fullC S.R Sinf)⁻¹ * S.fullC)
      = S.fullCᵀ * (S.R⁻¹
        * ((innov S.fullC S.R Sinf - S.R)
          * ((innov S.fullC S.R Sinf)⁻¹ * S.fullC))) := by
    rw [← h1]
    simp only [Matrix.mul_assoc]
  have h3 : S.R⁻¹ * ((innov S.fullC S.R Sinf - S.R)
      * ((innov S.fullC S.R Sinf)⁻¹ * S.fullC))
      = S.R⁻¹ * S.fullC
        - (innov S.fullC S.R Sinf)⁻¹ * S.fullC := by
    rw [Matrix.sub_mul, Matrix.mul_sub,
      ← Matrix.mul_assoc (innov S.fullC S.R Sinf) _ S.fullC,
      Matrix.mul_nonsing_inv _ hStdet, Matrix.one_mul,
      ← Matrix.mul_assoc S.R (innov S.fullC S.R Sinf)⁻¹ S.fullC,
      ← Matrix.mul_assoc S.R⁻¹
        (S.R * (innov S.fullC S.R Sinf)⁻¹) S.fullC,
      ← Matrix.mul_assoc S.R⁻¹ S.R (innov S.fullC S.R Sinf)⁻¹,
      Matrix.nonsing_inv_mul _ hRdet, Matrix.one_mul]
  calc S.fullCᵀ * (innov S.fullC S.R Sinf)⁻¹ * S.fullC
        + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf
          * (S.fullCᵀ * (innov S.fullC S.R Sinf)⁻¹ * S.fullC)
      = S.fullCᵀ * (innov S.fullC S.R Sinf)⁻¹ * S.fullC
        + S.fullCᵀ * (S.R⁻¹ * S.fullC
          - (innov S.fullC S.R Sinf)⁻¹ * S.fullC) := by
        rw [h2, h3]
  _ = S.fullCᵀ * S.R⁻¹ * S.fullC := by
      rw [Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel

/-! ### The two-sided block-triangularization (`eq:pencil-block`) -/

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
/-- `P·𝓜·T_Σ = diag(Aᵀ, I)` — the `𝓜`-side of `eq:pencil-block`,
its corner killed by **id2**. -/
lemma pencil_block_M (hS : S.IsStrongSolution Sinf) :
    Matrix.fromBlocks 1 0
        (-(errMap S.fullC S.R S.fullA Sinf * Sinf)) 1
      * Matrix.fromBlocks S.fullAᵀ 0 (-S.Qw) 1
      * Matrix.fromBlocks 1 0 Sinf 1
      = Matrix.fromBlocks S.fullAᵀ 0 0
        (1 : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) := by
  have hid2 := S.strong_id2 hS
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
      Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul]
    rw [← hid2]
    abel
  · simp

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
/-- `P·𝓛·T_Σ` is upper-triangular with `F∞` in the corner — the
`𝓛`-side of `eq:pencil-block`, its corner killed by **id1**. -/
lemma pencil_block_L (hS : S.IsStrongSolution Sinf) :
    Matrix.fromBlocks 1 0
        (-(errMap S.fullC S.R S.fullA Sinf * Sinf)) 1
      * Matrix.fromBlocks 1 (S.fullCᵀ * S.R⁻¹ * S.fullC) 0 S.fullA
      * Matrix.fromBlocks 1 0 Sinf 1
      = Matrix.fromBlocks
          (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf)
          (S.fullCᵀ * S.R⁻¹ * S.fullC) 0
          (errMap S.fullC S.R S.fullA Sinf) := by
  have hid1 := S.strong_id1 hS.posSemidef
  have hAS : S.fullA * Sinf
      = errMap S.fullC S.R S.fullA Sinf * Sinf
        + errMap S.fullC S.R S.fullA Sinf
          * (Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC) * Sinf) := by
    conv_lhs => rw [← hid1]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
  have hA : S.fullA
      = errMap S.fullC S.R S.fullA Sinf
        + errMap S.fullC S.R S.fullA Sinf
          * (Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC)) := by
    conv_lhs => rw [← hid1]
    rw [Matrix.mul_add, Matrix.mul_one]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
      Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul,
      Matrix.add_mul]
    generalize hF : errMap S.fullC S.R S.fullA Sinf = FF at hAS ⊢
    rw [hAS]
    simp only [Matrix.mul_assoc]
    abel
  · simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
      Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul]
    generalize hF : errMap S.fullC S.R S.fullA Sinf = FF at hA ⊢
    rw [hA]
    simp only [Matrix.mul_assoc]
    abel

/-! ### The gramian limit and the rate (`cor:attract`) -/

/-- The forward gramian is PSD at every horizon. -/
lemma fwdGram_posSemidef (hSpsd : Sinf.PosSemidef) (T : ℕ) :
    (S.fwdGram Sinf T).PosSemidef := by
  induction T with
  | zero => simpa using Matrix.PosSemidef.zero
  | succ T ih =>
    rw [S.fwdGram_succ]
    refine ih.add ?_
    have h := (S.innovWeight_posSemidef
      hSpsd).conjTranspose_mul_mul_same
      ((errMap S.fullC S.R S.fullA Sinf) ^ T)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_pow] at h

/-- The gramian is the running Stein iteration. -/
lemma fwdGram_eq_sylvIter (T : ℕ) :
    S.fwdGram Sinf T
      = sylvIter ((errMap S.fullC S.R S.fullA Sinf)ᵀ)
          (errMap S.fullC S.R S.fullA Sinf)
          (S.innovWeight Sinf) T := by
  induction T with
  | zero => simp [sylvIter]
  | succ T ih =>
    have h1 := sylvIter_succ_sub
      ((errMap S.fullC S.R S.fullA Sinf)ᵀ)
      (errMap S.fullC S.R S.fullA Sinf) (S.innovWeight Sinf) T
    have h2 : sylvIter ((errMap S.fullC S.R S.fullA Sinf)ᵀ)
        (errMap S.fullC S.R S.fullA Sinf)
        (S.innovWeight Sinf) (T + 1)
        = sylvIter ((errMap S.fullC S.R S.fullA Sinf)ᵀ)
            (errMap S.fullC S.R S.fullA Sinf)
            (S.innovWeight Sinf) T
          + ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T
            * S.innovWeight Sinf
            * (errMap S.fullC S.R S.fullA Sinf) ^ T := by
      rw [← h1]
      abel
    rw [h2, ← ih, ← S.fwdGram_succ]

/-- **The gramian limit** (`thm:formula`'s finiteness clause): under
a Schur strong loop the forward gramian increases to the finite Stein
solution `𝒢∞ = F∞ᵀ𝒢∞F∞ + Ω`. -/
theorem fwdGram_tendsto_stein (hSpsd : Sinf.PosSemidef)
    (hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf)) :
    ∃ Ginf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ,
      Ginf = (errMap S.fullC S.R S.fullA Sinf)ᵀ * Ginf
          * errMap S.fullC S.R S.fullA Sinf + S.innovWeight Sinf
        ∧ Ginf.PosSemidef
        ∧ Tendsto (fun T => ‖S.fwdGram Sinf T - Ginf‖)
            atTop (nhds 0) := by
  obtain ⟨Ginf, hfix, htend⟩ := sylvester_exists
    ((errMap S.fullC S.R S.fullA Sinf)ᵀ)
    (errMap S.fullC S.R S.fullA Sinf) (S.innovWeight Sinf)
    hFs.transpose hFs
  have htend' : Tendsto (fun T => ‖S.fwdGram Sinf T - Ginf‖)
      atTop (nhds 0) := by
    have h1 : (fun T => ‖S.fwdGram Sinf T - Ginf‖)
        = fun T => ‖sylvIter ((errMap S.fullC S.R S.fullA Sinf)ᵀ)
            (errMap S.fullC S.R S.fullA Sinf)
            (S.innovWeight Sinf) T - Ginf‖ := by
      funext T
      rw [S.fwdGram_eq_sylvIter]
    rw [h1]
    exact htend
  refine ⟨Ginf, hfix, ?_, htend'⟩
  exact posSemidef_of_tendsto
    (fun T => S.fwdGram_posSemidef hSpsd T) htend'

set_option maxHeartbeats 800000 in
/-- **`cor:attract`**: whenever the homographic slide is uniformly
bounded, the closed form decays at the doubled Schur rate. -/
theorem formula_rate (hS : S.IsStrongSolution Sinf)
    {L₀ : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hL₀ : L₀.PosSemidef) {b' : ℝ}
    (hb' : ∀ T, ‖(1 + S.fwdGram Sinf T * (L₀ - Sinf))⁻¹‖ ≤ b')
    (hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf)) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧ γ < 1 ∧
      ∀ T, ‖S.dareFrom L₀ T - Sinf‖ ≤ C * (γ * γ) ^ T := by
  obtain ⟨c, γ, hc, hγ0, hγ1, hp⟩ := hFs.exists_pow_norm_le
  set K : ℝ := (Fintype.card (ix n₁ na nm) : ℝ) with hK
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hb'0 : 0 ≤ b' := le_trans (norm_nonneg _) (hb' 0)
  refine ⟨c * ‖L₀ - Sinf‖ * b' * (K * c), γ, by positivity,
    hγ0, hγ1, fun T => ?_⟩
  have heq := (S.formula hS hL₀ T).2
  have hsub : S.dareFrom L₀ T - Sinf
      = (errMap S.fullC S.R S.fullA Sinf) ^ T * (L₀ - Sinf)
        * (1 + S.fwdGram Sinf T * (L₀ - Sinf))⁻¹
        * ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T := by
    rw [heq]
    abel
  rw [hsub]
  have hTp : ‖((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T‖
      ≤ K * (c * γ ^ T) := by
    rw [← Matrix.transpose_pow]
    refine le_trans (linfty_opNorm_transpose_le' _) ?_
    exact mul_le_mul_of_nonneg_left (hp T) hK0
  calc ‖(errMap S.fullC S.R S.fullA Sinf) ^ T * (L₀ - Sinf)
      * (1 + S.fwdGram Sinf T * (L₀ - Sinf))⁻¹
      * ((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T‖
      ≤ ‖(errMap S.fullC S.R S.fullA Sinf) ^ T * (L₀ - Sinf)
          * (1 + S.fwdGram Sinf T * (L₀ - Sinf))⁻¹‖
        * ‖((errMap S.fullC S.R S.fullA Sinf)ᵀ) ^ T‖ :=
        Matrix.linfty_opNorm_mul _ _
  _ ≤ (c * γ ^ T * ‖L₀ - Sinf‖ * b') * (K * (c * γ ^ T)) := by
      refine mul_le_mul ?_ hTp (norm_nonneg _) (by positivity)
      calc ‖(errMap S.fullC S.R S.fullA Sinf) ^ T * (L₀ - Sinf)
          * (1 + S.fwdGram Sinf T * (L₀ - Sinf))⁻¹‖
          ≤ ‖(errMap S.fullC S.R S.fullA Sinf) ^ T‖
            * ‖L₀ - Sinf‖
            * ‖(1 + S.fwdGram Sinf T * (L₀ - Sinf))⁻¹‖ :=
            norm_triple_le _ _ _
      _ ≤ c * γ ^ T * ‖L₀ - Sinf‖ * b' := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hp T)
            (norm_nonneg _)) (hb' T) (norm_nonneg _) ?_
          positivity
  _ = c * ‖L₀ - Sinf‖ * b' * (K * c) * (γ * γ) ^ T := by
      rw [mul_pow]
      ring


end DareSystem

end Dare
end Estimation

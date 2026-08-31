import LeanForControl.Estimation.Dare.System
import LeanForControl.Estimation.Dare.StrongSolution
import Architect

/-!
# Structure of the strong solution (`lem:structure`-1 / `lem:structure-marg`, antistable positivity)

The `fact:dare-strong` import bundle (`IsStrongSolution`, carrying
only what the paper's Fact 1 supplies and this file consumes:
PSD + fixed point + `ρ(F∞) ≤ 1`), and the antistable positivity of
the strong solution: `Σ∞|ₐₐ ≻ 0`, marginal-inclusive — the shared
core of `lem:structure`-1 and `lem:structure-marg`, obtained from the
corner-kernel spectrum theorem against `1 < |spec(Aₐ)|`.
-/

namespace Estimation
namespace Dare
namespace DareSystem

open Matrix LinearSystems

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-! ### The antistable-corner embedding -/

/-- The inclusion of the antistable coordinates,
`E : ℝ^{nₐ} → e₁ ⊕ (eₐ ⊕ eₘ)`. -/
def embA (n₁ na nm : ℕ) : Matrix (ix n₁ na nm) (Fin na) ℝ :=
  Matrix.fromRows 0 (Matrix.fromRows 1 0)

/-- The intertwining `AᵀE = EAₐᵀ`: the antistable coordinates are
`Aᵀ`-coherent because `A` has `e₂`-row `[0 A₂]` and `A₂ = Aₐ ⊕ Aₘ`. -/
lemma fullA_transpose_mul_embA :
    S.fullAᵀ * embA n₁ na nm = embA n₁ na nm * S.Aaᵀ := by
  ext i j
  cases i with
  | inl i₁ =>
    simp [embA, fullA, A₂, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr]
  | inr i₂ =>
    cases i₂ with
    | inl ia =>
      simp [embA, fullA, A₂, Matrix.mul_apply, Matrix.transpose_apply,
        Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
        Matrix.fromRows_apply_inr, Matrix.one_apply]
    | inr im =>
      simp [embA, fullA, A₂, Matrix.mul_apply, Matrix.transpose_apply,
        Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
        Matrix.fromRows_apply_inr]

/-- The embedding is injective over ℂ. -/
lemma embA_complexify_injective (u : Fin na → ℂ)
    (h : complexify (embA n₁ na nm) *ᵥ u = 0) : u = 0 := by
  funext i
  have h1 := congrFun h (Sum.inr (Sum.inl i))
  simpa [embA, complexify_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply,
    apply_ite (Complex.ofReal), ite_mul, Finset.sum_ite_eq] using h1

/-- The embedded corner is the `(a,a)` diagonal block. -/
lemma embA_corner_eq (M : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) :
    (embA n₁ na nm)ᵀ * M * embA n₁ na nm = M.toBlocks₂₂.toBlocks₁₁ := by
  ext i j
  simp [embA, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply,
    Matrix.toBlocks₂₂, Matrix.toBlocks₁₁]

/-! ### The `fact:dare-strong` import bundle -/

/-- **The strong-solution bundle** (`fact:dare-strong`, minimal
fields): `Σ∞ ⪰ 0` solves the DARE and its error map has spectral
radius at most one. Existence, uniqueness, maximality, and the
spectrum split `eq:Finf-spec` are *not* bundled here — they are added
as separate hypotheses only where a consumer genuinely reads them
(sprint-plan risk R7 discipline). -/
structure IsStrongSolution
    (Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) : Prop where
  posSemidef : Sinf.PosSemidef
  fixed : dareStep S.fullC S.R S.fullA S.Qw Sinf = Sinf
  specLe : ∀ μ ∈ spectrum ℂ
    (complexify (errMap S.fullC S.R S.fullA Sinf)), ‖μ‖ ≤ 1

/-! ### Antistable positivity of the strong solution -/

/-- **`lem:structure`-1 / `lem:structure-marg`, the antistable
positivity** (marginal-inclusive): the strong solution is positive
definite on the antistable block. A kernel direction would hand the
error map an un-reflected antistable mode (`|μ| > 1`), contradicting
`ρ(F∞) ≤ 1`. Consumes only the bundle's three fields — not
`eq:Finf-spec`. -/
theorem strong_corner_posDef
    {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hS : S.IsStrongSolution Sinf) :
    ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm).PosDef := by
  have hpsd : ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm).PosSemidef := by
    have h := hS.posSemidef.conjTranspose_mul_mul_same (embA n₁ na nm)
    rwa [show (embA n₁ na nm)ᴴ = (embA n₁ na nm)ᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun v hv => ?_
  rcases lt_or_eq_of_le (hpsd.quadForm_nonneg v) with h | h
  · exact h
  · exfalso
    have hker : ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm) *ᵥ v = 0 :=
      hpsd.mulVec_eq_zero_of_quadForm_eq_zero h.symm
    obtain ⟨μ, hμAa, hμF⟩ := exists_common_spectrum_of_corner_kernel
      S.hR hS.posSemidef hS.fixed S.hQ rfl
      S.fullA_transpose_mul_embA embA_complexify_injective
      hv hker
    have h1 := S.hAnti μ hμAa
    have h2 := hS.specLe μ hμF
    linarith

/-- The antistable diagonal block of the strong solution is positive
definite (`eq:Sinf-struct` / the `Σ∞|ₐₐ ≻ 0` half of
`eq:marg-extinct`). -/
theorem strong_toBlocks_posDef
    {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hS : S.IsStrongSolution Sinf) :
    Sinf.toBlocks₂₂.toBlocks₁₁.PosDef := by
  rw [← embA_corner_eq]
  exact S.strong_corner_posDef hS

/-! ### Antistable positivity along the recursion (`lem:structure`-3) -/

/-- No noise reaches the antistable corner. -/
lemma embA_transpose_mul_fullG :
    (embA n₁ na nm)ᵀ * S.fullG = 0 := by
  ext i j
  simp [embA, fullG, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply]

lemma embA_Qw_corner :
    (embA n₁ na nm)ᵀ * S.Qw * (embA n₁ na nm) = 0 := by
  unfold Qw
  calc (embA n₁ na nm)ᵀ * (S.fullG * S.Q * S.fullGᵀ) * embA n₁ na nm
      = ((embA n₁ na nm)ᵀ * S.fullG) * S.Q
          * (S.fullGᵀ * embA n₁ na nm) := by
        simp only [Matrix.mul_assoc]
  _ = 0 := by
      rw [S.embA_transpose_mul_fullG]
      have h : S.fullGᵀ * embA n₁ na nm
          = ((embA n₁ na nm)ᵀ * S.fullG)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [h, S.embA_transpose_mul_fullG]
      simp

/-- The antistable block is nonsingular. -/
lemma isUnit_Aa_det : IsUnit S.Aa.det := by
  rw [isUnit_iff_ne_zero]
  refine LinearSystems.det_ne_zero_of_zero_notMem_spectrum fun h0 => ?_
  have := S.hAnti 0 h0
  rw [norm_zero] at this
  linarith

/-- **`lem:structure`-3** (seed-general): a positive-definite
antistable corner propagates along the whole recursion. -/
theorem dareFrom_corner_posDef
    {L : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ} (hL : L.PosSemidef)
    (hc : ((embA n₁ na nm)ᵀ * L * embA n₁ na nm).PosDef) :
    ∀ T, ((embA n₁ na nm)ᵀ * S.dareFrom L T * embA n₁ na nm).PosDef
  | 0 => hc
  | T + 1 => by
    have hpsd : (S.dareFrom L T).PosSemidef :=
      dareIter_posSemidef S.hR S.Qw_posSemidef hL T
    exact dareStep_corner_posDef S.hR hpsd
      (dareFrom_corner_posDef hL hc T) S.fullA_transpose_mul_embA
      S.embA_Qw_corner S.isUnit_Aa_det

/-- **`lem:structure`-3 under C2w**: along the run from the prior, the
antistable information `J_T = (Σ_T|ₐₐ)⁻¹` is well defined. -/
theorem dare_corner_posDef (hC2w : S.C2w) :
    ∀ T, ((embA n₁ na nm)ᵀ * S.dare T * embA n₁ na nm).PosDef := by
  refine S.dareFrom_corner_posDef S.Sig0_posSemidef ?_
  rw [embA_corner_eq]
  exact S.criterion_w.mp hC2w

/-! ### The fixed-point Stein relation (`eq:Sinf-gram`, relation form) -/

/-- The corner fixed-point identity:
`Σ∞|ₐₐ = Aa · U(Σ∞)|ₐₐ · Aaᵀ`. -/
theorem strong_corner_fixed
    {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hS : S.IsStrongSolution Sinf) :
    (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm
      = S.Aa * ((embA n₁ na nm)ᵀ
          * updM S.fullC S.R Sinf * embA n₁ na nm) * S.Aaᵀ := by
  conv_lhs => rw [← hS.fixed]
  exact dareStep_corner_eq S.fullA_transpose_mul_embA S.embA_Qw_corner

/-- **`eq:Sinf-gram`, relation form**: the antistable information of
the strong solution satisfies the `Aa⁻¹`-Stein relation
`J∞ = Aa⁻ᵀ·(U-corner)⁻¹·Aa⁻¹` with a PSD injection
`(U-corner)⁻¹ − J∞ ⪰ 0`. (The unrolled gramian series is deferred to
its Phase-B consumer.) -/
theorem strong_stein
    {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hS : S.IsStrongSolution Sinf) :
    ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
      = (S.Aa⁻¹)ᵀ * ((embA n₁ na nm)ᵀ
          * updM S.fullC S.R Sinf * embA n₁ na nm)⁻¹ * S.Aa⁻¹
    ∧ (((embA n₁ na nm)ᵀ
          * updM S.fullC S.R Sinf * embA n₁ na nm)⁻¹
        - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹).PosSemidef := by
  have hUc : ((embA n₁ na nm)ᵀ
      * updM S.fullC S.R Sinf * embA n₁ na nm).PosDef :=
    updM_corner_posDef S.hR hS.posSemidef (S.strong_corner_posDef hS)
  constructor
  · rw [S.strong_corner_fixed hS, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_assoc]
  · have hcontr : ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm
        - (embA n₁ na nm)ᵀ * updM S.fullC S.R Sinf * embA n₁ na nm).PosSemidef := by
      have heq : (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm
          - (embA n₁ na nm)ᵀ * updM S.fullC S.R Sinf * embA n₁ na nm
          = (embA n₁ na nm)ᵀ * (Sinf - updM S.fullC S.R Sinf)
              * embA n₁ na nm := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [heq]
      have h := (sub_updM_posSemidef (C := S.fullC) S.hR
        hS.posSemidef).conjTranspose_mul_mul_same (embA n₁ na nm)
      rwa [show (embA n₁ na nm)ᴴ = (embA n₁ na nm)ᵀ from
        Matrix.conjTranspose_eq_transpose_of_trivial _] at h
    exact posSemidef_inv_sub_inv hUc (S.strong_corner_posDef hS) hcontr

end DareSystem
end Dare
end Estimation
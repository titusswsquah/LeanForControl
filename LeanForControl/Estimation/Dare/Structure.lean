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

end DareSystem
end Dare
end Estimation
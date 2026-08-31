import LeanForControl.Estimation.Dare.Supremal
import Architect

/-!
# The slaved seed (`lem:slaved-seed`, `eq:Ldef-slaved`)

The C2w-tight, rank-minimal lower initial condition: strip the prior
to its antistable-supported part `Σ₂⁽ᵃ⁾ = [I;Λ₀]·Σₐ·[I;Λ₀]ᵀ`
(`Λ₀ = Σₘₐ·Σₐ⁻¹`), scale by `δ ∈ (0,1]`, zero the stabilizable block.
It sits below every prior (the marginal Schur complement is what gets
removed), its antistable corner is `δ·Σₐ ≻ 0` exactly under C2w
(`eq:Lc2w` = the verified `criterion_w`), and its marginal row is
slaved to the antistable row (`eq:seed-slaved`) — the base case of
`lem:loading`.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

/-- Block expansion of a quadratic form over a sum index. -/
lemma quadForm_elim {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix (α ⊕ β) (α ⊕ β) ℝ) (u : α → ℝ) (v : β → ℝ) :
    quadForm M (Sum.elim u v)
      = quadForm M.toBlocks₁₁ u + u ⬝ᵥ (M.toBlocks₁₂ *ᵥ v)
        + v ⬝ᵥ (M.toBlocks₂₁ *ᵥ u) + quadForm M.toBlocks₂₂ v := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, mul_add,
    Finset.sum_add_distrib]
  ring

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The seed loading `Λ₀ = Σₘₐ·Σₐ⁻¹`. -/
noncomputable def lam0 : Matrix (Fin nm) (Fin na) ℝ :=
  S.Sig₂.toBlocks₂₁ * S.Siga⁻¹

/-- The column factor `[I; Λ₀]`. -/
noncomputable def lamCol : Matrix (Fin na ⊕ Fin nm) (Fin na) ℝ :=
  Matrix.fromRows 1 S.lam0

/-- The slaved antistable part `Σ₂⁽ᵃ⁾` (`eq:Sig2a`), written
blockwise. -/
noncomputable def sig2a : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ :=
  Matrix.fromBlocks S.Siga S.Sig₂.toBlocks₁₂
    S.Sig₂.toBlocks₂₁ (S.lam0 * S.Sig₂.toBlocks₁₂)

/-- The slaved seed (`eq:Ldef-slaved`). -/
noncomputable def slavedSeed (δ : ℝ) :
    Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  Matrix.fromBlocks 0 0 0 (δ • S.sig2a)

/-- The prior's cross blocks are transposes of one another. -/
lemma Sig₂_toBlocks₁₂_eq :
    S.Sig₂.toBlocks₁₂ = (S.Sig₂.toBlocks₂₁)ᵀ := by
  ext i j
  have h : S.Sig₂ (Sum.inl i) (Sum.inr j)
      = S.Sig₂ᵀ (Sum.inr j) (Sum.inl i) := rfl
  simp only [Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.of_apply,
    Matrix.transpose_apply]
  rw [h, S.hSig₂.1.transpose_eq_self]

lemma lam0_mul_Siga (hSa : S.Siga.PosDef) :
    S.lam0 * S.Siga = S.Sig₂.toBlocks₂₁ := by
  unfold lam0
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp hSa.isUnit), Matrix.mul_one]

lemma Siga_mul_lam0t (hSa : S.Siga.PosDef) :
    S.Siga * S.lam0ᵀ = S.Sig₂.toBlocks₁₂ := by
  have h := congrArg Matrix.transpose (S.lam0_mul_Siga hSa)
  rw [Matrix.transpose_mul, hSa.posSemidef.1.transpose_eq_self] at h
  rw [h, ← S.Sig₂_toBlocks₁₂_eq]

/-- `Σ₂⁽ᵃ⁾` as the conjugation `[I;Λ₀]·Σₐ·[I;Λ₀]ᵀ` (`eq:Sig2a`). -/
lemma sig2a_eq_conj (hSa : S.Siga.PosDef) :
    S.sig2a = S.lamCol * S.Siga * S.lamColᵀ := by
  unfold sig2a lamCol
  rw [Matrix.fromRows_mul, Matrix.transpose_fromRows,
    Matrix.transpose_one, Matrix.fromRows_mul_fromCols]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc S.lam0 S.Siga S.lam0ᵀ, S.Siga_mul_lam0t hSa,
    S.lam0_mul_Siga hSa]

lemma sig2a_posSemidef (hSa : S.Siga.PosDef) :
    S.sig2a.PosSemidef := by
  rw [S.sig2a_eq_conj hSa]
  have h := hSa.posSemidef.mul_mul_conjTranspose_same S.lamCol
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The conditional decomposition of the prior's quadratic form:
`x'Σ₂x = (u + Λ₀ᵀv)'Σₐ(u + Λ₀ᵀv) + v'·Smar·v`, with the marginal
Schur complement `Smar = Σₘₘ − Λ₀·Σₐₘ`. -/
lemma Sig₂_quadForm_decomp (hSa : S.Siga.PosDef)
    (u : Fin na → ℝ) (v : Fin nm → ℝ) :
    quadForm S.Sig₂ (Sum.elim u v)
      = quadForm S.Siga (u + S.lam0ᵀ *ᵥ v)
        + quadForm (S.Sig₂.toBlocks₂₂ - S.lam0 * S.Sig₂.toBlocks₁₂)
            v := by
  rw [quadForm_elim]
  have h1 : quadForm S.Siga (u + S.lam0ᵀ *ᵥ v)
      = quadForm S.Siga u + u ⬝ᵥ (S.Sig₂.toBlocks₁₂ *ᵥ v)
        + v ⬝ᵥ (S.Sig₂.toBlocks₂₁ *ᵥ u)
        + v ⬝ᵥ ((S.lam0 * S.Sig₂.toBlocks₁₂) *ᵥ v) := by
    unfold quadForm
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct,
      add_dotProduct]
    have h2 : S.Siga *ᵥ (S.lam0ᵀ *ᵥ v) = S.Sig₂.toBlocks₁₂ *ᵥ v := by
      rw [Matrix.mulVec_mulVec, S.Siga_mul_lam0t hSa]
    have h3 : (S.lam0ᵀ *ᵥ v) ⬝ᵥ (S.Siga *ᵥ u)
        = v ⬝ᵥ (S.Sig₂.toBlocks₂₁ *ᵥ u) := by
      rw [← dotProduct_mulVec_eq S.lam0 v (S.Siga *ᵥ u),
        Matrix.mulVec_mulVec, S.lam0_mul_Siga hSa]
    have h4 : (S.lam0ᵀ *ᵥ v) ⬝ᵥ (S.Sig₂.toBlocks₁₂ *ᵥ v)
        = v ⬝ᵥ ((S.lam0 * S.Sig₂.toBlocks₁₂) *ᵥ v) := by
      rw [← dotProduct_mulVec_eq S.lam0 v (S.Sig₂.toBlocks₁₂ *ᵥ v),
        Matrix.mulVec_mulVec]
    rw [h2, h3, h4]
    ring
  have h5 : quadForm (S.Sig₂.toBlocks₂₂ - S.lam0 * S.Sig₂.toBlocks₁₂) v
      = quadForm S.Sig₂.toBlocks₂₂ v
        - v ⬝ᵥ ((S.lam0 * S.Sig₂.toBlocks₁₂) *ᵥ v) := by
    unfold quadForm
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [h1, h5]
  unfold Siga
  ring

/-- The marginal Schur complement is PSD. -/
lemma smar_posSemidef (hSa : S.Siga.PosDef) :
    (S.Sig₂.toBlocks₂₂ - S.lam0 * S.Sig₂.toBlocks₁₂).PosSemidef := by
  have hherm : (S.Sig₂.toBlocks₂₂
      - S.lam0 * S.Sig₂.toBlocks₁₂).IsHermitian := by
    have h1 : (S.Sig₂.toBlocks₂₂).IsHermitian := by
      ext i j
      have h : S.Sig₂ (Sum.inr i) (Sum.inr j)
          = S.Sig₂ᵀ (Sum.inr j) (Sum.inr i) := rfl
      simp only [Matrix.conjTranspose_apply, Matrix.toBlocks₂₂,
        Matrix.of_apply, star_trivial]
      rw [h, S.hSig₂.1.transpose_eq_self]
    have h2 : (S.lam0 * S.Sig₂.toBlocks₁₂)ᵀ
        = S.lam0 * S.Sig₂.toBlocks₁₂ := by
      rw [S.Sig₂_toBlocks₁₂_eq]
      unfold lam0
      rw [Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose,
        (Matrix.PosDef.posSemidef hSa.inv).1.transpose_eq_self]
      simp only [Matrix.mul_assoc]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_sub, h2]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      at h1
    rw [h1]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v => ?_
  rw [star_trivial]
  have h := S.Sig₂_quadForm_decomp hSa (-(S.lam0ᵀ *ᵥ v)) v
  rw [neg_add_cancel] at h
  have h0 : quadForm S.Siga 0 = 0 := by
    simp [quadForm]
  rw [h0, zero_add] at h
  have h1 := S.hSig₂.quadForm_nonneg (Sum.elim (-(S.lam0ᵀ *ᵥ v)) v)
  rw [h] at h1
  exact h1

/-- **`lem:slaved-seed`-1** at the `e₂` level: `Σ₂ − δ·Σ₂⁽ᵃ⁾ ⪰ 0` for
`δ ∈ [0,1]`. -/
lemma Sig₂_sub_smul_sig2a_posSemidef (hSa : S.Siga.PosDef)
    {δ : ℝ} (hδ1 : δ ≤ 1) :
    (S.Sig₂ - δ • S.sig2a).PosSemidef := by
  have hdecomp : S.Sig₂ - δ • S.sig2a
      = (1 - δ) • S.sig2a
        + Matrix.fromBlocks 0 0 0
            (S.Sig₂.toBlocks₂₂ - S.lam0 * S.Sig₂.toBlocks₁₂) := by
    have hblocks : S.Sig₂ - S.sig2a
        = Matrix.fromBlocks 0 0 0
            (S.Sig₂.toBlocks₂₂ - S.lam0 * S.Sig₂.toBlocks₁₂) := by
      ext i j
      rcases i with i₁ | i₂ <;> rcases j with j₁ | j₂ <;>
        simp [sig2a, Siga, Matrix.sub_apply, Matrix.fromBlocks,
          Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
          Matrix.toBlocks₂₂]
    have h : S.Sig₂ - δ • S.sig2a
        = (1 - δ) • S.sig2a + (S.Sig₂ - S.sig2a) := by
      rw [sub_smul, one_smul]
      abel
    rw [h, hblocks]
  rw [hdecomp]
  refine Matrix.PosSemidef.add
    ((S.sig2a_posSemidef hSa).smul (by linarith)) ?_
  have hsm := S.smar_posSemidef hSa
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_zero]
    rw [hsm.1]
  · rw [star_trivial]
    have hx : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by
      funext i
      cases i <;> rfl
    rw [hx]
    have hd := quadForm_elim (Matrix.fromBlocks 0 0 0
      (S.Sig₂.toBlocks₂₂ - S.lam0 * S.Sig₂.toBlocks₁₂))
      (x ∘ Sum.inl) (x ∘ Sum.inr)
    have hq : quadForm (Matrix.fromBlocks (0 : Matrix (Fin na) (Fin na) ℝ)
        0 0 (S.Sig₂.toBlocks₂₂ - S.lam0 * S.Sig₂.toBlocks₁₂))
        (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr))
        = quadForm (S.Sig₂.toBlocks₂₂ - S.lam0 * S.Sig₂.toBlocks₁₂)
            (x ∘ Sum.inr) := by
      rw [hd]
      simp [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
        Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
        quadForm]
    have h2 : (0:ℝ) ≤ quadForm (Matrix.fromBlocks 0 0 0
        (S.Sig₂.toBlocks₂₂ - S.lam0 * S.Sig₂.toBlocks₁₂))
        (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr)) := by
      rw [hq]
      exact hsm.quadForm_nonneg _
    exact h2

/-- **`lem:slaved-seed`-1**: the slaved seed sits below the prior,
for every prior. -/
theorem slavedSeed_le_Sig0 (hSa : S.Siga.PosDef)
    {δ : ℝ} (hδ1 : δ ≤ 1) :
    (S.Sig0 - S.slavedSeed δ).PosSemidef := by
  have hblocks : S.Sig0 - S.slavedSeed δ
      = Matrix.fromBlocks S.Sig₁ 0 0 (S.Sig₂ - δ • S.sig2a) := by
    unfold Sig0 slavedSeed
    ext i j
    rcases i with i₁ | i₂ <;> rcases j with j₁ | j₂ <;>
      simp [Matrix.sub_apply, Matrix.fromBlocks]
  rw [hblocks]
  have h22 := S.Sig₂_sub_smul_sig2a_posSemidef hSa hδ1
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_zero]
    rw [S.hSig₁.1, h22.1]
  · rw [star_trivial]
    have hd : x ⬝ᵥ (Matrix.fromBlocks S.Sig₁ 0 0
          (S.Sig₂ - δ • S.sig2a) *ᵥ x)
        = quadForm S.Sig₁ (x ∘ Sum.inl)
          + quadForm (S.Sig₂ - δ • S.sig2a) (x ∘ Sum.inr) := by
      simp [quadForm, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
        Matrix.fromBlocks, Finset.mul_sum]
    rw [hd]
    exact add_nonneg (S.hSig₁.quadForm_nonneg _) (h22.quadForm_nonneg _)

lemma slavedSeed_posSemidef (hSa : S.Siga.PosDef) {δ : ℝ}
    (hδ0 : 0 ≤ δ) : (S.slavedSeed δ).PosSemidef := by
  unfold slavedSeed
  have h22 := (S.sig2a_posSemidef hSa).smul hδ0
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_zero]
    rw [h22.1]
  · rw [star_trivial]
    have hd : x ⬝ᵥ (Matrix.fromBlocks 0 0 0 (δ • S.sig2a) *ᵥ x)
        = quadForm (δ • S.sig2a) (x ∘ Sum.inr) := by
      simp [quadForm, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
        Matrix.fromBlocks]
    rw [hd]
    exact h22.quadForm_nonneg _

/-- **`lem:slaved-seed`-2 (`eq:Lc2w`)**: the seed's antistable corner
is `δ·Σₐ` — positive definite for `δ > 0` exactly under C2w
(`criterion_w`). -/
lemma slavedSeed_corner (δ : ℝ) :
    (embA n₁ na nm)ᵀ * S.slavedSeed δ * embA n₁ na nm = δ • S.Siga := by
  ext i j
  unfold slavedSeed sig2a embA
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.transpose_apply, Matrix.fromBlocks, Matrix.one_apply,
    mul_ite, ite_mul]

lemma slavedSeed_corner_posDef (hC2w : S.C2w) {δ : ℝ} (hδ : 0 < δ) :
    ((embA n₁ na nm)ᵀ * S.slavedSeed δ * embA n₁ na nm).PosDef := by
  rw [S.slavedSeed_corner δ]
  exact (S.criterion_w.mp hC2w).smul hδ

/-- Left-multiplying by `embMᵀ` selects the marginal rows. -/
lemma embM_transpose_mul {κ : Type*} [Fintype κ]
    (M : Matrix (ix n₁ na nm) κ ℝ) :
    (embM n₁ na nm)ᵀ * M
      = Matrix.of fun j k => M (Sum.inr (Sum.inr j)) k := by
  ext j k
  unfold embM
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.transpose_apply, Matrix.one_apply, Finset.sum_ite_eq']

/-- Left-multiplying by `embAᵀ` selects the antistable rows. -/
lemma embA_transpose_mul {κ : Type*} [Fintype κ]
    (M : Matrix (ix n₁ na nm) κ ℝ) :
    (embA n₁ na nm)ᵀ * M
      = Matrix.of fun i k => M (Sum.inr (Sum.inl i)) k := by
  ext i k
  unfold embA
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.transpose_apply, Matrix.one_apply, Finset.sum_ite_eq']

/-- **`lem:slaved-seed`-3 (`eq:seed-slaved`)**: the marginal row of
the seed is slaved to the antistable row by `Λ₀`. -/
theorem slavedSeed_slaved (hSa : S.Siga.PosDef) (δ : ℝ) :
    (embM n₁ na nm)ᵀ * S.slavedSeed δ
      = S.lam0 * ((embA n₁ na nm)ᵀ * S.slavedSeed δ) := by
  rw [embM_transpose_mul, embA_transpose_mul]
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rcases k with k₁ | k₂
  · unfold slavedSeed
    simp [Matrix.fromBlocks]
  · rcases k₂ with ka | km
    · show (S.slavedSeed δ) (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inl ka))
        = ∑ i, S.lam0 j i
            * (S.slavedSeed δ) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl ka))
      unfold slavedSeed sig2a
      simp only [Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₁₁,
        smul_eq_mul]
      have h : S.Sig₂.toBlocks₂₁ j ka
          = ∑ i, S.lam0 j i * S.Siga i ka := by
        rw [← Matrix.mul_apply, S.lam0_mul_Siga hSa]
      rw [h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · show (S.slavedSeed δ) (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inr km))
        = ∑ i, S.lam0 j i
            * (S.slavedSeed δ) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr km))
      unfold slavedSeed sig2a
      simp only [Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
        Matrix.fromBlocks_apply₁₂, smul_eq_mul]
      have h : (S.lam0 * S.Sig₂.toBlocks₁₂) j km
          = ∑ i, S.lam0 j i * S.Sig₂.toBlocks₁₂ i km :=
        Matrix.mul_apply
      rw [h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

end DareSystem

end Dare
end Estimation

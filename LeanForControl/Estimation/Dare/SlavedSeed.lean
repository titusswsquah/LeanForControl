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
lemma embM_transpose_mul {κ : Type*}
    (M : Matrix (ix n₁ na nm) κ ℝ) :
    (embM n₁ na nm)ᵀ * M
      = Matrix.of fun j k => M (Sum.inr (Sum.inr j)) k := by
  ext j k
  unfold embM
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.transpose_apply, Matrix.one_apply, Finset.sum_ite_eq']

/-- Left-multiplying by `embAᵀ` selects the antistable rows. -/
lemma embA_transpose_mul {κ : Type*}
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

/-! ### The pseudoinverse-free loading (`lem:slaved-seed`-1, general form)

The deck states `eq:Sig2a` with the Moore–Penrose pseudoinverse
`Λ₀ = Σₘₐ·Σₐₐ^†`. The pseudoinverse is only notational: all the lemma
needs is **a** loading `Λ₀` with `Σₘₐ = Λ₀·Σₐₐ`, and for a PSD prior one
always exists (`range Σₐₘ ⊆ range Σₐₐ`). We verify the existence by the
normal-equation rank argument — no pseudoinverse, no C2w — and rebuild
the seed and Part 1 from an arbitrary loading. -/

section GeneralLoading

variable {α β : Type*} [Fintype α] [Fintype β]

/-- For a PSD block matrix `[[A,B],[Bᵀ,C]]`, the kernel of `A` is
annihilated by the cross block: `A·x = 0 ⇒ Bᵀ·x = 0`. -/
lemma toBlocks_kernel_incl {M : Matrix (α ⊕ β) (α ⊕ β) ℝ}
    (hM : M.PosSemidef) {x : α → ℝ} (hx : M.toBlocks₁₁ *ᵥ x = 0) :
    (M.toBlocks₁₂)ᵀ *ᵥ x = 0 := by
  have hB21 : M.toBlocks₂₁ = (M.toBlocks₁₂)ᵀ := by
    ext i j
    have h : M (Sum.inr i) (Sum.inl j) = Mᵀ (Sum.inl j) (Sum.inr i) := rfl
    simp only [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.of_apply,
      Matrix.transpose_apply]
    rw [h, hM.1.transpose_eq_self]
  have hpsd22 : ∀ v : β → ℝ, 0 ≤ quadForm M.toBlocks₂₂ v := by
    intro v
    have h0 := hM.quadForm_nonneg (Sum.elim (0 : α → ℝ) v)
    rw [quadForm_elim] at h0
    simpa using h0
  have hzero : ∀ v : β → ℝ, x ⬝ᵥ (M.toBlocks₁₂ *ᵥ v) = 0 := by
    intro v
    set a := x ⬝ᵥ (M.toBlocks₁₂ *ᵥ v) with ha
    set c := quadForm M.toBlocks₂₂ v with hc
    have hcnn : 0 ≤ c := hpsd22 v
    have key : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * c := by
      intro t
      have h0 := hM.quadForm_nonneg (Sum.elim x (t • v))
      rw [quadForm_elim] at h0
      have h1 : quadForm M.toBlocks₁₁ x = 0 := by
        rw [quadForm, hx, dotProduct_zero]
      have h2 : x ⬝ᵥ (M.toBlocks₁₂ *ᵥ (t • v)) = t * a := by
        rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, ha]
      have h3 : (t • v) ⬝ᵥ (M.toBlocks₂₁ *ᵥ x) = t * a := by
        rw [hB21, smul_dotProduct, smul_eq_mul, dotProduct_comm,
          mulVec_dotProduct_eq, Matrix.transpose_transpose, ha]
      have h4 : quadForm M.toBlocks₂₂ (t • v) = t ^ 2 * c := by
        rw [quadForm_smul, hc]
      rw [h1, h2, h3, h4] at h0
      linarith
    have hc1 : (0:ℝ) < c + 1 := by linarith
    have h5 : a * a * (c + 2) ≤ 0 := by
      have h6 := key (-(a / (c + 1)))
      have h7 : (0:ℝ) < (c + 1) ^ 2 := by positivity
      have h8 : 0 ≤ (2 * (-(a / (c + 1))) * a + (-(a / (c + 1))) ^ 2 * c)
          * (c + 1) ^ 2 := mul_nonneg h6 h7.le
      have h9 : (2 * (-(a / (c + 1))) * a + (-(a / (c + 1))) ^ 2 * c)
          * (c + 1) ^ 2 = -(a * a * (c + 2)) := by
        field_simp
        ring
      rw [h9] at h8
      linarith
    have h6 : a * a ≤ 0 := by
      have h7 : 0 ≤ a * a * c := mul_nonneg (mul_self_nonneg a) hcnn
      nlinarith [h5, h7]
    have h7 : a * a = 0 := le_antisymm h6 (mul_self_nonneg a)
    exact mul_self_eq_zero.mp h7
  have hw := hzero ((M.toBlocks₁₂)ᵀ *ᵥ x)
  rw [dotProduct_mulVec_eq] at hw
  exact dotProduct_self_eq_zero.mp hw

/-- **Existential loading**: for a PSD block matrix the cross block lies
in the range of the `(1,1)` block — `∃ Z, A·Z = B`. The normal-equation
rank argument: `ker A ⊆ ker Bᵀ` forces `rank [A B] = rank A`, so the
column space of `[A B]` *is* the column space of `A`. -/
theorem exists_loading_of_posSemidef [DecidableEq α] [DecidableEq β]
    {M : Matrix (α ⊕ β) (α ⊕ β) ℝ} (hM : M.PosSemidef) :
    ∃ Z : Matrix α β ℝ, M.toBlocks₁₁ * Z = M.toBlocks₁₂ := by
  set A := M.toBlocks₁₁ with hA
  set B := M.toBlocks₁₂ with hB
  have hAsymm : Aᵀ = A := by
    ext i j
    have h : M (Sum.inl j) (Sum.inl i) = Mᵀ (Sum.inl i) (Sum.inl j) := rfl
    show M (Sum.inl j) (Sum.inl i) = M (Sum.inl i) (Sum.inl j)
    rw [h, hM.1.transpose_eq_self]
  -- the juxtaposition [A B] has the kernel of A (transposed picture)
  have hker : LinearMap.ker (Matrix.fromRows Aᵀ Bᵀ).mulVecLin
      = LinearMap.ker A.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      Matrix.fromRows_mulVec]
    constructor
    · intro h
      have h1 : (Aᵀ *ᵥ x) = 0 := funext fun i => congrFun h (Sum.inl i)
      rwa [hAsymm] at h1
    · intro h
      have h2 : Bᵀ *ᵥ x = 0 := toBlocks_kernel_incl hM h
      funext i
      cases i with
      | inl i =>
          show (Aᵀ *ᵥ x) i = 0
          rw [hAsymm, h]
          rfl
      | inr j =>
          show (Bᵀ *ᵥ x) j = 0
          rw [h2]
          rfl
  -- equal kernels ⇒ equal range dimensions (rank–nullity)
  have hfr : Module.finrank ℝ
        (LinearMap.range (Matrix.fromRows Aᵀ Bᵀ).mulVecLin)
      = Module.finrank ℝ (LinearMap.range A.mulVecLin) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (Matrix.fromRows Aᵀ Bᵀ).mulVecLin
    have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hker] at h1
    omega
  -- transpose: rank [A B] = rank A
  have htr : (Matrix.fromRows Aᵀ Bᵀ).rank = (Matrix.fromCols A B).rank := by
    rw [← Matrix.transpose_fromCols]
    exact Matrix.rank_transpose _
  have hfeq : Module.finrank ℝ (LinearMap.range A.mulVecLin)
      = Module.finrank ℝ
          (LinearMap.range (Matrix.fromCols A B).mulVecLin) := by
    have e1 : (Matrix.fromCols A B).rank
        = Module.finrank ℝ
            (LinearMap.range (Matrix.fromCols A B).mulVecLin) := rfl
    have e2 : (Matrix.fromRows Aᵀ Bᵀ).rank
        = Module.finrank ℝ
            (LinearMap.range (Matrix.fromRows Aᵀ Bᵀ).mulVecLin) := rfl
    rw [← e1, ← htr, e2, hfr]
  -- range inclusion + equal dimension ⇒ equal ranges
  have hle : LinearMap.range A.mulVecLin
      ≤ LinearMap.range (Matrix.fromCols A B).mulVecLin := by
    rintro y ⟨x, rfl⟩
    exact ⟨Sum.elim x 0, by
      show Matrix.fromCols A B *ᵥ Sum.elim x 0 = A *ᵥ x
      rw [Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, add_zero]⟩
  have hreq := Submodule.eq_of_le_of_finrank_eq hle hfeq
  -- read off the columns of B
  have hcol : ∀ j : β, ∃ z : α → ℝ, A *ᵥ z = B *ᵥ Pi.single j 1 := by
    intro j
    have hmem : B *ᵥ Pi.single j 1
        ∈ LinearMap.range (Matrix.fromCols A B).mulVecLin :=
      ⟨Sum.elim 0 (Pi.single j 1), by
        show Matrix.fromCols A B *ᵥ Sum.elim 0 (Pi.single j 1)
          = B *ᵥ Pi.single j 1
        rw [Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, zero_add]⟩
    rw [← hreq] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, by simpa using hz⟩
  choose z hz using hcol
  refine ⟨Matrix.of (fun i j => z j i), ?_⟩
  ext i j
  have h1 : (A * Matrix.of (fun i j => z j i)) i j = (A *ᵥ z j) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, hz j, Matrix.mulVec_single_one]
  rfl

end GeneralLoading

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- `Σₐₐ` is symmetric. -/
lemma Siga_transpose : S.Sigaᵀ = S.Siga := by
  ext i j
  have h : S.Sig₂ (Sum.inl j) (Sum.inl i)
      = S.Sig₂ᵀ (Sum.inl i) (Sum.inl j) := rfl
  show S.Sig₂ (Sum.inl j) (Sum.inl i) = S.Sig₂ (Sum.inl i) (Sum.inl j)
  rw [h, S.hSig₂.1.transpose_eq_self]

/-- **`lem:slaved-seed`-1, existential loading**: every PSD prior admits
a loading `Λ₀` with `Σₘₐ = Λ₀·Σₐₐ` — no pseudoinverse, no C2w. -/
theorem exists_loading :
    ∃ L : Matrix (Fin nm) (Fin na) ℝ,
      S.Sig₂.toBlocks₂₁ = L * S.Siga := by
  obtain ⟨Z, hZ⟩ := exists_loading_of_posSemidef S.hSig₂
  refine ⟨Zᵀ, ?_⟩
  show S.Sig₂.toBlocks₂₁ = Zᵀ * S.Sig₂.toBlocks₁₁
  have h := congrArg Matrix.transpose hZ
  rw [Matrix.transpose_mul] at h
  have htt : (S.Sig₂.toBlocks₁₁)ᵀ = S.Sig₂.toBlocks₁₁ := S.Siga_transpose
  have h12 : (S.Sig₂.toBlocks₁₂)ᵀ = S.Sig₂.toBlocks₂₁ := by
    rw [S.Sig₂_toBlocks₁₂_eq, Matrix.transpose_transpose]
  rw [htt, h12] at h
  exact h.symm

variable {L : Matrix (Fin nm) (Fin na) ℝ}

/-- The slaved antistable part built from an arbitrary loading
(`eq:Sig2a`, general form): `[I;Λ₀]·Σₐₐ·[I;Λ₀]ᵀ` written blockwise. -/
noncomputable def sig2aOf (L : Matrix (Fin nm) (Fin na) ℝ) :
    Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ :=
  Matrix.fromBlocks S.Siga (S.Siga * Lᵀ) (L * S.Siga) (L * S.Siga * Lᵀ)

/-- The general slaved seed (`eq:Ldef-slaved`, pseudoinverse-free). -/
noncomputable def slavedSeedOf (L : Matrix (Fin nm) (Fin na) ℝ) (δ : ℝ) :
    Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  Matrix.fromBlocks 0 0 0 (δ • S.sig2aOf L)

/-- `Σ₂⁽ᵃ⁾(Λ₀)` as the conjugation `[I;Λ₀]·Σₐₐ·[I;Λ₀]ᵀ` — no condition. -/
lemma sig2aOf_eq_conj (L : Matrix (Fin nm) (Fin na) ℝ) :
    S.sig2aOf L
      = Matrix.fromRows (1 : Matrix (Fin na) (Fin na) ℝ) L * S.Siga
        * (Matrix.fromRows (1 : Matrix (Fin na) (Fin na) ℝ) L)ᵀ := by
  unfold sig2aOf
  rw [Matrix.fromRows_mul, Matrix.transpose_fromRows, Matrix.transpose_one,
    Matrix.fromRows_mul_fromCols]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- `Σₐₐ` is PSD for every prior (no C2w). -/
lemma Siga_posSemidef : S.Siga.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      S.Siga_transpose]
  · rw [star_trivial]
    have h0 := S.hSig₂.quadForm_nonneg (Sum.elim x (0 : Fin nm → ℝ))
    rw [quadForm_elim] at h0
    simpa [quadForm] using h0

lemma sig2aOf_posSemidef (L : Matrix (Fin nm) (Fin na) ℝ) :
    (S.sig2aOf L).PosSemidef := by
  rw [S.sig2aOf_eq_conj]
  have h := S.Siga_posSemidef.mul_mul_conjTranspose_same
    (Matrix.fromRows (1 : Matrix (Fin na) (Fin na) ℝ) L)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The conditional decomposition of the prior's quadratic form, general
loading: needs only `Σₘₐ = Λ₀·Σₐₐ`. -/
lemma Sig₂_quadForm_decompOf (hL : S.Sig₂.toBlocks₂₁ = L * S.Siga)
    (u : Fin na → ℝ) (v : Fin nm → ℝ) :
    quadForm S.Sig₂ (Sum.elim u v)
      = quadForm S.Siga (u + Lᵀ *ᵥ v)
        + quadForm (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂) v := by
  have hB : S.Siga * Lᵀ = S.Sig₂.toBlocks₁₂ := by
    have h := congrArg Matrix.transpose hL
    rw [Matrix.transpose_mul, S.Siga_transpose] at h
    rw [← h, ← S.Sig₂_toBlocks₁₂_eq]
  rw [quadForm_elim]
  have h1 : quadForm S.Siga (u + Lᵀ *ᵥ v)
      = quadForm S.Siga u + u ⬝ᵥ (S.Sig₂.toBlocks₁₂ *ᵥ v)
        + v ⬝ᵥ (S.Sig₂.toBlocks₂₁ *ᵥ u)
        + v ⬝ᵥ ((L * S.Sig₂.toBlocks₁₂) *ᵥ v) := by
    unfold quadForm
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
    have h2 : S.Siga *ᵥ (Lᵀ *ᵥ v) = S.Sig₂.toBlocks₁₂ *ᵥ v := by
      rw [Matrix.mulVec_mulVec, hB]
    have h3 : (Lᵀ *ᵥ v) ⬝ᵥ (S.Siga *ᵥ u)
        = v ⬝ᵥ (S.Sig₂.toBlocks₂₁ *ᵥ u) := by
      rw [← dotProduct_mulVec_eq L v (S.Siga *ᵥ u),
        Matrix.mulVec_mulVec, ← hL]
    have h4 : (Lᵀ *ᵥ v) ⬝ᵥ (S.Sig₂.toBlocks₁₂ *ᵥ v)
        = v ⬝ᵥ ((L * S.Sig₂.toBlocks₁₂) *ᵥ v) := by
      rw [← dotProduct_mulVec_eq L v (S.Sig₂.toBlocks₁₂ *ᵥ v),
        Matrix.mulVec_mulVec]
    rw [h2, h3, h4]
    ring
  have h5 : quadForm (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂) v
      = quadForm S.Sig₂.toBlocks₂₂ v
        - v ⬝ᵥ ((L * S.Sig₂.toBlocks₁₂) *ᵥ v) := by
    unfold quadForm
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [h1, h5]
  unfold Siga
  ring

/-- The generalized marginal Schur complement is PSD. -/
lemma smarOf_posSemidef (hL : S.Sig₂.toBlocks₂₁ = L * S.Siga) :
    (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂).PosSemidef := by
  have hB : S.Siga * Lᵀ = S.Sig₂.toBlocks₁₂ := by
    have h := congrArg Matrix.transpose hL
    rw [Matrix.transpose_mul, S.Siga_transpose] at h
    rw [← h, ← S.Sig₂_toBlocks₁₂_eq]
  have hherm : (S.Sig₂.toBlocks₂₂
      - L * S.Sig₂.toBlocks₁₂).IsHermitian := by
    have h1 : (S.Sig₂.toBlocks₂₂).IsHermitian := by
      ext i j
      have h : S.Sig₂ (Sum.inr i) (Sum.inr j)
          = S.Sig₂ᵀ (Sum.inr j) (Sum.inr i) := rfl
      simp only [Matrix.conjTranspose_apply, Matrix.toBlocks₂₂,
        Matrix.of_apply, star_trivial]
      rw [h, S.hSig₂.1.transpose_eq_self]
    have h2 : (L * S.Sig₂.toBlocks₁₂)ᵀ = L * S.Sig₂.toBlocks₁₂ := by
      rw [← hB, ← Matrix.mul_assoc, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_transpose,
        S.Siga_transpose, Matrix.mul_assoc]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_sub, h2]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      at h1
    rw [h1]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v => ?_
  rw [star_trivial]
  have h := S.Sig₂_quadForm_decompOf hL (-(Lᵀ *ᵥ v)) v
  rw [neg_add_cancel] at h
  have h0 : quadForm S.Siga 0 = 0 := by simp [quadForm]
  rw [h0, zero_add] at h
  have h1 := S.hSig₂.quadForm_nonneg (Sum.elim (-(Lᵀ *ᵥ v)) v)
  rw [h] at h1
  exact h1

/-- **`lem:slaved-seed`-1 at the `e₂` level, general loading**:
`Σ₂ − δ·Σ₂⁽ᵃ⁾(Λ₀) ⪰ 0` for `δ ∈ [0,1]`. -/
lemma Sig₂_sub_smul_sig2aOf_posSemidef
    (hL : S.Sig₂.toBlocks₂₁ = L * S.Siga) {δ : ℝ} (hδ1 : δ ≤ 1) :
    (S.Sig₂ - δ • S.sig2aOf L).PosSemidef := by
  have hB : S.Siga * Lᵀ = S.Sig₂.toBlocks₁₂ := by
    have h := congrArg Matrix.transpose hL
    rw [Matrix.transpose_mul, S.Siga_transpose] at h
    rw [← h, ← S.Sig₂_toBlocks₁₂_eq]
  have h22 : L * S.Siga * Lᵀ = L * S.Sig₂.toBlocks₁₂ := by
    rw [Matrix.mul_assoc, hB]
  have hdecomp : S.Sig₂ - δ • S.sig2aOf L
      = (1 - δ) • S.sig2aOf L
        + Matrix.fromBlocks 0 0 0
            (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂) := by
    have hblocks : S.Sig₂ - S.sig2aOf L
        = Matrix.fromBlocks 0 0 0
            (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · show S.Sig₂ (Sum.inl i) (Sum.inl j) - S.Siga i j = 0
        show S.Sig₂ (Sum.inl i) (Sum.inl j)
          - S.Sig₂ (Sum.inl i) (Sum.inl j) = 0
        rw [sub_self]
      · show S.Sig₂ (Sum.inl i) (Sum.inr j) - (S.Siga * Lᵀ) i j = 0
        rw [hB]
        show S.Sig₂ (Sum.inl i) (Sum.inr j)
          - S.Sig₂ (Sum.inl i) (Sum.inr j) = 0
        rw [sub_self]
      · show S.Sig₂ (Sum.inr i) (Sum.inl j) - (L * S.Siga) i j = 0
        rw [← hL]
        show S.Sig₂ (Sum.inr i) (Sum.inl j)
          - S.Sig₂ (Sum.inr i) (Sum.inl j) = 0
        rw [sub_self]
      · show S.Sig₂ (Sum.inr i) (Sum.inr j) - (L * S.Siga * Lᵀ) i j
          = (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂) i j
        rw [h22]
        show S.Sig₂ (Sum.inr i) (Sum.inr j)
            - (L * S.Sig₂.toBlocks₁₂) i j
          = S.Sig₂ (Sum.inr i) (Sum.inr j)
            - (L * S.Sig₂.toBlocks₁₂) i j
        rfl
    have h : S.Sig₂ - δ • S.sig2aOf L
        = (1 - δ) • S.sig2aOf L + (S.Sig₂ - S.sig2aOf L) := by
      rw [sub_smul, one_smul]
      abel
    rw [h, hblocks]
  rw [hdecomp]
  refine Matrix.PosSemidef.add
    ((S.sig2aOf_posSemidef L).smul (by linarith)) ?_
  have hsm := S.smarOf_posSemidef hL
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
      (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂))
      (x ∘ Sum.inl) (x ∘ Sum.inr)
    have hq : quadForm (Matrix.fromBlocks (0 : Matrix (Fin na) (Fin na) ℝ)
        0 0 (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂))
        (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr))
        = quadForm (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂)
            (x ∘ Sum.inr) := by
      rw [hd]
      simp [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
        Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
        quadForm]
    have h2 : (0:ℝ) ≤ quadForm (Matrix.fromBlocks 0 0 0
        (S.Sig₂.toBlocks₂₂ - L * S.Sig₂.toBlocks₁₂))
        (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr)) := by
      rw [hq]
      exact hsm.quadForm_nonneg _
    exact h2

/-- **`lem:slaved-seed`-1, general form**: the seed built from any
loading sits below the prior — for every PSD prior, no C2w, no
pseudoinverse. -/
theorem slavedSeedOf_le_Sig0 (hL : S.Sig₂.toBlocks₂₁ = L * S.Siga)
    {δ : ℝ} (hδ1 : δ ≤ 1) :
    (S.Sig0 - S.slavedSeedOf L δ).PosSemidef := by
  have hblocks : S.Sig0 - S.slavedSeedOf L δ
      = Matrix.fromBlocks S.Sig₁ 0 0 (S.Sig₂ - δ • S.sig2aOf L) := by
    unfold Sig0 slavedSeedOf
    ext i j
    rcases i with i₁ | i₂ <;> rcases j with j₁ | j₂ <;>
      simp [Matrix.sub_apply, Matrix.fromBlocks]
  rw [hblocks]
  have h22 := S.Sig₂_sub_smul_sig2aOf_posSemidef hL hδ1
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_zero]
    rw [S.hSig₁.1, h22.1]
  · rw [star_trivial]
    have hd : x ⬝ᵥ (Matrix.fromBlocks S.Sig₁ 0 0
          (S.Sig₂ - δ • S.sig2aOf L) *ᵥ x)
        = quadForm S.Sig₁ (x ∘ Sum.inl)
          + quadForm (S.Sig₂ - δ • S.sig2aOf L) (x ∘ Sum.inr) := by
      simp [quadForm, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
        Matrix.fromBlocks, Finset.mul_sum]
    rw [hd]
    exact add_nonneg (S.hSig₁.quadForm_nonneg _) (h22.quadForm_nonneg _)

/-- The general seed is PSD — for every prior. -/
lemma slavedSeedOf_posSemidef (L : Matrix (Fin nm) (Fin na) ℝ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) : (S.slavedSeedOf L δ).PosSemidef := by
  unfold slavedSeedOf
  have h22 := (S.sig2aOf_posSemidef L).smul hδ0
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_zero]
    rw [h22.1]
  · rw [star_trivial]
    have hd : x ⬝ᵥ (Matrix.fromBlocks 0 0 0 (δ • S.sig2aOf L) *ᵥ x)
        = quadForm (δ • S.sig2aOf L) (x ∘ Sum.inr) := by
      simp [quadForm, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
        Matrix.fromBlocks]
    rw [hd]
    exact h22.quadForm_nonneg _

/-- **`lem:slaved-seed`-2 (`eq:Lc2w`), general form**: the seed's
antistable corner is `δ·Σₐ` for any loading. -/
lemma slavedSeedOf_corner (L : Matrix (Fin nm) (Fin na) ℝ) (δ : ℝ) :
    (embA n₁ na nm)ᵀ * S.slavedSeedOf L δ * embA n₁ na nm
      = δ • S.Siga := by
  ext i j
  unfold slavedSeedOf sig2aOf embA
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.transpose_apply, Matrix.fromBlocks, Matrix.one_apply,
    mul_ite, ite_mul]

/-- **`lem:slaved-seed`-3 (`eq:seed-slaved`), general form**: the
marginal row of the general seed is slaved to the antistable row by its
loading — unconditionally. -/
theorem slavedSeedOf_slaved (L : Matrix (Fin nm) (Fin na) ℝ) (δ : ℝ) :
    (embM n₁ na nm)ᵀ * S.slavedSeedOf L δ
      = L * ((embA n₁ na nm)ᵀ * S.slavedSeedOf L δ) := by
  rw [embM_transpose_mul, embA_transpose_mul]
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rcases k with k₁ | k₂
  · unfold slavedSeedOf
    simp [Matrix.fromBlocks]
  · rcases k₂ with ka | km
    · show (S.slavedSeedOf L δ) (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inl ka))
        = ∑ i, L j i
            * (S.slavedSeedOf L δ) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl ka))
      unfold slavedSeedOf sig2aOf
      simp only [Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₁₁,
        smul_eq_mul]
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · show (S.slavedSeedOf L δ) (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inr km))
        = ∑ i, L j i
            * (S.slavedSeedOf L δ) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr km))
      unfold slavedSeedOf sig2aOf
      simp only [Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
        Matrix.fromBlocks_apply₁₂, smul_eq_mul]
      have h : (L * S.Siga * Lᵀ) j km
          = ∑ i, L j i * (S.Siga * Lᵀ) i km := by
        rw [Matrix.mul_assoc, Matrix.mul_apply]
      rw [h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

/-- Under C2w the general seed specializes to the (unique-loading)
slaved seed: `Λ₀ = Σₘₐ·Σₐₐ⁻¹` and `slavedSeedOf lam0 = slavedSeed`. -/
theorem slavedSeedOf_lam0 (hSa : S.Siga.PosDef) (δ : ℝ) :
    S.slavedSeedOf S.lam0 δ = S.slavedSeed δ := by
  unfold slavedSeedOf slavedSeed
  have h : S.sig2aOf S.lam0 = S.sig2a := by
    unfold sig2aOf sig2a
    rw [Matrix.mul_assoc S.lam0 S.Siga S.lam0ᵀ, S.Siga_mul_lam0t hSa,
      S.lam0_mul_Siga hSa]
  rw [h]

end DareSystem

end Dare
end Estimation

import LeanForControl.Estimation.Dare.Main
import LeanForControl.Estimation.Dare.ReducedFacts
import LeanForControl.Estimation.GES
import Architect

/-!
# The payoff frame transfer (`thm:payoff`, F1)

The deck states the estimator dichotomy `eq:payoff-dich` in the
three-block frame `eq:three-block`; the verified arc1 layer proves it
on the two-block canonical `FIESystem`. The transfer lumps the
antistable and marginal blocks (`eₐ ⊕ eₘ → Fin (na+nm)`), carries the
frame hypotheses across (`hAnti` with `|λ| ≥ 1` holds for `Aₐ ⊕ Aₘ`),
proves the condition correspondences C1 ↔ C1, C2 ↔ C2, C3w ↔ C3w, and
transports `gas_ges_dichotomy` into the in-frame statement of
`thm:payoff` Part 2. Part 1 (the maps converge, `F_T → F∞`) is
assembled from `thm:main`-1 and the gain continuity; the spectrum
display is Phase D's `strong_spec_split`/`strong_exists_unit_eigenvalue`.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

/-! ### Reindexing transports -/

section Transport

variable {ι ι2 κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ι2] [DecidableEq ι2] [Fintype κ]

/-- The complexified spectrum is invariant under a symmetric
reindexing. -/
lemma spectrum_complexify_submatrix_equiv (e : ι ≃ ι2)
    (M : Matrix ι ι ℝ) :
    spectrum ℂ (complexify (M.submatrix ⇑e.symm ⇑e.symm))
      = spectrum ℂ (complexify M) := by
  have h1 : complexify (M.submatrix ⇑e.symm ⇑e.symm)
      = (Matrix.reindexAlgEquiv ℂ ℂ e) (complexify M) := by
    rw [Matrix.reindexAlgEquiv_apply]
    rfl
  rw [h1, AlgEquiv.spectrum_eq]

/-- Detectability is invariant under a symmetric state reindexing. -/
lemma isDetectable_submatrix_equiv (e : ι ≃ ι2)
    {A : Matrix ι ι ℝ} {C : Matrix κ ι ℝ} :
    IsDetectable (complexify (A.submatrix ⇑e.symm ⇑e.symm))
        (complexify (C.submatrix id ⇑e.symm))
      ↔ IsDetectable (complexify A) (complexify C) := by
  have hA : complexify (A.submatrix ⇑e.symm ⇑e.symm)
      = (complexify A).submatrix ⇑e.symm ⇑e.symm := rfl
  have hC : complexify (C.submatrix id ⇑e.symm)
      = (complexify C).submatrix id ⇑e.symm := rfl
  constructor
  · intro hd μ v hμ hAv hCv
    set w : ι2 → ℂ := v ∘ ⇑e.symm with hw
    have hwe : w ∘ ⇑e = v := by
      funext i
      simp [hw]
    have h1 : complexify (A.submatrix ⇑e.symm ⇑e.symm) *ᵥ w = μ • w := by
      rw [hA, Matrix.submatrix_mulVec_equiv]
      simp only [Equiv.symm_symm]
      rw [hwe]
      funext i
      simp [hw, hAv]
    have h2 : complexify (C.submatrix id ⇑e.symm) *ᵥ w = 0 := by
      rw [hC, Matrix.submatrix_mulVec_equiv]
      simp only [Equiv.symm_symm]
      rw [hwe]
      funext i
      simp [hCv]
    have h3 := hd μ w hμ h1 h2
    funext i
    have h4 := congrFun h3 (e i)
    simpa [hw] using h4
  · intro hd μ w hμ hAw hCw
    set v : ι → ℂ := w ∘ ⇑e with hv
    have hve : w = v ∘ ⇑e.symm := by
      funext i
      simp [hv]
    have h3 : (v ∘ ⇑e.symm) ∘ ⇑e.symm.symm = v := by
      funext j
      simp
    have h1 : complexify A *ᵥ v = μ • v := by
      rw [hA, Matrix.submatrix_mulVec_equiv, hve, h3] at hAw
      funext i
      have h2 := congrFun hAw (e i)
      simpa [hve] using h2
    have h2 : complexify C *ᵥ v = 0 := by
      rw [hC, Matrix.submatrix_mulVec_equiv, hve, h3] at hCw
      funext i
      exact congrFun hCw i
    have h3 := hd μ v hμ h1 h2
    rw [hve, h3]
    funext i
    simp

/-- Positive definiteness is invariant under a symmetric reindexing. -/
lemma posDef_submatrix_equiv (e : ι ≃ ι2) {M : Matrix ι ι ℝ} :
    (M.submatrix ⇑e.symm ⇑e.symm).PosDef ↔ M.PosDef := by
  constructor
  · intro h
    have h1 := h.submatrix (e := ⇑e) e.injective
    rwa [Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] at h1
  · intro h
    exact h.submatrix e.symm.injective

end Transport

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-! ### The spectrum of the lumped uncontrollable block -/

/-- `A₂ = Aₐ ⊕ Aₘ` complexified, blockwise. -/
lemma complexify_A₂ : complexify S.A₂
    = Matrix.fromBlocks (complexify S.Aa) 0 0 (complexify S.Am) := by
  unfold A₂ complexify
  rw [Matrix.fromBlocks_map]
  congr 1 <;> · ext i j; simp

/-- An eigenvector of `A₂` splits into `Aₐ`- and `Aₘ`-eigenvector
components. -/
lemma A₂_eigen_split {μ : ℂ} {v : Fin na ⊕ Fin nm → ℂ}
    (h : complexify S.A₂ *ᵥ v = μ • v) :
    complexify S.Aa *ᵥ (v ∘ Sum.inl) = μ • (v ∘ Sum.inl)
      ∧ complexify S.Am *ᵥ (v ∘ Sum.inr) = μ • (v ∘ Sum.inr) := by
  rw [S.complexify_A₂, Matrix.fromBlocks_mulVec] at h
  constructor
  · funext i
    have h1 := congrFun h (Sum.inl i)
    simpa using h1
  · funext j
    have h1 := congrFun h (Sum.inr j)
    simpa using h1

/-- Every eigenvalue of the lumped block is on or outside the unit
circle (the FIE frame hypothesis `hAnti`). -/
lemma A₂_spectrum_ge_one :
    ∀ μ ∈ spectrum ℂ (complexify S.A₂), 1 ≤ ‖μ‖ := by
  intro μ hμ
  obtain ⟨v, hv0, hveq⟩ := exists_eigenvector_of_mem_spectrum hμ
  obtain ⟨ha, hm⟩ := S.A₂_eigen_split hveq
  by_cases hva : v ∘ Sum.inl = 0
  · have hvm : v ∘ Sum.inr ≠ 0 := by
      intro hvm
      refine hv0 ?_
      funext i
      cases i with
      | inl i => exact congrFun hva i
      | inr j => exact congrFun hvm j
    have hμm := mem_spectrum_of_mulVec_eq_smul hvm hm
    rw [S.hMarg μ hμm]
  · have hμa := mem_spectrum_of_mulVec_eq_smul hva ha
    exact (S.hAnti μ hμa).le

/-- With no marginal block, every eigenvalue of the lumped block is
strictly outside the unit circle. -/
lemma A₂_spectrum_gt_one (hnm : nm = 0) :
    ∀ μ ∈ spectrum ℂ (complexify S.A₂), 1 < ‖μ‖ := by
  haveI : IsEmpty (Fin nm) := by subst hnm; infer_instance
  intro μ hμ
  obtain ⟨v, hv0, hveq⟩ := exists_eigenvector_of_mem_spectrum hμ
  obtain ⟨ha, _⟩ := S.A₂_eigen_split hveq
  have hva : v ∘ Sum.inl ≠ 0 := by
    intro hva
    refine hv0 ?_
    funext i
    cases i with
    | inl i => exact congrFun hva i
    | inr j => exact absurd j.2 (by simp [hnm])
  exact S.hAnti μ (mem_spectrum_of_mulVec_eq_smul hva ha)

/-- The marginal spectrum embeds in the lumped block's. -/
lemma Am_spectrum_subset :
    spectrum ℂ (complexify S.Am) ⊆ spectrum ℂ (complexify S.A₂) := by
  intro μ hμ
  obtain ⟨v, hv0, hveq⟩ := exists_eigenvector_of_mem_spectrum hμ
  refine mem_spectrum_of_mulVec_eq_smul
    (v := Sum.elim (0 : Fin na → ℂ) v) ?_ ?_
  · intro h
    refine hv0 ?_
    funext j
    exact congrFun h (Sum.inr j)
  · rw [S.complexify_A₂, Matrix.fromBlocks_mulVec]
    funext i
    cases i with
    | inl i => simp
    | inr j => simpa using congrFun hveq j

/-! ### The frame transfer (`thm:payoff`, the a⊕m lumping) -/

/-- The lumping equivalence for the full state. -/
def lumpE (n₁ na nm : ℕ) :
    ix n₁ na nm ≃ Fin n₁ ⊕ Fin (na + nm) :=
  Equiv.sumCongr (Equiv.refl (Fin n₁)) finSumFinEquiv

/-- **F1: the frame transfer.** A `DareSystem` presents an `FIESystem`
by lumping `eₐ ⊕ eₘ` into one uncontrollable block: the covariances
turn into penalties (`Qi = Q⁻¹`, `Ri = R⁻¹`), and the frame hypothesis
`|λ| ≥ 1` on `A₂ = Aₐ ⊕ Aₘ` follows from antistability and
marginality of the two blocks. -/
noncomputable def toFIE : FIESystem n₁ (na + nm) m p where
  A₁ := S.A₁
  A₁₂ := S.A₁₂.submatrix id ⇑finSumFinEquiv.symm
  A₂ := S.A₂.submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm
  G₁ := S.G₁
  C₁ := S.C₁
  C₂ := S.C₂.submatrix id ⇑finSumFinEquiv.symm
  Qi := S.Q⁻¹
  Ri := S.R⁻¹
  Sig₁ := S.Sig₁
  Sig₂ := S.Sig₂.submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm
  hQi := S.hQ.inv
  hRi := S.hR.inv
  hSig₁ := S.hSig₁
  hSig₂ := S.hSig₂.submatrix _
  hStab := S.hStab
  hAnti := by
    intro μ hμ
    rw [spectrum_complexify_submatrix_equiv finSumFinEquiv S.A₂] at hμ
    exact S.A₂_spectrum_ge_one μ hμ

/-! ### The condition correspondences -/

lemma toFIE_fullA : S.toFIE.fullA
    = S.fullA.submatrix ⇑(lumpE n₁ na nm).symm ⇑(lumpE n₁ na nm).symm := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    rfl

lemma toFIE_fullC : S.toFIE.fullC
    = S.fullC.submatrix id ⇑(lumpE n₁ na nm).symm := by
  ext i j
  rcases j with j | j <;> rfl

/-- **C1 ↔ C1**: detectability is frame-independent. -/
theorem toFIE_C1_iff : S.toFIE.C1 ↔ S.C1 := by
  unfold FIESystem.C1 C1
  rw [S.toFIE_fullA, S.toFIE_fullC]
  exact isDetectable_submatrix_equiv (lumpE n₁ na nm)

/-- **C2 ↔ C2**: the lumped prior block is positive definite iff the
kernel condition holds (`eq:prior-pos`(a)). -/
theorem toFIE_C2_iff : S.toFIE.C2 ↔ S.C2 := by
  unfold FIESystem.C2
  rw [show S.toFIE.Sig₂
      = S.Sig₂.submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm
      from rfl]
  rw [posDef_submatrix_equiv finSumFinEquiv]
  exact S.criterion.symm

/-- **C3w ↔ C3w**: no unit-circle uncontrollable eigenvalue iff no
marginal block. -/
theorem toFIE_C3w_iff : S.toFIE.C3w ↔ C3w (nm := nm) := by
  unfold FIESystem.C3w C3w
  constructor
  · intro h
    by_contra hnm
    haveI : Nonempty (Fin nm) := ⟨⟨0, Nat.pos_of_ne_zero hnm⟩⟩
    obtain ⟨μ, hμE⟩ := Module.End.exists_eigenvalue
      (Matrix.toLin' (complexify S.Am))
    have hμm : μ ∈ spectrum ℂ (complexify S.Am) := by
      rw [← Matrix.spectrum_toLin']
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hμE
    have hμ2 : μ ∈ spectrum ℂ (complexify S.toFIE.A₂) := by
      rw [show S.toFIE.A₂
          = S.A₂.submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm
          from rfl,
        spectrum_complexify_submatrix_equiv finSumFinEquiv S.A₂]
      exact S.Am_spectrum_subset hμm
    have h1 := h μ hμ2
    have h2 := S.hMarg μ hμm
    rw [h2] at h1
    exact lt_irrefl 1 h1
  · intro hnm μ hμ
    rw [show S.toFIE.A₂
        = S.A₂.submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm
        from rfl,
      spectrum_complexify_submatrix_equiv finSumFinEquiv S.A₂] at hμ
    exact S.A₂_spectrum_gt_one hnm μ hμ

/-! ### `thm:payoff` Part 2, in-frame -/

/-- **`thm:payoff` Part 2 (`eq:payoff-dich`), the three-block-frame
statement**: the full-information estimator of the lumped frame is GAS
iff C1 ∧ C2 and GES iff C1 ∧ C2 ∧ C3w — with all three conditions read
in the deck's three-block frame. The estimator semantics (optimizer
error; = TVKF error by `isGASkf_iff_isGAS`) are the verified arc1
layer's. -/
theorem payoff_dichotomy :
    (S.toFIE.IsGAS ↔ S.C1 ∧ S.C2)
      ∧ (S.toFIE.IsGES ↔ S.C1 ∧ S.C2 ∧ C3w (nm := nm)) := by
  obtain ⟨hgas, hges⟩ := S.toFIE.gas_ges_dichotomy
  constructor
  · rw [hgas, S.toFIE_C1_iff, S.toFIE_C2_iff]
  · rw [hges, S.toFIE_C1_iff, S.toFIE_C2_iff, S.toFIE_C3w_iff]

/-! ### `thm:payoff` Part 1: the maps converge -/

/-- **`thm:payoff` Part 1 (the limiting error map)**: under C1 + C2w
(with the marginal power bound), the covariance converges to the strong
solution and the error maps `F_T` converge to `F∞`. The spectrum of
`F∞` is the verified split `strong_spec_split` (stabilizable modes at
the reduced loop, marginal modes on the circle,
`strong_exists_unit_eigenvalue`). -/
theorem payoff_errMap_tendsto (hC1 : S.C1) (hC2w : S.C2w)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    ∃ Sinf, S.IsStrongSolution Sinf
      ∧ Tendsto (fun T => ‖errMap S.fullC S.R S.fullA (S.dare T)
          - errMap S.fullC S.R S.fullA Sinf‖) atTop (nhds 0) := by
  obtain ⟨Sinf, hS, hiff⟩ := S.main_strong_attraction hC1 hcm hPB
  refine ⟨Sinf, hS, ?_⟩
  exact errMap_tendsto_of_tendsto S.hR
    (fun T => dareIter_posSemidef S.hR S.Qw_posSemidef
      S.Sig0_posSemidef T)
    hS.posSemidef (hiff.mpr hC2w)

end DareSystem

end Dare
end Estimation

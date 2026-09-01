import LeanForControl.Estimation.Dare.Payoff
import Architect

/-!
# `cor:every-prior` — every-prior stability is a controllability property (F3)

The per-prior conditions C2w/C2 are kernel conditions on the prior;
they hold for **every** PSD prior iff the exceptional coordinate
subspace is trivial. In the frame `eq:three-block` this reads:

* covariance side: `(∀ prior, C2w) ↔ na = 0` (`𝒳_{a,uc} = 0`), and the
  every-prior attraction `Σ_T → Σ∞` is exactly that;
* error side: `(∀ prior, C2) ↔ na = 0 ∧ nm = 0`, which is exactly
  stabilizability of the full pair `(A, G)` (`𝒳_{u,uc} = 0`), and then
  C3w is automatic — so every-prior GAS and every-prior GES coincide.

`withPrior` swaps the prior blocks of a `DareSystem` (the dynamics,
conditions C1/C3w, and the frame hypotheses are untouched).
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The same system with a different prior. -/
def withPrior (Sig₁' : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Sig₂' : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ)
    (h₁ : Sig₁'.PosSemidef) (h₂ : Sig₂'.PosSemidef) :
    DareSystem n₁ na nm m p :=
  { S with Sig₁ := Sig₁', Sig₂ := Sig₂', hSig₁ := h₁, hSig₂ := h₂ }

/-- Changing the prior does not touch C1. -/
lemma withPrior_C1 {Sig₁' Sig₂'} (h₁ : Sig₁'.PosSemidef)
    (h₂ : Sig₂'.PosSemidef) :
    (S.withPrior Sig₁' Sig₂' h₁ h₂).C1 ↔ S.C1 :=
  Iff.rfl

/-- The zero-prior system has zero `Σ₀`. -/
lemma withPrior_zero_Sig0 :
    (S.withPrior 0 0 Matrix.PosSemidef.zero
      Matrix.PosSemidef.zero).Sig0 = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Sig0, withPrior, Matrix.fromBlocks]

/-! ### The covariance half: every-prior C2w ⟺ `𝒳_{a,uc} = 0` -/

/-- **`cor:every-prior`, covariance side, kernel form**: C2w holds for
every PSD prior iff there is no antistable uncontrollable subspace. -/
theorem everyPrior_C2w_iff :
    (∀ (Sig₁' : Matrix (Fin n₁) (Fin n₁) ℝ)
        (Sig₂' : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ)
        (h₁ : Sig₁'.PosSemidef) (h₂ : Sig₂'.PosSemidef),
        (S.withPrior Sig₁' Sig₂' h₁ h₂).C2w)
      ↔ na = 0 := by
  constructor
  · intro h
    by_contra hna
    have h0 := h 0 0 Matrix.PosSemidef.zero Matrix.PosSemidef.zero
    set i0 : Fin na := ⟨0, Nat.pos_of_ne_zero hna⟩ with hi0
    have h1 := h0 (Pi.single i0 1) (by
      rw [S.withPrior_zero_Sig0, Matrix.zero_mulVec])
    have h2 := congrFun h1 i0
    simp at h2
  · intro hna
    intro Sig₁' Sig₂' h₁ h₂ w _
    funext i
    exact absurd i.2 (by simp [hna])

/-- **`cor:every-prior`, error side, kernel form**: C2 holds for every
PSD prior iff there is no uncontrollable block at all. -/
theorem everyPrior_C2_iff :
    (∀ (Sig₁' : Matrix (Fin n₁) (Fin n₁) ℝ)
        (Sig₂' : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ)
        (h₁ : Sig₁'.PosSemidef) (h₂ : Sig₂'.PosSemidef),
        (S.withPrior Sig₁' Sig₂' h₁ h₂).C2)
      ↔ (na = 0 ∧ nm = 0) := by
  constructor
  · intro h
    have h0 := h 0 0 Matrix.PosSemidef.zero Matrix.PosSemidef.zero
    constructor
    · by_contra hna
      set i0 : Fin na := ⟨0, Nat.pos_of_ne_zero hna⟩ with hi0
      have h1 := h0 (Pi.single (Sum.inl i0) 1) (by
        rw [S.withPrior_zero_Sig0, Matrix.zero_mulVec])
      have h2 := congrFun h1 (Sum.inl i0)
      simp at h2
    · by_contra hnm
      set j0 : Fin nm := ⟨0, Nat.pos_of_ne_zero hnm⟩ with hj0
      have h1 := h0 (Pi.single (Sum.inr j0) 1) (by
        rw [S.withPrior_zero_Sig0, Matrix.zero_mulVec])
      have h2 := congrFun h1 (Sum.inr j0)
      simp at h2
  · rintro ⟨hna, hnm⟩
    intro Sig₁' Sig₂' h₁ h₂ w _
    funext i
    rcases i with i | i
    · exact absurd i.2 (by simp [hna])
    · exact absurd i.2 (by simp [hnm])

/-! ### The Hautus bridge: `𝒳_{u,uc} = 0` ⟺ `(A, G)` stabilizable -/

/-- The full state matrix, complexified blockwise. -/
lemma complexify_fullA : complexify S.fullA
    = Matrix.fromBlocks (complexify S.A₁) (complexify S.A₁₂)
        0 (complexify S.A₂) := by
  unfold fullA complexify
  rw [Matrix.fromBlocks_map]
  congr 1

/-- **`cor:every-prior`, the stabilizability bridge**: the full pair
`(A, G)` of the frame is stabilizable iff the uncontrollable block is
absent — `𝒳_{u,uc}(A,G) = 0`. -/
theorem fullStab_iff :
    IsStabilizable (complexify S.fullA) (complexify S.fullG)
      ↔ (na = 0 ∧ nm = 0) := by
  constructor
  · intro h
    by_contra hne
    have hnonempty : Nonempty (Fin na ⊕ Fin nm) := by
      rcases Decidable.not_and_iff_not_or_not.mp hne with hna | hnm
      · exact ⟨Sum.inl ⟨0, Nat.pos_of_ne_zero fun h0 => hna h0⟩⟩
      · exact ⟨Sum.inr ⟨0, Nat.pos_of_ne_zero fun h0 => hnm h0⟩⟩
    obtain ⟨μ, hμE⟩ := Module.End.exists_eigenvalue
      (Matrix.toLin' (complexify S.A₂)ᵀ)
    have hμ2 : μ ∈ spectrum ℂ (complexify S.A₂)ᵀ := by
      rw [← Matrix.spectrum_toLin']
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hμE
    have hμge : 1 ≤ ‖μ‖ :=
      S.A₂_spectrum_ge_one μ (mem_spectrum_transpose_iff.mp hμ2)
    obtain ⟨v, hv0, hveq⟩ := exists_eigenvector_of_mem_spectrum hμ2
    -- lift the left eigenvector to the full state
    set V : ix n₁ na nm → ℂ := Sum.elim 0 v with hV
    have hVne : V ≠ 0 := by
      intro hV0
      refine hv0 ?_
      funext j
      exact congrFun hV0 (Sum.inr j)
    have hVA : (complexify S.fullA)ᵀ *ᵥ V = μ • V := by
      rw [S.complexify_fullA, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i
      · simp [hV]
      · have h1 := congrFun hveq i
        simpa [hV] using h1
    have hVG : (complexify S.fullG)ᵀ *ᵥ V = 0 := by
      funext i
      show ∑ j, (complexify S.fullG)ᵀ i j * V j = 0
      rw [Fintype.sum_sum_type]
      have hg : ∀ j₂ : Fin na ⊕ Fin nm, S.fullG (Sum.inr j₂) i = 0 := by
        intro j₂
        unfold fullG
        simp [Matrix.fromRows_apply_inr]
      have hVl : ∀ j₁ : Fin n₁, V (Sum.inl j₁) = 0 := fun j₁ => by
        simp [hV]
      simp [hVl, hg, Matrix.transpose_apply, complexify]
    exact hVne (h μ V hμge hVA hVG)
  · rintro ⟨hna, hnm⟩
    haveI : IsEmpty (Fin na) := by subst hna; infer_instance
    haveI : IsEmpty (Fin nm) := by subst hnm; infer_instance
    intro μ V hμ hVA hVG
    have hV2 : ∀ j : Fin na ⊕ Fin nm, V (Sum.inr j) = 0 :=
      fun j => isEmptyElim j
    have hV1A : (complexify S.A₁)ᵀ *ᵥ (V ∘ Sum.inl)
        = μ • (V ∘ Sum.inl) := by
      rw [S.complexify_fullA, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_mulVec] at hVA
      funext i
      have h1 := congrFun hVA (Sum.inl i)
      simpa using h1
    have hV1G : (complexify S.G₁)ᵀ *ᵥ (V ∘ Sum.inl) = 0 := by
      funext i
      have h1 := congrFun hVG i
      show ∑ j₁, (complexify S.G₁)ᵀ i j₁ * V (Sum.inl j₁) = 0
      have h2 : ((complexify S.fullG)ᵀ *ᵥ V) i
          = ∑ j₁, (complexify S.G₁)ᵀ i j₁ * V (Sum.inl j₁) := by
        show ∑ j, (complexify S.fullG)ᵀ i j * V j = _
        rw [Fintype.sum_sum_type]
        have h3 : ∀ j₂ : Fin na ⊕ Fin nm,
            (complexify S.fullG)ᵀ i (Sum.inr j₂) * V (Sum.inr j₂) = 0 :=
          fun j₂ => by rw [hV2 j₂, mul_zero]
        simp only [h3, Finset.sum_const_zero, add_zero]
        rfl
      rw [← h2]
      exact h1
    have hV1 := S.hStab μ (V ∘ Sum.inl) hμ hV1A hV1G
    funext i
    rcases i with i | i
    · exact congrFun hV1 i
    · exact hV2 i

/-! ### Every-prior attraction and every-prior GAS/GES -/

/-- **`cor:every-prior`, covariance display**: the covariance is
attracted to the strong solution from every prior iff `𝒳_{a,uc} = 0`
(in-frame: `na = 0`). -/
theorem everyPrior_attraction_iff (hC1 : S.C1)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    (∀ (Sig₁' : Matrix (Fin n₁) (Fin n₁) ℝ)
        (Sig₂' : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ)
        (h₁ : Sig₁'.PosSemidef) (h₂ : Sig₂'.PosSemidef),
        ∃ Sinf, (S.withPrior Sig₁' Sig₂' h₁ h₂).IsStrongSolution Sinf
          ∧ Tendsto (fun T =>
              ‖(S.withPrior Sig₁' Sig₂' h₁ h₂).dare T - Sinf‖)
            atTop (nhds 0))
      ↔ na = 0 := by
  constructor
  · intro h
    rw [← S.everyPrior_C2w_iff]
    intro Sig₁' Sig₂' h₁ h₂
    obtain ⟨Sinf, hS, hconv⟩ := h Sig₁' Sig₂' h₁ h₂
    exact ((S.withPrior Sig₁' Sig₂' h₁ h₂).strong_attraction_iff_C2w
      ((S.withPrior_C1 h₁ h₂).mpr hC1) hS hcm hPB).mp hconv
  · intro hna Sig₁' Sig₂' h₁ h₂
    have hC2w : (S.withPrior Sig₁' Sig₂' h₁ h₂).C2w :=
      S.everyPrior_C2w_iff.mpr hna Sig₁' Sig₂' h₁ h₂
    obtain ⟨Sinf, hS, hiff⟩ :=
      (S.withPrior Sig₁' Sig₂' h₁ h₂).main_strong_attraction
        ((S.withPrior_C1 h₁ h₂).mpr hC1) hcm hPB
    exact ⟨Sinf, hS, hiff.mpr hC2w⟩

/-- **`cor:every-prior`, error display (GAS)**: the estimator is GAS
for every prior iff `(A, G)` is stabilizable. -/
theorem everyPrior_gas_iff (hC1 : S.C1) :
    (∀ (Sig₁' : Matrix (Fin n₁) (Fin n₁) ℝ)
        (Sig₂' : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ)
        (h₁ : Sig₁'.PosSemidef) (h₂ : Sig₂'.PosSemidef),
        (S.withPrior Sig₁' Sig₂' h₁ h₂).toFIE.IsGAS)
      ↔ IsStabilizable (complexify S.fullA) (complexify S.fullG) := by
  rw [S.fullStab_iff]
  constructor
  · intro h
    rw [← S.everyPrior_C2_iff]
    intro Sig₁' Sig₂' h₁ h₂
    exact (((S.withPrior Sig₁' Sig₂' h₁ h₂).payoff_dichotomy).1.mp
      (h Sig₁' Sig₂' h₁ h₂)).2
  · rintro ⟨hna, hnm⟩ Sig₁' Sig₂' h₁ h₂
    refine ((S.withPrior Sig₁' Sig₂' h₁ h₂).payoff_dichotomy).1.mpr
      ⟨(S.withPrior_C1 h₁ h₂).mpr hC1, ?_⟩
    exact S.everyPrior_C2_iff.mpr ⟨hna, hnm⟩ Sig₁' Sig₂' h₁ h₂

/-- **`cor:every-prior`, error display (GES)**: the estimator is GES
for every prior iff `(A, G)` is stabilizable. -/
theorem everyPrior_ges_iff (hC1 : S.C1) :
    (∀ (Sig₁' : Matrix (Fin n₁) (Fin n₁) ℝ)
        (Sig₂' : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ)
        (h₁ : Sig₁'.PosSemidef) (h₂ : Sig₂'.PosSemidef),
        (S.withPrior Sig₁' Sig₂' h₁ h₂).toFIE.IsGES)
      ↔ IsStabilizable (complexify S.fullA) (complexify S.fullG) := by
  rw [S.fullStab_iff]
  constructor
  · intro h
    have hgas : ∀ Sig₁' Sig₂' (h₁ : Matrix.PosSemidef Sig₁')
        (h₂ : Matrix.PosSemidef Sig₂'),
        (S.withPrior Sig₁' Sig₂' h₁ h₂).toFIE.IsGAS :=
      fun Sig₁' Sig₂' h₁ h₂ => (h Sig₁' Sig₂' h₁ h₂).isGAS
    rw [← S.everyPrior_C2_iff]
    intro Sig₁' Sig₂' h₁ h₂
    exact (((S.withPrior Sig₁' Sig₂' h₁ h₂).payoff_dichotomy).1.mp
      (hgas Sig₁' Sig₂' h₁ h₂)).2
  · rintro ⟨hna, hnm⟩ Sig₁' Sig₂' h₁ h₂
    refine ((S.withPrior Sig₁' Sig₂' h₁ h₂).payoff_dichotomy).2.mpr
      ⟨(S.withPrior_C1 h₁ h₂).mpr hC1, ?_, hnm⟩
    exact S.everyPrior_C2_iff.mpr ⟨hna, hnm⟩ Sig₁' Sig₂' h₁ h₂

/-- **`cor:every-prior`, the coincidence**: every-prior GAS and
every-prior GES are the same property — stabilizability already rules
out unit-circle uncontrollable modes, so nothing separates them at the
every-prior level. -/
theorem everyPrior_gas_iff_ges (hC1 : S.C1) :
    (∀ (Sig₁' : Matrix (Fin n₁) (Fin n₁) ℝ)
        (Sig₂' : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ)
        (h₁ : Sig₁'.PosSemidef) (h₂ : Sig₂'.PosSemidef),
        (S.withPrior Sig₁' Sig₂' h₁ h₂).toFIE.IsGAS)
      ↔ (∀ (Sig₁' : Matrix (Fin n₁) (Fin n₁) ℝ)
          (Sig₂' : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ)
          (h₁ : Sig₁'.PosSemidef) (h₂ : Sig₂'.PosSemidef),
          (S.withPrior Sig₁' Sig₂' h₁ h₂).toFIE.IsGES) := by
  rw [S.everyPrior_gas_iff hC1, S.everyPrior_ges_iff hC1]

end DareSystem

end Dare
end Estimation

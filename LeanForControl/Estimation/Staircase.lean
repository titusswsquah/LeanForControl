import LeanForControl.Estimation.General
import Architect

set_option linter.style.show false

/-!
# The stabilizability staircase (S4 of the generality sprint)

An adapted basis for `V₁ = reachable ⊔ stable` turns a general system
into the block-triangular canonical form of the paper — concretely, the
`Fin n₁ ⊕ Fin n₂`-indexed matrices that the reduced `FIESystem` layer
consumes. The structural facts (`A₂` completely unstable, `(A₁, G₁)`
stabilizable) fall to polynomial calculus with the spectral projections
(design note D1a of the sprint).
-/

namespace Estimation

namespace GeneralSystem

open Matrix LinearSystems Filter Module

open scoped Matrix.Norms.Operator

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-! ### Invariance of the stabilizable subspace -/

/-- Powers applied to input columns stay reachable. -/
lemma pow_G_mem (k : ℕ) (u : Fin m → ℝ) :
    S.A ^ k *ᵥ (S.G *ᵥ u) ∈ S.reachSub := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.lt_or_ge k n with hk | hk
  · -- a single slot of the reachability map
    refine ⟨(Pi.single ⟨k, hk⟩ u : Fin n → Fin m → ℝ), ?_⟩
    show (∑ j : Fin n, (S.A ^ (j : ℕ) * S.G)
      *ᵥ (Pi.single ⟨k, hk⟩ u : Fin n → Fin m → ℝ) j) = _
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · rw [Pi.single_eq_same, ← Matrix.mulVec_mulVec]
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij, Matrix.mulVec_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · -- reduce the power through Cayley–Hamilton
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · have h0 : S.A ^ k *ᵥ (S.G *ᵥ u) = 0 := by
        funext i
        exact absurd i.2 (by omega)
      rw [h0]
      exact Submodule.zero_mem _
    set q : Polynomial ℝ := Polynomial.X ^ n - S.A.charpoly with hq
    have hAn : S.A ^ n = Polynomial.aeval S.A q := by
      rw [hq, map_sub, Matrix.aeval_self_charpoly, sub_zero, map_pow,
        Polynomial.aeval_X]
    have hdegq : q.natDegree < n := by
      have hmon := S.A.charpoly_monic
      have hdeg : S.A.charpoly.natDegree = n := by
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      rcases eq_or_ne q 0 with h0 | h0
      · rw [h0]
        simpa using hn0
      have h1 : q.degree < (Polynomial.X ^ n : Polynomial ℝ).degree := by
        rw [hq]
        refine Polynomial.degree_sub_lt ?_
          (pow_ne_zero n Polynomial.X_ne_zero) ?_
        · rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree
            hmon.ne_zero, hdeg]
        · rw [Polynomial.leadingCoeff_X_pow, hmon.leadingCoeff]
      have h2 : q.degree < (n : ℕ) := by
        rwa [Polynomial.degree_X_pow] at h1
      exact Polynomial.natDegree_lt_iff_degree_lt h0 |>.mpr
        (by exact_mod_cast h2)
    have h1 : S.A ^ k = S.A ^ (k - n) * S.A ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have h2 := Polynomial.aeval_eq_sum_range (R := ℝ)
      (S := Matrix (Fin n) (Fin n) ℝ) (x := S.A) (p := q)
    have h3 : S.A ^ k = ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i • S.A ^ (k - n + i) := by
      rw [h1, hAn, h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_smul, ← pow_add]
    have hsplit : S.A ^ k *ᵥ (S.G *ᵥ u)
        = ∑ i ∈ Finset.range (q.natDegree + 1),
          q.coeff i • (S.A ^ (k - n + i) *ᵥ (S.G *ᵥ u)) := by
      rw [h3, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.smul_mulVec]
    rw [hsplit]
    refine Submodule.sum_mem _ fun i hi => ?_
    refine Submodule.smul_mem _ _ ?_
    exact ih (k - n + i) (by
      have := Finset.mem_range.mp hi
      omega)

/-- The reachable subspace is `A`-invariant. -/
lemma reachSub_invariant {x : Fin n → ℝ} (hx : x ∈ S.reachSub) :
    S.A *ᵥ x ∈ S.reachSub := by
  obtain ⟨us, rfl⟩ := hx
  have h1 : S.A *ᵥ S.realReachMap us
      = ∑ j : Fin n, S.A ^ ((j : ℕ) + 1) *ᵥ (S.G *ᵥ us j) := by
    show S.A *ᵥ (∑ j : Fin n, (S.A ^ (j : ℕ) * S.G) *ᵥ us j) = _
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      ← pow_succ']
  rw [h1]
  exact Submodule.sum_mem _ fun j _ => S.pow_G_mem _ _

/-- Input columns are reachable. -/
lemma G_mulVec_mem_reachSub (u : Fin m → ℝ) :
    S.G *ᵥ u ∈ S.reachSub := by
  have h1 := S.pow_G_mem 0 u
  rwa [pow_zero, Matrix.one_mulVec] at h1

/-- The stable subspace is `A`-invariant. -/
lemma stableSub_invariant {x : Fin n → ℝ}
    (hx : x ∈ stableSub S.A) : S.A *ᵥ x ∈ stableSub S.A := by
  obtain ⟨y, hy⟩ := hx
  rw [Matrix.mulVecLin_apply] at hy
  refine ⟨S.A *ᵥ y, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← stabProj_comm,
    ← Matrix.mulVec_mulVec, hy]

/-- The stabilizable subspace is `A`-invariant. -/
lemma stabilizableSub_invariant {x : Fin n → ℝ}
    (hx : x ∈ S.stabilizableSub) :
    S.A *ᵥ x ∈ S.stabilizableSub := by
  obtain ⟨r, hr, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
  rw [Matrix.mulVec_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (S.reachSub_invariant hr))
    (Submodule.mem_sup_right (S.stableSub_invariant hs))

/-! ### The adapted basis and the block form -/

/-- A complement of the stabilizable subspace (chosen). -/
noncomputable def compSub : Submodule ℝ (Fin n → ℝ) :=
  (S.stabilizableSub.exists_isCompl).choose

lemma isCompl_stab_comp : IsCompl S.stabilizableSub S.compSub :=
  (S.stabilizableSub.exists_isCompl).choose_spec

/-- The stabilizable dimension `n₁`. -/
noncomputable def rk1 : ℕ := Module.finrank ℝ S.stabilizableSub

/-- The antistable dimension `n₂`. -/
noncomputable def rk2 : ℕ := Module.finrank ℝ S.compSub

/-- The basis adapted to `V₁ ⊕ W`. -/
noncomputable def staircaseBasis :
    Basis (Fin S.rk1 ⊕ Fin S.rk2) ℝ (Fin n → ℝ) :=
  ((Module.finBasis ℝ S.stabilizableSub).prod
    (Module.finBasis ℝ S.compSub)).map
    (Submodule.prodEquivOfIsCompl _ _ S.isCompl_stab_comp)

/-- Coordinates in the second block vanish on the stabilizable
subspace. -/
lemma staircaseBasis_repr_inr_eq_zero {x : Fin n → ℝ}
    (hx : x ∈ S.stabilizableSub) (i : Fin S.rk2) :
    S.staircaseBasis.repr x (Sum.inr i) = 0 := by
  unfold staircaseBasis
  rw [Basis.map_repr]
  have h1 : ((Submodule.prodEquivOfIsCompl _ _
      S.isCompl_stab_comp).symm x).2 = 0 :=
    (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero _ _
      S.isCompl_stab_comp).mpr hx
  show ((Module.finBasis ℝ S.stabilizableSub).prod
    (Module.finBasis ℝ S.compSub)).repr
      ((Submodule.prodEquivOfIsCompl _ _ S.isCompl_stab_comp).symm x)
      (Sum.inr i) = 0
  rw [Basis.prod_repr_inr, h1, map_zero]
  rfl

/-- Vanishing second-block coordinates certify membership. -/
lemma mem_of_repr_inr_eq_zero {x : Fin n → ℝ}
    (hx : ∀ i, S.staircaseBasis.repr x (Sum.inr i) = 0) :
    x ∈ S.stabilizableSub := by
  have h2 : ((Submodule.prodEquivOfIsCompl _ _
      S.isCompl_stab_comp).symm x).2 = 0 := by
    have h3 : ∀ i, (Module.finBasis ℝ S.compSub).repr
        ((Submodule.prodEquivOfIsCompl _ _
          S.isCompl_stab_comp).symm x).2 i = 0 := by
      intro i
      have h4 := hx i
      unfold staircaseBasis at h4
      rw [Basis.map_repr] at h4
      exact h4
    have h5 : (Module.finBasis ℝ S.compSub).repr
        ((Submodule.prodEquivOfIsCompl _ _
          S.isCompl_stab_comp).symm x).2 = 0 := by
      ext i
      exact h3 i
    have h6 := (Module.finBasis ℝ S.compSub).repr.injective
      (a₁ := ((Submodule.prodEquivOfIsCompl _ _
        S.isCompl_stab_comp).symm x).2) (a₂ := 0)
    refine h6 ?_
    rw [h5, map_zero]
  exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero _ _
    S.isCompl_stab_comp).mp h2

/-- The first-block basis vectors lie in the stabilizable subspace. -/
lemma staircaseBasis_inl_mem (i : Fin S.rk1) :
    S.staircaseBasis (Sum.inl i) ∈ S.stabilizableSub := by
  refine S.mem_of_repr_inr_eq_zero fun k => ?_
  rw [Basis.repr_self]
  exact Finsupp.single_eq_of_ne (by simp)

/-- The staircase form of the dynamics. -/
noncomputable def stairA :
    Matrix (Fin S.rk1 ⊕ Fin S.rk2) (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  LinearMap.toMatrix S.staircaseBasis S.staircaseBasis S.A.mulVecLin

/-- The staircase form of the noise input. -/
noncomputable def stairG :
    Matrix (Fin S.rk1 ⊕ Fin S.rk2) (Fin m) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) S.staircaseBasis
    S.G.mulVecLin

/-- The staircase form of the output map. -/
noncomputable def stairC :
    Matrix (Fin p) (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  LinearMap.toMatrix S.staircaseBasis (Pi.basisFun ℝ (Fin p))
    S.C.mulVecLin

/-- Block-triangularity: the `(2,1)` block of the staircase dynamics
vanishes. -/
lemma stairA_toBlocks₂₁ : S.stairA.toBlocks₂₁ = 0 := by
  funext i j
  show S.stairA (Sum.inr i) (Sum.inl j) = 0
  unfold stairA
  rw [LinearMap.toMatrix_apply]
  rw [Matrix.mulVecLin_apply]
  exact S.staircaseBasis_repr_inr_eq_zero
    (S.stabilizableSub_invariant (S.staircaseBasis_inl_mem j)) i

/-- The noise enters only the stabilizable block. -/
lemma stairG_inr_eq_zero (i : Fin S.rk2) (j : Fin m) :
    S.stairG (Sum.inr i) j = 0 := by
  unfold stairG
  rw [LinearMap.toMatrix_apply]
  rw [Matrix.mulVecLin_apply]
  refine S.staircaseBasis_repr_inr_eq_zero ?_ i
  exact Submodule.mem_sup_left (S.G_mulVec_mem_reachSub _)

/-! ### The matrix-level intertwiner -/

/-- The coordinate map as a matrix: `W x = repr x`. -/
noncomputable def stairW : Matrix (Fin S.rk1 ⊕ Fin S.rk2) (Fin n) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) S.staircaseBasis
    LinearMap.id

/-- Its inverse: back to standard coordinates. -/
noncomputable def stairWinv : Matrix (Fin n) (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  LinearMap.toMatrix S.staircaseBasis (Pi.basisFun ℝ (Fin n))
    LinearMap.id

lemma stairW_mul_stairWinv : S.stairW * S.stairWinv = 1 := by
  unfold stairW stairWinv
  rw [← LinearMap.toMatrix_comp (v₂ := Pi.basisFun ℝ (Fin n)),
    LinearMap.id_comp, LinearMap.toMatrix_id]

lemma stairWinv_mul_stairW : S.stairWinv * S.stairW = 1 := by
  unfold stairW stairWinv
  rw [← LinearMap.toMatrix_comp (v₂ := S.staircaseBasis),
    LinearMap.id_comp, LinearMap.toMatrix_id]

private lemma toMatrix_basisFun_mulVecLin {k l : ℕ}
    (M : Matrix (Fin k) (Fin l) ℝ) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin l)) (Pi.basisFun ℝ (Fin k))
      M.mulVecLin = M := by
  rw [show LinearMap.toMatrix (Pi.basisFun ℝ (Fin l))
      (Pi.basisFun ℝ (Fin k)) = LinearMap.toMatrix' from rfl,
    ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

lemma stairA_conj : S.stairA * S.stairW = S.stairW * S.A := by
  have h1 : S.stairA * S.stairW
      = LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) S.staircaseBasis
        S.A.mulVecLin := by
    unfold stairA stairW
    rw [← LinearMap.toMatrix_comp (v₂ := S.staircaseBasis),
      LinearMap.comp_id]
  have h2 : S.stairW * S.A
      = LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) S.staircaseBasis
        S.A.mulVecLin := by
    unfold stairW
    conv_lhs => rw [show S.A = LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
      (Pi.basisFun ℝ (Fin n)) S.A.mulVecLin from
      (toMatrix_basisFun_mulVecLin S.A).symm]
    rw [← LinearMap.toMatrix_comp (v₂ := Pi.basisFun ℝ (Fin n)),
      LinearMap.id_comp]
  rw [h1, h2]

lemma stairG_eq : S.stairG = S.stairW * S.G := by
  have h2 : S.stairW * S.G
      = LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) S.staircaseBasis
        S.G.mulVecLin := by
    unfold stairW
    conv_lhs => rw [show S.G = LinearMap.toMatrix (Pi.basisFun ℝ (Fin m))
      (Pi.basisFun ℝ (Fin n)) S.G.mulVecLin from
      (toMatrix_basisFun_mulVecLin S.G).symm]
    rw [← LinearMap.toMatrix_comp (v₂ := Pi.basisFun ℝ (Fin n)),
      LinearMap.id_comp]
  rw [h2]
  rfl

lemma stairC_eq : S.stairC = S.C * S.stairWinv := by
  have h2 : S.C * S.stairWinv
      = LinearMap.toMatrix S.staircaseBasis (Pi.basisFun ℝ (Fin p))
        S.C.mulVecLin := by
    unfold stairWinv
    conv_lhs => rw [show S.C = LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
      (Pi.basisFun ℝ (Fin p)) S.C.mulVecLin from
      (toMatrix_basisFun_mulVecLin S.C).symm]
    rw [← LinearMap.toMatrix_comp (v₂ := Pi.basisFun ℝ (Fin n)),
      LinearMap.comp_id]
  rw [h2]
  rfl

end GeneralSystem

end Estimation

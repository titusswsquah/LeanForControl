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

/-! ### Polynomial calculus across the intertwiner -/

/-- Intertwining passes to polynomials. -/
lemma aeval_intertwine {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {M' : Matrix α α ℂ}
    {M : Matrix β β ℂ} {Q : Matrix α β ℂ}
    (h : M' * Q = Q * M) (q : Polynomial ℂ) :
    Polynomial.aeval M' q * Q = Q * Polynomial.aeval M q := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hq, hr]
  | monomial d a =>
    have hpow : ∀ j : ℕ, M' ^ j * Q = Q * M ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc M' ^ (j + 1) * Q = M' * (M' ^ j * Q) := by
              rw [pow_succ']
              simp only [Matrix.mul_assoc]
        _ = M' * (Q * M ^ j) := by rw [ih]
        _ = (M' * Q) * M ^ j := by simp only [Matrix.mul_assoc]
        _ = (Q * M) * M ^ j := by rw [h]
        _ = Q * M ^ (j + 1) := by
            rw [pow_succ']
            simp only [Matrix.mul_assoc]
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
    rw [hpow]

/-- Polynomials of a block-triangular matrix are block-triangular with
polynomial diagonal blocks. -/
lemma aeval_fromBlocks_triangular {k l : ℕ}
    (B₁₁ : Matrix (Fin k) (Fin k) ℂ) (B₁₂ : Matrix (Fin k) (Fin l) ℂ)
    (B₂₂ : Matrix (Fin l) (Fin l) ℂ) (q : Polynomial ℂ) :
    ∃ X : Matrix (Fin k) (Fin l) ℂ,
      Polynomial.aeval (Matrix.fromBlocks B₁₁ B₁₂ 0 B₂₂) q
        = Matrix.fromBlocks (Polynomial.aeval B₁₁ q) X 0
            (Polynomial.aeval B₂₂ q) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    obtain ⟨X, hX⟩ := hq
    obtain ⟨Y, hY⟩ := hr
    refine ⟨X + Y, ?_⟩
    rw [map_add, map_add, map_add, hX, hY, Matrix.fromBlocks_add,
      add_zero]
  | monomial d a =>
    have hpow : ∀ j : ℕ, ∃ Z : Matrix (Fin k) (Fin l) ℂ,
        Matrix.fromBlocks B₁₁ B₁₂ 0 B₂₂ ^ j
          = Matrix.fromBlocks (B₁₁ ^ j) Z 0 (B₂₂ ^ j) := by
      intro j
      induction j with
      | zero =>
        refine ⟨0, ?_⟩
        rw [pow_zero, pow_zero, pow_zero, ← Matrix.fromBlocks_one]
      | succ j ih =>
        obtain ⟨Z, hZ⟩ := ih
        refine ⟨B₁₁ * Z + B₁₂ * B₂₂ ^ j, ?_⟩
        rw [pow_succ', hZ, pow_succ', pow_succ',
          Matrix.fromBlocks_multiply]
        congr 1 <;> simp
    obtain ⟨Z, hZ⟩ := hpow d
    refine ⟨a • Z, ?_⟩
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul]
    rw [hZ]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks]

/-! ### Structural facts of the staircase blocks -/

/-- Action form of the intertwiner: `W` computes staircase
coordinates. -/
lemma stairW_mulVec (x : Fin n → ℝ) :
    S.stairW *ᵥ x = fun i => S.staircaseBasis.repr x i := by
  have h1 := LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin n))
    S.staircaseBasis LinearMap.id x
  rw [LinearMap.id_apply] at h1
  have h2 : ⇑((Pi.basisFun ℝ (Fin n)).repr x) = x := by
    funext j
    simp
  rw [h2] at h1
  exact h1

/-- The transformed stable projection. -/
noncomputable def stairPs :
    Matrix (Fin S.rk1 ⊕ Fin S.rk2) (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  S.stairW * stabProj S.A * S.stairWinv

/-- The transformed antistable projection. -/
noncomputable def stairPa :
    Matrix (Fin S.rk1 ⊕ Fin S.rk2) (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  S.stairW * antiProj S.A * S.stairWinv

lemma stairPs_add_stairPa : S.stairPs + S.stairPa = 1 := by
  unfold stairPs stairPa
  rw [← Matrix.add_mul, ← Matrix.mul_add, stabProj_add_antiProj,
    Matrix.mul_one, stairW_mul_stairWinv]

/-- The transformed stable projection lands in the first block. -/
lemma stairPs_inr_row (i : Fin S.rk2) (j : Fin S.rk1 ⊕ Fin S.rk2) :
    S.stairPs (Sum.inr i) j = 0 := by
  have h1 : S.stairPs *ᵥ Pi.single j 1
      = S.stairW *ᵥ (stabProj S.A *ᵥ (S.stairWinv *ᵥ Pi.single j 1)) := by
    unfold stairPs
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hmem : stabProj S.A *ᵥ (S.stairWinv *ᵥ Pi.single j 1)
      ∈ S.stabilizableSub :=
    Submodule.mem_sup_right ⟨S.stairWinv *ᵥ Pi.single j 1, rfl⟩
  have h2 : (S.stairPs *ᵥ Pi.single j 1) (Sum.inr i) = 0 := by
    rw [h1, stairW_mulVec]
    exact S.staircaseBasis_repr_inr_eq_zero hmem i
  rw [Matrix.mulVec_single_one] at h2
  exact h2

/-- Complexified version: second-block rows of the stable projection
vanish. -/
lemma stairPs_c_mulVec_inr (z : (Fin S.rk1 ⊕ Fin S.rk2) → ℂ)
    (i : Fin S.rk2) :
    (complexify S.stairPs *ᵥ z) (Sum.inr i) = 0 := by
  simp [Matrix.mulVec, dotProduct, stairPs_inr_row]

/-- Entry form of block triangularity. -/
lemma stairA_inr_inl (i : Fin S.rk2) (j : Fin S.rk1) :
    S.stairA (Sum.inr i) (Sum.inl j) = 0 := by
  have h := congrFun (congrFun S.stairA_toBlocks₂₁ i) j
  simpa [Matrix.toBlocks₂₁] using h

/-- The complexified staircase matrix in block form. -/
lemma stairA_c_blocks :
    complexify S.stairA = Matrix.fromBlocks
      (complexify S.stairA.toBlocks₁₁) (complexify S.stairA.toBlocks₁₂)
      0 (complexify S.stairA.toBlocks₂₂) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, stairA_inr_inl]

lemma stairA_c_comm :
    complexify S.stairA * complexify S.stairW
      = complexify S.stairW * complexify S.A := by
  rw [← complexify_mul, ← complexify_mul, stairA_conj]

/-- D1a(i): every eigenvalue of the second diagonal block is
antistable. -/
theorem stairA₂_antistable :
    ∀ μ ∈ spectrum ℂ (complexify S.stairA.toBlocks₂₂), 1 ≤ ‖μ‖ := by
  intro μ hμ
  by_contra hlt
  push Not at hlt
  -- extract an eigenvector
  have hspec : μ ∈ spectrum ℂ
      (Matrix.toLin' (complexify S.stairA.toBlocks₂₂)) := by
    rw [Matrix.spectrum_toLin']
    exact hμ
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    hspec).exists_hasEigenvector
  have hAv : complexify S.stairA.toBlocks₂₂ *ᵥ v = μ • v := by
    have h := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at h
  have hvne : v ≠ 0 := hv.2
  -- the second-block coordinate vector
  set y : (Fin S.rk1 ⊕ Fin S.rk2) → ℂ := Sum.elim 0 v with hy
  -- the antistable projection preserves the second block of `y`
  have hPay : ∀ i, (complexify S.stairPa *ᵥ y) (Sum.inr i) = v i := by
    intro i
    have h1 : complexify S.stairPa = 1 - complexify S.stairPs := by
      rw [eq_sub_iff_add_eq, ← complexify_one, ← complexify_add]
      rw [show S.stairPa + S.stairPs = 1 from by
        rw [add_comm]; exact S.stairPs_add_stairPa]
    rw [h1, Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec,
      stairPs_c_mulVec_inr, sub_zero]
    simp [hy]
  -- transferred annihilation identity
  have hann : Polynomial.aeval (complexify S.stairA)
      (antiPoly (complexify S.A)) * complexify S.stairPa = 0 := by
    have h2 : complexify S.stairPa = complexify S.stairW
        * complexify (antiProj S.A) * complexify S.stairWinv := by
      unfold stairPa
      rw [← complexify_mul, ← complexify_mul]
    rw [h2]
    calc Polynomial.aeval (complexify S.stairA)
          (antiPoly (complexify S.A))
          * (complexify S.stairW * complexify (antiProj S.A)
            * complexify S.stairWinv)
        = (Polynomial.aeval (complexify S.stairA)
            (antiPoly (complexify S.A)) * complexify S.stairW)
          * (complexify (antiProj S.A) * complexify S.stairWinv) := by
          simp only [Matrix.mul_assoc]
      _ = (complexify S.stairW * Polynomial.aeval (complexify S.A)
            (antiPoly (complexify S.A)))
          * (complexify (antiProj S.A) * complexify S.stairWinv) := by
          rw [aeval_intertwine S.stairA_c_comm]
      _ = complexify S.stairW
          * ((Polynomial.aeval (complexify S.A)
              (antiPoly (complexify S.A)) * complexify (antiProj S.A))
            * complexify S.stairWinv) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [antiPoly_mul_antiProj, Matrix.zero_mul, Matrix.mul_zero]
  -- push the annihilation to the second block
  have h0 : Polynomial.aeval (complexify S.stairA)
      (antiPoly (complexify S.A)) *ᵥ (complexify S.stairPa *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec, hann, Matrix.zero_mulVec]
  obtain ⟨X, hX⟩ := aeval_fromBlocks_triangular
    (complexify S.stairA.toBlocks₁₁) (complexify S.stairA.toBlocks₁₂)
    (complexify S.stairA.toBlocks₂₂) (antiPoly (complexify S.A))
  rw [S.stairA_c_blocks, hX] at h0
  have h3 : Polynomial.aeval (complexify S.stairA.toBlocks₂₂)
      (antiPoly (complexify S.A)) *ᵥ v = 0 := by
    funext i
    have h4 := congrFun h0 (Sum.inr i)
    rw [Matrix.fromBlocks_mulVec] at h4
    simp only [Sum.elim_inr, Pi.add_apply, Matrix.zero_mulVec,
      Pi.zero_apply, zero_add] at h4
    have h5 : ((complexify S.stairPa *ᵥ y) ∘ Sum.inr) = v := by
      funext k
      exact hPay k
    rw [h5] at h4
    exact h4
  -- eigenvalue calculus forces a root of the antistable factor
  rw [aeval_mulVec_eigenvector hAv] at h3
  have h6 : Polynomial.eval μ (antiPoly (complexify S.A)) = 0 := by
    by_contra hne
    exact hvne (by
      have := smul_eq_zero.mp h3
      rcases this with h | h
      · exact absurd h hne
      · exact h)
  exact antiPoly_root_ge (Polynomial.IsRoot.def.mpr h6) hlt

end GeneralSystem

end Estimation

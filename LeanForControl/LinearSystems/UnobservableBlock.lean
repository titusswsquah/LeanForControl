import LeanForControl.LinearSystems.Detectability
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Architect

/-!
# Unobservable trajectories have no antistable component

The algebraic heart of `lem:coercive`(1): for a block upper-triangular
system `A = [[A₁, A₁₂], [0, A₂]]` with `A₂` antistable and `(A, C)`
detectable, every vector whose whole `A`-orbit is invisible to `C` has
vanishing antistable block (`blk₂_eq_zero_of_unobservable`).

The proof is purely linear-algebraic (no Jordan form, no limits): the
unobservable subspace `N` is `A`-invariant and its image `π₂(N)` under the
antistable-block projection is `A₂`-invariant. If that image were nonzero
it would contain an `A₂`-eigenvector `w` at some `|λ| ≥ 1`; on the
invariant subspace `K = N ∩ π₂⁻¹(ℂ·w)` the map `A - λ` lands in the
strictly smaller `K₀ = N ∩ ker π₂`, so it has a kernel vector — an
undetected eigenvector at `|λ| ≥ 1`, contradicting detectability.

Also here: the Cayley–Hamilton window extension
(`unobservable_of_window`): output invisibility on a `dim`-length window
propagates to the whole orbit.
-/

namespace LinearSystems

open Matrix Module

/-! ### Cayley–Hamilton window extension -/

/-- If the output vanishes on a window of length `card ι`, it vanishes on
the whole orbit (Cayley–Hamilton). -/
theorem unobservable_of_window {𝕜 : Type*} [Field 𝕜] {ι κ' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ']
    (A : Matrix ι ι 𝕜) (C : Matrix κ' ι 𝕜) {v : ι → 𝕜}
    (h : ∀ k < Fintype.card ι, (C * A ^ k) *ᵥ v = 0) :
    ∀ k, (C * A ^ k) *ᵥ v = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge k (Fintype.card ι) with hk | hk
    · exact h k hk
    · rcases Nat.eq_zero_or_pos (Fintype.card ι) with hd0 | hd0
      · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd0
        have hv : v = 0 := funext fun i => (IsEmpty.false i).elim
        rw [hv, Matrix.mulVec_zero]
      · have hCH := Matrix.aeval_self_charpoly A
        have hdeg : A.charpoly.natDegree = Fintype.card ι :=
          Matrix.charpoly_natDegree_eq_dim A
        have hAd : A ^ Fintype.card ι
            = -∑ i ∈ Finset.range (Fintype.card ι),
                A.charpoly.coeff i • A ^ i := by
          have h1 := hCH
          rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ] at h1
          have hmonic : A.charpoly.coeff (Fintype.card ι) = 1 := by
            have hL := A.charpoly_monic
            rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] at hL
            exact hL
          rw [hmonic, one_smul] at h1
          exact eq_neg_of_add_eq_zero_right h1
        have hsplit : C * A ^ k
            = C * A ^ (k - Fintype.card ι) * A ^ Fintype.card ι := by
          rw [Matrix.mul_assoc, ← pow_add]
          congr 2
          omega
        rw [hsplit, hAd, Matrix.mul_neg, Matrix.neg_mulVec, neg_eq_zero,
          Matrix.mul_sum, Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [Matrix.mul_smul, Matrix.smul_mulVec]
        have heq : C * A ^ (k - Fintype.card ι) * A ^ i
            = C * A ^ (k - Fintype.card ι + i) := by
          rw [Matrix.mul_assoc, ← pow_add]
        rw [heq, ih (k - Fintype.card ι + i) (by omega), smul_zero]

/-! ### The vanishing theorem -/

variable {n₁ n₂ : ℕ} {κ' : Type*} [Fintype κ']

/-- **Unobservable vectors have no antistable block.** For a block
upper-triangular complex system with antistable `A₂` and detectable
`(A, C)`, `C A^k v = 0` for all `k` forces the second block of `v` to
vanish. -/
theorem blk₂_eq_zero_of_unobservable
    (A₁ : Matrix (Fin n₁) (Fin n₁) ℂ) (A₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℂ)
    (C : Matrix κ' (Fin n₁ ⊕ Fin n₂) ℂ)
    (hdet : IsDetectable (Matrix.fromBlocks A₁ A₁₂ 0 A₂) C)
    (hAnti : ∀ μ ∈ spectrum ℂ A₂, 1 ≤ ‖μ‖)
    {v : Fin n₁ ⊕ Fin n₂ → ℂ}
    (hv : ∀ k : ℕ, (C * Matrix.fromBlocks A₁ A₁₂ 0 A₂ ^ k) *ᵥ v = 0) :
    (fun i => v (Sum.inr i)) = 0 := by
  classical
  set A : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℂ :=
    Matrix.fromBlocks A₁ A₁₂ 0 A₂ with hA
  -- the unobservable subspace and the antistable projection
  set N : Submodule ℂ (Fin n₁ ⊕ Fin n₂ → ℂ) :=
    ⨅ k : ℕ, LinearMap.ker (C * A ^ k).mulVecLin with hN
  have hmemN : ∀ w, w ∈ N ↔ ∀ k, (C * A ^ k) *ᵥ w = 0 := by
    intro w
    simp [hN, Submodule.mem_iInf, LinearMap.mem_ker]
  have hNinv : ∀ w ∈ N, A *ᵥ w ∈ N := by
    intro w hw
    rw [hmemN] at hw ⊢
    intro k
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ]
    exact hw (k + 1)
  set π₂ : (Fin n₁ ⊕ Fin n₂ → ℂ) →ₗ[ℂ] (Fin n₂ → ℂ) :=
    LinearMap.funLeft ℂ ℂ Sum.inr with hπ
  have hπ₂apply : ∀ (w : Fin n₁ ⊕ Fin n₂ → ℂ) (i : Fin n₂),
      π₂ w i = w (Sum.inr i) := fun w i => rfl
  have hπA : ∀ w : Fin n₁ ⊕ Fin n₂ → ℂ, π₂ (A *ᵥ w) = A₂ *ᵥ π₂ w := by
    intro w
    have h1 : A *ᵥ w = Sum.elim
        (A₁ *ᵥ (w ∘ Sum.inl) + A₁₂ *ᵥ (w ∘ Sum.inr))
        ((0 : Matrix (Fin n₂) (Fin n₁) ℂ) *ᵥ (w ∘ Sum.inl)
          + A₂ *ᵥ (w ∘ Sum.inr)) := by
      rw [hA, Matrix.fromBlocks_mulVec]
    funext i
    rw [hπ₂apply, h1]
    simp only [Sum.elim_inr, Matrix.zero_mulVec, Pi.add_apply, Pi.zero_apply,
      zero_add]
    rfl
  -- the image of the unobservable subspace under `π₂`
  set Nπ : Submodule ℂ (Fin n₂ → ℂ) := N.map π₂ with hNπ
  suffices hbot : Nπ = ⊥ by
    have hvN : v ∈ N := (hmemN v).mpr hv
    have hπv : π₂ v ∈ Nπ := Submodule.mem_map_of_mem hvN
    rw [hbot, Submodule.mem_bot] at hπv
    funext i
    have := congrFun hπv i
    simpa [hπ₂apply] using this
  by_contra hne
  -- extract an `A₂`-eigenvector from the invariant image
  have hNπinv : ∀ w ∈ Nπ, A₂ *ᵥ w ∈ Nπ := by
    rintro w ⟨u, hu, rfl⟩
    exact ⟨A *ᵥ u, hNinv u hu, hπA u⟩
  haveI hNontriv : Nontrivial Nπ := Submodule.nontrivial_iff_ne_bot.mpr hne
  set A₂res : Module.End ℂ Nπ :=
    A₂.mulVecLin.restrict (fun w hw => hNπinv w hw) with hA₂res
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue A₂res
  obtain ⟨w, hw⟩ := hlam.exists_hasEigenvector
  have hwval : A₂ *ᵥ (w : Fin n₂ → ℂ) = lam • (w : Fin n₂ → ℂ) := by
    have heig := hw.apply_eq_smul
    have hval := congrArg Subtype.val heig
    simpa [hA₂res, LinearMap.restrict_apply, Matrix.mulVecLin_apply] using hval
  have hwne : (w : Fin n₂ → ℂ) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
  have hlam1 : 1 ≤ ‖lam‖ :=
    hAnti lam (mem_spectrum_of_mulVec_eq_smul hwne hwval)
  -- the invariant slice `K` and its floor `K₀`
  set K : Submodule ℂ (Fin n₁ ⊕ Fin n₂ → ℂ) :=
    N ⊓ Submodule.comap π₂ (Submodule.span ℂ {(w : Fin n₂ → ℂ)}) with hK
  set K₀ : Submodule ℂ (Fin n₁ ⊕ Fin n₂ → ℂ) :=
    N ⊓ LinearMap.ker π₂ with hK₀
  have hK₀K : K₀ ≤ K := by
    refine inf_le_inf_left N ?_
    intro u hu
    rw [LinearMap.mem_ker] at hu
    rw [Submodule.mem_comap, hu]
    exact Submodule.zero_mem _
  -- `(A - λ)` maps `K` into `K₀`
  have hAK : ∀ u ∈ K, A *ᵥ u - lam • u ∈ K₀ := by
    intro u hu
    obtain ⟨huN, huπ⟩ := Submodule.mem_inf.mp hu
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Submodule.sub_mem N (hNinv u huN) (Submodule.smul_mem N lam huN)
    · rw [LinearMap.mem_ker, map_sub, map_smul, hπA u]
      rw [Submodule.mem_comap, Submodule.mem_span_singleton] at huπ
      obtain ⟨c, hc⟩ := huπ
      rw [← hc, Matrix.mulVec_smul, hwval, smul_smul, smul_smul, mul_comm]
      exact sub_self _
  -- `K₀` is proper in `K`: a preimage of `w` lies in `K` but not `K₀`
  obtain ⟨u₀, hu₀N, hu₀π⟩ := w.2
  have hu₀K : u₀ ∈ K := by
    refine Submodule.mem_inf.mpr ⟨hu₀N, ?_⟩
    rw [Submodule.mem_comap, hu₀π]
    exact Submodule.mem_span_singleton_self _
  have hu₀notK₀ : u₀ ∉ K₀ := by
    intro hmem
    obtain ⟨-, hker⟩ := Submodule.mem_inf.mp hmem
    rw [LinearMap.mem_ker, hu₀π] at hker
    exact hwne hker
  have hlt : K₀ < K := lt_of_le_of_ne hK₀K fun h => hu₀notK₀ (h ▸ hu₀K)
  -- the restricted map `A - λ : K → K₀` cannot be injective
  set f : (Fin n₁ ⊕ Fin n₂ → ℂ) →ₗ[ℂ] (Fin n₁ ⊕ Fin n₂ → ℂ) :=
    A.mulVecLin - lam • LinearMap.id with hf
  have hfK : ∀ u : K, f (u : Fin n₁ ⊕ Fin n₂ → ℂ) ∈ K₀ := by
    intro u
    have h1 := hAK u u.2
    have h2 : f (u : Fin n₁ ⊕ Fin n₂ → ℂ)
        = A *ᵥ (u : Fin n₁ ⊕ Fin n₂ → ℂ)
          - lam • (u : Fin n₁ ⊕ Fin n₂ → ℂ) := by
      rw [hf]
      simp [Matrix.mulVecLin_apply]
    rw [h2]
    exact h1
  set g : K →ₗ[ℂ] K₀ := (f.domRestrict K).codRestrict K₀ hfK with hg
  have hker : LinearMap.ker g ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective g := LinearMap.ker_eq_bot.mp hbot
    have h1 : finrank ℂ K ≤ finrank ℂ K₀ :=
      LinearMap.finrank_le_finrank_of_injective hinj
    have h2 : finrank ℂ K₀ < finrank ℂ K :=
      Submodule.finrank_lt_finrank_of_lt hlt
    omega
  obtain ⟨u, huker, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hueig : A *ᵥ (u : Fin n₁ ⊕ Fin n₂ → ℂ)
      = lam • (u : Fin n₁ ⊕ Fin n₂ → ℂ) := by
    rw [LinearMap.mem_ker] at huker
    have h1 : f (u : Fin n₁ ⊕ Fin n₂ → ℂ) = 0 := by
      have h2 := congrArg Subtype.val huker
      simpa [hg] using h2
    rw [hf] at h1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Matrix.mulVecLin_apply] at h1
    linear_combination (norm := module) h1
  have hCu : C *ᵥ (u : Fin n₁ ⊕ Fin n₂ → ℂ) = 0 := by
    have h1 := (hmemN _).mp (Submodule.mem_inf.mp u.2).1 0
    rwa [pow_zero, Matrix.mul_one] at h1
  have huval_ne : (u : Fin n₁ ⊕ Fin n₂ → ℂ) ≠ 0 := fun h0 =>
    hune (Subtype.ext h0)
  exact huval_ne (hdet lam _ hlam1 hueig hCu)

end LinearSystems

import LeanForControl.LinearSystems.StabilizableBound
import Architect

/-!
# The real spectral split (S3 of the generality sprint)

Real stable/antistable Bezout projections for a real matrix `A`: the
complex projections built from the modulus-split factors of the
characteristic polynomial are invariant under entrywise conjugation
(the root multiset is conjugation-invariant and the projection does not
depend on the Bezout certificate, by a Cayley–Hamilton divisibility
argument), hence have real entries. Everything the staircase
construction (S4) needs is exported: idempotence, commutation, the sum
`Ps + Pa = 1`, and the factor annihilations over ℂ.
-/

namespace LinearSystems

open Matrix Polynomial

variable {d : ℕ}

/-- The characteristic polynomial of a complexified matrix is
conjugation-invariant. -/
lemma charpoly_complexify_conj (A : Matrix (Fin d) (Fin d) ℝ) :
    (complexify A).charpoly.map (starRingEnd ℂ)
      = (complexify A).charpoly := by
  have h1 : (complexify A).charpoly = A.charpoly.map Complex.ofRealHom := by
    have := Matrix.charpoly_map A Complex.ofRealHom
    rw [← this]
    rfl
  rw [h1, Polynomial.map_map]
  congr 1
  ext x
  simp [Complex.conj_ofReal]

/-- The root multiset of a complexified characteristic polynomial is
conjugation-invariant. -/
lemma roots_charpoly_complexify_conj (A : Matrix (Fin d) (Fin d) ℝ) :
    ((complexify A).charpoly.roots).map (starRingEnd ℂ)
      = (complexify A).charpoly.roots := by
  have hsplits : (complexify A).charpoly.Splits :=
    IsAlgClosed.splits (complexify A).charpoly
  have hcard : Multiset.card (complexify A).charpoly.roots
      = (complexify A).charpoly.natDegree :=
    Polynomial.splits_iff_card_roots.mp hsplits
  have h1 := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := (complexify A).charpoly) (f := starRingEnd ℂ)
    (RingHom.injective _) hcard
  rw [charpoly_complexify_conj] at h1
  exact h1

/-- The stable factor is conjugation-invariant. -/
lemma stabPoly_complexify_conj (A : Matrix (Fin d) (Fin d) ℝ) :
    (stabPoly (complexify A)).map (starRingEnd ℂ)
      = stabPoly (complexify A) := by
  unfold stabPoly
  have hmp := map_multiset_prod (Polynomial.mapRingHom (starRingEnd ℂ))
    ((((complexify A).charpoly.roots.filter
      (fun μ => ‖μ‖ < 1))).map (fun μ => X - C μ))
  simp only [Polynomial.coe_mapRingHom] at hmp
  rw [hmp, Multiset.map_map]
  congr 1
  have h1 : ((fun x => Polynomial.map (starRingEnd ℂ) x)
      ∘ fun μ => X - C μ) = (fun μ => X - C μ) ∘ (starRingEnd ℂ) := by
    funext μ
    simp only [Function.comp_apply, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
  rw [h1, ← Multiset.map_map]
  congr 1
  have h2 : ((complexify A).charpoly.roots.filter
      (fun μ => ‖μ‖ < 1)).map (starRingEnd ℂ)
      = ((complexify A).charpoly.roots.map (starRingEnd ℂ)).filter
        (fun μ => ‖μ‖ < 1) := by
    rw [Multiset.filter_map]
    congr 1
    refine Multiset.filter_congr fun μ _ => ?_
    simp
  rw [h2, roots_charpoly_complexify_conj]

/-- The antistable factor is conjugation-invariant. -/
lemma antiPoly_complexify_conj (A : Matrix (Fin d) (Fin d) ℝ) :
    (antiPoly (complexify A)).map (starRingEnd ℂ)
      = antiPoly (complexify A) := by
  unfold antiPoly
  have hmp := map_multiset_prod (Polynomial.mapRingHom (starRingEnd ℂ))
    ((((complexify A).charpoly.roots.filter
      (fun μ => ¬ ‖μ‖ < 1))).map (fun μ => X - C μ))
  simp only [Polynomial.coe_mapRingHom] at hmp
  rw [hmp, Multiset.map_map]
  congr 1
  have h1 : ((fun x => Polynomial.map (starRingEnd ℂ) x)
      ∘ fun μ => X - C μ) = (fun μ => X - C μ) ∘ (starRingEnd ℂ) := by
    funext μ
    simp only [Function.comp_apply, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
  rw [h1, ← Multiset.map_map]
  congr 1
  have h2 : ((complexify A).charpoly.roots.filter
      (fun μ => ¬ ‖μ‖ < 1)).map (starRingEnd ℂ)
      = ((complexify A).charpoly.roots.map (starRingEnd ℂ)).filter
        (fun μ => ¬ ‖μ‖ < 1) := by
    rw [Multiset.filter_map]
    congr 1
    refine Multiset.filter_congr fun μ _ => ?_
    simp
  rw [h2, roots_charpoly_complexify_conj]

/-- The spectral projection does not depend on the Bezout certificate
(a Cayley–Hamilton divisibility argument). -/
lemma bezout_proj_indep (M : Matrix (Fin d) (Fin d) ℂ)
    {u v u' v' : Polynomial ℂ}
    (h : u * stabPoly M + v * antiPoly M = 1)
    (h' : u' * stabPoly M + v' * antiPoly M = 1) :
    Polynomial.aeval M (v * antiPoly M)
      = Polynomial.aeval M (v' * antiPoly M) := by
  have h1 : (v - v') * antiPoly M = (u' - u) * stabPoly M := by
    have h0 : (u * stabPoly M + v * antiPoly M)
        - (u' * stabPoly M + v' * antiPoly M) = 0 := by
      rw [h, h']
      ring
    linear_combination h0
  have h2 : stabPoly M ∣ (v - v') * antiPoly M :=
    ⟨u' - u, by rw [h1]; ring⟩
  have h3 : stabPoly M ∣ (v - v') :=
    (isCoprime_stabPoly_antiPoly M).dvd_of_dvd_mul_right h2
  obtain ⟨w, hw⟩ := h3
  have h4 : v * antiPoly M - v' * antiPoly M
      = w * M.charpoly := by
    rw [← stabPoly_mul_antiPoly M]
    have h5 : v - v' = stabPoly M * w := hw
    linear_combination antiPoly M * h5
  have h6 : Polynomial.aeval M (v * antiPoly M)
      - Polynomial.aeval M (v' * antiPoly M) = 0 := by
    rw [← map_sub, h4, map_mul, Matrix.aeval_self_charpoly, mul_zero]
  exact sub_eq_zero.mp h6

/-- Entrywise conjugation of a polynomial in a matrix. -/
lemma map_conj_aeval (M : Matrix (Fin d) (Fin d) ℂ) (p : Polynomial ℂ) :
    (Polynomial.aeval M p).map (starRingEnd ℂ)
      = Polynomial.aeval (M.map (starRingEnd ℂ))
          (p.map (starRingEnd ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, map_add, ← hp, ← hq]
    funext i j
    simp [Matrix.map_apply]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.map_monomial,
      Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul, Matrix.one_mul]
    funext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      map_mul]
    congr 1
    -- entries of the mapped power
    have hpow : ∀ k : ℕ, (M ^ k).map (starRingEnd ℂ)
        = (M.map (starRingEnd ℂ)) ^ k := by
      intro k
      induction k with
      | zero =>
        funext i' j'
        simp [Matrix.map_apply, Matrix.one_apply, apply_ite]
      | succ k ih =>
        rw [pow_succ, pow_succ, ← ih]
        funext i' j'
        simp only [Matrix.map_apply, Matrix.mul_apply, map_sum,
          map_mul]
    have := congrFun (congrFun (hpow n) i) j
    simpa [Matrix.map_apply] using this

/-- **The real spectral split** (S3): real Bezout projections
separating the open-disc and closed-exterior spectra of a real
matrix. -/
theorem exists_real_split (A : Matrix (Fin d) (Fin d) ℝ) :
    ∃ Ps Pa : Matrix (Fin d) (Fin d) ℝ,
      Ps + Pa = 1 ∧
      A * Ps = Ps * A ∧ A * Pa = Pa * A ∧
      Ps * Ps = Ps ∧ Pa * Pa = Pa ∧
      Polynomial.aeval (complexify A) (stabPoly (complexify A))
        * complexify Ps = 0 ∧
      Polynomial.aeval (complexify A) (antiPoly (complexify A))
        * complexify Pa = 0 := by
  classical
  set M : Matrix (Fin d) (Fin d) ℂ := complexify A with hM
  obtain ⟨u, v, huv⟩ := isCoprime_stabPoly_antiPoly M
  set Psc : Matrix (Fin d) (Fin d) ℂ :=
    Polynomial.aeval M (v * antiPoly M) with hPsc
  -- conjugation invariance of the complex projection
  have hMconj : M.map (starRingEnd ℂ) = M := by
    funext i j
    simp [hM, Matrix.map_apply, complexify_apply, Complex.conj_ofReal]
  have hconjBezout : (v.map (starRingEnd ℂ)) * antiPoly M
      = ((v * antiPoly M).map (starRingEnd ℂ)) := by
    rw [Polynomial.map_mul, antiPoly_complexify_conj]
  have hconjBezoutPair :
      (u.map (starRingEnd ℂ)) * stabPoly M
        + (v.map (starRingEnd ℂ)) * antiPoly M = 1 := by
    have h1 := congrArg (Polynomial.map (starRingEnd ℂ)) huv
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_one] at h1
    rw [← stabPoly_complexify_conj A, ← antiPoly_complexify_conj A]
    exact h1
  have hconj : Psc.map (starRingEnd ℂ) = Psc := by
    rw [hPsc, map_conj_aeval, hMconj, ← hconjBezout]
    exact bezout_proj_indep M hconjBezoutPair huv
  -- extract the real projection
  set Ps : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (Psc i j).re
    with hPsR
  have hPsC : complexify Ps = Psc := by
    funext i j
    have h1 : (starRingEnd ℂ) (Psc i j) = Psc i j := by
      have := congrFun (congrFun hconj i) j
      simpa [Matrix.map_apply] using this
    have h2 : (Psc i j).im = 0 := by
      have h3 := Complex.conj_eq_iff_im.mp h1
      exact h3
    show ((Psc i j).re : ℂ) = Psc i j
    rw [← Complex.re_add_im (Psc i j), h2]
    simp
  -- the ℂ-side facts, once
  have hcommP : ∀ p : Polynomial ℂ,
      M * Polynomial.aeval M p = Polynomial.aeval M p * M := by
    intro p
    have h1 : M * Polynomial.aeval M p
        = Polynomial.aeval M (Polynomial.X * p) := by
      rw [map_mul, Polynomial.aeval_X]
    have h2 : Polynomial.aeval M p * M
        = Polynomial.aeval M (p * Polynomial.X) := by
      rw [map_mul, Polynomial.aeval_X]
    rw [h1, h2, mul_comm p Polynomial.X]
  have hchar0 : Polynomial.aeval M M.charpoly = 0 :=
    Matrix.aeval_self_charpoly M
  have hPsc2 : Psc * Psc = Psc := by
    have h2 : (v * antiPoly M) * (v * antiPoly M) - v * antiPoly M
        = -(v * u) * (stabPoly M * antiPoly M) := by
      have h3 : v * antiPoly M - 1 = -(u * stabPoly M) := by
        linear_combination huv
      calc (v * antiPoly M) * (v * antiPoly M) - v * antiPoly M
          = (v * antiPoly M) * (v * antiPoly M - 1) := by ring
      _ = (v * antiPoly M) * (-(u * stabPoly M)) := by rw [h3]
      _ = -(v * u) * (stabPoly M * antiPoly M) := by ring
    have h5 : Polynomial.aeval M (stabPoly M * antiPoly M)
        = (0 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [stabPoly_mul_antiPoly]
      exact hchar0
    have h4 : Psc * Psc - Psc = 0 := by
      show Polynomial.aeval M (v * antiPoly M)
          * Polynomial.aeval M (v * antiPoly M)
          - Polynomial.aeval M (v * antiPoly M) = 0
      rw [← map_mul, ← map_sub, h2, map_mul, h5, mul_zero]
    exact sub_eq_zero.mp h4
  have hMPsc : M * Psc = Psc * M := hcommP _
  have hstabPsc : Polynomial.aeval M (stabPoly M) * Psc = 0 := by
    rw [hPsc, ← map_mul,
      show stabPoly M * (v * antiPoly M)
        = v * (stabPoly M * antiPoly M) from by ring,
      stabPoly_mul_antiPoly, map_mul, hchar0, mul_zero]
  have hantiPac : Polynomial.aeval M (antiPoly M) * (1 - Psc) = 0 := by
    have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) - Psc
        = Polynomial.aeval M (u * stabPoly M) := by
      have h2 : Polynomial.aeval M (u * stabPoly M) + Psc = 1 := by
        rw [hPsc, ← map_add, huv, map_one]
      rw [← h2]
      abel
    rw [h1, ← map_mul,
      show antiPoly M * (u * stabPoly M)
        = u * (stabPoly M * antiPoly M) from by ring,
      stabPoly_mul_antiPoly, map_mul, hchar0, mul_zero]
  -- descend to ℝ
  have hcplxSub : complexify (1 - Ps) = 1 - complexify Ps := by
    funext i j
    simp [complexify_apply, Matrix.sub_apply, Matrix.one_apply,
      apply_ite]
  refine ⟨Ps, 1 - Ps, by abel, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply complexify_injective
    rw [complexify_mul, complexify_mul, hPsC]
    exact hMPsc
  · apply complexify_injective
    rw [complexify_mul, complexify_mul, hcplxSub, hPsC,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      hMPsc]
  · apply complexify_injective
    rw [complexify_mul, hPsC]
    exact hPsc2
  · apply complexify_injective
    rw [complexify_mul, hcplxSub, hPsC]
    have h1 : (1 - Psc) * (1 - Psc)
        = 1 - Psc - (Psc - Psc * Psc) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one]
    rw [h1, hPsc2, sub_self, sub_zero]
  · rw [hPsC]
    exact hstabPsc
  · rw [hcplxSub, hPsC]
    exact hantiPac

/-! ### The projections as definitions -/

/-- The real stable spectral projection (chosen). -/
noncomputable def stabProj (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (exists_real_split A).choose

/-- The real antistable spectral projection (chosen). -/
noncomputable def antiProj (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (exists_real_split A).choose_spec.choose

lemma stabProj_add_antiProj (A : Matrix (Fin d) (Fin d) ℝ) :
    stabProj A + antiProj A = 1 :=
  (exists_real_split A).choose_spec.choose_spec.1

lemma stabProj_comm (A : Matrix (Fin d) (Fin d) ℝ) :
    A * stabProj A = stabProj A * A :=
  (exists_real_split A).choose_spec.choose_spec.2.1

lemma antiProj_comm (A : Matrix (Fin d) (Fin d) ℝ) :
    A * antiProj A = antiProj A * A :=
  (exists_real_split A).choose_spec.choose_spec.2.2.1

lemma stabProj_idem (A : Matrix (Fin d) (Fin d) ℝ) :
    stabProj A * stabProj A = stabProj A :=
  (exists_real_split A).choose_spec.choose_spec.2.2.2.1

lemma antiProj_idem (A : Matrix (Fin d) (Fin d) ℝ) :
    antiProj A * antiProj A = antiProj A :=
  (exists_real_split A).choose_spec.choose_spec.2.2.2.2.1

lemma stabPoly_mul_stabProj (A : Matrix (Fin d) (Fin d) ℝ) :
    Polynomial.aeval (complexify A) (stabPoly (complexify A))
      * complexify (stabProj A) = 0 :=
  (exists_real_split A).choose_spec.choose_spec.2.2.2.2.2.1

lemma antiPoly_mul_antiProj (A : Matrix (Fin d) (Fin d) ℝ) :
    Polynomial.aeval (complexify A) (antiPoly (complexify A))
      * complexify (antiProj A) = 0 :=
  (exists_real_split A).choose_spec.choose_spec.2.2.2.2.2.2

/-- The real stable subspace. -/
noncomputable def stableSub (A : Matrix (Fin d) (Fin d) ℝ) :
    Submodule ℝ (Fin d → ℝ) :=
  LinearMap.range ((stabProj A).mulVecLin)

end LinearSystems

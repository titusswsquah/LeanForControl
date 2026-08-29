import LeanForControl.LinearSystems.LQ
import LeanForControl.LinearSystems.Schur
import LeanForControl.LinearSystems.Detectability
import LeanForControl.LinearSystems.StagedFacts
import LeanForControl.LinearSystems.Controllability
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Architect

/-!
# Uniform value bounds under stabilizability (M2 layer)

The quantitative heart of `fact:lqr`: under stabilizability the Riccati
value iterates admit a uniform quadratic bound. The route is a
**polynomial spectral split**: Bezout projections built from the
stable/antistable factors of the characteristic polynomial separate the
state into a geometrically decaying part (Gelfand, applied to `M·Ps`)
and a part inside the reachable subspace (Hautus pairing), which a
minimum-energy control removes in `n` steps.
-/

namespace LinearSystems

open Matrix Polynomial Filter

open scoped Matrix.Norms.Operator

variable {d : ℕ}

/-- The stable factor of the characteristic polynomial. -/
noncomputable def stabPoly (M : Matrix (Fin d) (Fin d) ℂ) : Polynomial ℂ :=
  ((M.charpoly.roots.filter (fun μ => ‖μ‖ < 1)).map
    (fun μ => Polynomial.X - Polynomial.C μ)).prod

/-- The antistable factor of the characteristic polynomial. -/
noncomputable def antiPoly (M : Matrix (Fin d) (Fin d) ℂ) : Polynomial ℂ :=
  ((M.charpoly.roots.filter (fun μ => ¬ ‖μ‖ < 1)).map
    (fun μ => Polynomial.X - Polynomial.C μ)).prod

lemma stabPoly_mul_antiPoly (M : Matrix (Fin d) (Fin d) ℂ) :
    stabPoly M * antiPoly M = M.charpoly := by
  have hmonic := M.charpoly_monic
  have hsplits : M.charpoly.Splits := IsAlgClosed.splits M.charpoly
  have hcard : Multiset.card M.charpoly.roots = M.charpoly.natDegree :=
    Polynomial.splits_iff_card_roots.mp hsplits
  have h1 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := M.charpoly) hcard
  rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul] at h1
  calc stabPoly M * antiPoly M
      = ((M.charpoly.roots.filter (fun μ => ‖μ‖ < 1)).map
          (fun μ => Polynomial.X - Polynomial.C μ)).prod
        * ((M.charpoly.roots.filter (fun μ => ¬ ‖μ‖ < 1)).map
          (fun μ => Polynomial.X - Polynomial.C μ)).prod := rfl
  _ = ((M.charpoly.roots.filter (fun μ => ‖μ‖ < 1)
        + M.charpoly.roots.filter (fun μ => ¬ ‖μ‖ < 1)).map
          (fun μ => Polynomial.X - Polynomial.C μ)).prod := by
      rw [Multiset.map_add, Multiset.prod_add]
  _ = M.charpoly := by
      rw [Multiset.filter_add_not]
      exact h1

lemma stabPoly_monic (M : Matrix (Fin d) (Fin d) ℂ) :
    (stabPoly M).Monic :=
  Polynomial.monic_multisetProd_X_sub_C _

lemma antiPoly_monic (M : Matrix (Fin d) (Fin d) ℂ) :
    (antiPoly M).Monic :=
  Polynomial.monic_multisetProd_X_sub_C _

lemma stabPoly_root_lt {M : Matrix (Fin d) (Fin d) ℂ} {μ : ℂ}
    (h : (stabPoly M).IsRoot μ) : ‖μ‖ < 1 := by
  unfold stabPoly at h
  rw [Polynomial.IsRoot.def, Polynomial.eval_multiset_prod] at h
  have hz := Multiset.prod_eq_zero_iff.mp h
  rw [Multiset.map_map, Multiset.mem_map] at hz
  obtain ⟨ν, hν, hz0⟩ := hz
  have h2 : μ = ν := by
    have h3 : Polynomial.eval μ (Polynomial.X - Polynomial.C ν) = 0 := by
      have h5 := hz0
      simpa using h5
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at h3
    exact h3
  have h4 := (Multiset.mem_filter.mp hν).2
  rwa [← h2] at h4

lemma antiPoly_root_ge {M : Matrix (Fin d) (Fin d) ℂ} {μ : ℂ}
    (h : (antiPoly M).IsRoot μ) : ¬ ‖μ‖ < 1 := by
  unfold antiPoly at h
  rw [Polynomial.IsRoot.def, Polynomial.eval_multiset_prod] at h
  have hz := Multiset.prod_eq_zero_iff.mp h
  rw [Multiset.map_map, Multiset.mem_map] at hz
  obtain ⟨ν, hν, hz0⟩ := hz
  have h2 : μ = ν := by
    have h3 : Polynomial.eval μ (Polynomial.X - Polynomial.C ν) = 0 := by
      have h5 := hz0
      simpa using h5
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at h3
    exact h3
  have h4 := (Multiset.mem_filter.mp hν).2
  rwa [← h2] at h4

/-- The stable and antistable factors are coprime. -/
lemma isCoprime_stabPoly_antiPoly (M : Matrix (Fin d) (Fin d) ℂ) :
    IsCoprime (stabPoly M) (antiPoly M) := by
  by_contra hnc
  have hgu : ¬ IsUnit (EuclideanDomain.gcd (stabPoly M) (antiPoly M)) :=
    fun h => hnc (EuclideanDomain.gcd_isUnit_iff.mp h)
  set g := EuclideanDomain.gcd (stabPoly M) (antiPoly M) with hgdef
  have hgs : g ∣ stabPoly M := EuclideanDomain.gcd_dvd_left _ _
  have hga : g ∣ antiPoly M := EuclideanDomain.gcd_dvd_right _ _
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 : stabPoly M = 0 := by
      have := hgs
      rw [h0] at this
      exact zero_dvd_iff.mp this
    exact (stabPoly_monic M).ne_zero h1
  have hdeg : 0 < g.degree := by
    rcases le_or_gt g.degree 0 with h | h
    · exfalso
      have hgc : g = Polynomial.C (g.coeff 0) :=
        Polynomial.eq_C_of_degree_le_zero h
      have ha : g.coeff 0 ≠ 0 := by
        intro h0
        exact hg0 (by rw [hgc, h0, Polynomial.C_0])
      refine hgu ?_
      rw [hgc]
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)
    · exact h
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hz1 : (stabPoly M).IsRoot z := by
    obtain ⟨q, hq⟩ := hgs
    rw [Polynomial.IsRoot.def, hq, Polynomial.eval_mul, hz, zero_mul]
  have hz2 : (antiPoly M).IsRoot z := by
    obtain ⟨q, hq⟩ := hga
    rw [Polynomial.IsRoot.def, hq, Polynomial.eval_mul, hz, zero_mul]
  exact antiPoly_root_ge hz2 (stabPoly_root_lt hz1)

end LinearSystems

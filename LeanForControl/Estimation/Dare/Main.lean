import LeanForControl.Estimation.Dare.Existence
import LeanForControl.Estimation.Dare.RateFloor
import Architect

/-!
# The odyssey headline theorems, assembled (Phase D close)

`thm:main` with **no hypothesized imports**: the strong solution's
existence (D4), `eq:Finf-spec` (D1), and the reduced import (D2/D3)
are all theorems, so the deck's dichotomy reads exactly as stated —
under C1 and the power-bounded marginal (the semisimple
qualification), the run from the prior is attracted to the (existing,
unique) strong solution **iff** C2w; with a marginal block present,
the repaired Part-2 converse holds; and the strong loop is Schur
**iff** C3w (`eq:Finf-c3w`).
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-- **`eq:Finf-c3w`, verified**: the strong loop is Schur stable iff
there is no marginal block. -/
theorem strong_isSchurStable_iff_C3w (hC1 : S.C1)
    (hS : S.IsStrongSolution Sinf) :
    IsSchurStable (errMap S.fullC S.R S.fullA Sinf)
      ↔ C3w (nm := nm) := by
  constructor
  · intro hSchur
    by_contra hnm
    obtain ⟨μ, hμ, hμ1⟩ := S.strong_exists_unit_eigenvalue hC1 hS
      (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hnm))
    have h := hSchur μ hμ
    rw [hμ1] at h
    exact lt_irrefl 1 h
  · intro hnm μ hμ
    rw [S.strong_spec_split hC1 hS] at hμ
    rcases hμ with hμ | hμ
    · exact S.strong_Fs_schur hC1 hS μ hμ
    · exfalso
      obtain ⟨v, hvne, _⟩ := exists_eigenvector_of_mem_spectrum hμ
      apply hvne
      have hnm' : nm = 0 := hnm
      subst hnm'
      funext i
      exact i.elim0

/-- **`thm:main`, Part 1, fully assembled** (Phase D exit): under C1
and the power-bounded marginal alone, the strong solution exists and
the run from the prior is attracted to it **iff** C2w. -/
theorem main_strong_attraction (hC1 : S.C1)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    ∃ Sinf, S.IsStrongSolution Sinf
      ∧ (Tendsto (fun T => ‖S.dare T - Sinf‖) atTop (nhds 0)
          ↔ S.C2w) := by
  obtain ⟨Sg, hSg⟩ := S.exists_strong_solution hC1
  exact ⟨Sg, hSg, S.strong_attraction_iff_C2w hC1 hSg hcm hPB⟩

/-- **`thm:main`, Part 2 converse, fully assembled**: with a marginal
block present (and the backward power bound — the semisimple
qualification), some C2 prior is not exponentially attracted. -/
theorem main_marg_not_exponential (hC1 : S.C1)
    (hnm : Nonempty (Fin nm)) {cm₂ : ℝ}
    (hPBi : ∀ k : ℕ, ‖(S.Am⁻¹) ^ k‖ ≤ cm₂) :
    ∃ Sinf, S.IsStrongSolution Sinf
      ∧ ¬∃ C ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ T : ℕ,
          ‖S.dareFrom (Sinf + embM n₁ na nm * (embM n₁ na nm)ᵀ) T
            - Sinf‖ ≤ C * ρ ^ T := by
  obtain ⟨Sg, hSg⟩ := S.exists_strong_solution hC1
  exact ⟨Sg, hSg, S.marg_not_exponential hC1 hSg hnm hPBi⟩

end DareSystem

end Dare
end Estimation

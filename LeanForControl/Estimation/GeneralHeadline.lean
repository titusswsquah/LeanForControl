import LeanForControl.Estimation.GeneralNecessity
import LeanForControl.Estimation.GES
import Architect

/-!
# The headline theorem in the paper's general coordinates

`thm:gas-ges-fi` of `costogo.tex` for an arbitrary `GeneralSystem` —
no canonical-form or block-diagonal-prior hypotheses: the
full-information estimator is GAS iff C1 ∧ C2, and GES iff
C1 ∧ C2 ∧ C3w, with the three conditions stated invariantly
(detectability; `ker Σ₀ ∩ 𝒳_{u,uc} = 0` for the annihilator-defined
unstable–uncontrollable subspace; no unit-circle unreachable modes).

Sufficiency and the C3w half of necessity transfer through the
staircase-plus-decoupling reduction (valid under C2); the C1 and C2
halves of necessity are proved directly at the general level in
`Estimation.GeneralNecessity`.
-/

namespace Estimation

namespace GeneralSystem

open LinearSystems

variable {n m p : ℕ} (S : GeneralSystem n m p)

theorem IsGES.isGAS {S : GeneralSystem n m p} (h : S.IsGES) :
    S.IsGAS := by
  obtain ⟨c, ρ, hc, hρ0, hρ1, hb⟩ := h
  refine ⟨fun T => c * ρ ^ T, ?_, hb⟩
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
  have h2 := h1.const_mul c
  simpa using h2

/-- **`thm:gas-ges-fi` (GAS half, general coordinates)**: the
full-information estimator is GAS iff C1 ∧ C2. -/
@[blueprint "thm:gas-fi-general"
  (statement := /-- For an arbitrary linear system with PSD prior
  $\Sigma_0$ (no structural hypotheses), the full-information estimator
  is GAS if and only if C1 and C2 hold, with C2 stated invariantly as
  $\ker \Sigma_0 \cap \mathcal{X}_{u,uc} = \{0\}$. -/)]
theorem isGAS_iff_C1_and_C2 : S.IsGAS ↔ S.C1 ∧ S.C2 := by
  constructor
  · intro h
    have hC1 := S.C1_of_isGAS h
    exact ⟨hC1, S.C2_of_isGAS hC1 h⟩
  · rintro ⟨hC1, hC2⟩
    refine S.isGAS_of_red hC2 (S.redSys.isGAS_iff_C1_and_C2.mpr
      ⟨S.red_C1_iff.mpr hC1, S.red_C2_iff.mpr hC2⟩)

/-- **`thm:gas-ges-fi` (GES half, general coordinates)**: the
full-information estimator is GES iff C1 ∧ C2 ∧ C3w. -/
@[blueprint "thm:ges-fi-general"
  (statement := /-- For an arbitrary linear system with PSD prior, the
  full-information estimator is GES if and only if C1, C2, and C3w
  hold. -/)]
theorem isGES_iff_C1_C2_C3w : S.IsGES ↔ S.C1 ∧ S.C2 ∧ S.C3w := by
  constructor
  · intro h
    have hgas : S.IsGAS := IsGES.isGAS h
    have hC1 := S.C1_of_isGAS hgas
    have hC2 := S.C2_of_isGAS hC1 hgas
    have hges' := S.red_isGES hC2 h
    have h3 := (S.redSys.isGES_iff_C1_C2_C3w.mp hges').2.2
    exact ⟨hC1, hC2, S.red_C3w_iff.mp h3⟩
  · rintro ⟨hC1, hC2, hC3w⟩
    refine S.isGES_of_red hC2 (S.redSys.isGES_iff_C1_C2_C3w.mpr
      ⟨S.red_C1_iff.mpr hC1, S.red_C2_iff.mpr hC2,
        S.red_C3w_iff.mpr hC3w⟩)

/-- **`thm:gas-ges-fi`** in full generality: the complete dichotomy. -/
@[blueprint "thm:gas-ges-fi-general"
  (statement := /-- The full-information estimator of an arbitrary
  linear system with PSD prior is GAS iff C1 ∧ C2 and GES iff
  C1 ∧ C2 ∧ C3w. -/)]
theorem gas_ges_dichotomy :
    (S.IsGAS ↔ S.C1 ∧ S.C2) ∧ (S.IsGES ↔ S.C1 ∧ S.C2 ∧ S.C3w) :=
  ⟨S.isGAS_iff_C1_and_C2, S.isGES_iff_C1_C2_C3w⟩

end GeneralSystem

end Estimation

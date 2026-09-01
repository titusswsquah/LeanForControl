import LeanForControl.Estimation.Dare.Reduced
import LeanForControl.LinearSystems.UniformExpStability
import Architect

/-!
# The reduced import, discharged (D3: `ReducedImport` is a theorem)

The declared import of `lem:condfilter`/`lem:lowsqueeze` — the
reduced `fact:dare-strong` plus the closed-loop product bound —
proved:

* the zero-seed reduced run converges to its stabilizing solution
  (`Dare/Reduced.lean`), and the strong solution's chart component
  `infP Σ∞` is itself a PSD fixed point of the reduced DARE
  (`strong_chart_fixed`) — whose loop is Schur by
  `fixed_point_schur` — so uniqueness identifies the two:
  `redP T → infP Σ∞` (`redP_tendsto_infP`);
* the reduced gains converge (`errMap` is continuous along a
  norm-convergent PSD run: resolvent identity for the innovation
  inverse, then the composable tendsto toolkit), so the closed-loop
  factors tend to the Schur limit loop and
  `transitionProd_norm_le_of_tendsto` (the verified half of
  `fact:uniexp`) gives a **geometric** product bound
  (`redProdF_geometric`) — of which the declared boundedness is a
  corollary (`reducedImport_holds`).

The geometric form feeds Phase E's rate work.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

variable {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}

/-! ### Continuity of the gain along a convergent PSD run -/

/-- The innovation inverses converge along a norm-convergent PSD run
(resolvent identity + the uniform `R`-floor bound). -/
lemma innovInv_tendsto_of_tendsto (hR : R.PosDef)
    {M : ℕ → Matrix ι ι ℝ} {Minf : Matrix ι ι ℝ}
    (hpsd : ∀ T, (M T).PosSemidef) (hMinf : Minf.PosSemidef)
    (h : Tendsto (fun T => ‖M T - Minf‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖(innov C R (M T))⁻¹ - (innov C R Minf)⁻¹‖)
      atTop (nhds 0) := by
  obtain ⟨bR, hbR, hbRb⟩ := innov_inv_norm_bound_general (C := C) hR
  have hinnov : Tendsto
      (fun T => ‖innov C R Minf - innov C R (M T)‖) atTop (nhds 0) := by
    have hid : ∀ T, innov C R Minf - innov C R (M T)
        = C * (Minf - M T) * Cᵀ := by
      intro T
      unfold innov
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel
    have hb2 : ∀ T, ‖innov C R Minf - innov C R (M T)‖
        ≤ ‖C‖ * ‖M T - Minf‖ * ‖Cᵀ‖ := by
      intro T
      rw [hid T]
      calc ‖C * (Minf - M T) * Cᵀ‖
          ≤ ‖C‖ * ‖Minf - M T‖ * ‖Cᵀ‖ := norm_triple_le _ _ _
      _ = ‖C‖ * ‖M T - Minf‖ * ‖Cᵀ‖ := by rw [norm_sub_rev]
    have hlim2 : Tendsto (fun T => ‖C‖ * ‖M T - Minf‖ * ‖Cᵀ‖)
        atTop (nhds 0) := by
      have h1 := (h.const_mul ‖C‖).mul_const ‖Cᵀ‖
      simpa using h1
    exact squeeze_zero (fun T => norm_nonneg _) hb2 hlim2
  have hb : ∀ T, ‖(innov C R (M T))⁻¹ - (innov C R Minf)⁻¹‖
      ≤ bR * ‖innov C R Minf - innov C R (M T)‖
        * ‖(innov C R Minf)⁻¹‖ := by
    intro T
    have hTPD : (innov C R (M T)).PosDef := innov_posDef hR (hpsd T)
    have hIPD : (innov C R Minf).PosDef := innov_posDef hR hMinf
    have hid : (innov C R (M T))⁻¹ - (innov C R Minf)⁻¹
        = (innov C R (M T))⁻¹
          * (innov C R Minf - innov C R (M T))
          * (innov C R Minf)⁻¹ := by
      have h1 : (innov C R (M T))⁻¹
          * (innov C R Minf - innov C R (M T))
          * (innov C R Minf)⁻¹
          = (innov C R (M T))⁻¹
              * (innov C R Minf * (innov C R Minf)⁻¹)
            - (innov C R (M T))⁻¹ * innov C R (M T)
              * (innov C R Minf)⁻¹ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        simp only [Matrix.mul_assoc]
      rw [h1, Matrix.mul_nonsing_inv _
          ((Matrix.isUnit_iff_isUnit_det _).mp hIPD.isUnit),
        Matrix.nonsing_inv_mul _
          ((Matrix.isUnit_iff_isUnit_det _).mp hTPD.isUnit),
        Matrix.mul_one, Matrix.one_mul]
    rw [hid]
    calc ‖(innov C R (M T))⁻¹
        * (innov C R Minf - innov C R (M T))
        * (innov C R Minf)⁻¹‖
        ≤ ‖(innov C R (M T))⁻¹‖
          * ‖innov C R Minf - innov C R (M T)‖
          * ‖(innov C R Minf)⁻¹‖ := norm_triple_le _ _ _
    _ ≤ bR * ‖innov C R Minf - innov C R (M T)‖
          * ‖(innov C R Minf)⁻¹‖ := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbRb _ (hpsd T))
            (norm_nonneg _)) (norm_nonneg _)
  have hlim : Tendsto (fun T =>
      bR * ‖innov C R Minf - innov C R (M T)‖
        * ‖(innov C R Minf)⁻¹‖) atTop (nhds 0) := by
    have h1 := (hinnov.const_mul bR).mul_const
      ‖(innov C R Minf)⁻¹‖
    simpa using h1
  exact squeeze_zero (fun T => norm_nonneg _) hb hlim

/-- The Kalman gains converge along a norm-convergent PSD run. -/
lemma kGain_tendsto_of_tendsto (hR : R.PosDef)
    {M : ℕ → Matrix ι ι ℝ} {Minf : Matrix ι ι ℝ}
    (hpsd : ∀ T, (M T).PosSemidef) (hMinf : Minf.PosSemidef)
    (h : Tendsto (fun T => ‖M T - Minf‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖kGain C R (M T) - kGain C R Minf‖)
      atTop (nhds 0) := by
  have h1 := tendsto_matmul
    (X := fun T => M T * Cᵀ) (Xl := Minf * Cᵀ)
    (Y := fun T => (innov C R (M T))⁻¹)
    (Yl := (innov C R Minf)⁻¹)
    (tendsto_matmul (X := M) (Xl := Minf)
      (Y := fun _ => (Cᵀ)) (Yl := Cᵀ) h (tendsto_matconst (Cᵀ)))
    (innovInv_tendsto_of_tendsto (C := C) hR hpsd hMinf h)
  unfold kGain
  exact h1

/-- The closed loops converge along a norm-convergent PSD run. -/
lemma errMap_tendsto_of_tendsto {A : Matrix ι ι ℝ} (hR : R.PosDef)
    {M : ℕ → Matrix ι ι ℝ} {Minf : Matrix ι ι ℝ}
    (hpsd : ∀ T, (M T).PosSemidef) (hMinf : Minf.PosSemidef)
    (h : Tendsto (fun T => ‖M T - Minf‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖errMap C R A (M T) - errMap C R A Minf‖)
      atTop (nhds 0) := by
  have hK := kGain_tendsto_of_tendsto (C := C) hR hpsd hMinf h
  have h2 := tendsto_matsub
    (X := fun _ => (1 : Matrix ι ι ℝ)) (Xl := 1)
    (Y := fun T => kGain C R (M T) * C) (Yl := kGain C R Minf * C)
    (tendsto_matconst (1 : Matrix ι ι ℝ))
    (tendsto_matmul (X := fun T => kGain C R (M T))
      (Xl := kGain C R Minf) (Y := fun _ => C) (Yl := C)
      hK (tendsto_matconst C))
  have h1 := tendsto_matmul (X := fun _ => A) (Xl := A)
    (Y := fun T => 1 - kGain C R (M T) * C)
    (Yl := 1 - kGain C R Minf * C)
    (tendsto_matconst A) h2
  unfold errMap
  exact h1

/-! ### The frame: `redP → infP Σ∞` and the product bound -/

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-- **The limit identification**: the zero-seed reduced run converges
to the strong solution's chart component — `infP Σ∞` is a PSD fixed
point of the reduced DARE (`strong_chart_fixed`), its loop is Schur
(`fixed_point_schur` needs stabilizability alone), and stabilizing
fixed points are unique. -/
theorem redP_tendsto_infP (hC1 : S.C1)
    (hS : S.IsStrongSolution Sinf) :
    Tendsto (fun T => ‖S.redP T - infP Sinf‖) atTop (nhds 0) := by
  obtain ⟨P, hPpsd, hPfix, hPschur, hPtend⟩ :=
    S.redP_exists_stabilizing hC1
  have hinffix : dareStep S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ)
      (infP Sinf) = infP Sinf :=
    (S.strong_chart_fixed hC1 hS).2.2
  have hinfpsd : (infP Sinf).PosSemidef := S.infP_posSemidef hS
  have hinfschur : IsSchurStable (errMap S.C₁ S.R S.A₁ (infP Sinf)) :=
    fixed_point_schur S.hR S.hQ hinfpsd hinffix S.hStab
  have hEq : P = infP Sinf :=
    stabilizing_fixed_unique S.hR hPpsd hinfpsd hPfix hinffix
      hPschur hinfschur
  rwa [hEq] at hPtend

/-- The reduced loops converge to the strong chart loop. -/
lemma redL_tendsto (hC1 : S.C1) (hS : S.IsStrongSolution Sinf) :
    Tendsto (fun T => ‖S.redL T
      - errMap S.C₁ S.R S.A₁ (infP Sinf)‖) atTop (nhds 0) :=
  errMap_tendsto_of_tendsto S.hR (fun T => S.redP_posSemidef T)
    (S.infP_posSemidef hS) (S.redP_tendsto_infP hC1 hS)

/-- The frame's products are the generic transition products. -/
lemma redProdF_eq_transitionProd (j k : ℕ) :
    S.redProdF j k = transitionProd S.redL j k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [redProdF, transitionProd, ih]

/-- **The geometric product bound** (`fact:uniexp`, consumed
direction, on the reduced run): the closed-loop transition products
decay geometrically, uniformly in the start time. -/
theorem redProdF_geometric (hC1 : S.C1)
    (hS : S.IsStrongSolution Sinf) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ j k : ℕ,
      ‖S.redProdF j k‖ ≤ c * ρ ^ k := by
  have hLlim : Tendsto S.redL atTop
      (nhds (errMap S.C₁ S.R S.A₁ (infP Sinf))) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (S.redL_tendsto hC1 hS)
  have hinfschur : IsSchurStable (errMap S.C₁ S.R S.A₁ (infP Sinf)) :=
    fixed_point_schur S.hR S.hQ (S.infP_posSemidef hS)
      ((S.strong_chart_fixed hC1 hS).2.2) S.hStab
  obtain ⟨c, ρ, hc, hρ0, hρ1, hb⟩ :=
    transitionProd_norm_le_of_tendsto S.redL _ hLlim hinfschur
  refine ⟨c, ρ, hc, hρ0, hρ1, fun j k => ?_⟩
  rw [S.redProdF_eq_transitionProd]
  exact hb j k

/-- **D3: the declared import is a theorem.** Under C1 and the strong
solution, `ReducedImport` holds — the reduced `fact:dare-strong`
(`redP → infP Σ∞`) and the uniform product bound. -/
theorem reducedImport_holds (hC1 : S.C1)
    (hS : S.IsStrongSolution Sinf) : S.ReducedImport Sinf := by
  obtain ⟨c, ρ, hc, hρ0, hρ1, hb⟩ := S.redProdF_geometric hC1 hS
  refine ⟨S.redP_tendsto_infP hC1 hS, c, hc.le, fun j k => ?_⟩
  calc ‖S.redProdF j k‖ ≤ c * ρ ^ k := hb j k
  _ ≤ c * 1 := by
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      exact pow_le_one₀ hρ0.le hρ1.le
  _ = c := mul_one c

end DareSystem

end Dare
end Estimation

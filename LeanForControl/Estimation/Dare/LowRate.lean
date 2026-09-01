import LeanForControl.Estimation.Dare.RateEngine
import Architect

/-!
# The lower anchor, geometrically (E2)

The Phase-B convergence chain of the slaved trajectory upgraded to
geometric rates, using the E1 engine and D3's geometric products:

`redP` (the reduced Riccati) → the gain chain (Lipschitz) → `Λₘₐ`
(closed form) → `Λ₁ₐ` (`lam_unroll` + convolution) → `Ξ` → the
information error (`conj_unroll` at `ρ(Aₐ⁻¹)²`) → `Σₐₐ` (resolvent)
→ the assembled `lowsqueeze_geometric` — `lem:condfilter`-3's,
`lem:jtransform`'s and `lem:lowsqueeze`'s "exponentially fast",
verified, marginal block included.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

/-! ### Geometric decay and its combinators -/

/-- A sequence is geometrically decaying. -/
def GeoDecay (f : ℕ → ℝ) : Prop :=
  ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ T, f T ≤ C * ρ ^ T

lemma GeoDecay.mono {f g : ℕ → ℝ} (h : GeoDecay f)
    (hle : ∀ T, g T ≤ f T) : GeoDecay g := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hb⟩ := h
  exact ⟨C, ρ, hC, hρ0, hρ1, fun T => le_trans (hle T) (hb T)⟩

lemma GeoDecay.add {f g : ℕ → ℝ} (hf : GeoDecay f)
    (hg : GeoDecay g) : GeoDecay (fun T => f T + g T) := by
  obtain ⟨C₁, ρ₁, hC₁, hρ₁0, hρ₁1, hb₁⟩ := hf
  obtain ⟨C₂, ρ₂, hC₂, hρ₂0, hρ₂1, hb₂⟩ := hg
  refine ⟨C₁ + C₂, max ρ₁ ρ₂, add_nonneg hC₁ hC₂,
    lt_max_of_lt_left hρ₁0, max_lt hρ₁1 hρ₂1, fun T => ?_⟩
  have h1 : ρ₁ ^ T ≤ (max ρ₁ ρ₂) ^ T :=
    pow_le_pow_left₀ hρ₁0.le (le_max_left _ _) T
  have h2 : ρ₂ ^ T ≤ (max ρ₁ ρ₂) ^ T :=
    pow_le_pow_left₀ hρ₂0.le (le_max_right _ _) T
  calc f T + g T ≤ C₁ * ρ₁ ^ T + C₂ * ρ₂ ^ T :=
        add_le_add (hb₁ T) (hb₂ T)
  _ ≤ C₁ * (max ρ₁ ρ₂) ^ T + C₂ * (max ρ₁ ρ₂) ^ T :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hC₁)
        (mul_le_mul_of_nonneg_left h2 hC₂)
  _ = (C₁ + C₂) * (max ρ₁ ρ₂) ^ T := by ring

lemma GeoDecay.const_mul {f : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : GeoDecay f) : GeoDecay (fun T => c * f T) := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hb⟩ := hf
  refine ⟨c * C, ρ, mul_nonneg hc hC, hρ0, hρ1, fun T => ?_⟩
  calc c * f T ≤ c * (C * ρ ^ T) :=
        mul_le_mul_of_nonneg_left (hb T) hc
  _ = c * C * ρ ^ T := by ring

lemma geoDecay_pow {c ρ : ℝ} (hc : 0 ≤ c) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) : GeoDecay (fun T => c * ρ ^ T) :=
  ⟨c, ρ, hc, hρ0, hρ1, fun _ => le_rfl⟩

lemma GeoDecay.bound {f : ℕ → ℝ} (h : GeoDecay f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T, f T ≤ B := by
  obtain ⟨C, ρ, hC, hρ0, hρ1, hb⟩ := h
  refine ⟨C, hC, fun T => le_trans (hb T) ?_⟩
  calc C * ρ ^ T ≤ C * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hρ0.le hρ1.le) hC
  _ = C := mul_one C

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-! ### The reduced Riccati rate (E2.1) -/

/-- **`redP` converges geometrically**: the exact two-seed
factorization `P_T − P∞ = Φ(T,0)·(P₀ − P∞)·(L∞ᵀ)^T` against the
geometric products (D3) and the Schur limit loop. -/
theorem redP_geometric (hC1 : S.C1) (hS : S.IsStrongSolution Sinf) :
    GeoDecay (fun T => ‖S.redP T - infP Sinf‖) := by
  have hfix := (S.strong_chart_fixed hC1 hS).2.2
  have herec : ∀ T, S.redP (T + 1) - infP Sinf
      = S.redL T * (S.redP T - infP Sinf)
        * (errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ := by
    intro T
    have h1 : S.redP (T + 1)
        = dareStep S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ)
          (S.redP T) := rfl
    rw [h1]
    conv_lhs => rw [← hfix]
    exact dareStep_diff S.hR (S.redP_posSemidef T)
      (S.infP_posSemidef hS)
  have hunroll : ∀ T, S.redP T - infP Sinf
      = S.redProdF 0 T * (S.redP 0 - infP Sinf)
        * ((errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ) ^ T := by
    intro T
    induction T with
    | zero => simp [redProdF]
    | succ T ih =>
      rw [herec T, ih]
      calc S.redL T * (S.redProdF 0 T * (S.redP 0 - infP Sinf)
            * ((errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ) ^ T)
            * (errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ
          = (S.redL T * S.redProdF 0 T) * (S.redP 0 - infP Sinf)
            * (((errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ) ^ T
              * (errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ) := by
            simp only [Matrix.mul_assoc]
      _ = S.redProdF 0 (T + 1) * (S.redP 0 - infP Sinf)
            * ((errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ) ^ (T + 1) := by
          rw [← pow_succ,
            show S.redProdF 0 (T + 1)
              = S.redL (0 + T) * S.redProdF 0 T from rfl,
            Nat.zero_add]
  obtain ⟨cΦ, ρΦ, hcΦ, hρΦ0, hρΦ1, hΦ⟩ := S.redProdF_geometric hC1 hS
  have hLschur : IsSchurStable (errMap S.C₁ S.R S.A₁ (infP Sinf)) :=
    fixed_point_schur S.hR S.hQ (S.infP_posSemidef hS) hfix S.hStab
  obtain ⟨cL, γL, hcL, hγ0, hγ1, hLp⟩ := hLschur.exists_pow_norm_le
  refine ⟨cΦ * ‖S.redP 0 - infP Sinf‖
      * ((Fintype.card (Fin n₁) : ℝ) * cL), ρΦ * γL, by positivity,
    by positivity, by nlinarith, fun T => ?_⟩
  show ‖S.redP T - infP Sinf‖ ≤ _
  rw [hunroll T]
  have hTp : ‖((errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ) ^ T‖
      ≤ (Fintype.card (Fin n₁) : ℝ) * (cL * γL ^ T) := by
    rw [← Matrix.transpose_pow]
    refine le_trans (linfty_opNorm_transpose_le' _) ?_
    exact mul_le_mul_of_nonneg_left (hLp T) (Nat.cast_nonneg _)
  calc ‖S.redProdF 0 T * (S.redP 0 - infP Sinf)
      * ((errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ) ^ T‖
      ≤ ‖S.redProdF 0 T‖ * ‖S.redP 0 - infP Sinf‖
        * ‖((errMap S.C₁ S.R S.A₁ (infP Sinf))ᵀ) ^ T‖ :=
        norm_triple_le _ _ _
  _ ≤ (cΦ * ρΦ ^ T) * ‖S.redP 0 - infP Sinf‖
        * ((Fintype.card (Fin n₁) : ℝ) * (cL * γL ^ T)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right (hΦ 0 T)
        (norm_nonneg _)) hTp (norm_nonneg _) ?_
      positivity
  _ = cΦ * ‖S.redP 0 - infP Sinf‖
        * ((Fintype.card (Fin n₁) : ℝ) * cL) * (ρΦ * γL) ^ T := by
      rw [mul_pow]
      ring

/-! ### The marginal loading rate (E2.2) -/

/-- **`Λₘₐ` decays geometrically** (the closed form against the Schur
`Aₐ⁻¹` and the power-bounded marginal). -/
theorem lowLamma_geometric {cm : ℝ}
    (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    GeoDecay (fun T => ‖S.lowLamma T‖) := by
  obtain ⟨ca, γa, hca, hγ0, hγ1, hap⟩ :=
    S.Aa_inv_isSchurStable.exists_pow_norm_le
  have hcm0 : 0 ≤ cm := le_trans (norm_nonneg _) (hPB 0)
  refine ⟨cm * ‖S.lam0‖ * ca, γa, by positivity, hγ0, hγ1,
    fun T => ?_⟩
  show ‖S.Am ^ T * S.lam0 * (S.Aa⁻¹) ^ T‖ ≤ _
  calc ‖S.Am ^ T * S.lam0 * (S.Aa⁻¹) ^ T‖
      ≤ ‖S.Am ^ T‖ * ‖S.lam0‖ * ‖(S.Aa⁻¹) ^ T‖ :=
        norm_triple_le _ _ _
  _ ≤ (cm * ‖S.lam0‖) * (ca * γa ^ T) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right (hPB T)
        (norm_nonneg _)) (hap T) (norm_nonneg _) ?_
      positivity
  _ = cm * ‖S.lam0‖ * ca * γa ^ T := by ring


/-! ### The conditional loading rate (E2.3, `lem:condfilter`-3) -/

set_option maxHeartbeats 1600000 in
/-- **`Λ₁ₐ` converges geometrically**: the error recursion rides the
geometric products against the Schur `Aₐ⁻¹`, driven by the loop and
drive errors, both geometric — the rate form of `lem:condfilter`-3. -/
theorem lowLam1a_geometric (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    {cm : ℝ} (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    GeoDecay (fun T => ‖S.lowLam1a T - infLam Sinf‖) := by
  classical
  -- the drive error
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → Matrix (Fin n₁) (Fin na) ℝ,
      η = fun T =>
        (S.redL T - errMap S.C₁ S.R S.A₁ (infP Sinf))
          * infLam Sinf * S.Aa⁻¹
        + (S.dOf (S.redP T) (S.lowLamma T)
          - S.dOf (infP Sinf) 0) := ⟨_, rfl⟩
  -- the error recursion
  have hfixΛ : infLam Sinf
      = errMap S.C₁ S.R S.A₁ (infP Sinf) * infLam Sinf * S.Aa⁻¹
        + S.dOf (infP Sinf) 0 := by
    conv_lhs => rw [← (S.strong_chart_fixed hC1 hS).2.1]
    rw [S.lamNext_eq]
  have herec : ∀ T, (fun T => S.lowLam1a T - infLam Sinf) (T + 1)
      = S.redL T * (fun T => S.lowLam1a T - infLam Sinf) T
          * S.Aa⁻¹ + η T := by
    intro T
    dsimp only
    rw [S.lowLam1a_rec T, hηdef]
    conv_lhs => rw [hfixΛ]
    dsimp only
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  -- the drive error is geometric
  have hPrate := S.redP_geometric hC1 hS
  have hΛmrate := S.lowLamma_geometric hPB
  obtain ⟨bP, hbP, hbPb⟩ := hPrate.bound
  obtain ⟨cE, hcE, hcEb⟩ :=
    errMap_diff_norm_le (C := S.C₁) (A := S.A₁) S.hR
      (S.infP_posSemidef hS)
  obtain ⟨cK, hcK, hcKb⟩ :=
    kGain_diff_norm_le (C := S.C₁) S.hR (S.infP_posSemidef hS)
  obtain ⟨bR, hbR, hbRb⟩ :=
    innov_inv_norm_bound_general (C := S.C₁) S.hR
  -- a uniform bound on the running gain
  have hKbd : ∀ T, ‖kGain S.C₁ S.R (S.redP T)‖
      ≤ cK * bP + ‖kGain S.C₁ S.R (infP Sinf)‖ := by
    intro T
    calc ‖kGain S.C₁ S.R (S.redP T)‖
        = ‖(kGain S.C₁ S.R (S.redP T)
            - kGain S.C₁ S.R (infP Sinf))
          + kGain S.C₁ S.R (infP Sinf)‖ := by rw [sub_add_cancel]
    _ ≤ ‖kGain S.C₁ S.R (S.redP T)
          - kGain S.C₁ S.R (infP Sinf)‖
        + ‖kGain S.C₁ S.R (infP Sinf)‖ := norm_add_le _ _
    _ ≤ cK * bP + ‖kGain S.C₁ S.R (infP Sinf)‖ := by
        refine add_le_add ?_ le_rfl
        calc ‖kGain S.C₁ S.R (S.redP T)
            - kGain S.C₁ S.R (infP Sinf)‖
            ≤ cK * ‖S.redP T - infP Sinf‖ :=
              hcKb _ (S.redP_posSemidef T)
        _ ≤ cK * bP := mul_le_mul_of_nonneg_left (hbPb T) hcK
  -- the dOf difference, identified and bounded
  have hdof0 : S.dOf (infP Sinf) 0
      = (S.A₁₂ * ea2 na nm
        - S.A₁ * kGain S.C₁ S.R (infP Sinf)
          * (S.fullC * embA n₁ na nm)) * S.Aa⁻¹ := by
    unfold dOf
    congr 1
    rw [Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
  have hdofdiff : ∀ T,
      S.dOf (S.redP T) (S.lowLamma T) - S.dOf (infP Sinf) 0
      = (S.A₁₂ * em2 na nm * S.lowLamma T
        - (S.A₁ * kGain S.C₁ S.R (S.redP T)
            - S.A₁ * kGain S.C₁ S.R (infP Sinf))
          * (S.fullC * embA n₁ na nm)
        - S.A₁ * kGain S.C₁ S.R (S.redP T)
          * (S.fullC * embM n₁ na nm * S.lowLamma T)) * S.Aa⁻¹ := by
    intro T
    rw [hdof0]
    unfold dOf
    rw [← Matrix.sub_mul]
    congr 1
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have hdofb : ∀ T,
      ‖S.dOf (S.redP T) (S.lowLamma T) - S.dOf (infP Sinf) 0‖
      ≤ ((‖S.A₁₂ * em2 na nm‖ * ‖S.lowLamma T‖
          + ‖S.A₁‖ * (cK * ‖S.redP T - infP Sinf‖)
            * ‖S.fullC * embA n₁ na nm‖
          + ‖S.A₁‖ * (cK * bP + ‖kGain S.C₁ S.R (infP Sinf)‖)
            * (‖S.fullC * embM n₁ na nm‖ * ‖S.lowLamma T‖)))
        * ‖S.Aa⁻¹‖ := by
    intro T
    rw [hdofdiff T]
    refine le_trans (Matrix.linfty_opNorm_mul _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine le_trans (norm_sub_le _ _) ?_
    refine add_le_add (le_trans (norm_sub_le _ _)
      (add_le_add ?_ ?_)) ?_
    · exact Matrix.linfty_opNorm_mul _ _
    · have h1 : S.A₁ * kGain S.C₁ S.R (S.redP T)
          - S.A₁ * kGain S.C₁ S.R (infP Sinf)
          = S.A₁ * (kGain S.C₁ S.R (S.redP T)
            - kGain S.C₁ S.R (infP Sinf)) := by
        rw [Matrix.mul_sub]
      rw [h1]
      calc ‖S.A₁ * (kGain S.C₁ S.R (S.redP T)
            - kGain S.C₁ S.R (infP Sinf))
          * (S.fullC * embA n₁ na nm)‖
          ≤ ‖S.A₁‖ * ‖kGain S.C₁ S.R (S.redP T)
              - kGain S.C₁ S.R (infP Sinf)‖
            * ‖S.fullC * embA n₁ na nm‖ := norm_triple_le _ _ _
      _ ≤ ‖S.A₁‖ * (cK * ‖S.redP T - infP Sinf‖)
            * ‖S.fullC * embA n₁ na nm‖ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (hcKb _ (S.redP_posSemidef T)) (norm_nonneg _))
            (norm_nonneg _)
    · calc ‖S.A₁ * kGain S.C₁ S.R (S.redP T)
          * (S.fullC * embM n₁ na nm * S.lowLamma T)‖
          ≤ ‖S.A₁‖ * ‖kGain S.C₁ S.R (S.redP T)‖
            * ‖S.fullC * embM n₁ na nm * S.lowLamma T‖ :=
            norm_triple_le _ _ _
      _ ≤ ‖S.A₁‖ * (cK * bP + ‖kGain S.C₁ S.R (infP Sinf)‖)
            * (‖S.fullC * embM n₁ na nm‖ * ‖S.lowLamma T‖) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hKbd T)
            (norm_nonneg _)) (Matrix.linfty_opNorm_mul _ _)
            (norm_nonneg _) ?_
          positivity
  -- η is geometric
  have hηgeo : GeoDecay (fun T => ‖η T‖) := by
    have hpart1 : GeoDecay (fun T =>
        ‖(S.redL T - errMap S.C₁ S.R S.A₁ (infP Sinf))
          * infLam Sinf * S.Aa⁻¹‖) := by
      refine GeoDecay.mono
        ((hPrate.const_mul (c := cE * (‖infLam Sinf‖ * ‖S.Aa⁻¹‖))
          (by positivity))) fun T => ?_
      calc ‖(S.redL T - errMap S.C₁ S.R S.A₁ (infP Sinf))
          * infLam Sinf * S.Aa⁻¹‖
          ≤ ‖S.redL T - errMap S.C₁ S.R S.A₁ (infP Sinf)‖
            * ‖infLam Sinf‖ * ‖S.Aa⁻¹‖ := norm_triple_le _ _ _
      _ ≤ (cE * ‖S.redP T - infP Sinf‖)
            * ‖infLam Sinf‖ * ‖S.Aa⁻¹‖ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (hcEb _ (S.redP_posSemidef T)) (norm_nonneg _))
            (norm_nonneg _)
      _ = cE * (‖infLam Sinf‖ * ‖S.Aa⁻¹‖)
            * ‖S.redP T - infP Sinf‖ := by ring
    have hpart2 : GeoDecay (fun T =>
        ‖S.dOf (S.redP T) (S.lowLamma T) - S.dOf (infP Sinf) 0‖) := by
      have hsum : GeoDecay (fun T =>
          (‖S.A₁₂ * em2 na nm‖
              + ‖S.A₁‖ * (cK * bP + ‖kGain S.C₁ S.R (infP Sinf)‖)
                * ‖S.fullC * embM n₁ na nm‖) * ‖S.Aa⁻¹‖
              * ‖S.lowLamma T‖
          + ‖S.A₁‖ * cK * ‖S.fullC * embA n₁ na nm‖ * ‖S.Aa⁻¹‖
              * ‖S.redP T - infP Sinf‖) := by
        refine GeoDecay.add ?_ ?_
        · exact hΛmrate.const_mul (by positivity)
        · exact hPrate.const_mul (by positivity)
      refine hsum.mono fun T => ?_
      refine le_trans (hdofb T) ?_
      have h0m : (0:ℝ) ≤ ‖S.lowLamma T‖ := norm_nonneg _
      have h0p : (0:ℝ) ≤ ‖S.redP T - infP Sinf‖ := norm_nonneg _
      have h0a : (0:ℝ) ≤ ‖S.Aa⁻¹‖ := norm_nonneg _
      nlinarith [norm_nonneg (S.A₁₂ * em2 na nm),
        norm_nonneg S.A₁, norm_nonneg (S.fullC * embA n₁ na nm),
        norm_nonneg (S.fullC * embM n₁ na nm),
        norm_nonneg (kGain S.C₁ S.R (infP Sinf)),
        mul_nonneg (mul_nonneg hcK hbP)
          (norm_nonneg (kGain S.C₁ S.R (infP Sinf)))]
    refine GeoDecay.mono (hpart1.add hpart2) fun T => ?_
    rw [hηdef]
    exact norm_add_le _ _
  -- unroll and convolve
  obtain ⟨Cη, ση, hCη, hση0, hση1, hηb⟩ := hηgeo
  obtain ⟨cΦ, ρΦ, hcΦ, hρΦ0, hρΦ1, hΦ⟩ := S.redProdF_geometric hC1 hS
  obtain ⟨ca, γa, hca, hγ0, hγ1, hap⟩ :=
    S.Aa_inv_isSchurStable.exists_pow_norm_le
  have hunroll := S.lam_unroll
    (x := fun T => S.lowLam1a T - infLam Sinf) (d := η) herec
  have hx : ∀ T, ‖S.lowLam1a T - infLam Sinf‖
      ≤ (cΦ * ‖S.lowLam1a 0 - infLam Sinf‖ * ca) * (ρΦ * γa) ^ T
        + (cΦ * Cη * ca)
          * ∑ j ∈ Finset.range T,
              (ρΦ * γa) ^ (T - 1 - j) * ση ^ j := by
    intro T
    have hu := hunroll T
    dsimp only at hu
    rw [hu]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · calc ‖S.redProdF 0 T * (S.lowLam1a 0 - infLam Sinf)
          * (S.Aa⁻¹) ^ T‖
          ≤ ‖S.redProdF 0 T‖ * ‖S.lowLam1a 0 - infLam Sinf‖
            * ‖(S.Aa⁻¹) ^ T‖ := norm_triple_le _ _ _
      _ ≤ (cΦ * ρΦ ^ T) * ‖S.lowLam1a 0 - infLam Sinf‖
            * (ca * γa ^ T) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hΦ 0 T)
            (norm_nonneg _)) (hap T) (norm_nonneg _) ?_
          positivity
      _ = (cΦ * ‖S.lowLam1a 0 - infLam Sinf‖ * ca)
            * (ρΦ * γa) ^ T := by
          rw [mul_pow]
          ring
    · refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      calc ‖S.redProdF (j + 1) (T - 1 - j) * η j
          * (S.Aa⁻¹) ^ (T - 1 - j)‖
          ≤ ‖S.redProdF (j + 1) (T - 1 - j)‖ * ‖η j‖
            * ‖(S.Aa⁻¹) ^ (T - 1 - j)‖ := norm_triple_le _ _ _
      _ ≤ (cΦ * ρΦ ^ (T - 1 - j)) * (Cη * ση ^ j)
            * (ca * γa ^ (T - 1 - j)) := by
          refine mul_le_mul (mul_le_mul (hΦ _ _) (hηb j)
            (norm_nonneg _) (by positivity)) (hap _)
            (norm_nonneg _) ?_
          positivity
      _ = (cΦ * Cη * ca)
            * ((ρΦ * γa) ^ (T - 1 - j) * ση ^ j) := by
          rw [mul_pow]
          ring
  obtain ⟨C, ρ, hC, hρ0, hρ1, hb⟩ := rate_of_unroll_bound
    (by positivity) (by positivity)
    (by positivity : (0:ℝ) ≤ ρΦ * γa) (by nlinarith)
    (by positivity : (0:ℝ) ≤ ρΦ * γa) (by nlinarith)
    hση0.le hση1 hx
  exact ⟨C, ρ, hC, hρ0, hρ1, hb⟩


/-! ### The effective observation and information rates (E2.4) -/

/-- The effective observation difference, identified. -/
lemma ceff_diff_eq (Λ : Matrix (Fin n₁) (Fin na) ℝ)
    (Λm : Matrix (Fin nm) (Fin na) ℝ) :
    S.ceff Λ Λm - S.ceff (infLam Sinf) 0
      = S.C₁ * (Λ - infLam Sinf)
        + S.fullC * embM n₁ na nm * Λm := by
  unfold ceff
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_sub]
  abel

/-- **The effective observation converges geometrically.** -/
theorem ceff_geometric (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    {cm : ℝ} (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    GeoDecay (fun T => ‖S.ceff (S.lowLam1a T) (S.lowLamma T)
      - S.ceff (infLam Sinf) 0‖) := by
  have hΛ := S.lowLam1a_geometric hC1 hS hPB
  have hΛm := S.lowLamma_geometric hPB
  refine GeoDecay.mono
    ((hΛ.const_mul (c := ‖S.C₁‖) (norm_nonneg _)).add
      (hΛm.const_mul (c := ‖S.fullC * embM n₁ na nm‖)
        (norm_nonneg _))) fun T => ?_
  rw [S.ceff_diff_eq]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · exact Matrix.linfty_opNorm_mul _ _
  · exact Matrix.linfty_opNorm_mul _ _

set_option maxHeartbeats 1600000 in
/-- **The information source converges geometrically**
(`Ξ_T → Ξ∞`). -/
theorem lowXi_geometric (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    {cm : ℝ} (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    GeoDecay (fun T =>
      ‖(S.ceff (S.lowLam1a T) (S.lowLamma T))ᵀ
          * (innov S.C₁ S.R (S.redP T))⁻¹
          * S.ceff (S.lowLam1a T) (S.lowLamma T)
        - (S.ceff (infLam Sinf) 0)ᵀ
          * (innov S.C₁ S.R (infP Sinf))⁻¹
          * S.ceff (infLam Sinf) 0‖) := by
  have hV := S.ceff_geometric hC1 hS hPB
  have hP := S.redP_geometric hC1 hS
  obtain ⟨bV, hbV, hbVb⟩ := hV.bound
  obtain ⟨bR, hbR, hbRb⟩ :=
    innov_inv_norm_bound_general (C := S.C₁) S.hR
  obtain ⟨cI, hcI, hcIb⟩ := innovInv_diff_norm_le (C := S.C₁) S.hR
  set K1 := (Fintype.card (Fin p) : ℝ)
  have hVbd : ∀ T, ‖S.ceff (S.lowLam1a T) (S.lowLamma T)‖
      ≤ bV + ‖S.ceff (infLam Sinf) 0‖ := by
    intro T
    calc ‖S.ceff (S.lowLam1a T) (S.lowLamma T)‖
        = ‖(S.ceff (S.lowLam1a T) (S.lowLamma T)
            - S.ceff (infLam Sinf) 0) + S.ceff (infLam Sinf) 0‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖S.ceff (S.lowLam1a T) (S.lowLamma T)
          - S.ceff (infLam Sinf) 0‖
        + ‖S.ceff (infLam Sinf) 0‖ := norm_add_le _ _
    _ ≤ bV + ‖S.ceff (infLam Sinf) 0‖ := by
        exact add_le_add (hbVb T) le_rfl
  set bV' := bV + ‖S.ceff (infLam Sinf) 0‖
  have hbV'0 : 0 ≤ bV' := le_trans (norm_nonneg _) (hVbd 0)
  refine GeoDecay.mono
    (((hV.const_mul (c := K1 * (bR * bV')) (by positivity)).add
      ((hP.const_mul
        (c := K1 * ‖S.ceff (infLam Sinf) 0‖ * cI * bV')
        (by positivity)).add
      (hV.const_mul
        (c := K1 * ‖S.ceff (infLam Sinf) 0‖ * bR)
        (by positivity))))) fun T => ?_
  dsimp only
  refine le_trans (diff_norm_triple_le _ _ _ _ _ _) ?_
  have hK10 : (0:ℝ) ≤ K1 := Nat.cast_nonneg _
  have h1 : ‖(S.ceff (S.lowLam1a T) (S.lowLamma T))ᵀ
      - (S.ceff (infLam Sinf) 0)ᵀ‖
      ≤ K1 * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)
          - S.ceff (infLam Sinf) 0‖ := by
    rw [← Matrix.transpose_sub]
    exact linfty_opNorm_transpose_le' _
  have h2 : ‖(innov S.C₁ S.R (S.redP T))⁻¹
      - (innov S.C₁ S.R (infP Sinf))⁻¹‖
      ≤ cI * ‖S.redP T - infP Sinf‖ :=
    hcIb _ _ (S.redP_posSemidef T) (S.infP_posSemidef hS)
  have h3 : ‖(S.ceff (infLam Sinf) 0)ᵀ‖
      ≤ K1 * ‖S.ceff (infLam Sinf) 0‖ :=
    linfty_opNorm_transpose_le' _
  have h4 := hbRb (S.redP T) (S.redP_posSemidef T)
  have h5 := hbRb (infP Sinf) (S.infP_posSemidef hS)
  have h6 := hVbd T
  have ht1 : ‖(S.ceff (S.lowLam1a T) (S.lowLamma T))ᵀ
        - (S.ceff (infLam Sinf) 0)ᵀ‖
      * ‖(innov S.C₁ S.R (S.redP T))⁻¹‖
      * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)‖
      ≤ K1 * (bR * bV')
        * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)
            - S.ceff (infLam Sinf) 0‖ := by
    calc ‖(S.ceff (S.lowLam1a T) (S.lowLamma T))ᵀ
          - (S.ceff (infLam Sinf) 0)ᵀ‖
        * ‖(innov S.C₁ S.R (S.redP T))⁻¹‖
        * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)‖
        ≤ (K1 * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)
            - S.ceff (infLam Sinf) 0‖) * bR * bV' := by
          refine mul_le_mul (mul_le_mul h1 h4 (norm_nonneg _)
            (by positivity)) h6 (norm_nonneg _) (by positivity)
    _ = K1 * (bR * bV')
          * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)
              - S.ceff (infLam Sinf) 0‖ := by ring
  have ht2 : ‖(S.ceff (infLam Sinf) 0)ᵀ‖
      * ‖(innov S.C₁ S.R (S.redP T))⁻¹
          - (innov S.C₁ S.R (infP Sinf))⁻¹‖
      * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)‖
      ≤ K1 * ‖S.ceff (infLam Sinf) 0‖ * cI * bV'
        * ‖S.redP T - infP Sinf‖ := by
    calc ‖(S.ceff (infLam Sinf) 0)ᵀ‖
        * ‖(innov S.C₁ S.R (S.redP T))⁻¹
            - (innov S.C₁ S.R (infP Sinf))⁻¹‖
        * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)‖
        ≤ (K1 * ‖S.ceff (infLam Sinf) 0‖)
          * (cI * ‖S.redP T - infP Sinf‖) * bV' := by
          refine mul_le_mul (mul_le_mul h3 h2 (norm_nonneg _)
            (by positivity)) h6 (norm_nonneg _) (by positivity)
    _ = K1 * ‖S.ceff (infLam Sinf) 0‖ * cI * bV'
          * ‖S.redP T - infP Sinf‖ := by ring
  have ht3 : ‖(S.ceff (infLam Sinf) 0)ᵀ‖
      * ‖(innov S.C₁ S.R (infP Sinf))⁻¹‖
      * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)
          - S.ceff (infLam Sinf) 0‖
      ≤ K1 * ‖S.ceff (infLam Sinf) 0‖ * bR
        * ‖S.ceff (S.lowLam1a T) (S.lowLamma T)
            - S.ceff (infLam Sinf) 0‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact mul_le_mul h3 h5 (norm_nonneg _) (by positivity)
  linarith

/-! ### The information recursion rate (E2.5, `lem:jtransform`) -/

/-- The strong solution's information fixed point (the inverse form
of `strong_chart_fixed`.1). -/
lemma strong_Jfix (hC1 : S.C1) (hS : S.IsStrongSolution Sinf) :
    ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
      = (S.Aaᵀ)⁻¹ * (((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
          + (S.ceff (infLam Sinf) 0)ᵀ
            * (innov S.C₁ S.R (infP Sinf))⁻¹
            * S.ceff (infLam Sinf) 0) * S.Aa⁻¹ := by
  have hcorner := S.strong_corner_posDef hS
  have hcornerU : IsUnit ((embA n₁ na nm)ᵀ * Sinf
      * embA n₁ na nm).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hcorner.isUnit
  have hUPD : (S.uhatOf (infP Sinf) (infLam Sinf) 0
      ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)).PosDef :=
    S.uhatOf_posDef (S.infP_posSemidef hS) _ _ hcorner
  have hUinv : (S.uhatOf (infP Sinf) (infLam Sinf) 0
      ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm))⁻¹
      = ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
        + (S.ceff (infLam Sinf) 0)ᵀ
          * (innov S.C₁ S.R (infP Sinf))⁻¹
          * S.ceff (infLam Sinf) 0 := by
    unfold uhatOf
    exact uhat_inv_eq rfl
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (S.sfullOf_posDef (S.infP_posSemidef hS) _ _
          hcorner.posSemidef).isUnit)
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (innov_posDef S.hR (S.infP_posSemidef hS)).isUnit)
      ((Matrix.isUnit_iff_isUnit_det _).mp hcorner.isUnit)
  conv_lhs => rw [← (S.strong_chart_fixed hC1 hS).1]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUinv]
  simp only [Matrix.mul_assoc]

set_option maxHeartbeats 1600000 in
/-- **The antistable information converges geometrically**
(`eq:J1-home` with its rate, `lem:jtransform`). -/
theorem lowJ_geometric (hC1 : S.C1) (hSa : S.Siga.PosDef)
    (hS : S.IsStrongSolution Sinf) {δ : ℝ} (hδ : 0 < δ)
    {cm : ℝ} (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    GeoDecay (fun T => ‖(S.lowSaa δ T)⁻¹
      - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹‖) := by
  classical
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → Matrix (Fin na) (Fin na) ℝ,
      η = fun T => (S.Aaᵀ)⁻¹
        * ((S.ceff (S.lowLam1a T) (S.lowLamma T))ᵀ
            * (innov S.C₁ S.R (S.redP T))⁻¹
            * S.ceff (S.lowLam1a T) (S.lowLamma T)
          - (S.ceff (infLam Sinf) 0)ᵀ
            * (innov S.C₁ S.R (infP Sinf))⁻¹
            * S.ceff (infLam Sinf) 0) * S.Aa⁻¹ := ⟨_, rfl⟩
  have herec : ∀ T, (fun T => (S.lowSaa δ T)⁻¹
      - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹) (T + 1)
      = (S.Aaᵀ)⁻¹ * (fun T => (S.lowSaa δ T)⁻¹
          - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹) T
          * S.Aa⁻¹ + η T := by
    intro T
    dsimp only
    rw [S.lowJ_rec hSa hδ T, hηdef]
    conv_lhs => rw [S.strong_Jfix hC1 hS]
    dsimp only
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul]
    abel
  have hΞ := S.lowXi_geometric hC1 hS hPB
  have hηgeo : GeoDecay (fun T => ‖η T‖) := by
    refine GeoDecay.mono
      (hΞ.const_mul (c := ‖(S.Aaᵀ)⁻¹‖ * ‖S.Aa⁻¹‖) (by positivity))
      fun T => ?_
    rw [hηdef]
    dsimp only
    calc ‖(S.Aaᵀ)⁻¹ * _ * S.Aa⁻¹‖
        ≤ ‖(S.Aaᵀ)⁻¹‖ * _ * ‖S.Aa⁻¹‖ := norm_triple_le _ _ _
    _ = ‖(S.Aaᵀ)⁻¹‖ * ‖S.Aa⁻¹‖ * _ := by ring
  obtain ⟨Cη, ση, hCη, hση0, hση1, hηb⟩ := hηgeo
  obtain ⟨ca, γa, hca, hγ0, hγ1, hap⟩ :=
    S.Aa_inv_isSchurStable.exists_pow_norm_le
  set Ka := (Fintype.card (Fin na) : ℝ)
  have hKa0 : (0:ℝ) ≤ Ka := Nat.cast_nonneg _
  have hAtp : ∀ k : ℕ, ‖((S.Aaᵀ)⁻¹) ^ k‖ ≤ Ka * (ca * γa ^ k) := by
    intro k
    have h1 : (S.Aaᵀ)⁻¹ = (S.Aa⁻¹)ᵀ :=
      (Matrix.transpose_nonsing_inv _).symm
    rw [h1, ← Matrix.transpose_pow]
    refine le_trans (linfty_opNorm_transpose_le' _) ?_
    exact mul_le_mul_of_nonneg_left (hap k) hKa0
  have hunroll := conj_unroll (L := (S.Aaᵀ)⁻¹) (B := S.Aa⁻¹)
    (e := fun T => (S.lowSaa δ T)⁻¹
      - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹)
    (η := η) herec
  have hx : ∀ T, ‖(S.lowSaa δ T)⁻¹
      - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹‖
      ≤ (Ka * ca * ‖(S.lowSaa δ 0)⁻¹
          - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹‖ * ca)
          * (γa * γa) ^ T
        + (Ka * ca * Cη * ca)
          * ∑ j ∈ Finset.range T,
              (γa * γa) ^ (T - 1 - j) * ση ^ j := by
    intro T
    have hu := hunroll T
    dsimp only at hu
    rw [hu]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · calc ‖((S.Aaᵀ)⁻¹) ^ T * ((S.lowSaa δ 0)⁻¹
          - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹)
          * (S.Aa⁻¹) ^ T‖
          ≤ ‖((S.Aaᵀ)⁻¹) ^ T‖ * ‖(S.lowSaa δ 0)⁻¹
              - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹‖
            * ‖(S.Aa⁻¹) ^ T‖ := norm_triple_le _ _ _
      _ ≤ (Ka * (ca * γa ^ T)) * ‖(S.lowSaa δ 0)⁻¹
            - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹‖
            * (ca * γa ^ T) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hAtp T)
            (norm_nonneg _)) (hap T) (norm_nonneg _) ?_
          positivity
      _ = (Ka * ca * ‖(S.lowSaa δ 0)⁻¹
            - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹‖ * ca)
            * (γa * γa) ^ T := by
          rw [mul_pow]
          ring
    · refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      calc ‖((S.Aaᵀ)⁻¹) ^ (T - 1 - j) * η j
          * (S.Aa⁻¹) ^ (T - 1 - j)‖
          ≤ ‖((S.Aaᵀ)⁻¹) ^ (T - 1 - j)‖ * ‖η j‖
            * ‖(S.Aa⁻¹) ^ (T - 1 - j)‖ := norm_triple_le _ _ _
      _ ≤ (Ka * (ca * γa ^ (T - 1 - j))) * (Cη * ση ^ j)
            * (ca * γa ^ (T - 1 - j)) := by
          refine mul_le_mul (mul_le_mul (hAtp _) (hηb j)
            (norm_nonneg _) (by positivity)) (hap _)
            (norm_nonneg _) ?_
          positivity
      _ = (Ka * ca * Cη * ca)
            * ((γa * γa) ^ (T - 1 - j) * ση ^ j) := by
          rw [mul_pow]
          ring
  obtain ⟨C, ρ, hC, hρ0, hρ1, hb⟩ := rate_of_unroll_bound
    (by positivity) (by positivity)
    (by positivity : (0:ℝ) ≤ γa * γa) (by nlinarith)
    (by positivity : (0:ℝ) ≤ γa * γa) (by nlinarith)
    hση0.le hση1 hx
  exact ⟨C, ρ, hC, hρ0, hρ1, hb⟩

set_option maxHeartbeats 1600000 in
/-- **The antistable block converges geometrically** (the resolvent
transfer of `lowJ_geometric`). -/
theorem lowSaa_geometric (hC1 : S.C1) (hSa : S.Siga.PosDef)
    (hS : S.IsStrongSolution Sinf) {δ : ℝ} (hδ : 0 < δ)
    {cm : ℝ} (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    GeoDecay (fun T => ‖S.lowSaa δ T
      - (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖) := by
  have hJ := S.lowJ_geometric hC1 hSa hS hδ hPB
  have hcorner := S.strong_corner_posDef hS
  -- a uniform bound on the running block
  have himp := S.reducedImport_holds hC1 hS
  have hqual := S.lowSaa_tendsto hC1 hSa hS hδ himp hPB
  obtain ⟨B, hB, hBb⟩ := exists_bound_of_tendsto_zero hqual
  have hSbd : ∀ T, ‖S.lowSaa δ T‖
      ≤ B + ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖ := by
    intro T
    calc ‖S.lowSaa δ T‖
        = ‖(S.lowSaa δ T
            - (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
          + (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖S.lowSaa δ T
          - (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖
        + ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖ :=
        norm_add_le _ _
    _ ≤ B + ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖ :=
        add_le_add (hBb T) le_rfl
  refine GeoDecay.mono
    (hJ.const_mul
      (c := (B + ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖)
        * ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖)
      (by positivity)) fun T => ?_
  have hTPD := S.lowSaa_posDef hSa hδ T
  have hres : S.lowSaa δ T - (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm
      = S.lowSaa δ T
        * (((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
          - (S.lowSaa δ T)⁻¹)
        * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm) := by
    have h1 : S.lowSaa δ T
        * (((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
          - (S.lowSaa δ T)⁻¹)
        * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
        = S.lowSaa δ T
            * (((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
              * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm))
          - S.lowSaa δ T * (S.lowSaa δ T)⁻¹
            * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp hcorner.isUnit),
      Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hTPD.isUnit),
      Matrix.mul_one, Matrix.one_mul]
  rw [hres]
  calc ‖S.lowSaa δ T
      * (((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
        - (S.lowSaa δ T)⁻¹)
      * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)‖
      ≤ ‖S.lowSaa δ T‖
        * ‖((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
            - (S.lowSaa δ T)⁻¹‖
        * ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖ :=
        norm_triple_le _ _ _
  _ ≤ (B + ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖)
        * ‖(S.lowSaa δ T)⁻¹
            - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹‖
        * ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖ := by
      rw [norm_sub_rev]
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hSbd T) (norm_nonneg _))
        (norm_nonneg _)
  _ = (B + ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖)
        * ‖(embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm‖
        * ‖(S.lowSaa δ T)⁻¹
            - ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹‖ := by
      ring

set_option maxHeartbeats 1600000 in
/-- **`lem:lowsqueeze`, with its rate**: the slaved trajectory is
attracted to the strong solution geometrically — marginal block
included. -/
theorem lowsqueeze_geometric (hC1 : S.C1) (hSa : S.Siga.PosDef)
    (hS : S.IsStrongSolution Sinf) {δ : ℝ} (hδ : 0 < δ)
    {cm : ℝ} (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ T, ‖S.dareFrom (S.slavedSeed δ) T - Sinf‖ ≤ C * ρ ^ T := by
  have hP := S.redP_geometric hC1 hS
  have hΛ := S.lowLam1a_geometric hC1 hS hPB
  have hΛm := S.lowLamma_geometric hPB
  have hSaa := S.lowSaa_geometric hC1 hSa hS hδ hPB
  -- the chart difference
  have hdec : ∀ T, S.dareFrom (S.slavedSeed δ) T - Sinf
      = emb1 n₁ na nm * (S.redP T - infP Sinf) * (emb1 n₁ na nm)ᵀ
        + (condV (S.lowLam1a T) (S.lowLamma T) * S.lowSaa δ T
            * (condV (S.lowLam1a T) (S.lowLamma T))ᵀ
          - condV (infLam Sinf) 0
            * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
            * (condV (infLam Sinf) 0)ᵀ) := by
    intro T
    rw [S.lowTraj_decomp hSa hδ T]
    conv_lhs => rw [S.strong_decomp hC1 hS]
    rw [Matrix.mul_sub (emb1 n₁ na nm), Matrix.sub_mul]
    abel
  -- the loading-vector difference
  have hVdiff : ∀ T,
      condV (S.lowLam1a T) (S.lowLamma T) - condV (infLam Sinf) 0
      = emb1 n₁ na nm * (S.lowLam1a T - infLam Sinf)
        + embM n₁ na nm * S.lowLamma T := by
    intro T
    unfold condV
    simp only [Matrix.mul_zero, add_zero, Matrix.mul_sub]
    abel
  have hVgeo : GeoDecay (fun T =>
      ‖condV (S.lowLam1a T) (S.lowLamma T)
        - condV (infLam Sinf) 0‖) := by
    refine GeoDecay.mono
      ((hΛ.const_mul (c := ‖emb1 n₁ na nm‖) (norm_nonneg _)).add
        (hΛm.const_mul (c := ‖embM n₁ na nm‖) (norm_nonneg _)))
      fun T => ?_
    rw [hVdiff T]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · exact Matrix.linfty_opNorm_mul _ _
    · exact Matrix.linfty_opNorm_mul _ _
  obtain ⟨bVd, hbVd, hbVdb⟩ := hVgeo.bound
  obtain ⟨bS, hbS, hbSb⟩ := hSaa.bound
  set K := (Fintype.card (ix n₁ na nm) : ℝ)
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg _
  set Vinf := condV (infLam Sinf) (0 : Matrix (Fin nm) (Fin na) ℝ)
  set SaaInf := (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm
  have hVbd : ∀ T, ‖condV (S.lowLam1a T) (S.lowLamma T)‖
      ≤ bVd + ‖Vinf‖ := by
    intro T
    calc ‖condV (S.lowLam1a T) (S.lowLamma T)‖
        = ‖(condV (S.lowLam1a T) (S.lowLamma T) - Vinf) + Vinf‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖ + ‖Vinf‖ :=
        norm_add_le _ _
    _ ≤ bVd + ‖Vinf‖ := add_le_add (hbVdb T) le_rfl
  have hSbd : ∀ T, ‖S.lowSaa δ T‖ ≤ bS + ‖SaaInf‖ := by
    intro T
    calc ‖S.lowSaa δ T‖
        = ‖(S.lowSaa δ T - SaaInf) + SaaInf‖ := by rw [sub_add_cancel]
    _ ≤ ‖S.lowSaa δ T - SaaInf‖ + ‖SaaInf‖ := norm_add_le _ _
    _ ≤ bS + ‖SaaInf‖ := add_le_add (hbSb T) le_rfl
  -- assemble the geometric bound
  have hgeo : GeoDecay (fun T =>
      ‖S.dareFrom (S.slavedSeed δ) T - Sinf‖) := by
    refine GeoDecay.mono
      (((hP.const_mul
          (c := ‖emb1 n₁ na nm‖ * ‖(emb1 n₁ na nm)ᵀ‖)
          (by positivity)).add
        (((hVgeo.const_mul
            (c := (bS + ‖SaaInf‖) * (K * (bVd + ‖Vinf‖))
              + ‖Vinf‖ * ‖SaaInf‖ * K)
            (by positivity)).add
          (hSaa.const_mul
            (c := ‖Vinf‖ * (K * (bVd + ‖Vinf‖)))
            (by positivity)))))) fun T => ?_
    rw [hdec T]
    refine le_trans (norm_add_le _ _) ?_
    have hpart1 : ‖emb1 n₁ na nm * (S.redP T - infP Sinf)
        * (emb1 n₁ na nm)ᵀ‖
        ≤ ‖emb1 n₁ na nm‖ * ‖(emb1 n₁ na nm)ᵀ‖
          * ‖S.redP T - infP Sinf‖ := by
      calc ‖emb1 n₁ na nm * (S.redP T - infP Sinf)
          * (emb1 n₁ na nm)ᵀ‖
          ≤ ‖emb1 n₁ na nm‖ * ‖S.redP T - infP Sinf‖
            * ‖(emb1 n₁ na nm)ᵀ‖ := norm_triple_le _ _ _
      _ = _ := by ring
    have hpart2 : ‖condV (S.lowLam1a T) (S.lowLamma T)
        * S.lowSaa δ T
        * (condV (S.lowLam1a T) (S.lowLamma T))ᵀ
        - Vinf * SaaInf * Vinfᵀ‖
        ≤ ((bS + ‖SaaInf‖) * (K * (bVd + ‖Vinf‖))
            + ‖Vinf‖ * ‖SaaInf‖ * K)
          * ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖
          + ‖Vinf‖ * (K * (bVd + ‖Vinf‖))
            * ‖S.lowSaa δ T - SaaInf‖ := by
      refine le_trans (diff_norm_triple_le _ _ _ _ _ _) ?_
      have h1 : ‖(condV (S.lowLam1a T) (S.lowLamma T))ᵀ‖
          ≤ K * (bVd + ‖Vinf‖) := by
        refine le_trans (linfty_opNorm_transpose_le' _) ?_
        exact mul_le_mul_of_nonneg_left (hVbd T) hK0
      have h2 : ‖(condV (S.lowLam1a T) (S.lowLamma T))ᵀ - Vinfᵀ‖
          ≤ K * ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖ := by
        rw [← Matrix.transpose_sub]
        exact linfty_opNorm_transpose_le' _
      have h3 := hSbd T
      have ht1 : ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖
          * ‖S.lowSaa δ T‖
          * ‖(condV (S.lowLam1a T) (S.lowLamma T))ᵀ‖
          ≤ (bS + ‖SaaInf‖) * (K * (bVd + ‖Vinf‖))
            * ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖ := by
        calc ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖
            * ‖S.lowSaa δ T‖
            * ‖(condV (S.lowLam1a T) (S.lowLamma T))ᵀ‖
            ≤ ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖
              * (bS + ‖SaaInf‖) * (K * (bVd + ‖Vinf‖)) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left h3
                (norm_nonneg _)) h1 (norm_nonneg _) ?_
              positivity
        _ = (bS + ‖SaaInf‖) * (K * (bVd + ‖Vinf‖))
              * ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖ := by
            ring
      have ht2 : ‖Vinf‖ * ‖S.lowSaa δ T - SaaInf‖
          * ‖(condV (S.lowLam1a T) (S.lowLamma T))ᵀ‖
          ≤ ‖Vinf‖ * (K * (bVd + ‖Vinf‖))
            * ‖S.lowSaa δ T - SaaInf‖ := by
        calc ‖Vinf‖ * ‖S.lowSaa δ T - SaaInf‖
            * ‖(condV (S.lowLam1a T) (S.lowLamma T))ᵀ‖
            ≤ ‖Vinf‖ * ‖S.lowSaa δ T - SaaInf‖
              * (K * (bVd + ‖Vinf‖)) := by
              refine mul_le_mul_of_nonneg_left h1 ?_
              positivity
        _ = ‖Vinf‖ * (K * (bVd + ‖Vinf‖))
              * ‖S.lowSaa δ T - SaaInf‖ := by ring
      have ht3 : ‖Vinf‖ * ‖SaaInf‖
          * ‖(condV (S.lowLam1a T) (S.lowLamma T))ᵀ - Vinfᵀ‖
          ≤ ‖Vinf‖ * ‖SaaInf‖ * K
            * ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖ := by
        calc ‖Vinf‖ * ‖SaaInf‖
            * ‖(condV (S.lowLam1a T) (S.lowLamma T))ᵀ - Vinfᵀ‖
            ≤ ‖Vinf‖ * ‖SaaInf‖
              * (K * ‖condV (S.lowLam1a T) (S.lowLamma T)
                  - Vinf‖) := by
              refine mul_le_mul_of_nonneg_left h2 ?_
              positivity
        _ = ‖Vinf‖ * ‖SaaInf‖ * K
              * ‖condV (S.lowLam1a T) (S.lowLamma T) - Vinf‖ := by
            ring
      linarith
    have h4 := hpart2
    have h5 := hpart1
    linarith
  obtain ⟨C, ρ, hC, hρ0, hρ1, hb⟩ := hgeo
  exact ⟨C, ρ, hC, hρ0, hρ1, hb⟩

end DareSystem

end Dare
end Estimation

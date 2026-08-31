import LeanForControl.Estimation.Dare.Necessity
import Architect

/-!
# The supremal upper anchor (`lem:supremal`, `eq:above`)

From any prior dominating the strong solution, the trajectory converges
to it. The gap `Δ_T := Σ̄_T − Σ∞` is PSD (comparison) and rides the
fixed strong loop (`eq:gap-ric`): restricted to the stabilizable ⊕
antistable coordinates the loop is Schur (`eq:Finf-spec`, taken as a
hypothesis — the deck imports the display), while the marginal block
dies by the verified `lem:marginal` and PSD Cauchy–Schwarz sends the
cross blocks after it. Iterating the restricted Löwner inequality
against the geometric kernel closes.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

variable {ι σ μ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype σ] [DecidableEq σ] [Fintype μ] [DecidableEq μ]

lemma norm_single_le_one (j : ι) :
    ‖(Pi.single j 1 : ι → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

omit [DecidableEq ι] in
/-- The conjugated entry as a bilinear evaluation. -/
lemma conj_entry (A : Matrix ι σ ℝ) (D : Matrix ι ι ℝ)
    (B : Matrix ι μ ℝ) (i : σ) (j : μ) :
    (Aᵀ * D * B) i j
      = (A *ᵥ (Pi.single i 1 : σ → ℝ))
          ⬝ᵥ (D *ᵥ (B *ᵥ (Pi.single j 1 : μ → ℝ))) := by
  have hA : A *ᵥ (Pi.single i 1 : σ → ℝ) = fun k => A k i := by
    funext k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hB : B *ᵥ (Pi.single j 1 : μ → ℝ) = fun l => B l j := by
    funext l
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hA, hB]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- **The Löwner iteration**: unrolling `D_{T+1} ⪯ F·D_T·Fᵀ + X_T`. -/
lemma loewner_iter {F : Matrix ι ι ℝ} {D X : ℕ → Matrix ι ι ℝ}
    (hstep : ∀ T, (F * D T * Fᵀ + X T - D (T + 1)).PosSemidef) :
    ∀ T, (F ^ T * D 0 * (F ^ T)ᵀ
      + (∑ j ∈ Finset.range T,
          F ^ (T - 1 - j) * X j * (F ^ (T - 1 - j))ᵀ)
      - D T).PosSemidef := by
  intro T
  induction T with
  | zero => simpa using Matrix.PosSemidef.zero
  | succ T ih =>
    have hconj := ih.mul_mul_conjTranspose_same F
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hconj
    have hkey : F ^ (T + 1) * D 0 * (F ^ (T + 1))ᵀ
        + (∑ j ∈ Finset.range (T + 1),
            F ^ (T + 1 - 1 - j) * X j * (F ^ (T + 1 - 1 - j))ᵀ)
        - D (T + 1)
      = F * (F ^ T * D 0 * (F ^ T)ᵀ
          + (∑ j ∈ Finset.range T,
              F ^ (T - 1 - j) * X j * (F ^ (T - 1 - j))ᵀ)
          - D T) * Fᵀ
        + (F * D T * Fᵀ + X T - D (T + 1)) := by
      have h1 : F * (F ^ T * D 0 * (F ^ T)ᵀ) * Fᵀ
          = F ^ (T + 1) * D 0 * (F ^ (T + 1))ᵀ := by
        rw [pow_succ' F T, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      have h2 : F * (∑ j ∈ Finset.range T,
            F ^ (T - 1 - j) * X j * (F ^ (T - 1 - j))ᵀ) * Fᵀ
          = ∑ j ∈ Finset.range T,
              F ^ (T - j) * X j * (F ^ (T - j))ᵀ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjT := Finset.mem_range.mp hj
        have hexp : T - 1 - j + 1 = T - j := by omega
        have hpow : F * F ^ (T - 1 - j) = F ^ (T - j) := by
          rw [← pow_succ' F (T - 1 - j), hexp]
        rw [← hpow, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      have h3 : ∑ j ∈ Finset.range (T + 1),
            F ^ (T + 1 - 1 - j) * X j * (F ^ (T + 1 - 1 - j))ᵀ
          = (∑ j ∈ Finset.range T,
              F ^ (T - j) * X j * (F ^ (T - j))ᵀ) + X T := by
        have hsimp : ∀ j, T + 1 - 1 - j = T - j := fun j => by omega
        simp only [hsimp]
        rw [Finset.sum_range_succ, Nat.sub_self, pow_zero,
          Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
        Matrix.add_mul, h1, h2, h3]
      abel
    rw [hkey]
    exact hconj.add (hstep T)

section Partition

variable {P : Matrix ι σ ℝ} {M : Matrix ι μ ℝ}

omit [DecidableEq σ] [DecidableEq μ] in
/-- Conjugating `H·D·Hᵀ` through a partition of the identity. -/
lemma conj_partition (hpart : P * Pᵀ + M * Mᵀ = 1)
    (H D : Matrix ι ι ℝ) :
    Pᵀ * (H * D * Hᵀ) * P
      = (Pᵀ * H * P) * (Pᵀ * D * P) * (Pᵀ * H * P)ᵀ
        + ((Pᵀ * H * P) * (Pᵀ * D * M) * (Pᵀ * H * M)ᵀ
          + (Pᵀ * H * M) * (Mᵀ * D * P) * (Pᵀ * H * P)ᵀ
          + (Pᵀ * H * M) * (Mᵀ * D * M) * (Pᵀ * H * M)ᵀ) := by
    have hPt : (Pᵀ * H * P)ᵀ = Pᵀ * Hᵀ * P := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_assoc]
    have hMt : (Pᵀ * H * M)ᵀ = Mᵀ * Hᵀ * P := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hPt, hMt]
    calc Pᵀ * (H * D * Hᵀ) * P
        = Pᵀ * (H * ((P * Pᵀ + M * Mᵀ) * D * (P * Pᵀ + M * Mᵀ)) * Hᵀ)
            * P := by
          rw [hpart, Matrix.one_mul, Matrix.mul_one]
    _ = (Pᵀ * H * P) * (Pᵀ * D * P) * (Pᵀ * Hᵀ * P)
        + ((Pᵀ * H * P) * (Pᵀ * D * M) * (Mᵀ * Hᵀ * P)
          + (Pᵀ * H * M) * (Mᵀ * D * P) * (Pᵀ * Hᵀ * P)
          + (Pᵀ * H * M) * (Mᵀ * D * M) * (Mᵀ * Hᵀ * P)) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        abel

omit [DecidableEq σ] [DecidableEq μ] in
/-- Reassembling a matrix from its partition blocks. -/
lemma partition_decomp (hpart : P * Pᵀ + M * Mᵀ = 1)
    (D : Matrix ι ι ℝ) :
    D = P * (Pᵀ * D * P) * Pᵀ + P * (Pᵀ * D * M) * Mᵀ
        + M * (Mᵀ * D * P) * Pᵀ + M * (Mᵀ * D * M) * Mᵀ := by
  calc D = (P * Pᵀ + M * Mᵀ) * D * (P * Pᵀ + M * Mᵀ) := by
        rw [hpart, Matrix.one_mul, Matrix.mul_one]
  _ = P * (Pᵀ * D * P) * Pᵀ + P * (Pᵀ * D * M) * Mᵀ
      + M * (Mᵀ * D * P) * Pᵀ + M * (Mᵀ * D * M) * Mᵀ := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      abel

end Partition

omit [DecidableEq ι] in
/-- Submultiplicativity for a triple product. -/
lemma norm_triple_le {κ₁ κ₂ κ₃ : Type*} [Fintype κ₁] [Fintype κ₂]
    [Fintype κ₃] (A : Matrix ι κ₁ ℝ) (B : Matrix κ₁ κ₂ ℝ)
    (C : Matrix κ₂ κ₃ ℝ) :
    ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := by
  calc ‖A * B * C‖ ≤ ‖A * B‖ * ‖C‖ := Matrix.linfty_opNorm_mul _ _
  _ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
      mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _)
        (norm_nonneg _)

/-- **The Löwner–Schur convergence engine**: a PSD sequence obeying
`D_{T+1} ⪯ F·D_T·Fᵀ + X_T` with geometrically decaying powers of `F`
and a null forcing `X` tends to zero in norm. -/
lemma tendsto_zero_of_loewner_schur {Fm : Matrix ι ι ℝ}
    {D X : ℕ → Matrix ι ι ℝ}
    (hDpsd : ∀ T, (D T).PosSemidef)
    (hstep : ∀ T, (Fm * D T * Fmᵀ + X T - D (T + 1)).PosSemidef)
    {cf γ : ℝ} (hcf : 0 < cf) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hFpow : ∀ k : ℕ, ‖Fm ^ k‖ ≤ cf * γ ^ k)
    (hX : Tendsto (fun T => ‖X T‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖D T‖) atTop (nhds 0) := by
  set K : ℝ := (Fintype.card ι : ℝ) with hK
  have hKnn : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hiter := loewner_iter hstep
  -- the conjugation bound
  have hconj : ∀ (k : ℕ) (Mx : Matrix ι ι ℝ),
      ‖Fm ^ k * Mx * (Fm ^ k)ᵀ‖
        ≤ K * cf ^ 2 * (γ * γ) ^ k * ‖Mx‖ := by
    intro k Mx
    have h1 : ‖Fm ^ k * Mx * (Fm ^ k)ᵀ‖
        ≤ ‖Fm ^ k‖ * ‖Mx‖ * ‖(Fm ^ k)ᵀ‖ := norm_triple_le _ _ _
    have h2 : ‖(Fm ^ k)ᵀ‖ ≤ K * ‖Fm ^ k‖ :=
      linfty_opNorm_transpose_le' _
    have h3 : ‖Fm ^ k‖ * ‖Mx‖ * ‖(Fm ^ k)ᵀ‖
        ≤ (cf * γ ^ k) * ‖Mx‖ * (K * (cf * γ ^ k)) := by
      have hp := hFpow k
      have hnn : (0 : ℝ) ≤ ‖Fm ^ k‖ := norm_nonneg _
      have hb : (0 : ℝ) ≤ cf * γ ^ k := by positivity
      refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
      · exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      · exact le_trans h2 (mul_le_mul_of_nonneg_left hp hKnn)
    calc ‖Fm ^ k * Mx * (Fm ^ k)ᵀ‖
        ≤ (cf * γ ^ k) * ‖Mx‖ * (K * (cf * γ ^ k)) := le_trans h1 h3
    _ = K * cf ^ 2 * (γ * γ) ^ k * ‖Mx‖ := by
        rw [mul_pow]; ring
  -- the norm-level unrolled bound
  have hbound : ∀ T, ‖D T‖
      ≤ (K ^ 3 * (K * cf ^ 2) * ‖D 0‖) * (γ * γ) ^ T
        + ∑ j ∈ Finset.range T,
            (γ * γ) ^ (T - 1 - j) * (K ^ 3 * (K * cf ^ 2) * ‖X j‖) := by
    intro T
    set RHS : Matrix ι ι ℝ := Fm ^ T * D 0 * (Fm ^ T)ᵀ
      + (∑ j ∈ Finset.range T,
          Fm ^ (T - 1 - j) * X j * (Fm ^ (T - 1 - j))ᵀ) with hRHS
    have hq : ∀ x, quadForm (D T) x ≤ (K * ‖RHS‖) * ‖x‖ ^ 2 := by
      intro x
      have h1 : quadForm (D T) x ≤ quadForm RHS x :=
        quadForm_le_quadForm_of_posSemidef_sub (hiter T) x
      calc quadForm (D T) x ≤ quadForm RHS x := h1
      _ ≤ K * ‖RHS‖ * ‖x‖ ^ 2 := quadForm_le_card_norm _ _
    have hRnn : (0 : ℝ) ≤ K * ‖RHS‖ := by positivity
    have h2 : ‖D T‖ ≤ K ^ 2 * (K * ‖RHS‖) :=
      posSemidef_norm_le_of_quadForm_le (hDpsd T) hRnn hq
    have h3 : ‖RHS‖ ≤ K * cf ^ 2 * (γ * γ) ^ T * ‖D 0‖
        + ∑ j ∈ Finset.range T,
            K * cf ^ 2 * (γ * γ) ^ (T - 1 - j) * ‖X j‖ := by
      calc ‖RHS‖ ≤ ‖Fm ^ T * D 0 * (Fm ^ T)ᵀ‖
          + ‖∑ j ∈ Finset.range T,
              Fm ^ (T - 1 - j) * X j * (Fm ^ (T - 1 - j))ᵀ‖ :=
            norm_add_le _ _
      _ ≤ K * cf ^ 2 * (γ * γ) ^ T * ‖D 0‖
          + ∑ j ∈ Finset.range T,
              K * cf ^ 2 * (γ * γ) ^ (T - 1 - j) * ‖X j‖ := by
          refine add_le_add (hconj T (D 0)) ?_
          refine le_trans (norm_sum_le _ _) ?_
          exact Finset.sum_le_sum fun j _ => hconj (T - 1 - j) (X j)
    calc ‖D T‖ ≤ K ^ 2 * (K * ‖RHS‖) := h2
    _ = K ^ 3 * ‖RHS‖ := by ring
    _ ≤ K ^ 3 * (K * cf ^ 2 * (γ * γ) ^ T * ‖D 0‖
          + ∑ j ∈ Finset.range T,
              K * cf ^ 2 * (γ * γ) ^ (T - 1 - j) * ‖X j‖) := by
        refine mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (K ^ 3 * (K * cf ^ 2) * ‖D 0‖) * (γ * γ) ^ T
        + ∑ j ∈ Finset.range T,
            (γ * γ) ^ (T - 1 - j) * (K ^ 3 * (K * cf ^ 2) * ‖X j‖) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          ring
  refine tendsto_zero_of_geometric_conv (a := K ^ 3 * (K * cf ^ 2) * ‖D 0‖)
    (ρ := γ * γ) (by positivity) (by positivity)
    (by nlinarith) (fun T => norm_nonneg _)
    (fun j => by positivity) ?_ hbound
  have h := hX.const_mul (K ^ 3 * (K * cf ^ 2))
  simpa using h

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The inclusion of the stabilizable ⊕ antistable coordinates
`e₁ ⊕ a` into the full state. -/
def embS (n₁ na nm : ℕ) :
    Matrix (ix n₁ na nm) (Fin n₁ ⊕ Fin na) ℝ :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromRows 1 0)

/-- `embS` and `embM` partition the identity. -/
lemma embS_embM_partition :
    embS n₁ na nm * (embS n₁ na nm)ᵀ
      + embM n₁ na nm * (embM n₁ na nm)ᵀ = 1 := by
  ext i j
  rcases i with i₁ | ia | im <;> rcases j with j₁ | ja | jm <;>
    simp [embS, embM, Matrix.mul_apply, Matrix.add_apply,
      Matrix.one_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.transpose_apply, Finset.sum_ite_eq, eq_comm]

variable {Sinf L₀ : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-- The strong solution is a fixed point of the whole recursion. -/
lemma dareFrom_strong_fixed (hS : S.IsStrongSolution Sinf) :
    ∀ T, S.dareFrom Sinf T = Sinf := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
    have h : S.dareFrom Sinf (T + 1)
        = dareStep S.fullC S.R S.fullA S.Qw (S.dareFrom Sinf T) := rfl
    rw [h, ih, hS.fixed]

/-- The from-above gap is PSD (comparison, `eq:comparison`). -/
lemma supremal_gap_posSemidef (hS : S.IsStrongSolution Sinf)
    (hL₀ : L₀.PosSemidef) (hdom : (L₀ - Sinf).PosSemidef) (T : ℕ) :
    (S.dareFrom L₀ T - Sinf).PosSemidef := by
  have h := dareIter_mono (C := S.fullC) (R := S.R) (A := S.fullA)
    (Qw := S.Qw) S.hR S.Qw_posSemidef hS.posSemidef hL₀ hdom T
  have hfix : dareIter S.fullC S.R S.fullA S.Qw Sinf T = Sinf :=
    S.dareFrom_strong_fixed hS T
  rwa [hfix] at h

/-- The gap rides the fixed strong loop (`eq:gap-ric`):
`Δ_{T+1} ⪯ F∞·Δ_T·F∞ᵀ`. -/
lemma supremal_gap_step (hS : S.IsStrongSolution Sinf)
    (hL₀ : L₀.PosSemidef) (hdom : (L₀ - Sinf).PosSemidef) (T : ℕ) :
    (errMap S.fullC S.R S.fullA Sinf * (S.dareFrom L₀ T - Sinf)
        * (errMap S.fullC S.R S.fullA Sinf)ᵀ
      - (S.dareFrom L₀ (T + 1) - Sinf)).PosSemidef := by
  have hV := S.supremal_gap_posSemidef hS hL₀ hdom T
  have h := gapRic_le (C := S.fullC) (A := S.fullA) (Qw := S.Qw)
    S.hR hS.posSemidef hV hS.fixed
  have hadd : Sinf + (S.dareFrom L₀ T - Sinf) = S.dareFrom L₀ T := by
    abel
  rw [hadd] at h
  have hsucc : dareStep S.fullC S.R S.fullA S.Qw (S.dareFrom L₀ T)
      = S.dareFrom L₀ (T + 1) := rfl
  rwa [hsucc] at h

/-- The marginal block of the gap dies (`lem:marginal` +
`eq:marg-extinct`). -/
lemma supremal_marg_tendsto (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    (hL₀ : L₀.PosSemidef) {cm : ℝ} (hcm : 0 ≤ cm)
    (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    Tendsto (fun T => ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
      * embM n₁ na nm‖) atTop (nhds 0) := by
  have hz : ∀ T, (embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
        * embM n₁ na nm
      = (embM n₁ na nm)ᵀ * S.dareFrom L₀ T * embM n₁ na nm := by
    intro T
    rw [Matrix.mul_sub (embM n₁ na nm)ᵀ (S.dareFrom L₀ T) Sinf,
      Matrix.sub_mul,
      Matrix.mul_assoc (embM n₁ na nm)ᵀ Sinf (embM n₁ na nm),
      S.strong_marg_extinct hC1 hS, Matrix.mul_zero, sub_zero]
  simp only [hz]
  exact S.marg_block_norm_tendsto hC1 hL₀ hcm hPB

/-- The (marginal, stab⊕anti) block is the transpose of the
(stab⊕anti, marginal) block. -/
lemma supremal_cross_transpose (hS : S.IsStrongSolution Sinf)
    (hL₀ : L₀.PosSemidef) (hdom : (L₀ - Sinf).PosSemidef) (T : ℕ) :
    (embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embS n₁ na nm
      = ((embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
          * embM n₁ na nm)ᵀ := by
  have h := (S.supremal_gap_posSemidef hS hL₀ hdom T).1.transpose_eq_self
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, h, ← Matrix.mul_assoc]

/-- The cross block of the gap dies (PSD Cauchy–Schwarz against the
marginal block, `fact:schur`). -/
lemma supremal_cross_tendsto (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    (hL₀ : L₀.PosSemidef) (hdom : (L₀ - Sinf).PosSemidef)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    Tendsto (fun T => ‖(embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
      * embM n₁ na nm‖) atTop (nhds 0) := by
  obtain ⟨bSig, hbSig, hbSigle⟩ := exists_dare_bound (C := S.fullC)
    (A := S.fullA) (Qw := S.Qw) S.hR S.Qw_posSemidef hL₀ hC1
  have hbSigle' : ∀ (T : ℕ) (x : ix n₁ na nm → ℝ),
      quadForm (S.dareFrom L₀ T) x ≤ bSig * ‖x‖ ^ 2 :=
    fun T x => hbSigle T x
  have hqΔ : ∀ (T : ℕ) (x : ix n₁ na nm → ℝ),
      quadForm (S.dareFrom L₀ T - Sinf) x ≤ bSig * ‖x‖ ^ 2 := by
    intro T x
    rw [quadForm_sub_matrix]
    have h1 := hbSigle' T x
    have h2 := hS.posSemidef.quadForm_nonneg x
    linarith
  set CX : ℝ := bSig * ‖embS n₁ na nm‖ ^ 2
    * (Fintype.card (Fin nm) : ℝ) with hCX
  -- entrywise Cauchy–Schwarz against the marginal block
  have hentry : ∀ (T : ℕ) (i : Fin n₁ ⊕ Fin na) (j : Fin nm),
      |((embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm) i j|
        ≤ Real.sqrt (CX * ‖(embM n₁ na nm)ᵀ
            * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm‖) := by
    intro T i j
    have hpsd := S.supremal_gap_posSemidef hS hL₀ hdom T
    have hqy : quadForm (S.dareFrom L₀ T - Sinf)
        (embS n₁ na nm *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ))
        ≤ bSig * ‖embS n₁ na nm‖ ^ 2 := by
      have h1 : ‖embS n₁ na nm
            *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ)‖
          ≤ ‖embS n₁ na nm‖ := by
        calc ‖embS n₁ na nm *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ)‖
            ≤ ‖embS n₁ na nm‖
              * ‖(Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ)‖ :=
              Matrix.linfty_opNorm_mulVec _ _
        _ ≤ ‖embS n₁ na nm‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_single_le_one i)
              (norm_nonneg _)
        _ = ‖embS n₁ na nm‖ := mul_one _
      calc quadForm (S.dareFrom L₀ T - Sinf)
            (embS n₁ na nm *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ))
          ≤ bSig * ‖embS n₁ na nm
              *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ)‖ ^ 2 :=
            hqΔ T _
      _ ≤ bSig * ‖embS n₁ na nm‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hbSig.le
          have := norm_nonneg (embS n₁ na nm
            *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ))
          nlinarith [h1]
    have hqx : quadForm (S.dareFrom L₀ T - Sinf)
        (embM n₁ na nm *ᵥ (Pi.single j 1 : Fin nm → ℝ))
        ≤ (Fintype.card (Fin nm) : ℝ)
          * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
              * embM n₁ na nm‖ := by
      have h1 : quadForm (S.dareFrom L₀ T - Sinf)
            (embM n₁ na nm *ᵥ (Pi.single j 1 : Fin nm → ℝ))
          = quadForm ((embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
              * embM n₁ na nm) (Pi.single j 1) :=
        quadForm_mulVec _ _ _
      rw [h1]
      calc quadForm ((embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
            * embM n₁ na nm) (Pi.single j 1)
          ≤ (Fintype.card (Fin nm) : ℝ)
            * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
                * embM n₁ na nm‖
            * ‖(Pi.single j 1 : Fin nm → ℝ)‖ ^ 2 :=
            quadForm_le_card_norm _ _
      _ ≤ (Fintype.card (Fin nm) : ℝ)
            * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
                * embM n₁ na nm‖ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_one₀ (norm_nonneg _) (norm_single_le_one j)
      _ = (Fintype.card (Fin nm) : ℝ)
            * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
                * embM n₁ na nm‖ := mul_one _
    have hcs := sq_dotProduct_mulVec_le hpsd
      (embM n₁ na nm *ᵥ (Pi.single j 1 : Fin nm → ℝ))
      (embS n₁ na nm *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ))
    rw [conj_entry]
    have hv2 : ((embS n₁ na nm *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ))
          ⬝ᵥ ((S.dareFrom L₀ T - Sinf)
            *ᵥ (embM n₁ na nm *ᵥ (Pi.single j 1 : Fin nm → ℝ)))) ^ 2
        ≤ CX * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
            * embM n₁ na nm‖ := by
      calc ((embS n₁ na nm *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ))
            ⬝ᵥ ((S.dareFrom L₀ T - Sinf)
              *ᵥ (embM n₁ na nm *ᵥ (Pi.single j 1 : Fin nm → ℝ)))) ^ 2
          ≤ quadForm (S.dareFrom L₀ T - Sinf)
              (embS n₁ na nm *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ))
            * quadForm (S.dareFrom L₀ T - Sinf)
              (embM n₁ na nm *ᵥ (Pi.single j 1 : Fin nm → ℝ)) := hcs
      _ ≤ (bSig * ‖embS n₁ na nm‖ ^ 2)
            * ((Fintype.card (Fin nm) : ℝ)
              * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
                  * embM n₁ na nm‖) :=
          mul_le_mul hqy hqx (hpsd.quadForm_nonneg _) (by positivity)
      _ = CX * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
            * embM n₁ na nm‖ := by rw [hCX]; ring
    calc |(embS n₁ na nm *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ))
          ⬝ᵥ ((S.dareFrom L₀ T - Sinf)
            *ᵥ (embM n₁ na nm *ᵥ (Pi.single j 1 : Fin nm → ℝ)))|
        = Real.sqrt (((embS n₁ na nm
            *ᵥ (Pi.single i 1 : (Fin n₁ ⊕ Fin na) → ℝ))
          ⬝ᵥ ((S.dareFrom L₀ T - Sinf)
            *ᵥ (embM n₁ na nm *ᵥ (Pi.single j 1 : Fin nm → ℝ)))) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (CX * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
          * embM n₁ na nm‖) := Real.sqrt_le_sqrt hv2
  -- sum the entries and squeeze
  have hnorm : ∀ T, ‖(embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
        * embM n₁ na nm‖
      ≤ ((Fintype.card (Fin n₁ ⊕ Fin na) : ℝ)
          * (Fintype.card (Fin nm) : ℝ))
        * Real.sqrt (CX * ‖(embM n₁ na nm)ᵀ
            * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm‖) := by
    intro T
    calc ‖(embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm‖
        ≤ ∑ i, ∑ j, |((embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
            * embM n₁ na nm) i j| := linfty_opNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin n₁ ⊕ Fin na, ∑ _j : Fin nm,
          Real.sqrt (CX * ‖(embM n₁ na nm)ᵀ
            * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm‖) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum
          fun j _ => hentry T i j
    _ = ((Fintype.card (Fin n₁ ⊕ Fin na) : ℝ)
          * (Fintype.card (Fin nm) : ℝ))
        * Real.sqrt (CX * ‖(embM n₁ na nm)ᵀ
            * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm‖) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hδ := S.supremal_marg_tendsto hC1 hS hL₀ hcm hPB
  have h1 : Tendsto (fun T => CX * ‖(embM n₁ na nm)ᵀ
      * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm‖) atTop (nhds 0) := by
    simpa using hδ.const_mul CX
  have h2 : Tendsto (fun T => Real.sqrt (CX * ‖(embM n₁ na nm)ᵀ
      * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm‖)) atTop (nhds 0) := by
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa [Function.comp_def, Real.sqrt_zero] using h3
  refine squeeze_zero (fun T => norm_nonneg _) hnorm ?_
  simpa using h2.const_mul ((Fintype.card (Fin n₁ ⊕ Fin na) : ℝ)
    * (Fintype.card (Fin nm) : ℝ))

/-- The transposed cross block dies too. -/
lemma supremal_mars_tendsto (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    (hL₀ : L₀.PosSemidef) (hdom : (L₀ - Sinf).PosSemidef)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    Tendsto (fun T => ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
      * embS n₁ na nm‖) atTop (nhds 0) := by
  have hcross := S.supremal_cross_tendsto hC1 hS hL₀ hdom hcm hPB
  refine squeeze_zero (fun T => norm_nonneg _)
    (g := fun T => (Fintype.card (Fin n₁ ⊕ Fin na) : ℝ)
      * ‖(embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm‖)
    (fun T => ?_) ?_
  · rw [S.supremal_cross_transpose hS hL₀ hdom T]
    exact linfty_opNorm_transpose_le' _
  · simpa using hcross.const_mul _

/-- The stabilizable ⊕ antistable block of the gap dies: the restricted
Löwner recursion against the Schur `F∞|ₑ₁ₐ` (`eq:Finf-spec`). -/
lemma supremal_stab_tendsto (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    (hL₀ : L₀.PosSemidef) (hdom : (L₀ - Sinf).PosSemidef)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm)
    (hFs : IsSchurStable ((embS n₁ na nm)ᵀ
      * errMap S.fullC S.R S.fullA Sinf * embS n₁ na nm)) :
    Tendsto (fun T => ‖(embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
      * embS n₁ na nm‖) atTop (nhds 0) := by
  obtain ⟨cf, γ, hcf, hγ0, hγ1, hFpow⟩ := hFs.exists_pow_norm_le
  have hcross := S.supremal_cross_tendsto hC1 hS hL₀ hdom hcm hPB
  have hmars := S.supremal_mars_tendsto hC1 hS hL₀ hdom hcm hPB
  have hmarg := S.supremal_marg_tendsto hC1 hS hL₀ hcm hPB
  -- PSD of the restricted gap
  have hDpsd : ∀ T, ((embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
      * embS n₁ na nm).PosSemidef := by
    intro T
    have h := (S.supremal_gap_posSemidef hS hL₀ hdom
      T).mul_mul_conjTranspose_same (embS n₁ na nm)ᵀ
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose] at h
  -- the restricted step through the partition
  have hstepS : ∀ T, (((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
        * embS n₁ na nm)
      * ((embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embS n₁ na nm)
      * (((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
        * embS n₁ na nm))ᵀ
      + (((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embS n₁ na nm)
        * ((embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm)
        * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embM n₁ na nm)ᵀ
        + ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embM n₁ na nm)
          * ((embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embS n₁ na nm)
          * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embS n₁ na nm)ᵀ
        + ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embM n₁ na nm)
          * ((embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm)
          * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embM n₁ na nm)ᵀ)
      - ((embS n₁ na nm)ᵀ * (S.dareFrom L₀ (T + 1) - Sinf)
        * embS n₁ na nm)).PosSemidef := by
    intro T
    have h := (S.supremal_gap_step hS hL₀ hdom
      T).mul_mul_conjTranspose_same (embS n₁ na nm)ᵀ
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose] at h
    have hexpand : (embS n₁ na nm)ᵀ
        * (errMap S.fullC S.R S.fullA Sinf * (S.dareFrom L₀ T - Sinf)
            * (errMap S.fullC S.R S.fullA Sinf)ᵀ
          - (S.dareFrom L₀ (T + 1) - Sinf)) * embS n₁ na nm
        = (embS n₁ na nm)ᵀ * (errMap S.fullC S.R S.fullA Sinf
            * (S.dareFrom L₀ T - Sinf)
            * (errMap S.fullC S.R S.fullA Sinf)ᵀ) * embS n₁ na nm
          - (embS n₁ na nm)ᵀ * (S.dareFrom L₀ (T + 1) - Sinf)
            * embS n₁ na nm := by
      rw [Matrix.mul_sub (embS n₁ na nm)ᵀ
        (errMap S.fullC S.R S.fullA Sinf * (S.dareFrom L₀ T - Sinf)
          * (errMap S.fullC S.R S.fullA Sinf)ᵀ)
        (S.dareFrom L₀ (T + 1) - Sinf), Matrix.sub_mul]
    rw [hexpand,
      conj_partition embS_embM_partition
        (errMap S.fullC S.R S.fullA Sinf) (S.dareFrom L₀ T - Sinf)] at h
    exact h
  -- the forcing dies
  have hXt : Tendsto (fun T =>
      ‖((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embS n₁ na nm)
        * ((embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm)
        * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embM n₁ na nm)ᵀ
        + ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embM n₁ na nm)
          * ((embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embS n₁ na nm)
          * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embS n₁ na nm)ᵀ
        + ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embM n₁ na nm)
          * ((embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm)
          * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embM n₁ na nm)ᵀ‖) atTop (nhds 0) := by
    have hb : ∀ T, ‖((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embS n₁ na nm)
        * ((embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm)
        * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embM n₁ na nm)ᵀ
        + ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embM n₁ na nm)
          * ((embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embS n₁ na nm)
          * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embS n₁ na nm)ᵀ
        + ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embM n₁ na nm)
          * ((embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf) * embM n₁ na nm)
          * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embM n₁ na nm)ᵀ‖
        ≤ ‖(embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embS n₁ na nm‖
          * ‖(embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
              * embM n₁ na nm‖
          * ‖((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
              * embM n₁ na nm)ᵀ‖
        + ‖(embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embM n₁ na nm‖
          * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
              * embS n₁ na nm‖
          * ‖((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
              * embS n₁ na nm)ᵀ‖
        + ‖(embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embM n₁ na nm‖
          * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
              * embM n₁ na nm‖
          * ‖((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
              * embM n₁ na nm)ᵀ‖ := by
      intro T
      refine le_trans (norm_add_le _ _) ?_
      refine add_le_add (le_trans (norm_add_le _ _) ?_)
        (norm_triple_le _ _ _)
      exact add_le_add (norm_triple_le _ _ _) (norm_triple_le _ _ _)
    refine squeeze_zero (fun T => norm_nonneg _) hb ?_
    have h1 := (hcross.const_mul ‖(embS n₁ na nm)ᵀ
      * errMap S.fullC S.R S.fullA Sinf * embS n₁ na nm‖).mul_const
      ‖((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
        * embM n₁ na nm)ᵀ‖
    have h2 := (hmars.const_mul ‖(embS n₁ na nm)ᵀ
      * errMap S.fullC S.R S.fullA Sinf * embM n₁ na nm‖).mul_const
      ‖((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
        * embS n₁ na nm)ᵀ‖
    have h3 := (hmarg.const_mul ‖(embS n₁ na nm)ᵀ
      * errMap S.fullC S.R S.fullA Sinf * embM n₁ na nm‖).mul_const
      ‖((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
        * embM n₁ na nm)ᵀ‖
    have h4 := (h1.add h2).add h3
    simpa [mul_assoc] using h4
  exact tendsto_zero_of_loewner_schur hDpsd hstepS hcf hγ0 hγ1 hFpow hXt

/-- **`lem:supremal` / `eq:above`, convergence half**: from any PSD
prior dominating the strong solution, the trajectory converges to it.
(The domination half of `eq:above` is `dareIter_mono`.) -/
theorem supremal_tendsto (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    (hL₀ : L₀.PosSemidef) (hdom : (L₀ - Sinf).PosSemidef)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm)
    (hFs : IsSchurStable ((embS n₁ na nm)ᵀ
      * errMap S.fullC S.R S.fullA Sinf * embS n₁ na nm)) :
    Tendsto (fun T => ‖S.dareFrom L₀ T - Sinf‖) atTop (nhds 0) := by
  have hstab := S.supremal_stab_tendsto hC1 hS hL₀ hdom hcm hPB hFs
  have hcross := S.supremal_cross_tendsto hC1 hS hL₀ hdom hcm hPB
  have hmars := S.supremal_mars_tendsto hC1 hS hL₀ hdom hcm hPB
  have hmarg := S.supremal_marg_tendsto hC1 hS hL₀ hcm hPB
  have hb : ∀ T, ‖S.dareFrom L₀ T - Sinf‖
      ≤ ‖embS n₁ na nm‖
          * ‖(embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
              * embS n₁ na nm‖ * ‖(embS n₁ na nm)ᵀ‖
        + ‖embS n₁ na nm‖
          * ‖(embS n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
              * embM n₁ na nm‖ * ‖(embM n₁ na nm)ᵀ‖
        + ‖embM n₁ na nm‖
          * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
              * embS n₁ na nm‖ * ‖(embS n₁ na nm)ᵀ‖
        + ‖embM n₁ na nm‖
          * ‖(embM n₁ na nm)ᵀ * (S.dareFrom L₀ T - Sinf)
              * embM n₁ na nm‖ * ‖(embM n₁ na nm)ᵀ‖ := by
    intro T
    conv_lhs => rw [partition_decomp embS_embM_partition
      (S.dareFrom L₀ T - Sinf)]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) ?_)
      (norm_triple_le _ _ _)
    refine add_le_add (le_trans (norm_add_le _ _) ?_)
      (norm_triple_le _ _ _)
    exact add_le_add (norm_triple_le _ _ _) (norm_triple_le _ _ _)
  refine squeeze_zero (fun T => norm_nonneg _) hb ?_
  have h1 := (hstab.const_mul ‖embS n₁ na nm‖).mul_const
    ‖(embS n₁ na nm)ᵀ‖
  have h2 := (hcross.const_mul ‖embS n₁ na nm‖).mul_const
    ‖(embM n₁ na nm)ᵀ‖
  have h3 := (hmars.const_mul ‖embM n₁ na nm‖).mul_const
    ‖(embS n₁ na nm)ᵀ‖
  have h4 := (hmarg.const_mul ‖embM n₁ na nm‖).mul_const
    ‖(embM n₁ na nm)ᵀ‖
  have h5 := ((h1.add h2).add h3).add h4
  simpa [mul_assoc] using h5

end DareSystem

end Dare
end Estimation

import LeanForControl.Estimation.Prelim
import LeanForControl.LinearSystems.SpectralGrowth
import LeanForControl.LinearSystems.UnobservableBlock
import Architect

/-!
# Finite-window coercivity (`lem:coercive`(1))

Under C1 the horizon-`(n₁+n₂)` value function is uniformly coercive in the
antistable initial block: `α‖e₂‖² ≤ (ξ, e₂)'(ric (n₁+n₂))(ξ, e₂)` for every
free stabilizable block `ξ` (`exists_window_coercivity`).

The chain: the free-`ξ` minimum is the generalized Schur complement
`W = Mᵀ (ric m) M` along the pseudoinverse injection
`M = [−P₁₁† P₁₂; I]` (solvability of the cross equation follows from
positive semidefiniteness and `Matrix.PosSemidef.exists_mulVec_eq`); a zero
of `W` yields a zero-cost optimal trajectory, whose stages vanish, making
the initial state output-invisible on a full window; Cayley–Hamilton
extends this to the whole orbit and the unobservable-block vanishing
theorem (`blk₂_eq_zero_of_unobservable`) kills the antistable block. So `W`
is positive definite, and `Matrix.PosDef.exists_le_quadForm` provides the
uniform constant.
-/

namespace Estimation

open Matrix LinearSystems

open scoped Matrix.Norms.Operator

variable {n₁ n₂ m p : ℕ}

namespace FIESystem

variable (Sys : FIESystem n₁ n₂ m p)

/-- Blocks of a real symmetric matrix: the `₂₁` block is the transpose of
the `₁₂` block. -/
lemma toBlocks₂₁_eq_transpose
    {M : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ}
    (hM : M.IsHermitian) : M.toBlocks₂₁ = M.toBlocks₁₂ᵀ := by
  have h := hM.transpose_eq_self
  ext i j
  have h1 := congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
  simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.transpose_apply] using
    h1.symm

/-- The `₁₁` block of a real symmetric matrix is symmetric. -/
lemma toBlocks₁₁_isHermitian
    {M : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ}
    (hM : M.IsHermitian) : M.toBlocks₁₁.IsHermitian := by
  have h := hM.transpose_eq_self
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  ext i j
  have h1 := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  simpa [Matrix.toBlocks₁₁, Matrix.transpose_apply] using h1

/-- Quadratic form of a symmetric matrix over the sum index, in blocks. -/
lemma quadForm_sumElim {M : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ}
    (hM : M.IsHermitian) (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) :
    quadForm M (Sum.elim x y)
      = quadForm M.toBlocks₁₁ x + 2 * (x ⬝ᵥ (M.toBlocks₁₂ *ᵥ y))
        + quadForm M.toBlocks₂₂ y := by
  rw [quadForm]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [Matrix.fromBlocks_mulVec, dotProduct_blocks]
  simp only [blk₁_sumElim, blk₂_sumElim, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [dotProduct_add, dotProduct_add, toBlocks₂₁_eq_transpose hM]
  have h1 : y ⬝ᵥ (M.toBlocks₁₂ᵀ *ᵥ x) = x ⬝ᵥ (M.toBlocks₁₂ *ᵥ y) := by
    rw [← mulVec_dotProduct_eq, dotProduct_comm]
  rw [h1, quadForm, quadForm]
  ring

/-- The pseudoinverse injection `e₂ ↦ (−P₁₁† P₁₂ e₂, e₂)` realizing the
free-`ξ` minimizer of the window value. -/
noncomputable def freeInj (T : ℕ) : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₂) ℝ :=
  Matrix.fromRows
    (-(symmPinv (toBlocks₁₁_isHermitian (Sys.lq.ric_isHermitian T)) *
        (Sys.lq.ric T).toBlocks₁₂))
    1

/-- The window curvature `W_T = (freeInj T)ᵀ (ric T) (freeInj T)` — the
generalized Schur complement of the value matrix. -/
noncomputable def Wmat (T : ℕ) : Matrix (Fin n₂) (Fin n₂) ℝ :=
  (Sys.freeInj T)ᵀ * Sys.lq.ric T * Sys.freeInj T

lemma Wmat_posSemidef (T : ℕ) : (Sys.Wmat T).PosSemidef := by
  have h := (Sys.lq.ric_posSemidef T).mul_mul_conjTranspose_same
    (Sys.freeInj T)ᵀ
  rwa [show ((Sys.freeInj T)ᵀ)ᴴ = Sys.freeInj T from by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]] at h

/-- The action of the free injection: `freeInj T *ᵥ e₂ = (ξ*(e₂), e₂)`. -/
lemma freeInj_mulVec (T : ℕ) (e₂ : Fin n₂ → ℝ) :
    Sys.freeInj T *ᵥ e₂
      = Sum.elim
          (-(symmPinv (toBlocks₁₁_isHermitian (Sys.lq.ric_isHermitian T))
            *ᵥ ((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂))) e₂ := by
  rw [freeInj, Matrix.fromRows_mulVec]
  congr 1
  · rw [Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  · rw [Matrix.one_mulVec]

/-- The cross equation `P₁₁ ξ = −P₁₂ e₂` is solvable: PSD-ness of the value
matrix bounds the mixed quadratic from below. -/
lemma exists_cross_solution (T : ℕ) (e₂ : Fin n₂ → ℝ) :
    ∃ ξ : Fin n₁ → ℝ,
      (Sys.lq.ric T).toBlocks₁₁ *ᵥ ξ = -((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂) := by
  have hpsd11 : (Sys.lq.ric T).toBlocks₁₁.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (toBlocks₁₁_isHermitian (Sys.lq.ric_isHermitian T)) fun x => ?_
    have h1 := (Sys.lq.ric_posSemidef T).quadForm_nonneg (Sum.elim x 0)
    rw [quadForm_sumElim (Sys.lq.ric_isHermitian T)] at h1
    simpa [quadForm] using h1
  refine hpsd11.exists_mulVec_eq
    (r := -((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂))
    (c := quadForm (Sys.lq.ric T).toBlocks₂₂ e₂) fun ξ => ?_
  have h1 := (Sys.lq.ric_posSemidef T).quadForm_nonneg (Sum.elim ξ e₂)
  rw [quadForm_sumElim (Sys.lq.ric_isHermitian T)] at h1
  have h2 : (-((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂)) ⬝ᵥ ξ
      = -(ξ ⬝ᵥ ((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂)) := by
    rw [neg_dotProduct, dotProduct_comm]
  rw [h2]
  linarith

/-- **Free-`ξ` domination**: the window curvature lower-bounds the value at
every mixed initial state. -/
theorem quadForm_Wmat_le (T : ℕ) (ξ : Fin n₁ → ℝ) (e₂ : Fin n₂ → ℝ) :
    quadForm (Sys.Wmat T) e₂ ≤ quadForm (Sys.lq.ric T) (Sum.elim ξ e₂) := by
  have hric := Sys.lq.ric_isHermitian T
  have hH := toBlocks₁₁_isHermitian hric
  set ξs : Fin n₁ → ℝ :=
    -(symmPinv hH *ᵥ ((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂)) with hξs
  -- `ξs` satisfies the cross equation, by solvability + the pinv-solve trick
  have hsolve : (Sys.lq.ric T).toBlocks₁₁ *ᵥ ξs
      = -((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂) := by
    obtain ⟨ξ₀, hξ₀⟩ := Sys.exists_cross_solution T e₂
    have h1 : (Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂
        = (Sys.lq.ric T).toBlocks₁₁ *ᵥ (-ξ₀) := by
      rw [Matrix.mulVec_neg, hξ₀, neg_neg]
    rw [hξs, Matrix.mulVec_neg, h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      self_mul_symmPinv_mul_self hH]
  -- the window curvature is the value at the injected point
  have hWq : quadForm (Sys.Wmat T) e₂
      = quadForm (Sys.lq.ric T) (Sum.elim ξs e₂) := by
    rw [show Sys.Wmat T = (Sys.freeInj T)ᵀ * Sys.lq.ric T * Sys.freeInj T
      from rfl, ← quadForm_mulVec, Sys.freeInj_mulVec, hξs]
  -- completion of squares in the free block
  have hzero : (Sys.lq.ric T).toBlocks₁₁ *ᵥ ξs
      + (Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂ = 0 := by
    rw [hsolve]
    abel
  have hexp : quadForm (Sys.lq.ric T) (Sum.elim ξ e₂)
      = quadForm (Sys.lq.ric T) (Sum.elim ξs e₂)
        + quadForm (Sys.lq.ric T).toBlocks₁₁ (ξ - ξs)
        + 2 * ((ξ - ξs) ⬝ᵥ
            ((Sys.lq.ric T).toBlocks₁₁ *ᵥ ξs
              + (Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂)) := by
    rw [quadForm_sumElim hric, quadForm_sumElim hric]
    have hsplit : ξ = ξs + (ξ - ξs) := by abel
    have hq : quadForm (Sys.lq.ric T).toBlocks₁₁ ξ
        = quadForm (Sys.lq.ric T).toBlocks₁₁ ξs
          + 2 * (ξs ⬝ᵥ ((Sys.lq.ric T).toBlocks₁₁ *ᵥ (ξ - ξs)))
          + quadForm (Sys.lq.ric T).toBlocks₁₁ (ξ - ξs) := by
      conv_lhs => rw [hsplit]
      rw [quadForm_add_of_isHermitian hH]
    have hcr : ξ ⬝ᵥ ((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂)
        = ξs ⬝ᵥ ((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂)
          + (ξ - ξs) ⬝ᵥ ((Sys.lq.ric T).toBlocks₁₂ *ᵥ e₂) := by
      conv_lhs => rw [hsplit]
      rw [add_dotProduct]
    have hsym : ξs ⬝ᵥ ((Sys.lq.ric T).toBlocks₁₁ *ᵥ (ξ - ξs))
        = (ξ - ξs) ⬝ᵥ ((Sys.lq.ric T).toBlocks₁₁ *ᵥ ξs) :=
      dotProduct_mulVec_comm hH ξs (ξ - ξs)
    rw [hq, hcr, hsym, dotProduct_add]
    ring
  have hpsd11 : (0 : ℝ) ≤ quadForm (Sys.lq.ric T).toBlocks₁₁ (ξ - ξs) := by
    have h1 := (Sys.lq.ric_posSemidef T).quadForm_nonneg (Sum.elim (ξ - ξs) 0)
    rw [quadForm_sumElim hric] at h1
    simpa [quadForm] using h1
  rw [hWq, hexp, hzero, dotProduct_zero]
  linarith


/-- Trajectories under vanishing inputs are matrix-power orbits. -/
lemma traj_eq_pow_of_zero_inputs (e₀ : Fin n₁ ⊕ Fin n₂ → ℝ)
    (u : ℕ → Fin m → ℝ) {T : ℕ} (hu : ∀ k < T, u k = 0) :
    ∀ k ≤ T, Sys.lq.traj e₀ u k = Sys.fullA ^ k *ᵥ e₀ := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [LQSystem.traj_zero]
  | succ k ih =>
    intro hk
    rw [LQSystem.traj_succ, ih (by omega), hu k (by omega),
      Matrix.mulVec_zero, add_zero]
    have h1 : Sys.lq.A = Sys.fullA := rfl
    rw [h1, Matrix.mulVec_mulVec, ← pow_succ']

/-- The complexified full state matrix in block form. -/
private lemma complexify_fullA_fromBlocks :
    complexify Sys.fullA
      = Matrix.fromBlocks (complexify Sys.A₁) (complexify Sys.A₁₂) 0
          (complexify Sys.A₂) := by
  unfold fullA complexify
  rw [Matrix.fromBlocks_map]
  congr 1

/-- **Kernel vectors of the window curvature vanish**: a zero-energy
initial antistable block is output-invisible on the window, hence (by
Cayley–Hamilton and the vanishing theorem) zero. -/
theorem eq_zero_of_quadForm_Wmat_eq_zero (hC1 : Sys.C1) {e₂ : Fin n₂ → ℝ}
    (h0 : quadForm (Sys.Wmat (n₁ + n₂)) e₂ = 0) : e₂ = 0 := by
  set T := n₁ + n₂ with hT
  set e₀ : Fin n₁ ⊕ Fin n₂ → ℝ := Sys.freeInj T *ᵥ e₂ with he₀
  have hric0 : quadForm (Sys.lq.ric T) e₀ = 0 := by
    rw [he₀, quadForm_mulVec]
    exact h0
  -- the optimal trajectory from `e₀` has zero cost, hence zero stages
  have hcost : Sys.lq.cost e₀ (Sys.lq.optCtrl e₀ T) T = 0 := by
    rw [Sys.lq.cost_optCtrl, hric0]
  have hstages : ∀ k ∈ Finset.range T,
      quadForm Sys.lq.Qs (Sys.lq.traj e₀ (Sys.lq.optCtrl e₀ T) k)
        + quadForm Sys.lq.Ru (Sys.lq.optCtrl e₀ T k) = 0 := by
    rw [LQSystem.cost] at hcost
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      Sys.lq.stage_nonneg _ _).mp hcost
  have hu : ∀ k < T, Sys.lq.optCtrl e₀ T k = 0 := by
    intro k hk
    have h1 := hstages k (Finset.mem_range.mpr hk)
    have h2 : 0 ≤ quadForm Sys.lq.Qs (Sys.lq.traj e₀ (Sys.lq.optCtrl e₀ T) k) :=
      Sys.lq.hQs.quadForm_nonneg _
    by_contra hne
    have h4 : 0 < quadForm Sys.lq.Ru (Sys.lq.optCtrl e₀ T k) :=
      Sys.lq.hRu.quadForm_pos hne
    linarith
  have hout : ∀ k < T, (Sys.fullC * Sys.fullA ^ k) *ᵥ e₀ = 0 := by
    intro k hk
    have h1 := hstages k (Finset.mem_range.mpr hk)
    have h3 : 0 ≤ quadForm Sys.lq.Ru (Sys.lq.optCtrl e₀ T k) :=
      Sys.lq.hRu.posSemidef.quadForm_nonneg _
    have h2 : quadForm Sys.lq.Qs (Sys.lq.traj e₀ (Sys.lq.optCtrl e₀ T) k) = 0 := by
      have h4 : 0 ≤ quadForm Sys.lq.Qs (Sys.lq.traj e₀ (Sys.lq.optCtrl e₀ T) k) :=
        Sys.lq.hQs.quadForm_nonneg _
      linarith
    rw [Sys.quadForm_Qs] at h2
    have h5 : Sys.fullC *ᵥ Sys.lq.traj e₀ (Sys.lq.optCtrl e₀ T) k = 0 := by
      by_contra hne
      exact absurd (Sys.hRi.quadForm_pos hne) (by linarith)
    rw [Sys.traj_eq_pow_of_zero_inputs e₀ _ hu k (le_of_lt hk)] at h5
    rw [← Matrix.mulVec_mulVec]
    exact h5
  -- Cayley–Hamilton extends invisibility to the whole orbit
  have hall : ∀ k, (Sys.fullC * Sys.fullA ^ k) *ᵥ e₀ = 0 := by
    refine unobservable_of_window Sys.fullA Sys.fullC fun k hk => ?_
    refine hout k ?_
    rwa [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hk
  -- transfer to `ℂ` and kill the antistable block
  have hallℂ : ∀ k,
      (complexify Sys.fullC * Matrix.fromBlocks (complexify Sys.A₁)
        (complexify Sys.A₁₂) 0 (complexify Sys.A₂) ^ k) *ᵥ
          complexifyVec e₀ = 0 := by
    intro k
    rw [← Sys.complexify_fullA_fromBlocks, ← complexify_pow, ← complexify_mul,
      complexify_mulVec, hall k, complexifyVec_zero]
  have hdet : IsDetectable
      (Matrix.fromBlocks (complexify Sys.A₁) (complexify Sys.A₁₂) 0
        (complexify Sys.A₂)) (complexify Sys.fullC) := by
    rw [← Sys.complexify_fullA_fromBlocks]
    exact hC1
  have hblk := blk₂_eq_zero_of_unobservable (complexify Sys.A₁)
    (complexify Sys.A₁₂) (complexify Sys.A₂) (complexify Sys.fullC)
    hdet Sys.hAnti hallℂ
  -- read off `e₂ = 0`
  have he₂blk : ∀ i, e₀ (Sum.inr i) = e₂ i := by
    intro i
    rw [he₀, Sys.freeInj_mulVec]
    rfl
  funext i
  have h1 := congrFun hblk i
  simp only [Pi.zero_apply] at h1 ⊢
  have h2 : complexifyVec e₀ (Sum.inr i) = (e₂ i : ℂ) := by
    rw [complexifyVec_apply, he₂blk i]
  rw [h2] at h1
  exact_mod_cast h1

/-- Under C1 the window curvature at horizon `n₁ + n₂` is positive
definite. -/
theorem Wmat_posDef (hC1 : Sys.C1) : (Sys.Wmat (n₁ + n₂)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Sys.Wmat_posSemidef (n₁ + n₂)).1 fun e₂ he₂ => ?_
  have hge := (Sys.Wmat_posSemidef (n₁ + n₂)).quadForm_nonneg e₂
  rcases eq_or_lt_of_le hge with heq | hlt
  · exact absurd (Sys.eq_zero_of_quadForm_Wmat_eq_zero hC1 heq.symm) he₂
  · simpa [quadForm] using hlt

/-- **Finite-window coercivity** (`lem:coercive`(1)): under C1, the value
of the horizon-`(n₁+n₂)` problem dominates a fixed multiple of the squared
antistable initial block, uniformly over the free stabilizable block. -/
theorem exists_window_coercivity (hC1 : Sys.C1) :
    ∃ α : ℝ, 0 < α ∧ ∀ (ξ : Fin n₁ → ℝ) (e₂ : Fin n₂ → ℝ),
      α * ‖e₂‖ ^ 2 ≤ quadForm (Sys.lq.ric (n₁ + n₂)) (Sum.elim ξ e₂) := by
  obtain ⟨α, hα, hbb⟩ := (Sys.Wmat_posDef hC1).exists_le_quadForm
  exact ⟨α, hα, fun ξ e₂ => le_trans (hbb e₂) (Sys.quadForm_Wmat_le _ ξ e₂)⟩


/-! ### The antistable block of trajectories and its forced decay -/

/-- The antistable block of any controlled error trajectory is autonomous:
`e₂(k) = A₂^k e₂(0)`. -/
lemma blk₂_traj (e₀ : Fin n₁ ⊕ Fin n₂ → ℝ) (ω : ℕ → Fin m → ℝ) : ∀ k,
    blk₂ (Sys.lq.traj e₀ ω k) = Sys.A₂ ^ k *ᵥ blk₂ e₀
  | 0 => by
    rw [LQSystem.traj_zero, pow_zero, Matrix.one_mulVec]
  | k + 1 => by
    rw [LQSystem.traj_succ, blk₂_add]
    have h1 : blk₂ (Sys.lq.A *ᵥ Sys.lq.traj e₀ ω k)
        = Sys.A₂ *ᵥ blk₂ (Sys.lq.traj e₀ ω k) := by
      rw [Sys.lq_A_eq, Matrix.fromBlocks_mulVec]
      funext i
      simp [blk₂, Matrix.zero_mulVec]
    have h2 : blk₂ (Sys.lq.B *ᵥ ω k) = 0 := by
      rw [Sys.lq_B_eq, Matrix.neg_mulVec, Matrix.fromRows_mulVec]
      funext i
      simp [blk₂]
    rw [h1, h2, add_zero, blk₂_traj e₀ ω k, Matrix.mulVec_mulVec, ← pow_succ']

/-- Antistability passes to powers (spectral mapping). -/
lemma hAnti_pow (M : ℕ) (hM : 1 ≤ M) :
    ∀ μ ∈ spectrum ℂ (complexify (Sys.A₂ ^ M)), 1 ≤ ‖μ‖ := by
  intro μ hμ
  rw [complexify_pow] at hμ
  have hdeg : 0 < (Polynomial.X ^ M : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast hM
  have h := spectrum.map_polynomial_aeval_of_degree_pos
    (complexify Sys.A₂) (Polynomial.X ^ M : Polynomial ℂ) hdeg
  rw [map_pow, Polynomial.aeval_X] at h
  rw [h] at hμ
  obtain ⟨ν, hν, hνμ⟩ := hμ
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at hνμ
  rw [← hνμ, norm_pow]
  exact one_le_pow₀ (Sys.hAnti ν hν)

/-- **Forced decay of the antistable optimal block**: under C1 ∧ C2 the
antistable block of the optimal initial error dies like `1/√T` — the
window-sum consequence of coercivity and Gramian growth. -/
theorem exists_optInit_blk₂_decay (hC1 : Sys.C1) (hC2 : Sys.C2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin n₁ ⊕ Fin n₂ → ℝ) (J T : ℕ),
      (n₁ + n₂) * J ≤ T →
      (J : ℝ) * ‖blk₂ (Sys.optInit a T)‖ ^ 2 ≤ c * ‖a‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos (n₁ + n₂) with hM0 | hM1
  · refine ⟨1, one_pos, fun a J T hJT => ?_⟩
    have hn₂ : n₂ = 0 := by omega
    subst hn₂
    have h0 : blk₂ (Sys.optInit a T) = 0 := Subsingleton.elim _ _
    rw [h0, norm_zero]
    have : (0 : ℝ) ≤ ‖a‖ ^ 2 := by positivity
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  · obtain ⟨α, hα, hcoer⟩ := Sys.exists_window_coercivity hC1
    obtain ⟨cval, hcval, hval⟩ := Sys.exists_value_bound hC1 hC2
    obtain ⟨cB, hcB, hgram⟩ :=
      gramian_growth (Sys.A₂ ^ (n₁ + n₂)) (Sys.hAnti_pow (n₁ + n₂) hM1)
    refine ⟨cval / (α * cB), by positivity, fun a J T hJT => ?_⟩
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ1
    · subst hJ0
      have : (0 : ℝ) ≤ cval / (α * cB) * ‖a‖ ^ 2 := by positivity
      simpa using this
    · set M := n₁ + n₂ with hMdef
      set e₀ := Sys.optInit a T with he₀
      set ω := Sys.lq.optCtrl e₀ T with hω
      -- each window value dominates the coercive bound at the restart point
      have h2 : ∀ j ∈ Finset.range J,
          α * ‖(Sys.A₂ ^ M) ^ j *ᵥ blk₂ e₀‖ ^ 2
            ≤ quadForm (Sys.lq.ric M) (Sys.lq.traj e₀ ω (j * M)) := by
        intro j _
        have h3 := hcoer (blk₁ (Sys.lq.traj e₀ ω (j * M)))
          (blk₂ (Sys.lq.traj e₀ ω (j * M)))
        rw [sumElim_blk] at h3
        have h4 : blk₂ (Sys.lq.traj e₀ ω (j * M)) = (Sys.A₂ ^ M) ^ j *ᵥ blk₂ e₀ := by
          rw [Sys.blk₂_traj, show j * M = M * j from mul_comm j M, pow_mul]
        rw [h4] at h3
        exact h3
      -- window sums are dominated by the total cost
      have h5 : ∑ j ∈ Finset.range J,
          quadForm (Sys.lq.ric M) (Sys.lq.traj e₀ ω (j * M))
            ≤ Sys.lq.cost e₀ ω T := by
        calc ∑ j ∈ Finset.range J,
            quadForm (Sys.lq.ric M) (Sys.lq.traj e₀ ω (j * M))
            ≤ ∑ j ∈ Finset.range J,
                Sys.lq.cost (Sys.lq.traj e₀ ω (j * M))
                  (fun r => ω (j * M + r)) M :=
              Finset.sum_le_sum fun j _ =>
                Sys.lq.quadForm_ric_le_cost _ _ M
        _ = Sys.lq.cost e₀ ω (J * M) :=
              (Sys.lq.cost_eq_sum_windows e₀ ω M J).symm
        _ ≤ Sys.lq.cost e₀ ω T := by
              refine Sys.lq.cost_mono e₀ ω ?_
              calc J * M = M * J := mul_comm J M
              _ ≤ T := hJT
      -- the total cost is dominated by the value bound
      have h6 : Sys.lq.cost e₀ ω T ≤ cval * ‖a‖ ^ 2 := by
        have h7 : Sys.lq.cost e₀ ω T = quadForm (Sys.lq.ric T) e₀ := by
          rw [hω, Sys.lq.cost_optCtrl]
        have h8 : quadForm (Sys.lq.ric T) e₀ ≤ Sys.value a T := by
          unfold value outerObj
          have h9 := Sys.priorPenalty_nonneg a (Sys.optInit a T)
          rw [← he₀]
          linarith
        have h10 := hval a T
        linarith [h7 ▸ h8]
      -- the gramian growth converts the window sums into linear growth
      have h11 : cB * J * ‖blk₂ e₀‖ ^ 2
          ≤ ∑ j ∈ Finset.range J, ‖(Sys.A₂ ^ M) ^ j *ᵥ blk₂ e₀‖ ^ 2 :=
        hgram (blk₂ e₀) J hJ1
      have h12 : α * (cB * J * ‖blk₂ e₀‖ ^ 2) ≤ cval * ‖a‖ ^ 2 := by
        calc α * (cB * J * ‖blk₂ e₀‖ ^ 2)
            ≤ α * ∑ j ∈ Finset.range J, ‖(Sys.A₂ ^ M) ^ j *ᵥ blk₂ e₀‖ ^ 2 :=
              mul_le_mul_of_nonneg_left h11 hα.le
        _ = ∑ j ∈ Finset.range J, α * ‖(Sys.A₂ ^ M) ^ j *ᵥ blk₂ e₀‖ ^ 2 :=
              Finset.mul_sum _ _ _
        _ ≤ ∑ j ∈ Finset.range J,
              quadForm (Sys.lq.ric M) (Sys.lq.traj e₀ ω (j * M)) :=
              Finset.sum_le_sum h2
        _ ≤ Sys.lq.cost e₀ ω T := h5
        _ ≤ cval * ‖a‖ ^ 2 := h6
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      calc (J : ℝ) * ‖blk₂ e₀‖ ^ 2 * (α * cB)
          = α * (cB * J * ‖blk₂ e₀‖ ^ 2) := by ring
      _ ≤ cval * ‖a‖ ^ 2 := h12

end FIESystem

end Estimation

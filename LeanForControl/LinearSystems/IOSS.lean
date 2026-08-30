import LeanForControl.LinearSystems.StagedFacts
import LeanForControl.LinearSystems.QuadForm
import Architect

/-!
# A quadratic IOSS-Lyapunov function from detectability

The paper's `eq:iioss-bounds`/`eq:iioss-dec` (Cai–Teel style, quadratic
case): for a detectable pair `(A, C)` and the system
`x⁺ = Ax + Gw`, `y = Cx`, there is `P ≻ 0` with

* `a₁‖x‖² ≤ x'Px ≤ a₂‖x‖²`, and
* `V(Ax + Gw) − V(x) ≤ −a₃‖x‖² + c₁‖w‖² + c₂‖y‖²`.

Construction: `L` from `detect_inj` makes `F := A − LC` Schur, and
`P := ∑ₖ (Fᵏ)'(Fᵏ)` solves the discrete Lyapunov equation
`F'PF − P = −I`; the dissipation follows from Young's inequality on the
cross terms of `Ax + Gw = Fx + (L y + G w)`. The rescaling freedom the
paper uses (`ρ·V_io`) is immediate since every inequality is
homogeneous in `P`.
-/

namespace LinearSystems

open Matrix Filter

open scoped Matrix.Norms.Operator

variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [Fintype σ]

/-- Crude Cauchy–Schwarz for the dot product in sup norms. -/
lemma abs_dotProduct_le (x y : ι → ℝ) :
    |x ⬝ᵥ y| ≤ (Fintype.card ι : ℝ) * ‖x‖ * ‖y‖ := by
  calc |x ⬝ᵥ y| ≤ ∑ i, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖x‖ * ‖y‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        have h1 : |x i| ≤ ‖x‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm x i
        have h2 : |y i| ≤ ‖y‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm y i
        exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card ι : ℝ) * ‖x‖ * ‖y‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

section LyapunovSum

variable {F : Matrix ι ι ℝ}

/-- Summability of the Lyapunov series for a Schur matrix. -/
lemma summable_lyapTerm (hF : IsSchurStable F) :
    Summable (fun k : ℕ => (F ^ k)ᵀ * F ^ k) := by
  obtain ⟨c, ρ, hc, hρ0, hρ1, hpow⟩ := hF.exists_pow_norm_le
  obtain ⟨c', ρ', hc', hρ0', hρ1', hpow'⟩ :=
    hF.transpose.exists_pow_norm_le
  refine Summable.of_norm_bounded
    (g := fun k => (c' * c) * (ρ' * ρ) ^ k) ?_ ?_
  · have h1 : (0:ℝ) ≤ ρ' * ρ := by positivity
    have h2 : ρ' * ρ < 1 := by nlinarith
    exact (summable_geometric_of_lt_one h1 h2).mul_left _
  · intro k
    calc ‖(F ^ k)ᵀ * F ^ k‖ ≤ ‖(F ^ k)ᵀ‖ * ‖F ^ k‖ :=
          Matrix.linfty_opNorm_mul _ _
      _ = ‖(Fᵀ) ^ k‖ * ‖F ^ k‖ := by rw [Matrix.transpose_pow]
      _ ≤ (c' * ρ' ^ k) * (c * ρ ^ k) := by
          refine mul_le_mul (hpow' k) (hpow k) (norm_nonneg _) ?_
          positivity
      _ = (c' * c) * (ρ' * ρ) ^ k := by
          rw [mul_pow]
          ring

/-- The Lyapunov sum `P = ∑ₖ (Fᵏ)'(Fᵏ)`. -/
noncomputable def lyapSum (F : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ∑' k : ℕ, (F ^ k)ᵀ * F ^ k

/-- The action of a matrix `tsum` is the `tsum` of actions. -/
private lemma tsum_mulVec {f : ℕ → Matrix ι ι ℝ} (hf : Summable f)
    (x : ι → ℝ) : (∑' k, f k) *ᵥ x = ∑' k, f k *ᵥ x := by
  have hL : IsLinearMap ℝ (fun M : Matrix ι ι ℝ => M *ᵥ x) :=
    ⟨fun M N => Matrix.add_mulVec M N x,
      fun c M => Matrix.smul_mulVec c M x⟩
  have h1 := (LinearMap.toContinuousLinearMap (hL.mk' _)).map_tsum hf
  simp only [LinearMap.coe_toContinuousLinearMap',
    IsLinearMap.mk'_apply] at h1
  exact h1

/-- The quadratic form of the Lyapunov sum is the orbit energy. -/
lemma quadForm_lyapSum (hF : IsSchurStable F) (x : ι → ℝ) :
    quadForm (lyapSum F) x = ∑' k, (F ^ k *ᵥ x) ⬝ᵥ (F ^ k *ᵥ x) := by
  unfold lyapSum quadForm
  rw [tsum_mulVec (summable_lyapTerm hF) x]
  have hsum : Summable (fun k => ((F ^ k)ᵀ * F ^ k) *ᵥ x) := by
    have hL : IsLinearMap ℝ (fun M : Matrix ι ι ℝ => M *ᵥ x) :=
      ⟨fun M N => Matrix.add_mulVec M N x,
        fun c M => Matrix.smul_mulVec c M x⟩
    have h2 := (LinearMap.toContinuousLinearMap
      (hL.mk' _)).summable (summable_lyapTerm hF)
    simp only [LinearMap.coe_toContinuousLinearMap',
      IsLinearMap.mk'_apply] at h2
    exact h2
  have hL2 : IsLinearMap ℝ (fun v : ι → ℝ => x ⬝ᵥ v) :=
    ⟨fun a b => dotProduct_add x a b, fun c v => by
      rw [dotProduct_smul, smul_eq_mul]⟩
  have h3 := (LinearMap.toContinuousLinearMap (hL2.mk' _)).map_tsum hsum
  simp only [LinearMap.coe_toContinuousLinearMap',
    IsLinearMap.mk'_apply] at h3
  rw [h3]
  refine tsum_congr fun k => ?_
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec_eq,
    Matrix.transpose_transpose]

/-- Summability of the orbit energies. -/
lemma summable_orbit (hF : IsSchurStable F) (x : ι → ℝ) :
    Summable (fun k => (F ^ k *ᵥ x) ⬝ᵥ (F ^ k *ᵥ x)) := by
  obtain ⟨c, ρ, hc, hρ0, hρ1, hpow⟩ := hF.exists_pow_norm_le
  refine Summable.of_norm_bounded
    (g := fun k => (Fintype.card ι : ℝ) * (c * ‖x‖) ^ 2 * (ρ ^ 2) ^ k)
    ?_ ?_
  · have h1 : (0:ℝ) ≤ ρ ^ 2 := by positivity
    have h2 : ρ ^ 2 < 1 := by nlinarith
    exact (summable_geometric_of_lt_one h1 h2).mul_left _
  · intro k
    have h3 : ‖F ^ k *ᵥ x‖ ≤ c * ρ ^ k * ‖x‖ := by
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hpow k) (norm_nonneg _)
    have h4 := abs_dotProduct_le (F ^ k *ᵥ x) (F ^ k *ᵥ x)
    have h5 : (0:ℝ) ≤ ‖F ^ k *ᵥ x‖ := norm_nonneg _
    have h6 : (0:ℝ) ≤ c * ρ ^ k * ‖x‖ := by positivity
    rw [Real.norm_eq_abs]
    calc |(F ^ k *ᵥ x) ⬝ᵥ (F ^ k *ᵥ x)|
        ≤ (Fintype.card ι : ℝ) * ‖F ^ k *ᵥ x‖ * ‖F ^ k *ᵥ x‖ := h4
      _ ≤ (Fintype.card ι : ℝ) * (c * ρ ^ k * ‖x‖)
          * (c * ρ ^ k * ‖x‖) := by
          have hcard : (0:ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
          nlinarith [mul_le_mul h3 h3 h5 h6]
      _ = (Fintype.card ι : ℝ) * (c * ‖x‖) ^ 2 * (ρ ^ 2) ^ k := by
          ring

/-- The Lyapunov identity `V(Fx) = V(x) − x⬝x`. -/
lemma quadForm_lyapSum_shift (hF : IsSchurStable F) (x : ι → ℝ) :
    quadForm (lyapSum F) (F *ᵥ x)
      = quadForm (lyapSum F) x - x ⬝ᵥ x := by
  rw [quadForm_lyapSum hF, quadForm_lyapSum hF]
  have h1 : (fun k => (F ^ k *ᵥ (F *ᵥ x)) ⬝ᵥ (F ^ k *ᵥ (F *ᵥ x)))
      = fun k => (F ^ (k + 1) *ᵥ x) ⬝ᵥ (F ^ (k + 1) *ᵥ x) := by
    funext k
    rw [Matrix.mulVec_mulVec, ← pow_succ]
  rw [h1]
  have h2 := (summable_orbit hF x).tsum_eq_zero_add
  have h3 : (F ^ 0 *ᵥ x) ⬝ᵥ (F ^ 0 *ᵥ x) = x ⬝ᵥ x := by
    rw [pow_zero, Matrix.one_mulVec]
  rw [h3] at h2
  linarith

/-- The Lyapunov sum is symmetric. -/
lemma lyapSum_isHermitian (hF : IsSchurStable F) :
    (lyapSum F).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  unfold lyapSum
  have hL : IsLinearMap ℝ (fun M : Matrix ι ι ℝ => Mᵀ) :=
    ⟨fun M N => Matrix.transpose_add M N, fun c M => rfl⟩
  have h2 := (LinearMap.toContinuousLinearMap
    (hL.mk' _)).map_tsum (summable_lyapTerm hF)
  simp only [LinearMap.coe_toContinuousLinearMap',
    IsLinearMap.mk'_apply] at h2
  rw [h2]
  refine tsum_congr fun k => ?_
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

end LyapunovSum

set_option maxHeartbeats 1000000 in
/-- **The quadratic IOSS-Lyapunov function** (`eq:iioss-bounds` and
`eq:iioss-dec`): detectability yields `P ≻ 0` whose quadratic form
dissipates along `x⁺ = Ax + Gw` up to input and output energies. -/
theorem exists_ioss_lyapunov (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (G : Matrix ι σ ℝ)
    (hdet : IsDetectable (complexify A) (complexify C)) :
    ∃ (P : Matrix ι ι ℝ) (a₁ a₂ a₃ c₁ c₂ : ℝ),
      P.PosDef ∧ 0 < a₁ ∧ 0 < a₂ ∧ 0 < a₃ ∧ 0 < c₁ ∧ 0 < c₂ ∧
      (∀ x, a₁ * ‖x‖ ^ 2 ≤ quadForm P x
        ∧ quadForm P x ≤ a₂ * ‖x‖ ^ 2) ∧
      (∀ x w, quadForm P (A *ᵥ x + G *ᵥ w) - quadForm P x
        ≤ -a₃ * ‖x‖ ^ 2 + c₁ * ‖w‖ ^ 2 + c₂ * ‖C *ᵥ x‖ ^ 2) := by
  classical
  obtain ⟨L, hL⟩ := detect_inj A C hdet
  set F := A - L * C with hFdef
  set P := lyapSum F with hPdef
  have hherm := lyapSum_isHermitian hL
  -- coarse data
  obtain ⟨cq, hcq, hbq⟩ := exists_quadForm_le P
  set n₀ : ℝ := (Fintype.card ι : ℝ) with hn₀
  have hcard : (0:ℝ) < n₀ ∨ n₀ = 0 := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · right; rw [hn₀]; exact_mod_cast h
    · left; rw [hn₀]; exact_mod_cast h
  -- trivial index type: everything degenerates
  rcases isEmpty_or_nonempty ι with hemp | hne
  · refine ⟨1, 1, 1, 1, 1, 1, Matrix.PosDef.one, one_pos, one_pos,
      one_pos, one_pos, one_pos, ?_, ?_⟩
    · intro x
      have hx0 : x = 0 := Subsingleton.elim x 0
      simp [hx0, quadForm]
    · intro x w
      have hAx : A *ᵥ x + G *ᵥ w = 0 :=
        Subsingleton.elim (A *ᵥ x + G *ᵥ w) 0
      have hx0 : x = 0 := Subsingleton.elim x 0
      rw [hAx, hx0]
      simp [quadForm]
  -- the real case
  have hn₀pos : (0:ℝ) < n₀ := by
    rw [hn₀]
    exact_mod_cast Fintype.card_pos
  -- lower bound: the k = 0 term
  have hlow : ∀ x : ι → ℝ, ‖x‖ ^ 2 ≤ quadForm P x := by
    intro x
    rw [hPdef, quadForm_lyapSum hL]
    have h1 : x ⬝ᵥ x ≤ ∑' k, (F ^ k *ᵥ x) ⬝ᵥ (F ^ k *ᵥ x) := by
      have h2 := (summable_orbit hL x).tsum_eq_zero_add
      have h3 : (F ^ 0 *ᵥ x) ⬝ᵥ (F ^ 0 *ᵥ x) = x ⬝ᵥ x := by
        rw [pow_zero, Matrix.one_mulVec]
      rw [h3] at h2
      have h4 : (0:ℝ) ≤ ∑' k, (F ^ (k + 1) *ᵥ x) ⬝ᵥ (F ^ (k + 1) *ᵥ x) := by
        refine tsum_nonneg fun k => ?_
        have := sq_norm_le_dotProduct (F ^ (k + 1) *ᵥ x)
        nlinarith [sq_nonneg ‖F ^ (k + 1) *ᵥ x‖]
      linarith
    have h5 := sq_norm_le_dotProduct x
    linarith
  have hPD : P.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm ?_
    intro x hx
    rw [star_trivial]
    have h1 := hlow x
    have h2 : (0:ℝ) < ‖x‖ ^ 2 := by
      have := norm_pos_iff.mpr hx
      positivity
    show 0 < x ⬝ᵥ (P *ᵥ x)
    unfold quadForm at h1
    linarith
  -- dissipation constants
  set cP : ℝ := ‖P‖ with hcP
  set cF : ℝ := ‖F‖ with hcF
  set K : ℝ := n₀ * cP * cF with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    positivity
  refine ⟨P, 1, cq, 1 / 2,
    2 * (2 * K ^ 2 + cq) * (‖G‖ + 1) ^ 2 + 1,
    2 * (2 * K ^ 2 + cq) * (‖L‖ + 1) ^ 2 + 1,
    hPD, one_pos, hcq, by norm_num, by positivity, by positivity,
    fun x => ⟨by rw [one_mul]; exact hlow x, hbq x⟩, ?_⟩
  intro x w
  set s : ι → ℝ := L *ᵥ (C *ᵥ x) + G *ᵥ w with hs
  have hsplit : A *ᵥ x + G *ᵥ w = F *ᵥ x + s := by
    rw [hFdef, hs, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    module
  rw [hsplit]
  have hexp : quadForm P (F *ᵥ x + s)
      = quadForm P (F *ᵥ x) + 2 * ((F *ᵥ x) ⬝ᵥ (P *ᵥ s))
        + quadForm P s :=
    quadForm_add_of_isHermitian hherm _ _
  have hshift := quadForm_lyapSum_shift hL x
  rw [← hPdef] at hshift
  -- the shifted term drops by the full dot square
  have hdrop : quadForm P (F *ᵥ x) ≤ quadForm P x - ‖x‖ ^ 2 := by
    have h1 := sq_norm_le_dotProduct x
    linarith
  -- cross-term bound and Young's inequality
  have hcross : |(F *ᵥ x) ⬝ᵥ (P *ᵥ s)| ≤ K * ‖x‖ * ‖s‖ := by
    calc |(F *ᵥ x) ⬝ᵥ (P *ᵥ s)|
        ≤ n₀ * ‖F *ᵥ x‖ * ‖P *ᵥ s‖ := abs_dotProduct_le _ _
      _ ≤ n₀ * (cF * ‖x‖) * (cP * ‖s‖) := by
          have h2 := Matrix.linfty_opNorm_mulVec F x
          have h3 := Matrix.linfty_opNorm_mulVec P s
          rw [← hcF] at h2
          rw [← hcP] at h3
          have h4 : (0:ℝ) ≤ ‖F *ᵥ x‖ := norm_nonneg _
          have h5 : (0:ℝ) ≤ n₀ := hn₀pos.le
          have h6 : (0:ℝ) ≤ cF * ‖x‖ := by
            rw [hcF]
            positivity
          nlinarith [norm_nonneg (P *ᵥ s), norm_nonneg s,
            mul_le_mul h2 h3 (norm_nonneg _) h6]
      _ = K * ‖x‖ * ‖s‖ := by
          rw [hK]
          ring
  have hyoung : 2 * ((F *ᵥ x) ⬝ᵥ (P *ᵥ s))
      ≤ (1 / 2) * ‖x‖ ^ 2 + 2 * K ^ 2 * ‖s‖ ^ 2 := by
    have h1 : (F *ᵥ x) ⬝ᵥ (P *ᵥ s) ≤ K * ‖x‖ * ‖s‖ :=
      le_trans (le_abs_self _) hcross
    nlinarith [sq_nonneg (‖x‖ - 2 * K * ‖s‖), norm_nonneg x,
      norm_nonneg s]
  have hVs : quadForm P s ≤ cq * ‖s‖ ^ 2 := hbq s
  -- the driving term
  have hsbound : ‖s‖ ^ 2 ≤ 2 * (‖L‖ + 1) ^ 2 * ‖C *ᵥ x‖ ^ 2
      + 2 * (‖G‖ + 1) ^ 2 * ‖w‖ ^ 2 := by
    have h1 : ‖s‖ ≤ ‖L‖ * ‖C *ᵥ x‖ + ‖G‖ * ‖w‖ := by
      rw [hs]
      refine (norm_add_le _ _).trans ?_
      have h2 := Matrix.linfty_opNorm_mulVec L (C *ᵥ x)
      have h3 := Matrix.linfty_opNorm_mulVec G w
      linarith
    have h4 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
    have h5 : (0:ℝ) ≤ ‖L‖ * ‖C *ᵥ x‖ + ‖G‖ * ‖w‖ := by positivity
    nlinarith [sq_nonneg (‖L‖ * ‖C *ᵥ x‖ - ‖G‖ * ‖w‖),
      norm_nonneg (C *ᵥ x), norm_nonneg w, norm_nonneg L, norm_nonneg G,
      sq_nonneg ‖C *ᵥ x‖, sq_nonneg ‖w‖,
      mul_nonneg (norm_nonneg L) (norm_nonneg (C *ᵥ x)),
      mul_nonneg (norm_nonneg G) (norm_nonneg w)]
  -- assemble
  have hfinal : quadForm P (F *ᵥ x + s) - quadForm P x
      ≤ -(1 / 2) * ‖x‖ ^ 2 + (2 * K ^ 2 + cq) * ‖s‖ ^ 2 := by
    rw [hexp]
    nlinarith
  have hcoef : (0:ℝ) ≤ 2 * K ^ 2 + cq := by positivity
  calc quadForm P (F *ᵥ x + s) - quadForm P x
      ≤ -(1 / 2) * ‖x‖ ^ 2 + (2 * K ^ 2 + cq) * ‖s‖ ^ 2 := hfinal
    _ ≤ -(1 / 2) * ‖x‖ ^ 2
        + (2 * K ^ 2 + cq) * (2 * (‖L‖ + 1) ^ 2 * ‖C *ᵥ x‖ ^ 2
          + 2 * (‖G‖ + 1) ^ 2 * ‖w‖ ^ 2) := by
        have := mul_le_mul_of_nonneg_left hsbound hcoef
        linarith
    _ ≤ -(1 / 2) * ‖x‖ ^ 2
        + (2 * (2 * K ^ 2 + cq) * (‖G‖ + 1) ^ 2 + 1) * ‖w‖ ^ 2
        + (2 * (2 * K ^ 2 + cq) * (‖L‖ + 1) ^ 2 + 1) * ‖C *ᵥ x‖ ^ 2 := by
        nlinarith [sq_nonneg ‖w‖, sq_nonneg ‖C *ᵥ x‖]

/-- **Summed dissipation** (`eq:iosssum` device): telescoping the
IOSS-Lyapunov decrease along a trajectory of `x⁺ = Ax + Gw` bounds the
terminal state by the initial state and the input/output energies. -/
theorem terminal_sq_bound_of_ioss {A : Matrix ι ι ℝ}
    {C : Matrix κ ι ℝ} {G : Matrix ι σ ℝ} {P : Matrix ι ι ℝ}
    {a₁ a₂ a₃ c₁ c₂ : ℝ} (ha₃ : 0 ≤ a₃)
    (hbounds : ∀ x, a₁ * ‖x‖ ^ 2 ≤ quadForm P x
      ∧ quadForm P x ≤ a₂ * ‖x‖ ^ 2)
    (hdiss : ∀ x w, quadForm P (A *ᵥ x + G *ᵥ w) - quadForm P x
      ≤ -a₃ * ‖x‖ ^ 2 + c₁ * ‖w‖ ^ 2 + c₂ * ‖C *ᵥ x‖ ^ 2)
    (x : ℕ → ι → ℝ) (w : ℕ → σ → ℝ)
    (hrec : ∀ k, x (k + 1) = A *ᵥ x k + G *ᵥ w k) (T : ℕ) :
    a₁ * ‖x T‖ ^ 2
      ≤ a₂ * ‖x 0‖ ^ 2
        + c₁ * ∑ k ∈ Finset.range T, ‖w k‖ ^ 2
        + c₂ * ∑ k ∈ Finset.range T, ‖C *ᵥ x k‖ ^ 2 := by
  have htel : ∀ N : ℕ, quadForm P (x N)
      ≤ quadForm P (x 0)
        + ∑ k ∈ Finset.range N,
            (c₁ * ‖w k‖ ^ 2 + c₂ * ‖C *ᵥ x k‖ ^ 2) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have h1 := hdiss (x N) (w N)
      rw [← hrec N] at h1
      have h2 : -a₃ * ‖x N‖ ^ 2 ≤ 0 := by
        have := sq_nonneg ‖x N‖
        nlinarith
      rw [Finset.sum_range_succ]
      linarith
  have h3 := (hbounds (x T)).1
  have h4 := (hbounds (x 0)).2
  have h5 := htel T
  have h6 : ∑ k ∈ Finset.range T,
      (c₁ * ‖w k‖ ^ 2 + c₂ * ‖C *ᵥ x k‖ ^ 2)
      = c₁ * ∑ k ∈ Finset.range T, ‖w k‖ ^ 2
        + c₂ * ∑ k ∈ Finset.range T, ‖C *ᵥ x k‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [h6] at h5
  linarith

end LinearSystems

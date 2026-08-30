import LeanForControl.Estimation.FIE
import LeanForControl.LinearSystems.RealSplit
import LeanForControl.LinearSystems.ConstrainedQuadratic
import Architect

/-!
# The general estimation problem (S2 of the generality sprint)

The paper's `ℙ_Te` in its own coordinates: a general system
`(A, G, C)` with prior `Σ₀ ⪰ 0` and penalties `Q⁻¹ ≻ 0`, `R⁻¹ ≻ 0` —
**no structural hypotheses**. The standing conditions C1/C2/C3w are
stated invariantly (D1 of the sprint note: the unstable, uncontrollable
subspace is the dot-product annihilator of
`V₁ = reachable ⊔ stable`), and stability is measured on the optimal
terminal error of the general problem, exactly as in `def:gas`.

The outer (initial-error) optimization mirrors the reduced layer with
the single-block parameterization `e₀ = a + Σ₀ v`.
-/

namespace Estimation

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

/-- The general estimation data: dynamics, noise input, output, prior,
and noise penalties. -/
structure GeneralSystem (n m p : ℕ) where
  /-- State matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- Noise input matrix. -/
  G : Matrix (Fin n) (Fin m) ℝ
  /-- Output matrix. -/
  C : Matrix (Fin p) (Fin n) ℝ
  /-- Prior covariance. -/
  Sig0 : Matrix (Fin n) (Fin n) ℝ
  /-- Process-noise penalty `Q⁻¹`. -/
  Qi : Matrix (Fin m) (Fin m) ℝ
  /-- Measurement-noise penalty `R⁻¹`. -/
  Ri : Matrix (Fin p) (Fin p) ℝ
  /-- `Σ₀ ⪰ 0`. -/
  hSig0 : Sig0.PosSemidef
  /-- `Q ≻ 0`. -/
  hQi : Qi.PosDef
  /-- `R ≻ 0`. -/
  hRi : Ri.PosDef

namespace GeneralSystem

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-- The tail LQ problem of the general system (identical in shape to
the reduced one; the prior does not enter). -/
noncomputable def glq : LQSystem (Fin n) (Fin m) where
  A := S.A
  B := -S.G
  Qs := S.Cᵀ * S.Ri * S.C
  Ru := S.Qi
  hQs := by
    have h := S.hRi.posSemidef.mul_mul_conjTranspose_same S.Cᵀ
    rwa [show (S.Cᵀ)ᴴ = S.C from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]]
      at h
  hRu := S.hQi

lemma glq_A_eq : S.glq.A = S.A := rfl

lemma glq_B_eq : S.glq.B = -S.G := rfl

lemma quadForm_glq_Qs (e : Fin n → ℝ) :
    quadForm S.glq.Qs e = quadForm S.Ri (S.C *ᵥ e) := by
  rw [quadForm_mulVec]
  rfl

/-- The prior penalty `‖e₀ - a‖²_{Σ₀†}`. -/
noncomputable def priorPen (a e₀ : Fin n → ℝ) : ℝ :=
  quadForm (symmPinv S.hSig0.1) (e₀ - a)

/-- The support constraint: the prior deviation lies in `ran Σ₀`. -/
def Feasible (a e₀ : Fin n → ℝ) : Prop :=
  ∃ z, e₀ - a = S.Sig0 *ᵥ z

/-- The horizon-`T` general full-information objective. -/
noncomputable def gCost (a e₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ)
    (T : ℕ) : ℝ :=
  S.priorPen a e₀ + S.glq.cost e₀ ω T

lemma priorPen_nonneg (a e₀ : Fin n → ℝ) : 0 ≤ S.priorPen a e₀ :=
  S.hSig0.symmPinv.quadForm_nonneg _

/-! ### The outer optimization (single-block KKT) -/

/-- Stationarity of an initial-error decision. -/
def IsStationary (a e₀ : Fin n → ℝ) (T : ℕ) : Prop :=
  S.Feasible a e₀ ∧ ∀ d : Fin n → ℝ, (∃ z, d = S.Sig0 *ᵥ z) →
    (symmPinv S.hSig0.1 *ᵥ (e₀ - a)) ⬝ᵥ d
      + (S.glq.ric T *ᵥ e₀) ⬝ᵥ d = 0

lemma ric_transpose_eq (T : ℕ) : (S.glq.ric T)ᵀ = S.glq.ric T := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact S.glq.ric_isHermitian T

/-- The outer gap formula at a stationary point. -/
theorem outerObj_gap {a e₀s : Fin n → ℝ} {T : ℕ}
    (hstat : S.IsStationary a e₀s T) {e₀ : Fin n → ℝ}
    (hfeas : S.Feasible a e₀) :
    S.priorPen a e₀ + quadForm (S.glq.ric T) e₀
      = S.priorPen a e₀s + quadForm (S.glq.ric T) e₀s
        + (quadForm (symmPinv S.hSig0.1) (e₀ - e₀s)
          + quadForm (S.glq.ric T) (e₀ - e₀s)) := by
  obtain ⟨hfs, hvar⟩ := hstat
  have hdir : ∃ z, e₀ - e₀s = S.Sig0 *ᵥ z := by
    obtain ⟨z, hz⟩ := hfeas
    obtain ⟨z', hz'⟩ := hfs
    refine ⟨z - z', ?_⟩
    rw [Matrix.mulVec_sub, ← hz, ← hz']
    abel
  have hvd := hvar (e₀ - e₀s) hdir
  have hsplit : e₀ - a = (e₀s - a) + (e₀ - e₀s) := by abel
  have hsplit' : e₀ = e₀s + (e₀ - e₀s) := by abel
  have hq1 : quadForm (symmPinv S.hSig0.1) (e₀ - a)
      = quadForm (symmPinv S.hSig0.1) (e₀s - a)
        + 2 * ((e₀s - a) ⬝ᵥ (symmPinv S.hSig0.1 *ᵥ (e₀ - e₀s)))
        + quadForm (symmPinv S.hSig0.1) (e₀ - e₀s) := by
    rw [hsplit, quadForm_add_of_isHermitian (symmPinv_isHermitian _)]
  have hq3 : quadForm (S.glq.ric T) e₀
      = quadForm (S.glq.ric T) e₀s
        + 2 * (e₀s ⬝ᵥ (S.glq.ric T *ᵥ (e₀ - e₀s)))
        + quadForm (S.glq.ric T) (e₀ - e₀s) := by
    conv_lhs => rw [hsplit']
    rw [quadForm_add_of_isHermitian (S.glq.ric_isHermitian T)]
  have hc1 : (e₀s - a) ⬝ᵥ (symmPinv S.hSig0.1 *ᵥ (e₀ - e₀s))
      = (symmPinv S.hSig0.1 *ᵥ (e₀s - a)) ⬝ᵥ (e₀ - e₀s) := by
    rw [dotProduct_mulVec_eq,
      (symmPinv_isHermitian S.hSig0.1).transpose_eq_self]
  have hc3 : e₀s ⬝ᵥ (S.glq.ric T *ᵥ (e₀ - e₀s))
      = (S.glq.ric T *ᵥ e₀s) ⬝ᵥ (e₀ - e₀s) := by
    rw [dotProduct_mulVec_eq, S.ric_transpose_eq]
  unfold priorPen
  rw [hq1, hq3, hc1, hc3]
  linarith [hvd]

/-- Existence of a stationary point. -/
theorem exists_isStationary (a : Fin n → ℝ) (T : ℕ) :
    ∃ e₀, S.IsStationary a e₀ T := by
  classical
  set L := S.Sig0 + S.Sig0ᵀ * S.glq.ric T * S.Sig0 with hL
  set sv : Fin n → ℝ := S.Sig0ᵀ *ᵥ (S.glq.ric T *ᵥ a) with hsv
  have hSig0t : S.Sig0ᵀ = S.Sig0 := S.hSig0.1.transpose_eq_self
  have hLpsd : L.PosSemidef := by
    refine S.hSig0.add ?_
    have h := (S.glq.ric_posSemidef T).mul_mul_conjTranspose_same S.Sig0ᵀ
    rwa [show (S.Sig0ᵀ)ᴴ = S.Sig0 from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]]
      at h
  have hψ : ∀ v, S.priorPen a (a + S.Sig0 *ᵥ v)
      + quadForm (S.glq.ric T) (a + S.Sig0 *ᵥ v)
      = quadForm L v + 2 * (sv ⬝ᵥ v)
        + quadForm (S.glq.ric T) a := by
    intro v
    unfold priorPen
    rw [add_sub_cancel_left, quadForm_symmPinv_image S.hSig0,
      quadForm_add_of_isHermitian (S.glq.ric_isHermitian T),
      quadForm_mulVec]
    have hcross : a ⬝ᵥ (S.glq.ric T *ᵥ (S.Sig0 *ᵥ v)) = sv ⬝ᵥ v := by
      rw [Matrix.mulVec_mulVec, dotProduct_mulVec_eq,
        Matrix.transpose_mul, hsv, ← Matrix.mulVec_mulVec,
        S.ric_transpose_eq]
    rw [hcross, hL, quadForm_add_matrix]
    ring
  have hbdd : ∀ v, 2 * ((-sv) ⬝ᵥ v)
      ≤ quadForm L v + quadForm (S.glq.ric T) a := by
    intro v
    have h1 : 0 ≤ S.priorPen a (a + S.Sig0 *ᵥ v)
        + quadForm (S.glq.ric T) (a + S.Sig0 *ᵥ v) :=
      add_nonneg (S.priorPen_nonneg _ _)
        ((S.glq.ric_posSemidef T).quadForm_nonneg _)
    rw [hψ v] at h1
    have h2 : (-sv) ⬝ᵥ v = -(sv ⬝ᵥ v) := by simp
    rw [h2]
    linarith
  obtain ⟨v, hv⟩ := hLpsd.exists_mulVec_eq hbdd
  refine ⟨a + S.Sig0 *ᵥ v, ⟨v, by rw [add_sub_cancel_left]⟩, ?_⟩
  rintro d ⟨w, hw⟩
  rw [add_sub_cancel_left, hw]
  have t1 : (symmPinv S.hSig0.1 *ᵥ (S.Sig0 *ᵥ v)) ⬝ᵥ (S.Sig0 *ᵥ w)
      = (S.Sig0 *ᵥ v) ⬝ᵥ w := by
    rw [dotProduct_mulVec_eq, hSig0t, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, self_mul_symmPinv_mul_self S.hSig0.1]
  have t2 : (S.glq.ric T *ᵥ (a + S.Sig0 *ᵥ v)) ⬝ᵥ (S.Sig0 *ᵥ w)
      = sv ⬝ᵥ w
        + ((S.Sig0ᵀ * S.glq.ric T * S.Sig0) *ᵥ v) ⬝ᵥ w := by
    rw [Matrix.mulVec_add, add_dotProduct]
    congr 1
    · rw [dotProduct_mulVec_eq, hsv]
    · rw [dotProduct_mulVec_eq]
      congr 1
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSig0t]
  have h5 : (L *ᵥ v) ⬝ᵥ w
      = (S.Sig0 *ᵥ v) ⬝ᵥ w
        + ((S.Sig0ᵀ * S.glq.ric T * S.Sig0) *ᵥ v) ⬝ᵥ w := by
    rw [hL, Matrix.add_mulVec, add_dotProduct]
  have h6 : (L *ᵥ v) ⬝ᵥ w = -(sv ⬝ᵥ w) := by
    rw [hv]
    simp
  rw [t1, t2]
  linarith

/-- Uniqueness of the stationary point. -/
theorem isStationary_unique {a e₀ e₀' : Fin n → ℝ} {T : ℕ}
    (h : S.IsStationary a e₀ T) (h' : S.IsStationary a e₀' T) :
    e₀ = e₀' := by
  have hg := S.outerObj_gap h h'.1
  have hg' := S.outerObj_gap h' h.1
  have hq1 := S.hSig0.symmPinv.quadForm_nonneg (e₀' - e₀)
  have hq2 := (S.glq.ric_posSemidef T).quadForm_nonneg (e₀' - e₀)
  have hq3 := S.hSig0.symmPinv.quadForm_nonneg (e₀ - e₀')
  have hq4 := (S.glq.ric_posSemidef T).quadForm_nonneg (e₀ - e₀')
  have h1 : quadForm (symmPinv S.hSig0.1) (e₀' - e₀) = 0 := by
    linarith
  obtain ⟨z, hz⟩ := h'.1
  obtain ⟨z', hz'⟩ := h.1
  have hd : e₀' - e₀ = S.Sig0 *ᵥ (z - z') := by
    rw [Matrix.mulVec_sub, ← hz, ← hz']
    abel
  rw [hd, quadForm_symmPinv_image S.hSig0] at h1
  have h2 := S.hSig0.mulVec_eq_zero_of_quadForm_eq_zero h1
  rw [← hd] at h2
  have h3 : e₀' = e₀ + 0 := by
    rw [← h2]
    abel
  rw [h3, add_zero]

/-- The optimal initial error of the general problem. -/
noncomputable def optInit (a : Fin n → ℝ) (T : ℕ) : Fin n → ℝ :=
  Classical.choose (S.exists_isStationary a T)

lemma optInit_isStationary (a : Fin n → ℝ) (T : ℕ) :
    S.IsStationary a (S.optInit a T) T :=
  Classical.choose_spec (S.exists_isStationary a T)

lemma optInit_feasible (a : Fin n → ℝ) (T : ℕ) :
    S.Feasible a (S.optInit a T) :=
  (S.optInit_isStationary a T).1

/-- The optimal value of the general horizon-`T` problem. -/
noncomputable def value (a : Fin n → ℝ) (T : ℕ) : ℝ :=
  S.priorPen a (S.optInit a T)
    + quadForm (S.glq.ric T) (S.optInit a T)

lemma value_nonneg (a : Fin n → ℝ) (T : ℕ) : 0 ≤ S.value a T :=
  add_nonneg (S.priorPen_nonneg _ _)
    ((S.glq.ric_posSemidef T).quadForm_nonneg _)

/-- Joint optimality. -/
theorem value_le_gCost {a e₀ : Fin n → ℝ} (hfeas : S.Feasible a e₀)
    (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    S.value a T ≤ S.gCost a e₀ ω T := by
  have h1 : S.priorPen a e₀ + quadForm (S.glq.ric T) e₀
      ≤ S.gCost a e₀ ω T := by
    unfold gCost
    have h2 := S.glq.quadForm_ric_le_cost e₀ ω T
    linarith
  have h3 := S.outerObj_gap (S.optInit_isStationary a T) hfeas
  have h4 := S.hSig0.symmPinv.quadForm_nonneg (e₀ - S.optInit a T)
  have h5 := (S.glq.ric_posSemidef T).quadForm_nonneg
    (e₀ - S.optInit a T)
  unfold value
  linarith

/-- The value is attained by the optimal control. -/
theorem gCost_optCtrl (a : Fin n → ℝ) (T : ℕ) :
    S.gCost a (S.optInit a T) (S.glq.optCtrl (S.optInit a T) T) T
      = S.value a T := by
  unfold gCost value
  rw [S.glq.cost_optCtrl]

/-- The optimal terminal error of the general problem. -/
noncomputable def optTerm (a : Fin n → ℝ) (T : ℕ) : Fin n → ℝ :=
  S.glq.optTraj (S.optInit a T) T T

/-- Global asymptotic stability (`def:gas`, general coordinates). -/
def IsGAS : Prop :=
  ∃ σ : ℕ → ℝ, Tendsto σ atTop (nhds 0) ∧
    ∀ (T : ℕ) (a : Fin n → ℝ), ‖S.optTerm a T‖ ≤ σ T * ‖a‖

/-- Global exponential stability (`def:ges-fi`, general coordinates). -/
def IsGES : Prop :=
  ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧
    ∀ (T : ℕ) (a : Fin n → ℝ), ‖S.optTerm a T‖ ≤ c * ρ ^ T * ‖a‖

/-! ### The invariant standing conditions -/

/-- The real reachability map. -/
noncomputable def realReachMap :
    (Fin n → Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := fun us => ∑ j : Fin n, (S.A ^ (j : ℕ) * S.G) *ᵥ us j
  map_add' := fun us vs => by
    simp only [Pi.add_apply, Matrix.mulVec_add]
    rw [Finset.sum_add_distrib]
  map_smul' := fun c us => by
    simp only [Pi.smul_apply, Matrix.mulVec_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

/-- The reachable subspace of `(A, G)`. -/
noncomputable def reachSub : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.range S.realReachMap

/-- The stabilizable subspace `V₁ = reachable ⊔ stable`. -/
noncomputable def stabilizableSub : Submodule ℝ (Fin n → ℝ) :=
  S.reachSub ⊔ stableSub S.A

/-- The unstable, uncontrollable subspace (D1): the dot-product
annihilator of the stabilizable subspace — the span of
`col(0, I_{n₂})` in the orthogonal canonical form of the paper. -/
noncomputable def uucSub : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | ∀ u ∈ S.stabilizableSub, u ⬝ᵥ v = 0}
  add_mem' := fun ha hb u hu => by
    rw [dotProduct_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => by rw [dotProduct_zero]
  smul_mem' := fun c v hv u hu => by
    rw [dotProduct_smul, hv u hu, smul_zero]

/-- **C1**: `(A, C)` is detectable. -/
def C1 : Prop := IsDetectable (complexify S.A) (complexify S.C)

/-- **C2**: the kernel of the prior meets the unstable, uncontrollable
subspace only at the origin. -/
def C2 : Prop := ∀ v : Fin n → ℝ, S.Sig0 *ᵥ v = 0 → v ∈ S.uucSub →
  v = 0

/-- **C3w**: no uncontrollable eigenvalues on the unit circle (PBH
left-eigenvector form). -/
def C3w : Prop := ∀ (μ : ℂ) (v : Fin n → ℂ), ‖μ‖ = 1 →
  (complexify S.A)ᵀ *ᵥ v = μ • v → (complexify S.G)ᵀ *ᵥ v = 0 → v = 0

end GeneralSystem

end Estimation

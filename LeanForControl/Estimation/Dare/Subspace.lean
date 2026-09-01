import LeanForControl.Estimation.Dare.Formula
import Architect

/-!
# The attraction denominator (E4, `lem:sysinterp`)

Arc 1's geometry: the limiting denominator `M∞ = I + 𝒢∞D` of
`eq:formula` is nonsingular **iff** C2. The antistable deflating pair
`(X₋, Y₋, E₋)` of the pencil is the one imported object
(`DeflatingPair`, Lancaster–Rodman); everything downstream is
verified:

* `intertwine` (`F∞Z = ZE₋`) and `sylv` (`eq:sylv`) from the raw
  deflating rows and `id1`/`id2`;
* the **link** `𝒢∞Z = X₋` and `eq:link` — by Sylvester uniqueness,
  no series;
* the Lagrangian property (`X₋ᵀY₋` symmetric) and the reverse-time
  **energy certificate** `−X₋ᵀY₋ ⪰ 0` (`eq:energy`) — both again by
  Sylvester uniqueness against `eq:perstep`;
* the **info-fix** `𝒢∞Σ∞|ₐ = eₐ` (`eq:info-fix`) — the necessity
  lever: an uninformed antistable prior direction kills `M∞`
  (`sysinterp_singular`).

The `⊆`-side (`kernel_sub`, `transversal`, `sysinterp_nonsingular`)
follows in the second half of the file.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-! ### Frame helpers -/

/-- The innovation weight `H_C = CᵀR⁻¹C` is symmetric. -/
lemma HC_transpose : (S.fullCᵀ * S.R⁻¹ * S.fullC)ᵀ
    = S.fullCᵀ * S.R⁻¹ * S.fullC := by
  have hRinv : (S.R⁻¹)ᵀ = S.R⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, S.hR.1.transpose_eq_self]
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hRinv]
  simp only [Matrix.mul_assoc]

/-- `H_C` is PSD. -/
lemma HC_posSemidef : (S.fullCᵀ * S.R⁻¹ * S.fullC).PosSemidef := by
  have h := S.hR.inv.posSemidef.conjTranspose_mul_mul_same S.fullC
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The gain–weight identity `K∞C = Σ∞Ω`. -/
lemma kGainC_eq_innovWeight :
    kGain S.fullC S.R Sinf * S.fullC
      = Sinf * S.innovWeight Sinf := by
  unfold kGain innovWeight
  simp only [Matrix.mul_assoc]

/-- `F∞ᵀ = (I − ΩΣ∞)Aᵀ` — the transposed shear form of the loop. -/
lemma errMap_transpose_shear (hSpsd : Sinf.PosSemidef) :
    (errMap S.fullC S.R S.fullA Sinf)ᵀ
      = (1 - S.innovWeight Sinf * Sinf) * S.fullAᵀ := by
  have h1 : errMap S.fullC S.R S.fullA Sinf
      = S.fullA * (1 - Sinf * S.innovWeight Sinf) := by
    unfold errMap
    rw [S.kGainC_eq_innovWeight]
  rw [h1, Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_mul,
    S.innovWeight_transpose hSpsd, hSpsd.1.transpose_eq_self]

/-- `id1` transposed: `Aᵀ = (I + H_CΣ∞)F∞ᵀ`. -/
lemma strong_id1_transpose (hSpsd : Sinf.PosSemidef) :
    S.fullAᵀ = (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf)
      * (errMap S.fullC S.R S.fullA Sinf)ᵀ := by
  have h := congrArg Matrix.transpose (S.strong_id1 hSpsd)
  rw [Matrix.transpose_mul, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_mul,
    S.HC_transpose, hSpsd.1.transpose_eq_self] at h
  exact h.symm

/-- The `Σ∞`-shear is nonsingular. -/
lemma shear_unit (hSpsd : Sinf.PosSemidef) :
    IsUnit (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf).det := by
  have hRdet : IsUnit S.R.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp S.hR.isUnit
  have hSt : (innov S.fullC S.R Sinf).PosDef :=
    innov_posDef S.hR hSpsd
  have h1 : (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf).det
      = (1 + S.R⁻¹ * S.fullC * Sinf * S.fullCᵀ).det := by
    have h2 := Matrix.det_one_add_mul_comm S.fullCᵀ
      (S.R⁻¹ * S.fullC * Sinf)
    simp only [Matrix.mul_assoc] at h2 ⊢
    exact h2
  have h3 : (1 : Matrix (Fin p) (Fin p) ℝ)
      + S.R⁻¹ * S.fullC * Sinf * S.fullCᵀ
      = S.R⁻¹ * innov S.fullC S.R Sinf := by
    unfold innov
    rw [Matrix.mul_add, ← Matrix.nonsing_inv_mul S.R hRdet]
    simp only [Matrix.mul_assoc]
    abel
  rw [h1, h3, Matrix.det_mul]
  exact (S.hR.inv.isUnit.map Matrix.detMonoidHom).mul
    ((Matrix.isUnit_iff_isUnit_det _).mp hSt.isUnit)

/-! ### The imported deflating pair -/

/-- **The antistable deflating pair** of the filter pencil
(`eq:deflate`, `eq:deflate-rows`, `eq:frame`) — the one imported
object of `lem:sysinterp` (complementary deflating subspaces of a
regular pencil with split spectrum; Lancaster–Rodman 1995). -/
structure DeflatingPair (S : DareSystem n₁ na nm m p)
    (Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ)
    (κq : Type*) [Fintype κq] [DecidableEq κq] : Type _ where
  /-- The upper block of the basis. -/
  Xm : Matrix (ix n₁ na nm) κq ℝ
  /-- The lower block of the basis. -/
  Ym : Matrix (ix n₁ na nm) κq ℝ
  /-- The reflected block. -/
  Em : Matrix κq κq ℝ
  /-- The reflected block is Schur. -/
  schur : IsSchurStable Em
  /-- Row (i) of `eq:deflate-rows`. -/
  row1 : Xm + S.fullCᵀ * S.R⁻¹ * S.fullC * Ym
    = S.fullAᵀ * Xm * Em
  /-- Row (ii) of `eq:deflate-rows`. -/
  row2 : S.fullA * Ym = Ym * Em - S.Qw * (Xm * Em)
  /-- The frame `eq:frame` spans: every prior-plane vector splits. -/
  surj : ∀ v : ix n₁ na nm → ℝ, ∃ α β, v = α + Xm *ᵥ β
    ∧ S.Sig0 *ᵥ v = Sinf *ᵥ α + Ym *ᵥ β

namespace DeflatingPair

variable {S} {κq : Type*} [Fintype κq] [DecidableEq κq]
variable (dp : S.DeflatingPair Sinf κq)

lemma Ym_mul_Em : dp.Ym * dp.Em
    = S.fullA * dp.Ym + S.Qw * (dp.Xm * dp.Em) := by
  have h := dp.row2
  rw [eq_sub_iff_add_eq] at h
  exact h.symm

lemma At_mul_XmEm : S.fullAᵀ * (dp.Xm * dp.Em)
    = dp.Xm + S.fullCᵀ * S.R⁻¹ * S.fullC * dp.Ym := by
  have h := dp.row1
  rw [Matrix.mul_assoc S.fullAᵀ dp.Xm dp.Em] at h
  exact h.symm

/-- **The intertwining** `F∞·Z = Z·E₋`, `Z := Σ∞X₋ − Y₋`
(the lower conjugated row). -/
lemma intertwine (hS : S.IsStrongSolution Sinf) :
    errMap S.fullC S.R S.fullA Sinf * (Sinf * dp.Xm - dp.Ym)
      = (Sinf * dp.Xm - dp.Ym) * dp.Em := by
  have hid2 := S.strong_id2 hS
  have hid1 := S.strong_id1 hS.posSemidef
  have hAY : S.fullA * dp.Ym
      = errMap S.fullC S.R S.fullA Sinf * dp.Ym
        + errMap S.fullC S.R S.fullA Sinf
          * (Sinf * (S.fullCᵀ * S.R⁻¹ * S.fullC * dp.Ym)) := by
    conv_lhs => rw [← hid1]
    rw [Matrix.mul_assoc, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_add]
    simp only [Matrix.mul_assoc]
  have h2 : Sinf * (dp.Xm * dp.Em) - S.Qw * (dp.Xm * dp.Em)
      = errMap S.fullC S.R S.fullA Sinf
        * (Sinf * (S.fullAᵀ * (dp.Xm * dp.Em))) := by
    rw [← Matrix.sub_mul, hid2]
    simp only [Matrix.mul_assoc]
  calc errMap S.fullC S.R S.fullA Sinf * (Sinf * dp.Xm - dp.Ym)
      = errMap S.fullC S.R S.fullA Sinf * (Sinf * dp.Xm)
        - errMap S.fullC S.R S.fullA Sinf * dp.Ym := by
        rw [Matrix.mul_sub]
  _ = errMap S.fullC S.R S.fullA Sinf
        * (Sinf * (dp.Xm
          + S.fullCᵀ * S.R⁻¹ * S.fullC * dp.Ym))
      - S.fullA * dp.Ym := by
      rw [hAY, Matrix.mul_add, Matrix.mul_add]
      simp only [Matrix.mul_assoc]
      abel
  _ = errMap S.fullC S.R S.fullA Sinf
        * (Sinf * (S.fullAᵀ * (dp.Xm * dp.Em)))
      - S.fullA * dp.Ym := by
      rw [dp.At_mul_XmEm]
  _ = Sinf * (dp.Xm * dp.Em) - S.Qw * (dp.Xm * dp.Em)
      - S.fullA * dp.Ym := by
      rw [h2]
  _ = (Sinf * dp.Xm - dp.Ym) * dp.Em := by
      rw [Matrix.sub_mul, dp.Ym_mul_Em]
      simp only [Matrix.mul_assoc]
      abel

/-- **`eq:sylv`**: `X₋ = F∞ᵀ·X₋·E₋ + Ω·Z` (the upper conjugated
row, the shear cancelled). -/
lemma sylv (hS : S.IsStrongSolution Sinf) :
    dp.Xm = (errMap S.fullC S.R S.fullA Sinf)ᵀ * dp.Xm * dp.Em
      + S.innovWeight Sinf * (Sinf * dp.Xm - dp.Ym) := by
  have hshear := S.shear_mul_innovWeight hS.posSemidef
  have hsunit := S.shear_unit hS.posSemidef
  -- multiply the claim by the nonsingular shear
  have hmul : (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf)
      * ((errMap S.fullC S.R S.fullA Sinf)ᵀ * dp.Xm * dp.Em
        + S.innovWeight Sinf * (Sinf * dp.Xm - dp.Ym))
      = (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf) * dp.Xm := by
    rw [Matrix.mul_add]
    have h1 : (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf)
        * ((errMap S.fullC S.R S.fullA Sinf)ᵀ * dp.Xm * dp.Em)
        = S.fullAᵀ * (dp.Xm * dp.Em) := by
      rw [S.strong_id1_transpose hS.posSemidef]
      simp only [Matrix.mul_assoc]
    have h2 : (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf)
        * (S.innovWeight Sinf * (Sinf * dp.Xm - dp.Ym))
        = S.fullCᵀ * S.R⁻¹ * S.fullC
          * (Sinf * dp.Xm - dp.Ym) := by
      rw [← Matrix.mul_assoc, hshear]
    rw [h1, h2, dp.At_mul_XmEm, Matrix.mul_sub, Matrix.add_mul,
      Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    abel
  have hcancel := congrArg
    (fun M => (1 + S.fullCᵀ * S.R⁻¹ * S.fullC * Sinf)⁻¹ * M) hmul
  dsimp only at hcancel
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hsunit,
    Matrix.one_mul, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hsunit, Matrix.one_mul] at hcancel
  exact hcancel.symm

/-- **The link** `𝒢∞·Z = X₋` — both sides solve the same Sylvester
equation with Schur factors, so they coincide. -/
lemma link (hS : S.IsStrongSolution Sinf)
    (hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf))
    {Ginf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hG : Ginf = (errMap S.fullC S.R S.fullA Sinf)ᵀ * Ginf
      * errMap S.fullC S.R S.fullA Sinf + S.innovWeight Sinf) :
    Ginf * (Sinf * dp.Xm - dp.Ym) = dp.Xm := by
  refine sylvester_unique (d := S.innovWeight Sinf
    * (Sinf * dp.Xm - dp.Ym)) hFs.transpose dp.schur ?_ ?_
  · conv_lhs => rw [hG]
    rw [Matrix.add_mul]
    have h1 : (errMap S.fullC S.R S.fullA Sinf)ᵀ * Ginf
        * errMap S.fullC S.R S.fullA Sinf
        * (Sinf * dp.Xm - dp.Ym)
        = (errMap S.fullC S.R S.fullA Sinf)ᵀ
          * (Ginf * (Sinf * dp.Xm - dp.Ym)) * dp.Em := by
      rw [Matrix.mul_assoc ((errMap S.fullC S.R S.fullA Sinf)ᵀ
          * Ginf) (errMap S.fullC S.R S.fullA Sinf) _,
        dp.intertwine hS]
      simp only [Matrix.mul_assoc]
    rw [h1]
  · exact dp.sylv hS

/-- **`eq:link`**: `M∞·X₋ = 𝒢∞·(Σ₀X₋ − Y₋)`. -/
lemma link_M (hS : S.IsStrongSolution Sinf)
    (hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf))
    {Ginf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hG : Ginf = (errMap S.fullC S.R S.fullA Sinf)ᵀ * Ginf
      * errMap S.fullC S.R S.fullA Sinf + S.innovWeight Sinf) :
    (1 + Ginf * (S.Sig0 - Sinf)) * dp.Xm
      = Ginf * (S.Sig0 * dp.Xm - dp.Ym) := by
  have hlink := dp.link hS hFs hG
  have h1 : Ginf * (S.Sig0 * dp.Xm - dp.Ym)
      = Ginf * (S.Sig0 * dp.Xm)
        - Ginf * (Sinf * dp.Xm) + Ginf * (Sinf * dp.Xm - dp.Ym) := by
    rw [Matrix.mul_sub, Matrix.mul_sub]
    abel
  rw [h1, hlink, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  abel

/-- **`eq:perstep`**: the per-step drop of the reverse-time energy is
the innovation and process energies. -/
lemma perstep :
    dp.Emᵀ * (dp.Xmᵀ * dp.Ym) * dp.Em
      = dp.Xmᵀ * dp.Ym
        + (dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
          + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em)) := by
  have h1 : dp.Emᵀ * (dp.Xmᵀ * dp.Ym) * dp.Em
      = (dp.Xm * dp.Em)ᵀ * (dp.Ym * dp.Em) := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, dp.Ym_mul_Em, Matrix.mul_add]
  have h2 : (dp.Xm * dp.Em)ᵀ * S.fullA * dp.Ym
      = dp.Xmᵀ * dp.Ym
        + dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym := by
    have h3 : (dp.Xm * dp.Em)ᵀ * S.fullA
        = (dp.Xm + S.fullCᵀ * S.R⁻¹ * S.fullC * dp.Ym)ᵀ := by
      have h4 := congrArg Matrix.transpose (dp.At_mul_XmEm)
      rw [Matrix.transpose_mul, Matrix.transpose_transpose] at h4
      exact h4
    rw [h3, Matrix.transpose_add, Matrix.transpose_mul,
      S.HC_transpose, Matrix.add_mul]
  rw [← Matrix.mul_assoc ((dp.Xm * dp.Em)ᵀ) S.fullA dp.Ym, h2]
  simp only [Matrix.mul_assoc]
  abel

/-- The per-step energy `Π` is PSD. -/
lemma perstep_posSemidef :
    (dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
      + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em)).PosSemidef := by
  have h1 := S.HC_posSemidef.conjTranspose_mul_mul_same dp.Ym
  have h2 := S.Qw_posSemidef.conjTranspose_mul_mul_same
    (dp.Xm * dp.Em)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact h1.add h2

/-- The Lagrangian property: `X₋ᵀY₋` is symmetric (`K = E₋ᵀKE₋`
against a Schur `E₋`). -/
lemma lagrangian : (dp.Xmᵀ * dp.Ym)ᵀ = dp.Xmᵀ * dp.Ym := by
  have hPisym : (dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
      + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em))ᵀ
      = dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
        + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em) :=
    dp.perstep_posSemidef.1.transpose_eq_self
  have hK : dp.Xmᵀ * dp.Ym - (dp.Xmᵀ * dp.Ym)ᵀ
      = dp.Emᵀ * (dp.Xmᵀ * dp.Ym - (dp.Xmᵀ * dp.Ym)ᵀ) * dp.Em
        + 0 := by
    have h1 := dp.perstep
    have h2 : dp.Emᵀ * (dp.Xmᵀ * dp.Ym)ᵀ * dp.Em
        = (dp.Xmᵀ * dp.Ym)ᵀ
          + (dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
            + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em)) := by
      have h5 := congrArg Matrix.transpose h1
      rw [Matrix.transpose_add, hPisym, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.mul_assoc] at h5
      exact h5
    rw [add_zero, Matrix.mul_sub, Matrix.sub_mul, h1, h2]
    abel
  have h0 : (0 : Matrix κq κq ℝ)
      = dp.Emᵀ * (0 : Matrix κq κq ℝ) * dp.Em + 0 := by simp
  have := sylvester_unique (d := (0 : Matrix κq κq ℝ))
    dp.schur.transpose dp.schur hK h0
  rw [← sub_eq_zero]
  rw [← neg_sub (dp.Xmᵀ * dp.Ym) ((dp.Xmᵀ * dp.Ym)ᵀ), this,
    neg_zero]

/-- The reverse-time energy is a Sylvester fixed point of the
per-step drop. -/
lemma energy_fix : -(dp.Xmᵀ * dp.Ym)
    = dp.Emᵀ * (-(dp.Xmᵀ * dp.Ym)) * dp.Em
      + (dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
        + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em)) := by
  have h1 := dp.perstep
  rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [h1]
  abel

/-- **`eq:energy`**: the reverse-time energy certificate
`−X₋ᵀY₋ ⪰ 0`. -/
lemma energy_posSemidef : (-(dp.Xmᵀ * dp.Ym)).PosSemidef := by
  have hPi := dp.perstep_posSemidef
  have hfix := dp.energy_fix
  obtain ⟨N', hN'fix, hN'tend⟩ := sylvester_exists dp.Emᵀ dp.Em
    (dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
      + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em))
    dp.schur.transpose dp.schur
  have hEqN : -(dp.Xmᵀ * dp.Ym) = N' :=
    sylvester_unique dp.schur.transpose dp.schur hfix hN'fix
  rw [hEqN]
  refine posSemidef_of_tendsto (M := fun N => sylvIter dp.Emᵀ dp.Em
    (dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
      + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em)) N)
    ?_ hN'tend
  intro n
  induction n with
  | zero => exact Matrix.PosSemidef.zero
  | succ n ih =>
    show (dp.Emᵀ * sylvIter _ _ _ n * dp.Em + _).PosSemidef
    refine Matrix.PosSemidef.add ?_ hPi
    have h := ih.conjTranspose_mul_mul_same dp.Em
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

set_option maxHeartbeats 3200000 in
/-- **The kernel inclusion (`⊆`, `eq:kernel-id`)**: a kernel
direction of the criterion object is an uninformed prior direction
supported off `e₁` — the reverse-time energy dies along the whole
reflected orbit, and the stabilizing output injection (the verified
replacement for the deck's invariant-subspace split) collapses the
backward `e₁`-orbit. -/
lemma kernel_sub (_hS : S.IsStrongSolution Sinf) {u : κq → ℝ}
    (hu : (S.Sig0 * dp.Xm - dp.Ym) *ᵥ u = 0) :
    S.Sig0 *ᵥ (dp.Xm *ᵥ u) = 0
      ∧ (emb1 n₁ na nm)ᵀ *ᵥ (dp.Xm *ᵥ u) = 0 := by
  classical
  -- the pairing: prior energy + reverse-time energy vanish together
  have hdot : quadForm S.Sig0 (dp.Xm *ᵥ u)
      + quadForm (-(dp.Xmᵀ * dp.Ym)) u = 0 := by
    have h1 : quadForm (-(dp.Xmᵀ * dp.Ym)) u
        = -((dp.Xm *ᵥ u) ⬝ᵥ (dp.Ym *ᵥ u)) := by
      unfold quadForm
      rw [Matrix.neg_mulVec, dotProduct_neg, neg_inj,
        ← Matrix.mulVec_mulVec]
      rw [← mulVec_dotProduct_eq]
    have h2 : quadForm S.Sig0 (dp.Xm *ᵥ u)
        = (dp.Xm *ᵥ u) ⬝ᵥ ((S.Sig0 * dp.Xm) *ᵥ u) := by
      unfold quadForm
      rw [Matrix.mulVec_mulVec]
    rw [h1, h2]
    have h3 : (dp.Xm *ᵥ u) ⬝ᵥ ((S.Sig0 * dp.Xm) *ᵥ u)
        - (dp.Xm *ᵥ u) ⬝ᵥ (dp.Ym *ᵥ u)
        = (dp.Xm *ᵥ u) ⬝ᵥ ((S.Sig0 * dp.Xm - dp.Ym) *ᵥ u) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
    have h4 := h3
    rw [hu, dotProduct_zero] at h4
    linarith [h4]
  have hq1 := S.Sig0_posSemidef.quadForm_nonneg (dp.Xm *ᵥ u)
  have hq2 := dp.energy_posSemidef.quadForm_nonneg u
  have hqSig : quadForm S.Sig0 (dp.Xm *ᵥ u) = 0 := by linarith
  have hqN : quadForm (-(dp.Xmᵀ * dp.Ym)) u = 0 := by linarith
  have hSig0X : S.Sig0 *ᵥ (dp.Xm *ᵥ u) = 0 :=
    S.Sig0_posSemidef.mulVec_eq_zero_of_quadForm_eq_zero hqSig
  refine ⟨hSig0X, ?_⟩
  -- the criterion kernel kills `Y₋u`
  have hYu : dp.Ym *ᵥ u = 0 := by
    have h5 : (S.Sig0 * dp.Xm) *ᵥ u - dp.Ym *ᵥ u = 0 := by
      rw [← Matrix.sub_mulVec, hu]
    rw [Matrix.mulVec_mulVec] at hSig0X
    rw [hSig0X, zero_sub, neg_eq_zero] at h5
    exact h5
  -- the reverse-time energy dies along the reflected orbit
  have hqstep : ∀ x : κq → ℝ,
      quadForm (-(dp.Xmᵀ * dp.Ym)) x
        = quadForm (-(dp.Xmᵀ * dp.Ym)) (dp.Em *ᵥ x)
          + quadForm (dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
            + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em)) x := by
    intro x
    conv_lhs => rw [dp.energy_fix]
    rw [quadForm_add_matrix]
    congr 1
    rw [quadForm_mulVec]
  have hPipsd := dp.perstep_posSemidef
  have hNpsd := dp.energy_posSemidef
  have horbN : ∀ k : ℕ,
      quadForm (-(dp.Xmᵀ * dp.Ym)) (dp.Em ^ k *ᵥ u) = 0 := by
    intro k
    induction k with
    | zero => simpa using hqN
    | succ k ih =>
      have h := hqstep (dp.Em ^ k *ᵥ u)
      rw [ih] at h
      have hEk : dp.Em *ᵥ (dp.Em ^ k *ᵥ u)
          = dp.Em ^ (k + 1) *ᵥ u := by
        rw [Matrix.mulVec_mulVec, ← pow_succ']
      rw [hEk] at h
      have h1 := hNpsd.quadForm_nonneg (dp.Em ^ (k + 1) *ᵥ u)
      have h2 := hPipsd.quadForm_nonneg (dp.Em ^ k *ᵥ u)
      linarith
  have horbPi : ∀ k : ℕ,
      quadForm (dp.Ymᵀ * (S.fullCᵀ * S.R⁻¹ * S.fullC) * dp.Ym
        + (dp.Xm * dp.Em)ᵀ * S.Qw * (dp.Xm * dp.Em))
        (dp.Em ^ k *ᵥ u) = 0 := by
    intro k
    have h := hqstep (dp.Em ^ k *ᵥ u)
    rw [horbN k] at h
    have hEk : dp.Em *ᵥ (dp.Em ^ k *ᵥ u)
        = dp.Em ^ (k + 1) *ᵥ u := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hEk, horbN (k + 1)] at h
    linarith
  -- the process-noise kill along the orbit
  have hGkill : ∀ k : ℕ,
      S.fullGᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ (k + 1) *ᵥ u)) = 0 := by
    intro k
    have h := horbPi k
    rw [quadForm_add_matrix] at h
    have h1 := (S.HC_posSemidef.conjTranspose_mul_mul_same
      dp.Ym)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    have h2 := (S.Qw_posSemidef.conjTranspose_mul_mul_same
      (dp.Xm * dp.Em))
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
    have h3 := h1.quadForm_nonneg (dp.Em ^ k *ᵥ u)
    have h4 := h2.quadForm_nonneg (dp.Em ^ k *ᵥ u)
    have hQwq : quadForm ((dp.Xm * dp.Em)ᵀ * S.Qw
        * (dp.Xm * dp.Em)) (dp.Em ^ k *ᵥ u) = 0 := by
      linarith
    have h5 : quadForm S.Qw
        ((dp.Xm * dp.Em) *ᵥ (dp.Em ^ k *ᵥ u)) = 0 := by
      rw [quadForm_mulVec]
      exact hQwq
    have h6 : quadForm S.Q (S.fullGᵀ
        *ᵥ ((dp.Xm * dp.Em) *ᵥ (dp.Em ^ k *ᵥ u))) = 0 := by
      have h7 := quadForm_mulVec S.Q (S.fullGᵀ)
        ((dp.Xm * dp.Em) *ᵥ (dp.Em ^ k *ᵥ u))
      rw [Matrix.transpose_transpose] at h7
      rw [h7]
      show quadForm S.Qw _ = 0
      exact h5
    have h8 := eq_zero_of_quadForm_eq_zero_of_posDef S.hQ h6
    have hXE : (dp.Xm * dp.Em) *ᵥ (dp.Em ^ k *ᵥ u)
        = dp.Xm *ᵥ (dp.Em ^ (k + 1) *ᵥ u) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc, ← pow_succ']
    rwa [hXE] at h8
  have hQwkill : ∀ k : ℕ,
      S.Qw *ᵥ (dp.Xm *ᵥ (dp.Em ^ (k + 1) *ᵥ u)) = 0 := by
    intro k
    show (S.fullG * S.Q * S.fullGᵀ) *ᵥ _ = 0
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hGkill k, Matrix.mulVec_zero, Matrix.mulVec_zero]
  -- the lower orbit vanishes
  have hqorb : ∀ k : ℕ, dp.Ym *ᵥ (dp.Em ^ k *ᵥ u) = 0 := by
    intro k
    induction k with
    | zero => simpa using hYu
    | succ k ih =>
      have h := congrArg (fun M => M *ᵥ (dp.Em ^ k *ᵥ u)) dp.row2
      dsimp only at h
      rw [Matrix.sub_mulVec] at h
      have h1 : (S.fullA * dp.Ym) *ᵥ (dp.Em ^ k *ᵥ u) = 0 := by
        rw [← Matrix.mulVec_mulVec, ih, Matrix.mulVec_zero]
      have h2 : (S.Qw * (dp.Xm * dp.Em)) *ᵥ (dp.Em ^ k *ᵥ u)
          = 0 := by
        rw [← Matrix.mulVec_mulVec]
        have hXE : (dp.Xm * dp.Em) *ᵥ (dp.Em ^ k *ᵥ u)
            = dp.Xm *ᵥ (dp.Em ^ (k + 1) *ᵥ u) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            Matrix.mul_assoc, ← pow_succ']
        rw [hXE]
        exact hQwkill k
      rw [h1, h2, sub_zero] at h
      have h3 : (dp.Ym * dp.Em) *ᵥ (dp.Em ^ k *ᵥ u)
          = dp.Ym *ᵥ (dp.Em ^ (k + 1) *ᵥ u) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          Matrix.mul_assoc, ← pow_succ']
      rw [h3] at h
      exact h.symm
  -- the backward `e₁`-orbit and the stabilizing injection
  have hprec : ∀ k : ℕ, dp.Xm *ᵥ (dp.Em ^ k *ᵥ u)
      = S.fullAᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ (k + 1) *ᵥ u)) := by
    intro k
    have h := congrArg (fun M => M *ᵥ (dp.Em ^ k *ᵥ u)) dp.row1
    dsimp only at h
    rw [Matrix.add_mulVec] at h
    have h1 : (S.fullCᵀ * S.R⁻¹ * S.fullC * dp.Ym)
        *ᵥ (dp.Em ^ k *ᵥ u) = 0 := by
      rw [← Matrix.mulVec_mulVec, hqorb k, Matrix.mulVec_zero]
    rw [h1, add_zero] at h
    have h2 : (S.fullAᵀ * dp.Xm * dp.Em) *ᵥ (dp.Em ^ k *ᵥ u)
        = S.fullAᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ (k + 1) *ᵥ u)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
        ← pow_succ']
      simp only [Matrix.mul_assoc]
    rw [h2] at h
    exact h
  have harec : ∀ k : ℕ,
      (emb1 n₁ na nm)ᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ k *ᵥ u))
      = S.A₁ᵀ *ᵥ ((emb1 n₁ na nm)ᵀ
        *ᵥ (dp.Xm *ᵥ (dp.Em ^ (k + 1) *ᵥ u))) := by
    intro k
    have h1 : (emb1 n₁ na nm)ᵀ * S.fullAᵀ
        = S.A₁ᵀ * (emb1 n₁ na nm)ᵀ := by
      have h := congrArg Matrix.transpose S.fullA_mul_emb1
      rwa [Matrix.transpose_mul, Matrix.transpose_mul] at h
    rw [hprec k, Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
  have hGa : ∀ k : ℕ, S.G₁ᵀ *ᵥ ((emb1 n₁ na nm)ᵀ
      *ᵥ (dp.Xm *ᵥ (dp.Em ^ (k + 1) *ᵥ u))) = 0 := by
    intro k
    have h1 : S.fullGᵀ = S.G₁ᵀ * (emb1 n₁ na nm)ᵀ := by
      have h := congrArg Matrix.transpose S.fullG_eq
      rwa [Matrix.transpose_mul] at h
    rw [Matrix.mulVec_mulVec, ← h1]
    exact hGkill k
  obtain ⟨L, hL⟩ := detect_inj S.A₁ᵀ S.G₁ᵀ S.hStab
  have haL : ∀ k : ℕ,
      (emb1 n₁ na nm)ᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ k *ᵥ u))
      = (S.A₁ᵀ - L * S.G₁ᵀ)
        *ᵥ ((emb1 n₁ na nm)ᵀ
          *ᵥ (dp.Xm *ᵥ (dp.Em ^ (k + 1) *ᵥ u))) := by
    intro k
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hGa k,
      Matrix.mulVec_zero, sub_zero]
    exact harec k
  have hiter : ∀ mIt : ℕ,
      (emb1 n₁ na nm)ᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ 0 *ᵥ u))
      = ((S.A₁ᵀ - L * S.G₁ᵀ) ^ mIt)
        *ᵥ ((emb1 n₁ na nm)ᵀ
          *ᵥ (dp.Xm *ᵥ (dp.Em ^ mIt *ᵥ u))) := by
    intro mIt
    induction mIt with
    | zero => simp
    | succ mIt ih =>
      rw [ih, haL mIt, Matrix.mulVec_mulVec, ← pow_succ]
  -- the orbit is bounded, the injection contracts, so `a₀ = 0`
  obtain ⟨cE, γE, hcE, hγE0, hγE1, hEp⟩ :=
    dp.schur.exists_pow_norm_le
  obtain ⟨cL', γL', hcL', hγL0, hγL1, hLp⟩ := hL.exists_pow_norm_le
  have habnd : ∀ k : ℕ,
      ‖(emb1 n₁ na nm)ᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ k *ᵥ u))‖
      ≤ ‖(emb1 n₁ na nm)ᵀ‖ * (‖dp.Xm‖ * (cE * ‖u‖)) := by
    intro k
    calc ‖(emb1 n₁ na nm)ᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ k *ᵥ u))‖
        ≤ ‖(emb1 n₁ na nm)ᵀ‖ * ‖dp.Xm *ᵥ (dp.Em ^ k *ᵥ u)‖ :=
          Matrix.linfty_opNorm_mulVec _ _
    _ ≤ ‖(emb1 n₁ na nm)ᵀ‖ * (‖dp.Xm‖ * ‖dp.Em ^ k *ᵥ u‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine le_trans (Matrix.linfty_opNorm_mulVec _ _) ?_
        exact le_rfl
    _ ≤ ‖(emb1 n₁ na nm)ᵀ‖ * (‖dp.Xm‖ * (cE * ‖u‖)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          (norm_nonneg _)
        calc ‖dp.Em ^ k *ᵥ u‖
            ≤ ‖dp.Em ^ k‖ * ‖u‖ := Matrix.linfty_opNorm_mulVec _ _
        _ ≤ cE * γE ^ k * ‖u‖ := by
            exact mul_le_mul_of_nonneg_right (hEp k) (norm_nonneg _)
        _ ≤ cE * ‖u‖ := by
            have h1 : γE ^ k ≤ 1 := pow_le_one₀ hγE0.le hγE1.le
            nlinarith [norm_nonneg u, hcE.le,
              mul_nonneg hcE.le (norm_nonneg u)]
  have hlim : Tendsto (fun mIt : ℕ =>
      (cL' * γL' ^ mIt)
        * (‖(emb1 n₁ na nm)ᵀ‖ * (‖dp.Xm‖ * (cE * ‖u‖))))
      atTop (nhds 0) := by
    have h1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one hγL0.le
      hγL1).const_mul cL').mul_const
      (‖(emb1 n₁ na nm)ᵀ‖ * (‖dp.Xm‖ * (cE * ‖u‖)))
    simpa using h1
  have hb : ∀ mIt : ℕ,
      ‖(emb1 n₁ na nm)ᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ 0 *ᵥ u))‖
      ≤ (cL' * γL' ^ mIt)
        * (‖(emb1 n₁ na nm)ᵀ‖ * (‖dp.Xm‖ * (cE * ‖u‖))) := by
    intro mIt
    rw [hiter mIt]
    calc ‖((S.A₁ᵀ - L * S.G₁ᵀ) ^ mIt)
        *ᵥ ((emb1 n₁ na nm)ᵀ
          *ᵥ (dp.Xm *ᵥ (dp.Em ^ mIt *ᵥ u)))‖
        ≤ ‖(S.A₁ᵀ - L * S.G₁ᵀ) ^ mIt‖
          * ‖(emb1 n₁ na nm)ᵀ
              *ᵥ (dp.Xm *ᵥ (dp.Em ^ mIt *ᵥ u))‖ :=
          Matrix.linfty_opNorm_mulVec _ _
    _ ≤ (cL' * γL' ^ mIt)
          * (‖(emb1 n₁ na nm)ᵀ‖ * (‖dp.Xm‖ * (cE * ‖u‖))) := by
        refine mul_le_mul (hLp mIt) (habnd mIt) (norm_nonneg _) ?_
        positivity
  have hle : ‖(emb1 n₁ na nm)ᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ 0 *ᵥ u))‖
      ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall hb)
  have h0 : (emb1 n₁ na nm)ᵀ *ᵥ (dp.Xm *ᵥ (dp.Em ^ 0 *ᵥ u)) = 0 := by
    rw [← norm_le_zero_iff]
    exact hle
  rw [pow_zero, Matrix.one_mulVec] at h0
  exact h0

/-- **Transversality**: a kernel vector of `M∞` lies on the deflating
subspace through a kernel vector of the criterion object. -/
lemma transversal (hS : S.IsStrongSolution Sinf)
    (hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf))
    {Ginf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hG : Ginf = (errMap S.fullC S.R S.fullA Sinf)ᵀ * Ginf
      * errMap S.fullC S.R S.fullA Sinf + S.innovWeight Sinf)
    {v : ix n₁ na nm → ℝ}
    (hv : (1 + Ginf * (S.Sig0 - Sinf)) *ᵥ v = 0) :
    ∃ β, (S.Sig0 * dp.Xm - dp.Ym) *ᵥ β = 0 ∧ v = dp.Xm *ᵥ β := by
  obtain ⟨α, β, hvαβ, hSv⟩ := dp.surj v
  have h1 : (S.Sig0 * dp.Xm - dp.Ym) *ᵥ β
      = -((S.Sig0 - Sinf) *ᵥ α) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    have h2 : dp.Ym *ᵥ β = S.Sig0 *ᵥ v - Sinf *ᵥ α := by
      rw [hSv]
      abel
    have h3 : dp.Xm *ᵥ β = v - α := by
      rw [hvαβ]
      abel
    rw [h2, h3, Matrix.mulVec_sub]
    abel
  -- push through `eq:link` and use `M∞v = 0`
  have hlinkv := congrArg (fun M => M *ᵥ β) (dp.link_M hS hFs hG)
  dsimp only at hlinkv
  -- `M∞·(Xmβ) = 𝒢∞·((Σ₀Xm − Ym)β) = −𝒢∞·D·α`
  have h4 : (1 + Ginf * (S.Sig0 - Sinf)) *ᵥ (dp.Xm *ᵥ β)
      = -(Ginf *ᵥ ((S.Sig0 - Sinf) *ᵥ α)) := by
    rw [Matrix.mulVec_mulVec, hlinkv, ← Matrix.mulVec_mulVec, h1,
      Matrix.mulVec_neg]
  -- `M∞·(Xmβ) = M∞·(v − α) = −M∞·α`
  have h5 : (1 + Ginf * (S.Sig0 - Sinf)) *ᵥ (dp.Xm *ᵥ β)
      = -((1 + Ginf * (S.Sig0 - Sinf)) *ᵥ α) := by
    have h6 : dp.Xm *ᵥ β = v - α := by
      rw [hvαβ]
      abel
    rw [h6, Matrix.mulVec_sub, hv, zero_sub]
  -- hence `α = 0`
  have hα : α = 0 := by
    have h7 : (1 + Ginf * (S.Sig0 - Sinf)) *ᵥ α
        = Ginf *ᵥ ((S.Sig0 - Sinf) *ᵥ α) := by
      have h8 := h4.symm.trans h5
      have h9 := congrArg Neg.neg h8
      rw [neg_neg, neg_neg] at h9
      exact h9.symm
    rw [Matrix.add_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec] at h7
    have h10 : α + Ginf *ᵥ ((S.Sig0 - Sinf) *ᵥ α)
        - Ginf *ᵥ ((S.Sig0 - Sinf) *ᵥ α) = 0 := by
      rw [h7]
      abel
    rw [add_sub_cancel_right] at h10
    exact h10
  refine ⟨β, ?_, ?_⟩
  · rw [h1, hα, Matrix.mulVec_zero, neg_zero]
  · rw [hvαβ, hα, zero_add]

end DeflatingPair

/-- The `e₁`-selector of a vector. -/
lemma emb1t_mulVec (v : ix n₁ na nm → ℝ) :
    (emb1 n₁ na nm)ᵀ *ᵥ v = fun i => v (Sum.inl i) := by
  funext i
  simp [emb1, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.one_apply]

/-- **`lem:sysinterp`, the criterion (`⊆`-side)**: under C2 the
limiting denominator is nonsingular. -/
theorem sysinterp_nonsingular {κq : Type*} [Fintype κq]
    [DecidableEq κq] (dp : S.DeflatingPair Sinf κq)
    (hS : S.IsStrongSolution Sinf)
    (hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf))
    {Ginf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hG : Ginf = (errMap S.fullC S.R S.fullA Sinf)ᵀ * Ginf
      * errMap S.fullC S.R S.fullA Sinf + S.innovWeight Sinf)
    (hC2 : S.C2) :
    IsUnit (1 + Ginf * (S.Sig0 - Sinf)).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hvne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨β, hβker, hβv⟩ := dp.transversal hS hFs hG hv0
  obtain ⟨hSig0v', he1'⟩ := dp.kernel_sub hS hβker
  rw [← hβv] at hSig0v' he1'
  rw [emb1t_mulVec] at he1'
  apply hvne
  have hv2 : v = Sum.elim (0 : Fin n₁ → ℝ)
      (fun j => v (Sum.inr j)) := by
    funext i
    rcases i with i₁ | i₂
    · have := congrFun he1' i₁
      simpa using this
    · rfl
  have h2 := hC2 (fun j => v (Sum.inr j)) (by rw [← hv2]; exact hSig0v')
  rw [hv2, h2]
  funext i
  rcases i with i₁ | i₂ <;> rfl



/-! ### The info-fix and the necessity direction (`eq:info-fix`) -/

/-- The strong solution rides `Aₐᵀ` backwards on the antistable
columns: `F∞·(Σ∞eₐ) = Σ∞eₐ·(Aₐᵀ)⁻¹`. -/
lemma strong_antistable_cols (hS : S.IsStrongSolution Sinf) :
    errMap S.fullC S.R S.fullA Sinf * (Sinf * embA n₁ na nm)
      = Sinf * embA n₁ na nm * (S.Aaᵀ)⁻¹ := by
  have hid2 := S.strong_id2 hS
  have hAadet : IsUnit S.Aaᵀ.det := by
    rw [Matrix.det_transpose]
    exact S.isUnit_Aa_det
  have hQwA : S.Qw * embA n₁ na nm = 0 := by
    unfold Qw
    have h1 : S.fullGᵀ * embA n₁ na nm = 0 := by
      have h := congrArg Matrix.transpose S.embA_transpose_mul_fullG
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_zero] at h
    rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  have hSigA : Sinf * embA n₁ na nm
      = errMap S.fullC S.R S.fullA Sinf
        * (Sinf * (embA n₁ na nm * S.Aaᵀ)) := by
    have h1 : Sinf = errMap S.fullC S.R S.fullA Sinf * Sinf
        * S.fullAᵀ + S.Qw := by
      rw [← hid2]
      abel
    calc Sinf * embA n₁ na nm
        = (errMap S.fullC S.R S.fullA Sinf * Sinf * S.fullAᵀ
            + S.Qw) * embA n₁ na nm := by rw [← h1]
    _ = errMap S.fullC S.R S.fullA Sinf * Sinf
          * (S.fullAᵀ * embA n₁ na nm) := by
        rw [Matrix.add_mul, hQwA, add_zero]
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [S.fullA_transpose_mul_embA]
        simp only [Matrix.mul_assoc]
  have h2 := congrArg (fun M => M * (S.Aaᵀ)⁻¹) hSigA
  dsimp only at h2
  rw [Matrix.mul_assoc (errMap S.fullC S.R S.fullA Sinf)
    (Sinf * (embA n₁ na nm * S.Aaᵀ)) ((S.Aaᵀ)⁻¹)] at h2
  have h3 : Sinf * (embA n₁ na nm * S.Aaᵀ) * (S.Aaᵀ)⁻¹
      = Sinf * embA n₁ na nm := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hAadet, Matrix.mul_one]
  rw [h3] at h2
  exact h2.symm

/-- The transposed shear on the antistable columns:
`F∞ᵀ·eₐ·(Aₐᵀ)⁻¹ = (I − ΩΣ∞)·eₐ`. -/
lemma errMapT_antistable_cols (hS : S.IsStrongSolution Sinf) :
    (errMap S.fullC S.R S.fullA Sinf)ᵀ * embA n₁ na nm * (S.Aaᵀ)⁻¹
      = (1 - S.innovWeight Sinf * Sinf) * embA n₁ na nm := by
  have hAadet : IsUnit S.Aaᵀ.det := by
    rw [Matrix.det_transpose]
    exact S.isUnit_Aa_det
  rw [S.errMap_transpose_shear hS.posSemidef,
    Matrix.mul_assoc _ S.fullAᵀ (embA n₁ na nm),
    S.fullA_transpose_mul_embA,
    Matrix.mul_assoc _ (embA n₁ na nm * S.Aaᵀ) ((S.Aaᵀ)⁻¹),
    Matrix.mul_assoc (embA n₁ na nm) S.Aaᵀ ((S.Aaᵀ)⁻¹),
    Matrix.mul_nonsing_inv _ hAadet, Matrix.mul_one]

/-- **`eq:info-fix`**: `𝒢∞·Σ∞·eₐ = eₐ` — the steady information
inverts the steady covariance on the antistable directions
(Sylvester uniqueness again). -/
theorem info_fix (hS : S.IsStrongSolution Sinf)
    (hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf))
    {Ginf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hG : Ginf = (errMap S.fullC S.R S.fullA Sinf)ᵀ * Ginf
      * errMap S.fullC S.R S.fullA Sinf + S.innovWeight Sinf) :
    Ginf * (Sinf * embA n₁ na nm) = embA n₁ na nm := by
  have hAaInvT : IsSchurStable ((S.Aaᵀ)⁻¹) := by
    have h := S.Aa_inv_isSchurStable.transpose
    rwa [Matrix.transpose_nonsing_inv] at h
  refine sylvester_unique (d := S.innovWeight Sinf
    * (Sinf * embA n₁ na nm)) hFs.transpose hAaInvT ?_ ?_
  · conv_lhs => rw [hG]
    rw [Matrix.add_mul]
    have h1 : (errMap S.fullC S.R S.fullA Sinf)ᵀ * Ginf
        * errMap S.fullC S.R S.fullA Sinf
        * (Sinf * embA n₁ na nm)
        = (errMap S.fullC S.R S.fullA Sinf)ᵀ
          * (Ginf * (Sinf * embA n₁ na nm)) * (S.Aaᵀ)⁻¹ := by
      rw [Matrix.mul_assoc ((errMap S.fullC S.R S.fullA Sinf)ᵀ
          * Ginf) (errMap S.fullC S.R S.fullA Sinf) _,
        S.strong_antistable_cols hS]
      simp only [Matrix.mul_assoc]
    rw [h1]
  · -- `eₐ = F∞ᵀ·eₐ·(Aₐᵀ)⁻¹ + ΩΣ∞·eₐ` by the transposed shear
    have h2 := S.errMapT_antistable_cols hS
    rw [Matrix.sub_mul, Matrix.one_mul] at h2
    rw [h2]
    simp only [Matrix.mul_assoc]
    abel

/-- **The necessity direction**: an uninformed antistable prior
direction kills the limiting denominator — `¬C2w` makes `M∞`
singular. -/
theorem sysinterp_singular (hS : S.IsStrongSolution Sinf)
    (hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf))
    {Ginf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hG : Ginf = (errMap S.fullC S.R S.fullA Sinf)ᵀ * Ginf
      * errMap S.fullC S.R S.fullA Sinf + S.innovWeight Sinf)
    (hnC2w : ¬ S.C2w) :
    ∃ v, v ≠ 0 ∧ (1 + Ginf * (S.Sig0 - Sinf)) *ᵥ v = 0 := by
  rw [C2w, not_forall] at hnC2w
  obtain ⟨w, hw⟩ := hnC2w
  rw [Classical.not_imp] at hw
  obtain ⟨hker, hwne⟩ := hw
  have hvA : embA n₁ na nm *ᵥ w
      = Sum.elim (0 : Fin n₁ → ℝ)
        (Sum.elim w (0 : Fin nm → ℝ)) := by
    funext i
    rcases i with i₁ | ia | im <;>
      simp [embA, Matrix.mulVec, dotProduct,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
        Matrix.one_apply]
  refine ⟨embA n₁ na nm *ᵥ w, ?_, ?_⟩
  · intro h0
    apply hwne
    funext j
    have h1 := congrFun h0 (Sum.inr (Sum.inl j))
    rw [hvA] at h1
    simpa using h1
  · have hSig0v : S.Sig0 *ᵥ (embA n₁ na nm *ᵥ w) = 0 := by
      rw [hvA]
      exact hker
    have hfix := S.info_fix hS hFs hG
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    have h2 : (Ginf * (S.Sig0 - Sinf)) *ᵥ (embA n₁ na nm *ᵥ w)
        = -(embA n₁ na nm *ᵥ w) := by
      calc (Ginf * (S.Sig0 - Sinf)) *ᵥ (embA n₁ na nm *ᵥ w)
          = Ginf *ᵥ ((S.Sig0 - Sinf) *ᵥ (embA n₁ na nm *ᵥ w)) := by
            rw [← Matrix.mulVec_mulVec]
      _ = Ginf *ᵥ (-(Sinf *ᵥ (embA n₁ na nm *ᵥ w))) := by
          rw [Matrix.sub_mulVec, hSig0v, zero_sub]
      _ = -((Ginf * (Sinf * embA n₁ na nm)) *ᵥ w) := by
          rw [Matrix.mulVec_neg]
          congr 1
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            Matrix.mul_assoc]
      _ = -(embA n₁ na nm *ᵥ w) := by rw [hfix]
    rw [h2, add_neg_cancel]

end DareSystem

end Dare
end Estimation

# Kalman and Riccati definitions — 9 items

Source at the pinned snapshot: `LeanForControl/Estimation/KalmanFilter.lean`.

## 1. `Qcov`

```lean
noncomputable def Qcov : Matrix (Fin m) (Fin m) ℝ := S.Qi⁻¹
```

**Rendered meaning.** Recover the process covariance Q by inverting the positive-definite penalty Q⁻¹.

**Paper counterpart.** The process noise has covariance Q > 0, while the optimization uses Q⁻¹.

## 2. `Rcov`

```lean
noncomputable def Rcov : Matrix (Fin p) (Fin p) ℝ := S.Ri⁻¹
```

**Rendered meaning.** Recover the measurement covariance R by inverting the positive-definite penalty R⁻¹.

**Paper counterpart.** The measurement noise has covariance R > 0, while the optimization uses R⁻¹.

## 3. `innovS`

```lean
noncomputable def innovS : Matrix (Fin p) (Fin p) ℝ :=
  S.C * Sg * S.Cᵀ + S.Rcov
```

**Rendered meaning.** For covariance Σ, the innovation covariance is CΣCᵀ + R.

**Paper counterpart.** This is the matrix inverted in the DRE and Kalman gain: CΣ(k)Cᵀ + R.

## 4. `measM`

```lean
noncomputable def measM : Matrix (Fin n) (Fin n) ℝ :=
  1 - Sg * S.Cᵀ * (S.innovS Sg)⁻¹ * S.C
```

**Rendered meaning.** The posterior measurement-update factor is I − ΣCᵀ(CΣCᵀ + R)⁻¹C.

**Paper counterpart.** The paper does not name this factor. Expanding A times this matrix produces A − L(k)C.

## 5. `dreStep`

```lean
noncomputable def dreStep : Matrix (Fin n) (Fin n) ℝ :=
  S.A * (S.measM Sg * Sg) * S.Aᵀ + S.G * S.Qcov * S.Gᵀ
```

**Rendered meaning.** One covariance update is A[I − ΣCᵀ(CΣCᵀ+R)⁻¹C]ΣAᵀ + GQGᵀ.

**Paper counterpart.** The DRE is Σ(k+1) = GQGᵀ + AΣ(k)Aᵀ − AΣ(k)Cᵀ[CΣ(k)Cᵀ+R]⁻¹CΣ(k)Aᵀ. The expressions are algebraically equal.

## 6. `kfGain`

```lean
noncomputable def kfGain : Matrix (Fin n) (Fin p) ℝ :=
  S.A * Sg * S.Cᵀ * (S.innovS Sg)⁻¹
```

**Rendered meaning.** The prediction-form Kalman gain is L = AΣCᵀ(CΣCᵀ + R)⁻¹.

**Paper counterpart.** The paper defines L(k) by exactly this formula with Σ = Σ(k).

## 7. `errF`

```lean
noncomputable def errF : Matrix (Fin n) (Fin n) ℝ :=
  S.A - S.kfGain Sg * S.C
```

**Rendered meaning.** The one-step nominal error transition is F = A − LC.

**Paper counterpart.** The filter error satisfies ê(k+1) = [A − L(k)C]ê(k).

## 8. `dre`

```lean
noncomputable def dre : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => S.Sig0
  | k + 1 => S.dreStep (dre k)
```

**Rendered meaning.** Starting from Σ(0) = Σ₀, recursively apply the discrete Riccati update.

**Paper counterpart.** The paper's DRE starts at Σ₀ and defines Σ(k+1) by its displayed recursion for k ≥ 0.

## 9. `kfErrTrans`

```lean
noncomputable def kfErrTrans : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | k + 1 => S.errF (S.dre k) * kfErrTrans k
```

**Rendered meaning.** M(0) = I and M(k+1) = [A − L(k)C]M(k), so M(k) is the ordered product of all error transitions through time k−1.

**Paper counterpart.** The paper defines M(k) = [A−L(k−1)C]⋯[A−L(0)C], M(0)=I, and ê(k)=M(k)ê(0).


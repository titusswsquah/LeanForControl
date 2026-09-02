# Paper-result declaration interfaces — 14 items

The Lean blocks give the exact declaration interfaces at commit `f83321c8896778cef6af93709add4f439a4feb6c`. Proof bodies are omitted because the semantic audit compares theorem types; the separate build and axiom audit checks the proof terms.

## A. Existence, value, and infinite-horizon results

### 1. `chiOpt_unique`

Source: `LeanForControl/Estimation/ChiProblem.lean`.

```lean
theorem chiOpt_unique {x₀ xbar χ₀ : Fin n → ℝ} {ω : ℕ → Fin m → ℝ}
    {T : ℕ} (hfeas : S.ChiFeasible xbar χ₀)
    (hmin : S.chiCost x₀ xbar χ₀ ω T = S.value (x₀ - xbar) T) :
    χ₀ = S.chiOpt x₀ xbar T ∧ ∀ k < T, ω k = S.chiOptCtrl x₀ xbar T k := by
```

**Rendered meaning.** Every feasible pair attaining the optimal value has the same initial estimate and the same first T process-noise decisions as the constructed optimizer.

**Paper counterpart.** Lemma `lem:exist`: V_T⁰ exists and its minimizer is unique for all A,G,C with Q>0, R>0, and Σ₀≥0.

**Audit note.** The theorem is a uniqueness characterization conditional on feasibility and equality to `value`; existence/attainment is supplied by other declarations (`chiCost_chiOpt`, feasibility of `chiOpt`). The paper's one-sentence lemma therefore maps to a cluster, not this theorem alone.

### 2. `exists_value_bound_C2`

Source: `LeanForControl/Estimation/InfhorGeneral.lean`.

```lean
theorem exists_value_bound_C2 (hC2 : S.C2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin n → ℝ) (T : ℕ),
      S.value a T ≤ c * ‖a‖ ^ 2 := by
```

**Rendered meaning.** Under C2, one positive constant c uniformly bounds every finite-horizon optimal value by c‖a‖².

**Paper counterpart.** Lemma `lem:unibounded`: under C2 and nominal measurements, V_T⁰ ≤ c_v‖x(0)−x̄₀‖² for every horizon.

**Audit note.** Lean's `value` is twice the paper's V_T⁰, so the witness constant is correspondingly rescaled.

### 3. `tendsto_value`

Source: `LeanForControl/Estimation/InfhorGeneral.lean`.

```lean
theorem tendsto_value (hC2 : S.C2) (a : Fin n → ℝ) :
    Tendsto (fun T => S.value a T) atTop (nhds (S.valueLim a)) := by
```

**Rendered meaning.** Under C2, the finite-horizon optimal values converge to the supremum called `valueLim`.

**Paper counterpart.** Lemma `lem:unibounded` says the nondecreasing bounded sequence (V_T⁰) converges and defines V_∞⁰.

### 4. `tendsto_lastStage`

Source: `LeanForControl/Estimation/InfhorGeneral.lean`.

```lean
theorem tendsto_lastStage (hC2 : S.C2) (a : Fin n → ℝ) :
    Tendsto (fun T => quadForm S.glq.Qs
        (S.glq.traj (S.optInit a (T + 1))
          (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1)) T)
      + quadForm S.glq.Ru (S.glq.optCtrl (S.optInit a (T + 1)) (T + 1) T))
      atTop (nhds 0) := by
```

**Rendered meaning.** For the optimizer of horizon T+1, its final stage cost at time T tends to zero.

**Paper counterpart.** Equation `eq:ellT`: ℓ(ŵ(T | T+1), ν̂(T | T+1)) tends to zero.

**Audit note.** The Lean expression uses the error output Ce in place of the residual and twice the paper's stage cost.

### 5. `prop_infhor_zlim`

Source: `LeanForControl/Estimation/ChiProblem.lean`.

```lean
theorem prop_infhor_zlim (hC2 : S.C2) (x₀ xbar : Fin n → ℝ) :
    Tendsto (fun T => S.chiOpt x₀ xbar T) atTop
        (nhds (S.chiOptLim x₀ xbar))
      ∧ ∀ k, Tendsto (fun T => S.chiOptCtrl x₀ xbar T k) atTop
        (nhds (S.chiOptCtrlLim x₀ xbar k)) := by
```

**Rendered meaning.** Under C2, the optimal initial estimates converge, and for each fixed k the optimal process-noise decisions converge as the horizon grows.

**Paper counterpart.** Proposition `prop:infhor`, item `it:zlim`, asserts the existence of x̂(0 | ∞) and ŵ(j | ∞) for every fixed j.

**Audit note.** Lean takes the control limit over all natural T; values for T≤k exist because `optCtrl` is total, whereas the paper describes the tail T≥k+1. A finite prefix does not affect the limit.

### 6. `prop_infhor_xTT`

Source: `LeanForControl/Estimation/ChiProblem.lean`.

```lean
theorem prop_infhor_xTT (hC1 : S.C1) (hC2 : S.C2)
    (x₀ xbar : Fin n → ℝ) :
    Tendsto (fun T => S.chiOptTraj x₀ xbar T T
        - S.chiOptTrajLim x₀ xbar T) atTop (nhds 0) := by
```

**Rendered meaning.** Under C1 and C2, the diagonal finite-horizon terminal estimate approaches the time-T point on the limiting trajectory.

**Paper counterpart.** Proposition `prop:infhor`, item `it:xTT`: x̂(T | T) − x̂(T | ∞) → 0.

### 7. `prop_infhor_Vlim`

Source: `LeanForControl/Estimation/ChiProblem.lean`.

```lean
theorem prop_infhor_Vlim (hC2 : S.C2) (x₀ xbar : Fin n → ℝ) :
    S.chiInfCost x₀ xbar (S.chiOptLim x₀ xbar)
        (S.chiOptCtrlLim x₀ xbar)
      = S.valueLim (x₀ - xbar) := by
```

**Rendered meaning.** Under C2, the infinite-horizon cost of the limiting optimizer equals the limit of the finite-horizon optimal values.

**Paper counterpart.** Proposition `prop:infhor`, item `it:Vlim`: V_∞ evaluated at the limiting pair equals V_∞⁰.

## B. Modified-Q results

### 8. `exists_modQ`

Source: `LeanForControl/Estimation/QFunction.lean`.

```lean
theorem exists_modQ (hC1 : S.C1) (hC2 : S.C2) :
    ∃ (Q : (Fin n → ℝ) → ℕ → ℕ → ℝ) (c₀ cl cd : ℝ),
      0 < c₀ ∧ 0 < cl ∧ 0 < cd ∧
      (∀ a k, Q a 0 k ≤ c₀ * ‖a‖ ^ 2) ∧
      (∀ a k j, j ≤ k → cl * ‖S.eTraj a k j‖ ^ 2 ≤ Q a j k) ∧
      (∀ a k j, Q a (j + 1) k ≤ Q a j k - cd * ‖S.eTraj a k j‖ ^ 2) ∧
      (∀ a j, ∃ L, Tendsto (fun k => Q a j k) atTop (nhds L)) := by
```

**Rendered meaning.** Under C1 and C2 there is a modified Q-function with positive quadratic constants: an initial upper bound, a state-error lower bound, a one-step decrease, and a horizon limit for each fixed a,j.

**Paper counterpart.** Proposition `prop:tvkfQuns`: C1 and C2 imply a modified Q-function, and μ₀, μ₁, μ₃ can be quadratic. The paper's definition applies the lower and decrease inequalities only inside the horizon.

**Audit note.** The Lean decrease clause has no `j < k` guard. It is therefore stronger/different outside the paper's stated domain. The theorem constructs a Q satisfying this all-index condition, but the paper-to-Lean correspondence should not silently identify the two definitions.

### 9. `isGAS_of_modQ`

Source: `LeanForControl/Estimation/QFunction.lean`.

```lean
theorem isGAS_of_modQ (hC1 : S.C1) (hC2 : S.C2)
    (Q : (Fin n → ℝ) → ℕ → ℕ → ℝ) (c₀ cl cd : ℝ)
    (_hc₀ : 0 < c₀) (hcl : 0 < cl) (hcd : 0 < cd)
    (_hinit : ∀ a k, Q a 0 k ≤ c₀ * ‖a‖ ^ 2)
    (hlb : ∀ a k j, j ≤ k → cl * ‖S.eTraj a k j‖ ^ 2 ≤ Q a j k)
    (hdec : ∀ a k j, Q a (j + 1) k ≤ Q a j k - cd * ‖S.eTraj a k j‖ ^ 2)
    (hconv : ∀ a j, ∃ L, Tendsto (fun k => Q a j k) atTop (nhds L)) :
    S.IsGAS := by
```

**Rendered meaning.** If C1 and C2 hold and a Q has the listed positive quadratic bounds, all-index decrease, and fixed-j horizon limits, then the optimal terminal error is GAS.

**Paper counterpart.** Proposition `prop:modQgas`: if the optimal linear time-varying estimator admits a modified Q-function, every Q(j | k) has a horizon limit, and x̂(T | T)−x̂(T | ∞)→0, then the estimator is GAS.

**Audit warning.** This is not a literal formalization of the paper proposition. Lean assumes C1 and C2 directly, uses those assumptions to obtain trajectory convergence internally, specializes the class-K∞ functions to positive quadratic constants, and requires decrease for every j,k. The paper assumes diagonal trajectory convergence directly and only uses the in-horizon Q inequalities.

## C. Optimizer and Kalman headline results

### 10. `prop_tvkf_optimizer`

Source: `LeanForControl/Estimation/QFunction.lean`.

```lean
theorem prop_tvkf_optimizer : S.IsGAS ↔ S.C1 ∧ S.C2 := by
```

**Rendered meaning.** The optimization problem's terminal error is globally asymptotically stable exactly when C1 and C2 hold.

**Paper counterpart.** The main proposition says the time-varying linear optimal estimator is asymptotically stable if and only if C1 and C2 hold. This theorem is the optimizer-coordinate form; it becomes the recursive Kalman statement only after `semiPT_error` and `isGASkf_iff_isGAS`.

### 11. `prop_tvkf_optimizer_kl`

Source: `LeanForControl/Estimation/QFunction.lean`.

```lean
theorem prop_tvkf_optimizer_kl : S.IsGASkl ↔ S.C1 ∧ S.C2 := by
```

**Rendered meaning.** The optimizer admits the monotone product-form decay bound exactly when C1 and C2 hold.

**Paper counterpart.** The paper's `def:GAS` uses a KL bound and derives β(r,k)=rα(k) from linearity.

**Audit warning.** `IsGASkl` omits explicit positivity and strictness requirements normally associated with K and L classes. The error bound forces enough nonnegativity when nonzero errors exist, but the declared predicate is not literally “β is class KL.”

### 12. `semiPT_error`

Source: `LeanForControl/Estimation/Arrival.lean`.

```lean
theorem semiPT_error (a : Fin n → ℝ) (T : ℕ) :
    S.optTerm a T = S.kfErrTrans T *ᵥ a := by
```

**Rendered meaning.** For nominal data and initial error a, the horizon-T optimizer's terminal error is exactly the Kalman error M(T)a.

**Paper counterpart.** Lemma `lem:semiPT` claims a one-to-one correspondence between the semidefinite-prior optimization P_T and the time-varying Kalman filter.

**Audit warning.** This theorem proves the nominal terminal-error identity needed for stability. It does not alone formalize the paper's full one-to-one correspondence for arbitrary measurements, the entire estimate trajectory, and every optimizer component.

### 13. `prop_tvkf`

Source: `LeanForControl/Estimation/Arrival.lean`.

```lean
theorem prop_tvkf : S.IsGASkf ↔ S.C1 ∧ S.C2 := by
```

**Rendered meaning.** The recursive time-varying Kalman error has a uniform scalar decay rate if and only if the system is detectable and the prior misses no unstable uncontrollable direction.

**Paper counterpart.** Proposition `prop:tvkf`: the time-varying linear optimal estimator is asymptotically stable if and only if C1 and C2 hold.

**Audit note.** This is the closest literal headline match, subject to the norm convention and the precise GAS predicate described above.

### 14. `prop_tvkf_kl`

Source: `LeanForControl/Estimation/Arrival.lean`.

```lean
theorem prop_tvkf_kl :
    (∃ α : ℕ → ℝ, Antitone α ∧ Filter.Tendsto α Filter.atTop (nhds 0) ∧
      ∀ (k : ℕ) (a : Fin n → ℝ), ‖S.kfErrTrans k *ᵥ a‖ ≤ α k * ‖a‖)
      ↔ S.C1 ∧ S.C2 := by
```

**Rendered meaning.** A nonincreasing rate α tending to zero uniformly bounds every recursive Kalman error M(k)a exactly when C1 and C2 hold.

**Paper counterpart.** The paper defines GAS by ‖x(k)−x̂(k)‖ ≤ β(‖x(0)−x̄₀‖,k) and, using linearity, constructs β(r,k)=rα(k) with α(k)=supreme over j≥k of ‖M(j)‖.

**Audit warning.** As above, the formal predicate captures the product decay bound but does not encode every strict class-KL side condition.

## Result-to-paper coverage summary

| Paper item | Lean declarations |
|---|---|
| `lem:exist` | `chiOpt_unique`, together with optimizer attainment/feasibility lemmas outside this 14-item endpoint list |
| `lem:unibounded` | `exists_value_bound_C2`, `tendsto_value`, `tendsto_lastStage` |
| `prop:infhor` | `prop_infhor_zlim`, `prop_infhor_xTT`, `prop_infhor_Vlim` |
| `prop:tvkfQuns` | `exists_modQ` |
| `prop:modQgas` | `isGAS_of_modQ`, with the signature differences stated above |
| `lem:semiPT` | `semiPT_error`, only in nominal terminal-error form |
| `prop:tvkf` | `prop_tvkf_optimizer`, `prop_tvkf_optimizer_kl`, `prop_tvkf`, `prop_tvkf_kl` |


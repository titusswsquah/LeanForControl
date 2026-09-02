# Comments to the authors — action items from the Lean verification

Context in one line: every theorem-level claim of paper.tex is
machine-verified, sorry-free, by the paper's own proof routes — except
`prop:modQgas`, which is verified only under the restated hypotheses
of item 3 below (`notes/leanverify-2026a-program.md` has the full
mapping tables). Below is only what needs a change or a decision in
the text.

## Must fix

1. **`lem:unibounded` claims C2 alone but its proof uses C1.** The
   deferred proof invokes `eq:cc`, whose hypotheses include
   detectability, and says "(A₁,R^{−1/2}C₁) is detectable since (A,C)
   is detectable" — C1 inside a C2-only lemma; `prop:infhor`
   it:zlim/it:Vlim inherit the leak. The claim IS true under C2 alone.
   **Patch:** restate `eq:cc` for an *arbitrary stabilizing feedback*:
   stabilizability gives `K̃` with `A+BK̃` Schur, and the Lyapunov
   equation `S − (A+BK̃)'S(A+BK̃) = Q̃ + K̃'R̃K̃` yields cost
   `≤ ½λ̄(S)‖x₀‖²`. Detectability is only needed to make the
   LQR-*optimal* feedback stabilizing, which an upper bound never
   needs. (The Lean proof is the C2-only version.)

2. **`lem:semiPT` carries no proof and no source in paper.tex.** It is
   the paper's one unproven lemma. It is now machine-verified via the
   arrival-cost recursion (gas-lyap draft `lem:arrival`), reworked
   pseudoinverse-free: image parameterization `ξ = c(T) + Σ(T)z` plus
   the identity `MΣ(1 + CᵀR⁻¹CΣ) = Σ`. **Patch:** cite a source (the
   gas-lyap draft or RMD20) or absorb the argument — the pinv-free
   version is shorter on paper too.

3. **`def:modQ`/`prop:modQgas` carry hidden hypotheses.** Three
   leaks, all silent in the statement of `prop:modQgas`:
   (a) *Horizon limits.* The proof takes `Q(j|∞) := lim_k Q(j|k)` to
   exist "by `prop:infhor` and continuity" — but that argument is
   specific to the *constructed* Q of `prop:tvkfQuns`; an arbitrary
   function satisfying only `eq:QunsInitUB`/`eq:QunsLBUB`/
   `eq:QunsDecrease` need not converge along horizons.
   (b) *C1 ∧ C2.* The appeal to `prop:infhor` also imports that
   proposition's standing hypotheses — `prop:infhor` is stated under
   exactly C1 and C2, while `prop:modQgas` carries no hypotheses
   beyond admitting a modified Q-function.
   (c) *Index range.* The proof uses the decrease inequality at
   indices `eq:QunsDecrease` does not cover: `eq:QunsDecrease`
   restricts to `0 ≤ j ≤ k−1`, and the limit argument needs it for
   all `j`.
   **Patch:** restate the hypotheses of `prop:modQgas` (a convergence
   clause alone is not enough): assume C1 ∧ C2, convergent horizon
   limits, and decrease at all indices — or fold (a)/(c) into
   `def:modQ`. The Lean version (`isGAS_of_modQ`) does exactly this,
   and the constructed Q of `prop:tvkfQuns` supplies all three, so
   the intended application is unaffected.
   *(Status 2026-09-02: adopted — the revised `prop:modQgas`
   hypothesizes the horizon limits and the transfer
   `x̂(T|T) − x̂(T|∞) → 0`, and `isGAS_of_modQ` now matches it: no
   C1 ∧ C2, decrease consumed only on `0 ≤ j ≤ k − 1`.)*

## Minor text fixes

4. Stray "()" in "Refactoring `V_T` about `ẑ_T` ()".
5. The `F_T` "up to a z-independent term" clause deserves a note that
   `δν` is *linear* (not affine) in `δz`.
6. `it:zlim`'s "`j ∈ [0:T−1]`" index scoping reads oddly for a
   `T → ∞` limit (each fixed `j ≥ 0` is meant).

## Optional simplifications (verified to work; no correctness issue)

7. **The `M(k)` KL-uniformization needs no DRE argument.** Once
   `lem:semiPT` identifies the filter error with the (linear-in-`a`)
   optimizer, the pointwise-to-uniform bound is the standard-basis
   column trick on `M(k)` itself; the proof can say just that.
8. **`def:modQ`'s K∞-functions are only ever quadratic** in this
   paper: `prop:tvkfQuns` supplies quadratic μ's and `prop:modQgas`
   composes them. Stating the quadratic form would simplify
   `μ₁⁻¹∘μ₀` to explicit √-formulas; general K∞ is a free but unused
   generality.
9. **`it:xTT` wording flux is settled:** both the active IOSS-summation
   wording and the commented-out output-injection variant are verified;
   the IOSS wording is the one certified route-faithfully, so it is
   safe to keep and delete the comment.

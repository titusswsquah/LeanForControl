<!-- BEGIN FILE: 00-problem.md -->
<!-- All results below are referenced by their LaTeX label name, not by number. -->

# Setup

We study where the discrete-time filtering Riccati recursion lands. From an arbitrary prior $\Sigma_0 \succeq 0$, the filtered error covariance evolves by a Riccati recursion; we ask whether it converges, to which solution of the algebraic Riccati equation, and under what condition on $\Sigma_0$. The answer is organized by a single dichotomy — the recursion is attracted to the **stabilizing** solution exponentially under a controllability-side condition, and to the **strong** solution under a strictly weaker one. For the exponential (C3w) branch treated here the method is a **closed form**: the gap $\Sigma_T - \Sigma_\infty$ is written explicitly as the fixed strong loop $F_\infty$ acting on both sides of a homographic slide (`thm:formula`, the discrete image of the stabilizing-solution formula of Callier, Winkin and Willems 1994), so convergence, its rate $\rho(F_\infty)^2$, and its exact criterion all read off one identity rather than a two-sided squeeze. That criterion is geometric — the prior plane must be transverse to the antistable deflating subspace of the filter pencil, which is exactly C2 (`lem:sysinterp`). The one discrete obstruction — that time cannot be run backward on a singular state matrix — is met by keeping the symplectic *pencil* uninverted, its null modes passing to eigenvalues at infinity; no antistabilizing solution and no $A^{-1}$ appear. (The marginal branch C1 + C2w, where $F_\infty$ sits on the unit circle and the slide diverges, instead keeps the monotone-in-initial-condition squeeze — a universal lower bound and a dominating upper bound pinned to the same limit — supplied in Arc 2.)

## The system and the filtering Riccati

We consider the linear, discrete, time-invariant system

<!-- eq:linsys -->
$$ x^+ = Ax + Gw \qquad y = Cx + v \tag{eq:linsys} $$

with independent $x(0) \sim N(x_0, \Sigma_0)$, $w(k) \sim N(0, Q)$, $v(k) \sim N(0, R)$, and throughout $Q \succ 0$, $R \succ 0$, $\Sigma_0 \succeq 0$. The filtered error covariance $\Sigma_T := \operatorname{cov}(e(T\mid T))$ is seeded at $\Sigma_0$ and propagated, in measurement-update then time-update form, by the Riccati recursion

<!-- eq:cov-rec -->
$$ \Sigma_{T+1} = A\Big[\, \Sigma_T - \Sigma_T C'\big(C\Sigma_TC' + R\big)^{-1} C\, \Sigma_T \,\Big] A' + GQG' \qquad \Sigma_0 \text{ the prior} \tag{eq:cov-rec} $$

while the filtered error advances by the time-invariant linear **error map**

<!-- eq:filter -->
$$ e^\star(T+1\mid T+1) = F_T\, e^\star(T\mid T) \qquad F_T := A\Big( I - \Sigma_T C'\big(C\Sigma_TC' + R\big)^{-1} C \Big) \tag{eq:filter} $$

Both depend only on the running covariance and the time-invariant data $(A, G, C, Q, R)$, not on any horizon. Should the covariance settle, $\Sigma_T \to \Sigma_\infty$, its limit solves the **discrete algebraic Riccati equation** (DARE)

<!-- eq:dare -->
$$ \Sigma_\infty = A\Big[\, \Sigma_\infty - \Sigma_\infty C'\big(C\Sigma_\infty C' + R\big)^{-1} C\, \Sigma_\infty \,\Big] A' + GQG' \tag{eq:dare} $$

and the error map freezes to $F_\infty := A\big( I - \Sigma_\infty C'(C\Sigma_\infty C' + R)^{-1}C \big)$. The recursion `eq:cov-rec` is deployable but opaque — neither its convergence nor the spectrum of $F_\infty$ is visible in it; exposing both is the work of this development.

## Strong and stabilizing solutions

The solutions of the DARE `eq:dare` are classified by the spectrum of their error map relative to the **unit circle**.

<!-- def:strong -->
### Definition (def:strong) — Strong solution

A solution $\Sigma_\infty = \Sigma_\infty' \succeq 0$ of the DARE `eq:dare` is the **strong** solution if its error map $F_\infty$ has spectrum in the closed unit disk, $\rho(F_\infty) \le 1$. Under detectability (C1) it exists, is unique, and is the maximal positive-semidefinite solution (`fact:dare-strong`); it is the candidate limit of `eq:cov-rec`. The present development takes its existence/uniqueness from `fact:dare-strong` and establishes its block **structure** (`lem:structure`) and that `eq:cov-rec` is **attracted** to it.

<!-- def:stab -->
### Definition (def:stab) — Stabilizing solution

The strong solution is **stabilizing** when $F_\infty$ is Schur, $\rho(F_\infty) < 1$.

## Subspaces and conditions

Two subspaces of the state, intrinsic to $(A, G)$, organize the hypotheses. Let $\mathcal{X}_{uc}$ be the uncontrollable subspace of $(A, G)$, and on it distinguish modes by modulus:

- the **unstable–uncontrollable** subspace $\mathcal{X}_{u,uc}(A, G)$ — the $A$-invariant span of generalized eigenvectors at uncontrollable eigenvalues with $|\lambda| \ge 1$;
- the **antistable–uncontrollable** subspace $\mathcal{X}_{a,uc}(A, G)$ — the same, restricted to $|\lambda| > 1$.

Thus $\mathcal{X}_{a,uc} \subseteq \mathcal{X}_{u,uc}$, the two differing exactly by the uncontrollable modes on the unit circle. We make the standing assumptions

- **C1:** $(A, C)$ is detectable.
- **C2:** $\ker\Sigma_0 \cap \mathcal{X}_{u,uc} = \{0\}$.
- **C2w:** $\ker\Sigma_0 \cap \mathcal{X}_{a,uc} = \{0\}$.
- **C3w:** $(A, G)$ has no uncontrollable eigenvalue on the unit circle.

Since $\mathcal{X}_{a,uc} \subseteq \mathcal{X}_{u,uc}$, **C2 $\Rightarrow$ C2w**; under C3w there are no unit-circle uncontrollable modes, $\mathcal{X}_{u,uc} = \mathcal{X}_{a,uc}$, and **C2 $\iff$ C2w**. C1 guarantees the strong solution exists; **C2w** — that the prior leaves no purely antistable uncontrollable direction uninformed — is the condition for attraction to it. **This development treats the exponential regime C1 + C2 + C3w first**, where the uncontrollable–unstable part is antistable-only; the marginal extension to C1 + C2w follows.

## The antistable–marginal frame

The development works in a frame in which the stabilizable part, the strictly-antistable part, and the unit-circle part are separated, **in that order**, so that the reduced stabilizable-plus-antistable system occupies the leading principal block. By the state similarity and prior congruence of `app:frame` — which leave `eq:dare`, the spectrum of the error map, and the conditions unchanged — we take, **without loss of generality**,

<!-- eq:three-block -->
$$ A = \begin{bmatrix} A_1 & A_{1a} & A_{1m} \\ 0 & A_a & 0 \\ 0 & 0 & A_m \end{bmatrix} \qquad G = \begin{bmatrix} G_1 \\ 0 \\ 0 \end{bmatrix} \qquad C = [\,C_1\ \ C_a\ \ C_m\,] \qquad \Sigma_0 = \operatorname{diag}(\Sigma_1, \Sigma_2) \tag{eq:three-block} $$

with

- $(A_1, G_1)$ stabilizable and $(A_1, C_1)$ detectable (C1); its closed loop under the strong-solution gain, $A_c$ (the stabilizing closed loop of the reduced $(A_1,G_1,C_1)$ filter — **not** the $e_1$-diagonal block of $F_\infty$, which is not a spectral part: the antistable rows couple back through the gain), is Schur, $\rho_c := \rho(A_c) < 1$ (`eq:Finf-spec`) — the block that converges **forward**, needing no reversal;
- $A_a$ antistable, $|\lambda(A_a)| > 1$, with $A_a^{-1}$ Schur, $\rho_a := \rho(A_a^{-1}) < 1$ — the **antistable** block;
- $A_m$ on the unit circle, $|\lambda(A_m)| = 1$ — the **marginal** block ($A_m^{-1}$ exists but is **not** Schur); **absent under C3w**;
- $\Sigma_1 \succeq 0$ the stabilizable prior block, $\Sigma_2 = \big[\begin{smallmatrix} \Sigma_{aa} & \Sigma_{am} \\ \Sigma_{am}' & \Sigma_{mm} \end{smallmatrix}\big] \succeq 0$ the lumped uncontrollable prior block.

The uncontrollable block is the direct sum $A_2 := A_a \oplus A_m$, and the conditions read off the frame as $\mathcal{X}_{u,uc} = \{0\}^{n_1} \times \mathbb{R}^{n_a} \times \mathbb{R}^{n_m}$ (the $e_2$ coordinates) and $\mathcal{X}_{a,uc} = \{0\}^{n_1} \times \mathbb{R}^{n_a} \times \{0\}^{n_m}$ (the $e_a$ coordinates). The **reduced system** occupies the leading $e_1 \oplus e_a$ block; setting the marginal block empty gives the two-block form $A_2 = A_a$ — the **C3w / stabilizing regime**, in which $e_1 \oplus e_a$ is the entire state.

**The reversal is legal on $A_2$, and only there.** The proof runs time backward; in discrete time this requires inverting the dynamics, which fails on a singular $A$. The obstruction lives entirely in $A_2$, and there reversal is available:

<!-- eq:A2-inv -->
$$ A_2 = A_a \oplus A_m \quad\text{has}\quad |\lambda(A_2)| \ge 1 \quad\Longrightarrow\quad A_2 \ \text{nonsingular} \qquad A_2^{-1} = A_a^{-1} \oplus A_m^{-1} \tag{eq:A2-inv} $$

with $A_a^{-1}$ Schur (rate $\rho_a$) and $A_m^{-1}$ on the unit circle. Every backward object of the development — the uncontrollable–unstable information gramian `eq:Jgram` — is built from $A_2^{-1}$ on the $e_2$ subspace; the stabilizable block $A_1$ is never inverted.

## Definitions

<!-- def:attract -->
### Definition (def:attract) — Attraction to the strong solution

The recursion `eq:cov-rec` is **attracted to the strong solution** if $\Sigma_T \to \Sigma_\infty$ as $T \to \infty$, with $\Sigma_\infty$ the strong solution (`def:strong`).

<!-- def:rate -->
### Definition (def:rate) — Exponential vs. polynomial rate

The attraction is **exponential** if there is $\gamma \in (0, 1)$ such that for every prior $\Sigma_0 \succeq 0$ *satisfying C2* there is $c < \infty$ with $\|\Sigma_T - \Sigma_\infty\| \le c\, \gamma^T$ for all $T$; otherwise it is slower (the numerics show $\|\Sigma_T - \Sigma_\infty\| \sim c\, T^{-r}$ from marginal-informing priors). The quantifier over admissible priors is part of the definition: for a *fixed* prior, exponential convergence can coexist with marginal uncontrollable modes (an exactly-known marginal block runs as a marginal-free subsystem — `thm:main`-2's remark), so it is the every-C2-prior property that characterizes C3w.

## The dichotomy

The development culminates in the strong/stabilizing dichotomy `eq:dichotomy`, assembled last in the main theorem (forthcoming), and stated exponential-branch first:

<!-- eq:dichotomy -->
$$ \text{C1}\!: \text{C3w} \iff \big(\Sigma_T \to \Sigma_\infty\ \text{exponentially from every C2 prior}\big)\ (\rho(F_\infty) < 1) \qquad\qquad \text{C1} + \text{C2w} \iff \Sigma_T \to \Sigma_\infty\ (\rho(F_\infty) \le 1) \tag{eq:dichotomy} $$

The first line is the exponentially-attracting, **stabilizing** regime: with no uncontrollable unit-circle mode the reduced $e_1 \oplus e_a$ system is the whole state, $F_\infty$ is Schur, and the approach is geometric (the discrete-time counterpart of Callier, Winkin and Willems 1994). The second relaxes C2 + C3w to C2w alone: the marginal modes survive in the limit, $F_\infty$ sits on the unit circle, and the approach is slower — marginal uncontrollable modes slow the recursion but do not stop it (the discrete counterpart of the critical-mode phenomenon of Callier and Winkin 1995). The marginal branch currently carries `lem:marginal`'s standing qualification (semisimple marginal modes, itself a verified implication — semisimple ⇒ power-bounded; defective case open), and its rate is observed ($\sim 1/T$) but not proved.

**Remark (boundary cases).** If $(A, G)$ is controllable, $\mathcal{X}_{uc} = \{0\}$ and C2/C2w hold for every prior. If $(A, C)$ is observable, C1 is automatic. With the marginal block empty, `eq:three-block` is the two-block C3w form and `eq:dichotomy` reduces to its first line. Each such case is read by setting the corresponding block to be absent.
<!-- END FILE: 00-problem.md -->

<!-- BEGIN FILE: 01-structure.md -->
<!-- lem:structure — structure of Sigma+ under C3w: the uncontrollable block is antistable-only, so -->
<!-- Sigma+|22 = Sigma+|aa > 0 is nonsingular, its information is the steady A_a^{-1}-gramian, F_inf is Schur. -->
<!-- Plus uniform boundedness and antistable positivity along the recursion. No marginal block here. -->
<!-- lem:structure -->
### Lemma (lem:structure) — Structure of the strong solution, boundedness, antistable positivity

Let C1 and C3w hold. The strong solution $\Sigma_\infty$ of `eq:dare` exists and is unique (`fact:dare-strong`); in the frame `eq:three-block` the uncontrollable block is antistable-only ($e_2 = e_a$, $n_m = 0$):

<!-- lem:structure-1 -->
**1. (Uncontrollable block positive definite; the error map is Schur.)**

<!-- eq:Sinf-struct -->
$$ \Sigma_\infty\!\mid_{aa} \succ 0 \qquad\text{(the entire uncontrollable block)} \tag{eq:Sinf-struct} $$

and the antistable information is the steady $A_a^{-1}$-gramian

<!-- eq:Sinf-gram -->
$$ (\Sigma_\infty\!\mid_{aa})^{-1} = \sum_{j=0}^{\infty} \big(A_a^{-j}\big)'\, W_\infty\!\mid_{aa}\, A_a^{-j} \qquad W_\infty\!\mid_{aa} := (\Sigma_\infty\!\mid_{aa})^{-1} - A_a^{-1\prime}(\Sigma_\infty\!\mid_{aa})^{-1} A_a^{-1} \succeq 0 \tag{eq:Sinf-gram} $$

a finite sum, since $A_a^{-1}$ is Schur (`eq:A2-inv`). From this the strong error map $F_\infty = A(I - L_\infty C)$, $L_\infty := \Sigma_\infty C'(C\Sigma_\infty C' + R)^{-1}$, has the spectrum `eq:Finf-spec` (Fact 1),

$$ \operatorname{spec}(F_\infty) = \operatorname{spec}(A_c)\ \cup\ \{\,\lambda^{-1} : \lambda \in \operatorname{spec}(A_a)\,\} $$

— the stabilizable closed loop ($A_c$, Schur) and the antistable spectrum **reflected** inside the disk ($A_a \mapsto A_a^{-1}$). Both parts are strictly inside, so **$F_\infty$ is Schur**, $\rho(F_\infty) < 1$ — the stabilizing solution (`def:stab`, `eq:Finf-c3w`).

<!-- lem:structure-2 -->
**2. (Uniform boundedness.)** For every prior $\Sigma_0$ the iterates are bounded,

<!-- eq:bounded -->
$$ \sup_{T \ge 0}\, \Sigma_T(\Sigma_0) \preceq \bar\Pi(\Sigma_0) < \infty \tag{eq:bounded} $$

<!-- lem:structure-3 -->
**3. (Antistable positivity along the recursion.)** If $\Sigma_{0}\!\mid_{aa} \succ 0$, then $\Sigma_T\!\mid_{aa} \succ 0$ for all $T$, so the antistable information $J_T^{aa} := (\Sigma_T\!\mid_{aa})^{-1}$ is well defined.

*Proof.*

**Part 1.** $\Sigma_\infty\succeq0$ is the strong solution (`fact:dare-strong`). Under C3w the uncontrollable block carries only antistable modes, so $\Sigma_\infty\!\mid_{22} = \Sigma_\infty\!\mid_{aa}$, and no singular marginal sub-block appears. **Positivity by kernel invariance** (only $\rho(F_\infty)\le1$ of Fact 1 is consumed here, not the spectrum). At the fixed point, written $\Sigma_\infty = A\,\mathcal U(\Sigma_\infty)\,A' + GQG'$, any $w\in\ker\Sigma_\infty$ splits $0 = w'\Sigma_\infty w = \|A'w\|^2_{\mathcal U(\Sigma_\infty)} + \|G'w\|^2_{Q}$ into two nonnegative terms, so $\mathcal U(\Sigma_\infty)(A'w) = 0$ — hence $\Sigma_\infty(A'w) = 0$, the update preserving kernels (`fact:update-kernel`) — and $G'w = 0$ ($Q\succ0$): **$\ker\Sigma_\infty$ is $A'$-invariant**. Moreover the filter does not act on directions it knows exactly: $F_\infty'w = A'w - C'S_\infty^{-1}C\,\Sigma_\infty(A'w) = A'w$ on $\ker\Sigma_\infty$. A direction $v\in\ker(\Sigma_\infty\!\mid_{aa})$ embeds in $\ker\Sigma_\infty$ ($\Sigma_\infty\succeq0$), and the $e_a$-supported part of the kernel is itself $A'$-invariant with $A'$ acting there as $A_a'$ ($A$ is upper block-triangular with $e_2$-diagonal $A_2 = A_a$ here). So a nontrivial $\ker(\Sigma_\infty\!\mid_{aa})$ is an $F_\infty'$-invariant subspace on which $F_\infty'$ acts as $A_a'$, handing $F_\infty$ an eigenvalue of $A_a$ verbatim — $|\lambda|>1$, against $\rho(F_\infty)\le1$. Hence $\Sigma_\infty\!\mid_{aa}\succ0$, and its information $J_\infty^{aa}:=(\Sigma_\infty\!\mid_{aa})^{-1}$ is well defined. Because $A_2=A_a$ here, the $e_2$-fixed-point identity (`app:machinery`-2, $GQG'\!\mid_{22}=0$) reads $\Sigma_\infty\!\mid_{aa}=A_a\,\mathcal U(\Sigma_\infty)\!\mid_{aa}\,A_a'$; inverting (both sides $\succ0$, $A_a$ nonsingular) gives $J_\infty^{aa}=A_a^{-1\prime}J_\infty^{aa}A_a^{-1}+W_\infty^{aa}$, where $W_\infty^{aa}:=J_\infty^{aa}-A_a^{-1\prime}J_\infty^{aa}A_a^{-1}$. This $W_\infty^{aa}\succeq0$ because the measurement update **contracts** the block, $\mathcal U(\Sigma_\infty)\!\mid_{aa}\preceq\Sigma_\infty\!\mid_{aa}$, so $(\mathcal U(\Sigma_\infty)\!\mid_{aa})^{-1}\succeq J_\infty^{aa}$ and therefore $J_\infty^{aa}\succeq A_a^{-1\prime}J_\infty^{aa}A_a^{-1}$. Since $A_a^{-1}$ is Schur (`eq:A2-inv`), the relation unrolls to the convergent steady gramian `eq:Sinf-gram` (a finite sum), and observability of the antistable mode (C1) keeps the injection — hence $J_\infty^{aa}$ — positive definite. The stabilizable diagonal block of $F_\infty$ is $A_c$, Schur by the strong-solution gain; with the antistable modes reflected inside and no marginal block, $\rho(F_\infty)<1$.

**Part 2.** Detectability (C1) is exactly the existence of a fixed gain $L$ with $A - LC$ Schur. The domination is algebraic: completing the square in the predictor form about $L^* := A\Sigma C'S(\Sigma)^{-1}$, $S(\Sigma) := C\Sigma C' + R$, gives for every $\Sigma\succeq0$ and **every** gain $L$

$$ (A-LC)\Sigma(A-LC)' + LRL' + GQG' \;-\; \mathcal R(\Sigma) \;=\; (L - L^*)\,S(\Sigma)\,(L - L^*)' \;\succeq\; 0, $$

so one covariance step is dominated by the fixed-gain Lyapunov step. With $\Pi_{T+1} = (A - LC)\Pi_T(A - LC)' + LRL' + GQG'$, $\Pi_0 = \Sigma_0$: the Lyapunov step is Löwner-monotone (a congruence plus a constant), so $\Sigma_{T+1} = \mathcal R(\Sigma_T) \preceq (A-LC)\Sigma_T(A-LC)' + LRL' + GQG' \preceq \Pi_{T+1}$ by induction, and $\Pi_T \preceq \bar\Pi < \infty$ since $A - LC$ is Schur (`fact:schur-decay`). This is `eq:bounded`, with no appeal to estimator optimality. (The completed square must be taken in the *predictor* form: the update-form square reaches only gains of the shape $AK$, which for singular $A$ misses the injection $L$ that detectability supplies.)

**Part 3.** The antistable block obeys $\Sigma_{T+1}\!\mid_{aa} = A_a\,\mathcal{U}(\Sigma_T)\!\mid_{aa}\,A_a'$ (the unconditional $(a,a)$-block identity of `app:machinery`-2, valid for every $\Sigma\succeq0$). By `fact:update-kernel`, $\Sigma_T\!\mid_{aa}\succ0 \Rightarrow \mathcal{U}(\Sigma_T)\!\mid_{aa}\succ0$ — the diagonal sub-block alone drives the conclusion, no full positive-definiteness of $\Sigma_T$ being required. With $A_a$ nonsingular, $\Sigma_{T+1}\!\mid_{aa}\succ0$. Since $\Sigma_0\!\mid_{aa}\succ0$, induction gives the claim. ∎

<!-- verify: under C3w Sigma+|22 = Sigma+|aa > 0 is NONSINGULAR (no marginal block), so the whole-block information J_inf = (Sigma+|22)^{-1} = J^aa is well-defined — the P3 conflation cannot arise here. Sigma+|aa>0 by KERNEL INVARIANCE (ker Sigma_inf is A'-invariant + G'-annihilated at the fixed point; F_inf' = A' on ker Sigma_inf; the e_a-supported kernel is F_inf'-invariant acting as A_a' => an Aa-eigenvalue of F_inf, contra rho(F_inf)<=1) — consumes only rho<=1 of Fact 1, NOT eq:Finf-spec; scratch/check_kernel_invariance.py: all three identities exact on a singular non-strong fixed point (the unreflected eig 2 appears in spec F). Replaces the prior unreflected-direction heuristic (Lean verification finding 2, soft). Gramian eq:Sinf-gram with W_inf^aa>=0 from the U-contraction. F_inf Schur (spec A_c inside + reflected A_a^{-1} inside, no marginal). check_a03.py [A],[C] residual 3e-16; check_structure_p3.py min eig Saa=8.87>0, antistable eig 2 -> 0.5 reflected, rho(F_inf)=0.5<1. Boundedness: predictor-form Joseph square (holds for EVERY gain L; scratch/check_pjoseph.py resid 3e-14) + fixed-gain Lyapunov domination — fact:filter-opt no longer consumed here (Lean verification finding 1, adopted; the MMSE import remains only for the FIE=TVKF identification in 09-payoff). -->
<!-- verify: LIVE consumers — lem:structure-1 (F_inf Schur, eq:Sinf-struct/eq:Sinf-gram) feeds thm:formula, lem:sysinterp, thm:sufficiency, thm:payoff; eq:bounded feeds thm:formula (finite-T denominator nonsingularity) and thm:sufficiency (sup||M_T^-1||<inf, early T). The retired anchors also read eq:bounded/eq:Sinf-gram/Part 3 — that path is dead. Necessity (Sigma+|aa>0 as its lever) is flagged open. Marginal case (Sigma+|mm=0) is lem:structure-marg below. -->
<!-- verify: LEAN (phase A): Sigma_inf|aa>0 = DareSystem.strong_corner_posDef / strong_toBlocks_posDef (Estimation/Dare/Structure.lean; marginal-inclusive); eq:bounded = Dare.exists_dare_bound (Estimation/Dare/Bounded.lean); Part 3 = DareSystem.dare_corner_posDef under C2w (+ seed-general dareFrom_corner_posDef); eq:Sinf-gram = DareSystem.strong_stein (relation form; the unrolled series lands with its Phase-B consumer). F_inf Schur under C3w: VERIFIED (phase D) = DareSystem.strong_isSchurStable_iff_C3w (Estimation/Dare/Main.lean; Schur IFF no marginal block, via strong_spec_split + strong_Fs_schur + the unit-circle witness). fact:dare-strong: existence/uniqueness now THEOREMS (phase D4, Estimation/Dare/Existence.lean; existence under C1 alone). Axioms clean throughout. -->

<!-- lem:structure-marg — MARGINAL structure of Sigma+ (Arc 2, n_m>=1): extinction Sigma+|_{.m}=0, so -->
<!-- Sigma+|22 = diag(Sigma+|aa, 0) with Sigma+|aa > 0; F_inf carries spec(A_m) on the unit circle (rho=1), -->
<!-- F_inf|_{e1+a} Schur. Separated from lem:structure (C3w) for confinement: C3w consumers cite lem:structure, -->
<!-- marginal consumers (03 C2w criterion, 05 squeeze limit, 06b-C necessity) cite this. -->
<!-- lem:structure-marg -->
### Lemma (lem:structure-marg) — Marginal structure of the strong solution

Let C1 hold and let a marginal block be present, $n_m \ge 1$, in the frame `eq:three-block` ($A_2 = A_a \oplus A_m$, $|\lambda(A_m)| = 1$). Then the strong solution **extinguishes on the marginal directions**,

<!-- eq:marg-extinct -->
$$ \Sigma_\infty\!\mid_{\cdot\, m} = 0, \qquad\text{hence}\qquad \Sigma_\infty\!\mid_{22} = \begin{bmatrix} \Sigma_\infty\!\mid_{aa} & 0 \\ 0 & 0 \end{bmatrix}, \quad \Sigma_\infty\!\mid_{aa} \succ 0, \tag{eq:marg-extinct} $$

and its error map is block upper-triangular for the $(e_1\oplus a\,|\,m)$ split, carrying the marginal spectrum on the unit circle, unreflected, and Schur off it:
$$ \operatorname{spec}(F_\infty) = \operatorname{spec}\big(F_\infty\!\mid_{e_1\oplus a}\big)\ \sqcup\ \operatorname{spec}(A_m), \qquad F_\infty\!\mid_{e_1\oplus a}\ \text{Schur}, \qquad \rho(F_\infty) = 1 $$
(`eq:Finf-spec`, `eq:Finf-c3w`; the finer reciprocal identification of the Schur part, $\Lambda_{\mathrm{in}}\sqcup\{\lambda^{-1}:\lambda\in\operatorname{spec}(A_a)\}$, is `fact:dare-strong`'s pencil statement — Arc 1 territory, not consumed by the dichotomy).

*Proof.* The antistable block is exactly as in `lem:structure`-1: the kernel-invariance argument there uses only $\rho(F_\infty)\le1$ (`fact:dare-strong`) and applies verbatim with a marginal block present — $A_2 = A_a\oplus A_m$ is block-diagonal, so $A'$ still acts on the $e_a$-supported kernel as $A_a'$; hence $\Sigma_\infty\!\mid_{aa}\succ0$. The spectrum claims are proved at the end, from extinction; they consume only $\rho(F_\infty)\le1$ (`fact:dare-strong`). Everything else follows from extinction $\Sigma_\infty\!\mid_{\cdot\,m}=0$, which gives the block form of `eq:marg-extinct` directly. Let $\Delta := \Sigma_\infty C'(C\Sigma_\infty C'+R)^{-1}C\Sigma_\infty \succeq 0$ be the measurement correction, so $\mathcal U(\Sigma_\infty) = \Sigma_\infty - \Delta$, and write $P := \Sigma_\infty\!\mid_{mm}\succeq0$.

**The marginal correction vanishes.** The $(2,2)$-block fixed-point identity (`app:machinery`-2: $GQG'\!\mid_{22}=0$, $A$ has $e_2$-row $[\,0\ A_2\,]$, $A_2 = A_a\oplus A_m$) reads $\Sigma_\infty\!\mid_{22} = A_2\,\mathcal U(\Sigma_\infty)\!\mid_{22}\,A_2'$; its $(m,m)$ entry, $A_2$ being block-diagonal, is $P = A_m\,\mathcal U(\Sigma_\infty)\!\mid_{mm}\,A_m' = A_m(P - \Delta\!\mid_{mm})A_m'$. Since $A_m$ is nonsingular this rearranges to the Stein relation

<!-- eq:marg-stein -->
$$ P - A_m^{-1}\,P\,A_m^{-\prime} = \Delta\!\mid_{mm} \;\succeq\; 0. \tag{eq:marg-stein} $$

Unrolling `eq:marg-stein` telescopes **exactly**: with $B := A_m^{-\prime}$, the per-step identity $u'\Delta\!\mid_{mm}u = u'Pu - (Bu)'P(Bu)$ gives, for every $N$ and every $u$,
$$ \sum_{k=0}^{N-1} (B^k u)'\,\Delta\!\mid_{mm}\,(B^k u) \;=\; u'Pu - (B^N u)'P(B^N u) \;\le\; u'Pu, $$
so the $\Delta\!\mid_{mm}$-energy along every backward orbit is summable. Were $\Delta\!\mid_{mm}\ne0$, pick $x$ with $x'\Delta\!\mid_{mm}x>0$ and set $v := \Delta\!\mid_{mm}x\ne0$; Cauchy–Schwarz for the PSD form gives $(v'B^ku)^2 \le (x'\Delta\!\mid_{mm}x)\,(B^ku)'\Delta\!\mid_{mm}(B^ku)$, so $\sum_k (v'B^ku)^2<\infty$ for every $u$, hence $v'B^ku\to0$ for every $u$ — that is, $A_m^{-k}v\to0$ componentwise. Every eigenvalue of $A_m^{-1}$ has modulus $1$, so `fact:no-decay` forces $v=0$ — a contradiction. Therefore $\Delta\!\mid_{mm}=0$. (No matrix-series convergence and no spectral factorization of $\Delta\!\mid_{mm}$ are needed.)

**The marginal columns are unobservable, hence zero.** With $B := \Sigma_\infty C'$ and $S := C\Sigma_\infty C'+R\succ0$, the vanishing block $\Delta\!\mid_{mm} = B_m\,S^{-1}B_m' = 0$ forces $B_m = \Sigma_\infty\!\mid_{m\,\cdot}\,C' = 0$, i.e. $C\,\Sigma_\infty\!\mid_{\cdot\,m}=0$. Hence $\Delta\!\mid_{\cdot\,m} = \Sigma_\infty C'S^{-1}(C\,\Sigma_\infty\!\mid_{\cdot\,m}) = 0$, and the marginal-column fixed point $\Sigma_\infty\!\mid_{\cdot\,m} = [A\,\mathcal U(\Sigma_\infty)\,A']\!\mid_{\cdot\,m}$ collapses to $Z = A\,Z\,A_m'$ for $Z := \Sigma_\infty\!\mid_{\cdot\,m}$. Thus $A Z = Z A_m^{-\prime}$. Take the stabilizing output injection detectability supplies (as in Part 2 of `lem:structure`): $L$ with $A - LC$ Schur. Since $CZ = 0$,
$$ (A - LC)\,Z = A Z = Z A_m^{-\prime}, \qquad\text{hence}\qquad (A-LC)^k Z = Z A_m^{-k\prime} \quad (k \ge 0). $$
The left side decays geometrically ($A - LC$ Schur, `fact:schur-decay`), so $Z A_m^{-k\prime} \to 0$; transposing, $A_m^{-k} Z' \to 0$ — each row of $Z$ rides the unit-modulus $A_m^{-1}$ to zero, and `fact:no-decay` forces every row to vanish. Hence $Z = \Sigma_\infty\!\mid_{\cdot\,m} = 0$. (The unobservable-subspace confinement $\mathcal{NO}(C,A)\subseteq\{|\lambda|<1\}$ — a fact not among `app:facts` — is not needed; the injection argument uses only declared facts.)

**The spectrum splits and the $e_1\oplus a$ part is Schur.** Extinction kills the marginal rows of the gain ($\Sigma_\infty\!\mid_{m\,\cdot} = 0$ gives $L_\infty\!\mid_{m\,\cdot} = 0$), so $e_m'F_\infty = A_m e_m'$: $F_\infty$ is block upper-triangular for the $(e_1\oplus a\,|\,m)$ split, and the spectrum splits as displayed, with the compression $F_s := E_s'F_\infty E_s$ ($E_s$ the $e_1\oplus a$ inclusion) satisfying the invariance $F_\infty E_s = E_s F_s$. Then $\rho(F_\infty) = 1$: $\le$ is `fact:dare-strong`, and the unreflected marginal part supplies a unit-modulus eigenvalue. $F_s$ is Schur by a **one-step PBH–Stein argument**. An eigenvalue $\mu$ of $F_s$ with $|\mu| > 1$ is impossible outright: the invariance embeds its eigenvector into one of $F_\infty$, against $\rho(F_\infty)\le1$. For $|\mu| = 1$, take a left eigenvector $w$ of $F_s$ and set $e := E_s w$, a left *quasi*-eigenvector of $F_\infty$ whose marginal drift is annihilated inside the $\Sigma_\infty$-energy by extinction. One step of the fixed point in predictor-Joseph form, $\Sigma_\infty = F_\infty\Sigma_\infty F_\infty' + (AL_\infty)R(AL_\infty)' + GQG'$, transported along $e$, balances exactly at $|\mu|^2 = 1$ (the rotation cancels in $\mathrm{re}^2+\mathrm{im}^2$; no power induction is needed), forcing $(AL_\infty)'e = 0$ and $G'e = 0$. Hence $A'e = F_\infty'e = \mu e$ modulo the annihilated drift: $e$ is a left eigenvector of $A$ unexcited by $G$ — its $e_1$ part dies by stabilizability (PBH), its $a$ part by $|\lambda(A_a)| > 1$, and it has no $m$ part ($e_m'E_s = 0$); so $e = 0$, a contradiction. ∎

<!-- verify: GATE-2 (check_extinction_proof.py). Extinction Sigma_inf|_{.m} -> 0 across semisimple rotation e^{+-0.7i} AND defective Jordan blocks at +1, -1 (size 2). eq:marg-stein identity (P - Am^-1 P Am^-') = Delta_mm holds ~1e-10; Delta_mm -> 0; C Z -> 0; Z -> 0; Sigma_inf|_aa = 4.19 > 0. Defective cases converge slower (polynomial w/ Jordan factor) but same limit. Telescope form of the unroll + Z-fixed-point identity exact at the approximate fixed point: scratch/check_extinction_route.py. Correction-kill rewritten to the telescope + PSD Cauchy-Schwarz + fact:no-decay route (Lean verification finding 3, adopted): drops the uncited matrix monotone-series convergence and the spectral factorization. -->
<!-- verify: hypotheses/DAG. lem:structure-marg: C1 (twice: rho(F_inf)<=1 for the antistable half; the stabilizing output injection A-LC Schur for the row kill — the NO(C,A)-confinement import is GONE, Lean verification finding 4 adopted), app:machinery-2 ((2,2) block identity, unconditional), fact:no-decay (twice: correction kill and row kill, |lambda(Am^-1)|=1), fact:schur-decay, fact:dare-strong (rho<=1; eq:Finf-spec only for the displayed spectrum). Antistable Sigma_inf|_aa>0 reused verbatim from lem:structure-1. CONSUMERS: 03 (C2w criterion), 05 (squeeze limit Sigma_inf|_mm=0), 06b-C (marginal necessity). No forward refs. -->
<!-- verify: CONFINEMENT — this lemma is the MARGINAL (GAS) branch; it does NOT read C3w and is not read by the C3w/exponential chain (04, 06). rho(F_inf)=1 here (marginal present) vs rho<1 in lem:structure. Extinction is the discrete dual of CW eq:ker-gap (riccaflow, critical block of the gap = 0). -->
<!-- verify: LEAN (phase A): the antistable half (Sigma_inf|aa>0) = DareSystem.strong_corner_posDef (marginal-inclusive, same declaration as lem:structure-1); extinction Sigma_inf|.m = 0 = DareSystem.strong_marg_extinct (Estimation/Dare/Marginal.lean; correction kill = strong_marg_correction_eq_zero via the orbit-kill lemma posSemidef_eq_zero_of_orbit_summable, output kill = strong_marg_output_eq_zero, column kill via detect_inj + fact:schur-decay + no_decay). The displayed spectrum is VERIFIED (phase D): the split = DareSystem.strong_spec_split, F_inf|e1+a Schur = DareSystem.strong_Fs_schur (one-step PBH-Stein via strong_predictor_stein and the extinction kill), the unit-modulus witness for rho(F_inf)=1 = strong_exists_unit_eigenvalue (Estimation/Dare/Spectrum.lean); only rho(F_inf)<=1 is consumed from the IsStrongSolution bundle. Axioms clean. -->
<!-- END FILE: 01-structure.md -->

<!-- BEGIN FILE: 02-criterion.md -->
<!-- 02-criterion — the prior-positivity form of C2w: the seed the antistable information needs. -->
<!-- Port of riccastep 04-criterion-v2; restated for the slaved frame (name lem:criterion-w). -->
<!-- sec:criterion — main text -->
<!-- lem:criterion-w -->
### Lemma (lem:criterion-w) — C2w in prior-block coordinates

In the frame `eq:three-block`, with $\Sigma_a := \Sigma_{aa}$ the antistable diagonal block of the prior,

<!-- eq:criterion -->
$$ \text{C2w} \quad\iff\quad \Sigma_a \succ 0. \tag{eq:criterion} $$

Equivalently, C2w is exactly the statement that the antistable information $J_0^{aa} := \Sigma_a^{-1}$ — the seed of the recursion `eq:Jrec` on the antistable block — is **finite**.

*Proof.* The equivalence is `eq:prior-pos`(b): $\mathcal X_{a,uc}$ is the $e_a$ coordinate block, and $\ker\Sigma_0\cap\mathcal X_{a,uc}=\{0\}$ holds iff the antistable diagonal block $\Sigma_a$ of the (possibly coupled) prior block $\Sigma_2$ is nonsingular. Finiteness of $J_0^{aa}=\Sigma_a^{-1}$ is then immediate. ∎

**Remark (why this is the criterion).** The antistable block of the covariance is **uncontrollable** — no process noise refreshes it — so its information is never created by the recursion; it can only be inherited from the prior and propagated by $A_a^{-1}$ (`app:machinery`, `eq:Jrec`). C2w ($\Sigma_a\succ0$) is the demand that this inherited antistable information be finite in every direction. When it holds, the prior seed $J_0^{aa}$ is finite, the discrete $J$-transform contracts it and the steady $A_a^{-1}$-gramian $(\Sigma_\infty\!\mid_{aa})^{-1}$ takes over (`lem:jtransform`, `lem:lowsqueeze`); when it fails, some antistable direction carries infinite information — zero covariance — merely rotated, never resolved (`thm:necessity`). This is the discrete, estimation-side image of the antistable-coordinate positivity condition of Callier and Winkin (1995). The coupling matters: $\ker\Sigma_2$ may contain *mixed* antistable–marginal directions even when $\Sigma_a\succ0$, so C2w forbids only a *purely* antistable kernel direction (`eq:prior-pos`).

<!-- verify: eq:criterion is eq:prior-pos(b) (a01-frame), validated structurally there; seed-finiteness is its restatement. Deps: eq:three-block, eq:prior-pos, eq:Jrec/app:machinery. CONSUMERS: lem:slaved-seed (eq:Lc2w restates it on the seed), lem:lowsqueeze / lem:jtransform (finite J_0^aa under C2w), thm:sufficiency (C2w through it), thm:main. PORT of riccastep 04-criterion-v2. -->
<!-- verify: LEAN (phase A): lem:criterion-w / eq:criterion = DareSystem.criterion_w (Estimation/Dare/System.lean; C2w defined in the paper's kernel form, positivity proved); axioms clean. -->
<!-- END FILE: 02-criterion.md -->

<!-- BEGIN FILE: 03-supremal.md -->
<!-- 03-supremal — Charybdis, the upper anchor of the GAS squeeze (marginal modes semisimple). From any dominating prior the trajectory -->
<!-- dominates the run and converges to Sigma_inf, through the FIXED strong loop F_inf (the gap-Riccati -->
<!-- eq:gap-ric in a02-machinery). Antistable reaches Sigma_inf|aa>0 exponentially (A_a^-1 Schur), marginal -->
<!-- reaches 0 polynomially (lem:marginal). Discrete image of Callier-Winkin lem:supremal; the "smallest CW -->
<!-- deviation" (stablistep-handoff §1): CW's monotone ceiling R(Sigma-bar)<=Sigma-bar has NO discrete analog -->
<!-- (antistable amplification), so anchor at ANY Sigma-bar >= Sigma_inf and contract the gap through F_inf. -->
<!-- Ported from riccastep 01-marginal-v3 + 05-supremal-v3; the gap engine (eq:diff-id/eq:gap-ric) already -->
<!-- lives in a02-machinery, so this file is the two anchor lemmas built on it. -->
<!-- sec:supremal — main text -->
### The upper anchor: marginal extinction and the supremal bound

The from-above gap has a fixed contraction the from-below gap lacks: for $V\succeq0$, `eq:gap-ric` gives $\mathcal R(\Sigma_\infty + V) - \Sigma_\infty \preceq F_\infty V F_\infty'$, so above $\Sigma_\infty$ the gap rides the **fixed** strong loop $F_\infty$, Schur on $e_1\oplus a$ (`eq:Finf-spec`). The only unit-circle modes of $F_\infty$ are the marginal block, and there the upper trajectory's marginal covariance is driven to zero by observation — the one piece needing its own argument. We record it first.

<!-- lem:marginal -->
### Lemma (lem:marginal) — Extinction of the marginal block

Let C1 hold, let the marginal block be **forward power-bounded** — $c_m := \sup_{k\ge0}\|A_m^k\| < \infty$; in particular when the unit-circle marginal eigenvalues are semisimple — and let $\bar\Sigma_T := \mathcal R^T(\overline\Sigma_0)$ for **any** PSD prior $\overline\Sigma_0$. The marginal block is driven to zero,

<!-- eq:marg-zero -->
$$ \bar\Sigma_T\!\mid_{mm} \;\longrightarrow\; 0 \qquad (T\to\infty), \tag{eq:marg-zero} $$

for every prior directly — no comparison step and no positivity of any block is needed (consistent with $\Sigma_\infty\!\mid_{mm}=0$, `eq:marg-extinct`). No rate is claimed. **The defective-marginal case is OPEN**: the numerics support the same conclusion with Jordan-degraded rates, but no proof is currently on the page, and every downstream use carries the semisimple qualification. (The qualification is itself a verified sufficient condition: semisimple ⇒ both power bounds, `marg_powers_bounded`; the identified tool for the defective case is the verified linear Gramian floor `fact:gramian` — in-frame `marg_gramian_growth` — which supplies a lower bound where no power bound exists.)

*Proof.* No positivity is used anywhere (full positive-definiteness of $\bar\Sigma_T$ need **not** persist when $\ker A'\cap\ker G'\ne\{0\}$, and even the $e_2$-corner positivity is not needed). Track the **backward-transported uncontrollable columns**

<!-- eq:Ydef -->
$$ Y_T := \bar\Sigma_T\,E_2\,A_2^{-T\prime} \qquad (E_2 := \text{the } e_2\text{-inclusion}); \tag{eq:Ydef} $$

no information coordinates and no injected-information floor appear.

**(i) The output energy of $Y_T$ is summable.** For fixed $u$, the transported quadratic $\varphi_T(u) := (A_2^{-T\prime}u)'\,\bar\Sigma_T\!\mid_{22}\,(A_2^{-T\prime}u)$ steps by the $e_2$-block identity $\bar\Sigma_{T+1}\!\mid_{22} = A_2\,\mathcal U(\bar\Sigma_T)\!\mid_{22}\,A_2'$ (`app:machinery`-2) to $\varphi_{T+1}(u) = w'\,\mathcal U(\bar\Sigma_T)\!\mid_{22}\,w$ with $w := A_2^{-T\prime}u$. The variational form of the update — the Joseph square evaluated at the rank-one gain $K = \beta\,(E_2w)b'$ and minimized over $\beta$, cf. Part 2 of `lem:structure` — gives, for every output direction $b\ne0$,
$$ \varphi_{T+1}(u) \;\le\; \varphi_T(u) \;-\; \frac{\big(b'\,C\,Y_T\,u\big)^2}{b'S_Tb}, \qquad S_T := C\bar\Sigma_TC'+R \preceq \bar S \ \ (\text{`eq:bounded`}), $$
using $C\bar\Sigma_TE_2w = C\,Y_T\,u$. So $\varphi_T(u)$ is nonincreasing and, telescoping over $T$ and ranging $b,u$ over basis vectors,
$$ \sum_{T\ge0} \|C\,Y_T\|^2 \;<\; \infty. $$

**(ii) $Y_T$ rides the error map and dies.** The $e_2$-column identities ($A'E_2 = E_2A_2'$, $GQG'E_2 = 0$) give $\bar\Sigma_{T+1}E_2 = A\,\mathcal U(\bar\Sigma_T)E_2\,A_2'$, hence
$$ Y_{T+1} \;=\; A\,Y_T \;-\; AK_T\,(C\,Y_T), \qquad K_T := \bar\Sigma_TC'S_T^{-1}\ \text{bounded (`eq:bounded`, } S_T^{-1}\preceq R^{-1}). $$
Insert the stabilizing injection $L$ of C1 ($A-LC$ Schur, as in Part 2 of `lem:structure`): $Y_{T+1} = (A-LC)\,Y_T + E_T$ with $\|E_T\| \le c_E\,\|CY_T\|$ square-summable by (i). Unrolling against the geometric kernel of $A-LC$ (`fact:schur-decay`) and splitting each convolution at its midpoint (head: geometric decay against a bounded $\ell^2$-mass; tail: an $\ell^2$-tail against a summable kernel), $Y_T \to 0$.

**(iii) Power-boundedness closes.** Since $A_2 = A_a\oplus A_m$, the marginal columns of $Y_T$ are $\bar\Sigma_T E_m A_m^{-T\prime}$, so $\bar\Sigma_T\!\mid_{mm} = \big(E_m'\,\bar\Sigma_T E_m A_m^{-T\prime}\big)A_m^{T\prime}$ and
$$ \|\bar\Sigma_T\!\mid_{mm}\| \;\le\; \text{const}\cdot\|Y_T\|\cdot\|A_m^{T}\| \;\le\; \text{const}\cdot c_m\,\|Y_T\| \;\longrightarrow\; 0. $$
Only the *forward* powers of $A_m$ are ever bounded; the backward powers appear solely inside $Y_T$, which dies in norm regardless. ∎

**Remark (what changed and why).** An earlier version argued through the injected information: the $(m,m)$ block of `eq:Jrec` with a uniform windowed coercivity of the increments $\widehat W_T^{mm}$. That display windowed a *single* $\widehat W_T$ where the unrolled sum needs windows of *consecutive* increments, and its uniformity argument negated a uniform-in-$T$ bound into a single exact-zero vector — a hole (Lean verification finding 5). The present proof needs no information coordinates, no $\widehat W$-floor, and no `fact:gramian`/`fact:poly-growth`; the price is the power-bounded (semisimple) qualification, whose removal is the flagged open problem.

<!-- verify: LEAN (phase B): lem:marginal / eq:marg-zero = DareSystem.marg_block_norm_tendsto (Estimation/Dare/MarginalUpper.lean; engine: Variational.updM_quadForm_le_sub + Convolution.tendsto_zero_of_geometric_conv + margY_succ/margPhi_step/margY_output_entry_summable/margY_norm_tendsto). The Lean proved slightly MORE than first repaired (finding 8, adopted): any PSD prior, no corner positivity, no comparison step, forward power-boundedness only. Axioms clean. -->
<!-- verify: GATE-2 (scratch/check_marginal_route.py): phi_T(u) monotone nonincreasing EXACTLY (max violation 0.0); sum ||C Y_T||^2 converges (tail 1e-4/1e-6 at T=4000); ||Y_T|| -> 0; Sigma_T|mm -> 0 on both a semisimple rotation AND a defective Jordan block (numerics only for the latter — the proof covers power-bounded Am). Old-route checks (check_marg_coercive_uniform.py etc.) retired with the route. -->
<!-- verify: deps — app:machinery-2 (e2 (2,2)-identity and column identities), eq:A2-inv, eq:comparison, eq:bounded (uniform innovation bound + K_T bounded), C1 (via the stabilizing injection, as in lem:structure-2), fact:schur-decay, the Joseph variational square (lem:structure-2 mechanism), lem:structure-3 mechanism (corner positivity). fact:gramian / fact:poly-growth NO LONGER consumed here. eq:marg-extinct cited for consistency, not needed in-proof. CONSUMER: lem:supremal (marginal half), thm:sufficiency, 08 (all now carrying the semisimple qualification on the marginal branch). Confinement: MARGINAL branch, no C3w. -->

<!-- lem:supremal -->
### Lemma (lem:supremal) — The supremal upper bound converges to $\Sigma_\infty$

Let C1 hold, with semisimple marginal modes (`lem:marginal`), and fix any $\overline\Sigma_0 \succeq \Sigma_\infty$ (e.g. $\overline\Sigma_0 = cI$, $c$ large; no block-positivity of the prior is needed — `lem:marginal` runs from any PSD seed). The **supremal** trajectory $\bar\Sigma_T := \mathcal R^T(\overline\Sigma_0)$ dominates every trajectory below it and converges to the strong solution:

<!-- eq:above -->
$$ \mathcal R^T(\Sigma_0) \preceq \bar\Sigma_T \ \ (\Sigma_0\preceq\overline\Sigma_0) \qquad\text{and}\qquad \bar\Sigma_T \;\longrightarrow\; \Sigma_\infty, \tag{eq:above} $$

the antistable block reaching $\Sigma_\infty\!\mid_{aa}\succ0$ exponentially ($A_a^{-1}$ Schur, `eq:Sinf-gram`), the marginal block reaching $\Sigma_\infty\!\mid_{mm}=0$ (`lem:marginal`; no rate claimed there).

*Proof.* **Domination** is comparison (`eq:comparison`): $\Sigma_0\preceq\overline\Sigma_0 \Rightarrow \mathcal R^T(\Sigma_0)\preceq\mathcal R^T(\overline\Sigma_0)$.

**Convergence.** Let $\Delta_T := \bar\Sigma_T - \Sigma_\infty\succeq0$ ($\overline\Sigma_0\succeq\Sigma_\infty$, $\Sigma_\infty$ a fixed point, comparison). By `eq:gap-ric`, $\Delta_{T+1}\preceq F_\infty\Delta_T F_\infty'$. In the frame `eq:three-block` the only unit-circle modes of $F_\infty$ are the marginal block; $F_\infty$ is Schur on $e_1\oplus a$ (`eq:Finf-spec`: $A_c$ and the reflected $A_a^{-1}$), $\rho(F_\infty\!\mid_{e_1\oplus a})<1$.

*Marginal/cross.* $\Delta_T\!\mid_{mm} = \bar\Sigma_T\!\mid_{mm}\to0$ (`lem:marginal`, `eq:marg-zero`), and $\Delta_T\succeq0$ with `fact:schur` sends every marginal row/column to zero: $\|\Delta_T\!\mid_{m,\,e_1a}\|^2 \le \|\Delta_T\!\mid_{mm}\|\,\|\Delta_T\!\mid_{e_1a}\|\to0$ ($\Delta_T\!\mid_{e_1a}$ bounded, `eq:bounded`).

*Stabilizable–antistable.* Restricting `eq:gap-ric` to $e_1\oplus a$, $\Delta_{T+1}\!\mid_{e_1a}\preceq F_\infty\!\mid_{e_1\oplus a}\Delta_T\!\mid_{e_1a}F_\infty\!\mid_{e_1\oplus a}' + \Xi_T$, where $\Xi_T$ collects the marginal-routed terms (each carrying $\Delta_T\!\mid_{m,\,e_1a}$ or $\Delta_T\!\mid_{mm}$), so $\|\Xi_T\|\to0$. The Stein operator $\delta\mapsto F_\infty\!\mid_{e_1\oplus a}\delta F_\infty\!\mid_{e_1\oplus a}'$ has spectral radius $\rho(F_\infty\!\mid_{e_1\oplus a})^2<1$, so $\|F_\infty\!\mid_{e_1\oplus a}^{\,k}\|\le c\gamma^k$, $\gamma<1$ (`fact:schur-decay`); iterating the Löwner inequality and taking norms, $\|\Delta_T\!\mid_{e_1a}\| \le c^2\gamma^{2T}\|\Delta_0\!\mid_{e_1a}\| + \sum_{k<T}c^2\gamma^{2(T-1-k)}\|\Xi_k\|\to0$ (geometric kernel against a null sequence), closing the boundedness used above.

Both blocks vanish, so $\Delta_T\to0$, i.e. $\bar\Sigma_T\to\Sigma_\infty$: antistable exponentially (through the Schur $A_a^{-1}$, `eq:Sinf-gram`), marginal by `lem:marginal`. ∎

<!-- verify: LEAN (phase B): lem:supremal / eq:above convergence = DareSystem.supremal_tendsto (Estimation/Dare/Supremal.lean); domination = the existing dareIter_mono (eq:comparison). Engine: gapRic_le -> supremal_gap_step, restricted through the embS/embM partition of identity (conj_partition), marginal block killed by marg_block_norm_tendsto + strong_marg_extinct, cross blocks by entrywise PSD Cauchy-Schwarz (sq_dotProduct_mulVec_le), e1+a block by tendsto_zero_of_loewner_schur (Loewner unroll vs Schur powers + geometric-kernel convolution). eq:Finf-spec (F_inf|e1a Schur) enters as an explicit IsSchurStable hypothesis, mirroring its imported status in the deck. The Lean needed LESS than stated (finding 9, adopted): no barSig0|22 > 0 — any PSD prior >= Sinf. Axioms clean.. The IsSchurStable hypothesis (eq:Finf-spec on e1+a) is kept general in this lemma and discharged at every consumer by strong_Fs_schur (phase D, Estimation/Dare/Spectrum.lean) -->
<!-- verify: GATE-2 (check_dsgg_upper.py, seed barSig0=Sig0+Sinf >= Sinf): domination barSig_T >= Sig_T held all T<=20000 (min eig >= -1e-9); barSig_T -> Sinf; marginal block (barSig-Sinf)_mm ~ 1/T polynomial (log-log slope -0.95), antistable exp -- the marginal paces. Gap eq:gap-ric Delta_{T+1} <= F_inf Delta_T F_inf' throughout (riccastep check_dom.py, min eig >= -2e-11). -->
<!-- verify: deps — eq:comparison (domination), eq:gap-ric (from-above fixed-F_inf gap, a02-machinery), eq:Finf-spec (F_inf Schur on e1+a), fact:schur-decay (Stein rho^2<1), fact:schur (marginal rows via PSD), eq:bounded (Delta|e1a bounded), lem:marginal (eq:marg-zero), eq:Sinf-gram (antistable rate). CONSUMER: thm:sufficiency (eq:above, upper half of the squeeze). Confinement: does not read C3w (rho(F_inf)=1 with marginal present). PORT of riccastep 05-supremal-v3 Part 3; Parts 1-2 (eq:diff-id/eq:gap-ric) already in a02-machinery. -->
<!-- verify: CW correspondence — this is CW lem:supremal discrete (stablistep-handoff §1 "smallest CW deviation"): drop the monotone ceiling (no discrete analog, antistable amplification R(cI) can grow), keep the gap-to-Sigma_inf through the FIXED F_inf. NOT DSGG 4.2 (which gives convergence but no rate and breaks CW lineage); DSGG stays a fact:dare-strong citation. -->
<!-- END FILE: 03-supremal.md -->

<!-- BEGIN FILE: 04-evolution.md -->
<!-- 04-evolution — MAIN TEXT: the discrete J-transform on the slaved block. -->
<!-- This is arc2's core contribution — the discrete image of the Callier-Winkin J-transform — so it is a -->
<!-- main-text anchor lemma feeding the lower anchor 05-lowsqueeze, not an appendix result. -->
<!-- The rank-chart isolates the antistable information J_1 = (Sigma|aa)^{-1} from the rank-deficient -->
<!-- (marginal-slaved) e2-block; J_1 rides a FIXED A_a^{-1}-Stein recursion driven by a data source Xi_T. -->
<!-- Source-boundedness is the antistable-DARE floor, and it closes NON-CIRCULARLY via the conditional-filter -->
<!-- loading lem:condfilter: e_1 is conditionally FILTERED (its own isolated Kalman-Riccati), not slaved. -->
<!-- Discrete dual of CW app:evolution eq:Jsys/eq:J12-decay/eq:J1-limit; the second loading Lambda_1a has no -->
<!-- CW analog (CW's antistrong coordinates carry no stable block), and is exactly what this file must earn. -->
<!-- sec:evolution — main text -->
### The discrete $J$-transform (main text)

The lower anchor's evolution is read on a chart of the singular uncontrollable block: the antistable information plus two loadings. Two of the three pieces are slaved-block dynamics — the marginal loading `lem:loading` (this section) and the antistable information `lem:jtransform` — while the stabilizable loading `lem:condfilter` is the conditionally-filtered piece with no continuous-time analog. We first record the marginal slaving.

<!-- lem:loading -->
### Lemma (lem:loading) — Full marginal slaving and the loading dynamics

Seed the lower trajectory with the slaved $\underline\Sigma_0$ of `lem:slaved-seed` (`eq:Ldef-slaved`): its uncontrollable block is rank-$n_a$, antistable-supported, with $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_a\succ0$ (C2w) and marginal row slaved (`eq:seed-slaved`) by the seed loading $\Lambda_{ma,0}=\Sigma_{ma}\Sigma_{aa}^{-1}$. Define the **marginal loading** $\Lambda_{ma} := \underline\Sigma_T\!\mid_{ma}(\underline\Sigma_T\!\mid_{aa})^{-1}$ (well defined, $\underline\Sigma_T\!\mid_{aa}\succ0$ by `lem:structure`-3). Then for every $T\ge0$:

<!-- lem:loading-a -->
**(a) (Full row slaving.)** The whole marginal row is the antistable row scaled by the loading,

<!-- eq:row-slaved -->
$$ \underline\Sigma_T\!\mid_{m,:} = \Lambda_{ma}\,\underline\Sigma_T\!\mid_{a,:}, \tag{eq:row-slaved} $$

so $\underline\Sigma_T\!\mid_{mm}=\Lambda_{ma}\underline\Sigma_T\!\mid_{am}$, $\underline\Sigma_T\!\mid_{m1}=\Lambda_{ma}\underline\Sigma_T\!\mid_{a1}$ — the marginal carries no covariance independent of the antistable, in *any* block. The measurement update preserves it with the **same** loading, $\hat\Lambda_{ma}=\Lambda_{ma}$.

<!-- lem:loading-b -->
**(b) (Loading recursion and geometric decay.)** In the dynamics-decoupled frame `eq:three-block` ($A_{ma}=0$),

<!-- eq:loading-rec -->
$$ \Lambda_{ma}^+ = A_m\,\Lambda_{ma}\,A_a^{-1}, \tag{eq:loading-rec} $$

a Stein map with $\rho = \rho(A_m)\rho(A_a^{-1}) = \rho(A_a^{-1}) < 1$ (`eq:A2-inv`), so

<!-- eq:loading-conv -->
$$ \Lambda_{ma,T} \longrightarrow 0 \quad\text{geometrically at rate } \rho(A_a^{-1}). \tag{eq:loading-conv} $$

*Proof.* **(a),(b) by induction.** At $T=0$, `eq:seed-slaved` gives the base case. Assume `eq:row-slaved` at $T$. Since $(\Sigma C')\!\mid_{m,:}=\Lambda_{ma}(\Sigma C')\!\mid_{a,:}$, the update inherits it: $\mathcal U(\underline\Sigma_T)\!\mid_{m,:}=\Lambda_{ma}\,\mathcal U(\underline\Sigma_T)\!\mid_{a,:}$, i.e. $\hat\Lambda_{ma}=\Lambda_{ma}$. With $A\!\mid_{m,:}=[\,0\ A_m\ 0\,]$ (decoupled, $A_{ma}=0$), $A\!\mid_{a,:}=[\,0\ 0\ A_a\,]$, $G\!\mid_{m,:}=0$, prediction gives $\underline\Sigma_{T+1}\!\mid_{m,:}=A_m\,\mathcal U\!\mid_{m,:}\,A'=A_m\Lambda_{ma}\,\mathcal U\!\mid_{a,:}\,A'$ and $\underline\Sigma_{T+1}\!\mid_{a,:}=A_a\,\mathcal U\!\mid_{a,:}\,A'$, so $\underline\Sigma_{T+1}\!\mid_{m,:}=A_m\Lambda_{ma}A_a^{-1}\,\underline\Sigma_{T+1}\!\mid_{a,:}$ — this is `eq:row-slaved` at $T+1$ with the loading `eq:loading-rec`. The Stein spectrum is the product set $\{\mu\eta:\mu\in\operatorname{spec}(A_m),\eta\in\operatorname{spec}(A_a^{-1})\}$; every $|\mu|=1$, $|\eta|<1$, so $\rho<1$ and `eq:loading-conv` follows (`fact:schur-decay`; a defective marginal Jordan block contributes only a bounded polynomial factor absorbed into the rate, since $\rho(A_a^{-1})$ strictly dominates). ∎

**Remark (why the marginal does not obstruct the forgetting).** The marginal's whole contribution to $\underline\Sigma_T$ is the deterministic readout `eq:row-slaved` of the antistable block through $\Lambda_{ma}$; both factors converge geometrically (`eq:loading-conv` and `lem:jtransform`), so the marginal blocks converge *with* them at the antistable rate $\rho(A_a^{-1})$, never at the unit-circle rate of $A_m$ — the eigenvalues of $A_m$ enter only multiplied by $\rho(A_a^{-1})$. This is CW's $J_{12}$-decay (`eq:J12-decay`), discretized. **Condition hygiene:** uses only $\delta\Sigma_a\succ0$ (via `lem:structure`-3) and `eq:A2-inv`; no floor, no C3w.

<!-- verify: LEAN (phase B): lem:loading = RowSlaved + RowSlaved.updM (hatLam = Lam) + RowSlaved.dareStep (eq:loading-rec) + rowSlaved_dareIter (closed form Lam_T = Am^T Lam0 (Aa^-1)^T) + Aa_inv_isSchurStable + loading_tendsto (eq:loading-conv), Estimation/Dare/Loading.lean; base case = slavedSeed_slaved (SlavedSeed.lean). Matrix-row implementation of eq:row-slaved (embM' Sigma = Lam embA' Sigma). Axioms clean. -->
<!-- verify: (a) full-row slaving ||Sig|m,: - Lambda_ma Sig|a,:|| < 1.1e-14 incl. e1-marginal cross, T=1..11; hatLam_ma=Lambda_ma exact (check_full_slaving.py). (b) ||Lam_{T+1} - A_m Lam_T A_a^-1|| < 3e-15, T=0..9; ||Lam_ma|| -> 0 at ratio -> rho(A_a^-1) (check_loading_rec.py). Binding case (defective marginal Jordan / unit-circle A_m): rho unchanged = rho(A_m)rho(A_a^-1). PORT of riccastep 07-loading-v4 (decoupled-frame specialization A_ma=0). -->
<!-- verify: deps — a02-machinery (Rmap/U, the A|m,:=[0 A_m 0]/A|a,:=[0 0 A_a]/G no-e2-row structure of eq:three-block), eq:A2-inv, lem:structure-3 (Sig_T|aa>0), fact:schur-decay, lem:slaved-seed (eq:seed-slaved base case). CONSUMERS: lem:condfilter (hatLam_ma=Lambda_ma, Lambda_ma->0), lem:jtransform (Ceff convergence), 05-lowsqueeze (marginal half of the anchor). -->

The lower anchor stays slaved for all $T$ (`lem:loading`): its uncontrollable block $\underline\Sigma_T\!\mid_{22}$ is rank-$n_a$, supported on the antistable coordinates, with $\underline\Sigma_T\!\mid_{aa}\succ0$ (`lem:structure`-3, since $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_a\succ0$ under C2w). The full block is singular and cannot be inverted; instead **chart it by its full-rank antistable corner** — the antistable information and the two loadings

<!-- eq:jchart -->
$$ J_1 := (\underline\Sigma_T\!\mid_{aa})^{-1}, \qquad \Lambda_{ma} := \underline\Sigma_T\!\mid_{ma}(\underline\Sigma_T\!\mid_{aa})^{-1}, \qquad \Lambda_{1a} := \underline\Sigma_T\!\mid_{1a}(\underline\Sigma_T\!\mid_{aa})^{-1}, \tag{eq:jchart} $$

with the marginal recovered by slaving, $\underline\Sigma_T\!\mid_{mm} = \Lambda_{ma}\,\underline\Sigma_T\!\mid_{aa}\,\Lambda_{ma}'$. Invert only the antistable corner; carry the loadings separately. On this chart the antistable information rides a *fixed* $A_a^{-1}$-Stein recursion (`lem:jtransform`, the discrete image of the Callier–Winkin $J$-transform `eq:Jsys`), whose source is the measurement's antistable information increment. The marginal loading $\Lambda_{ma}$ decays autonomously (`lem:loading`, CW's $J_{12}$). The *second* loading $\Lambda_{1a}$ — the stabilizable block's regression onto the antistable — has no CW analog: it exists only because the strong (not antistrong) closed loop retains a stable block $A_c=e_1$, and controlling it is the one genuinely new step. It closes because **$e_1$ is not slaved but conditionally filtered**, `lem:condfilter`.

<!-- lem:condfilter -->
### Lemma (lem:condfilter) — The conditional-filter loading is bounded and homes

On the slaved lower trajectory, write the **conditional covariance** of $e_1$ given $e_a$,

<!-- eq:condcov -->
$$ P_T := \underline\Sigma_T\!\mid_{11} - \Lambda_{1a}\,\underline\Sigma_T\!\mid_{aa}\,\Lambda_{1a}' \;=\; \underline\Sigma_T\!\mid_{11} - \underline\Sigma_T\!\mid_{1a}(\underline\Sigma_T\!\mid_{aa})^{-1}\underline\Sigma_T\!\mid_{a1} \;\succeq\;0, \tag{eq:condcov} $$

and the conditional-filter gain and error map

<!-- eq:condgain -->
$$ K_T := P_T C_1'\big(R + C_1 P_T C_1'\big)^{-1}, \qquad L_T := A_1\big(I - K_T C_1\big). \tag{eq:condgain} $$

Then:

<!-- lem:condfilter-1 -->
**1. (The conditional covariance is an isolated $e_1$-filter, independent of the antistable scale.)** $P_T$ obeys the Kalman–Riccati recursion of the reduced system $(A_1, C_1, G_1)$,

<!-- eq:condric -->
$$ P_{T+1} = A_1\big(I - K_T C_1\big) P_T A_1' + G_1 Q G_1' \;=\; L_T P_T A_1' + G_1 Q G_1', \tag{eq:condric} $$

in which the antistable block $\underline\Sigma_T\!\mid_{aa}$ does not appear. By C1 (its restriction $(A_1,C_1)$ detectable) and $(A_1,G_1)$ stabilizable, $P_T\to P_\infty$, so $K_T$ is bounded, $L_T\to L_\infty$, and $\rho(L_\infty) < 1$ (`fact:schur-decay`): the transition products $\Phi_L(T,j) := L_{T-1}\cdots L_j$ are uniformly bounded, $\sup_{T\ge j}\|\Phi_L(T,j)\| \le c_L < \infty$.

<!-- lem:condfilter-2 -->
**2. (Loading recursion.)** The measurement sends the loading through the conditional error map, $\hat\Lambda_{1a} = (I - K_T C_1)\Lambda_{1a} - K_T(C_a + C_m\Lambda_{ma})$, and prediction closes it:

<!-- eq:cf-rec -->
$$ \Lambda_{1a}^+ = L_T\,\Lambda_{1a}\,A_a^{-1} + d_T, \qquad d_T := \big[\,A_{1a} + A_{1m}\Lambda_{ma} - A_1 K_T(C_a + C_m\Lambda_{ma})\,\big]A_a^{-1}. \tag{eq:cf-rec} $$

<!-- lem:condfilter-3 -->
**3. (Bounded, and homes.)** $\sup_{T\ge0}\|\Lambda_{1a,T}\| < \infty$, and $\Lambda_{1a,T}\to\Lambda_{1a}^\infty$, the unique fixed point of $\Lambda = L_\infty\Lambda A_a^{-1} + d_\infty$.

*Proof.*

**Part 1.** Slaving decomposes the covariance through the regression $(x_1, x_a, x_m) = M(e, x_a)$, $e := x_1 - \Lambda_{1a}x_a$, $x_m = \Lambda_{ma}x_a$, with $M = \big[\begin{smallmatrix} I & \Lambda_{1a} \\ 0 & I \\ 0 & \Lambda_{ma}\end{smallmatrix}\big]$ and $(e, x_a)$ uncorrelated of covariance $\operatorname{blkdiag}(P_T, \underline\Sigma_T\!\mid_{aa})$. Hence $C M = [\,C_1,\ C_{\mathrm{eff}}\,]$ with the **effective antistable observation**

<!-- eq:Ceff -->
$$ C_{\mathrm{eff}} := C_a + C_1\Lambda_{1a} + C_m\Lambda_{ma}, \tag{eq:Ceff} $$

so $C\underline\Sigma_T C' + R = C_1 P_T C_1' + C_{\mathrm{eff}}\,\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}' + R$. Conditioning on $x_a$, the measurement residual is $y - C_{\mathrm{eff}}x_a = C_1 e + v$ with $v\sim(0,R)$: the conditional part $e$ is observed through $(A_1, C_1)$ with noise $R$ alone. Its update is the Kalman contraction $\mathcal U_1(P) = (I - K_T C_1)P = P - P C_1'(C_1 P C_1' + R)^{-1}C_1 P$, and its one-step prediction is $A_1(\cdot)A_1' + G_1 Q G_1'$ ($x_a^+ = A_a x_a$ is deterministic given $x_a$, contributing no conditional covariance). Composing gives `eq:condric`, in which $\underline\Sigma_T\!\mid_{aa}$ is absent. The pair $(A_1, C_1)$ is detectable and $(A_1, G_1)$ stabilizable (C1, restricted to $e_1$), so `eq:condric` converges to the reduced stabilizing solution $P_\infty$ (`fact:dare-strong` on the reduced system), whose closed loop $L_\infty = A_1(I - K_\infty C_1)$ is Schur; $L_T\to L_\infty$ gives uniformly bounded products (`fact:schur-decay`).

**Part 2.** With $S := C\underline\Sigma_T C' + R$ and the slaving identities $\underline\Sigma_T\!\mid_{a\bullet}C' = \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'$, $\underline\Sigma_T\!\mid_{1\bullet}C' = P_T C_1' + \Lambda_{1a}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'$, the update blocks are
$$ \mathcal U(\underline\Sigma_T)\!\mid_{aa} = \big(I - \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\big)\underline\Sigma_T\!\mid_{aa}, \qquad \mathcal U(\underline\Sigma_T)\!\mid_{1a} = \big[\Lambda_{1a} - P_T C_1'S^{-1}C_{\mathrm{eff}} - \Lambda_{1a}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\big]\underline\Sigma_T\!\mid_{aa}. $$
Dividing and applying the push-through identity $S^{-1}C_{\mathrm{eff}}\big(I - \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\big)^{-1} = \tilde S^{-1}C_{\mathrm{eff}}$, where $\tilde S := S - C_{\mathrm{eff}}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}' = R + C_1 P_T C_1'$, collapses the post-update loading to
$$ \hat\Lambda_{1a} := \mathcal U(\underline\Sigma_T)\!\mid_{1a}\big(\mathcal U(\underline\Sigma_T)\!\mid_{aa}\big)^{-1} = \Lambda_{1a} - P_T C_1'\tilde S^{-1}C_{\mathrm{eff}} = \Lambda_{1a} - K_T C_{\mathrm{eff}} = (I - K_T C_1)\Lambda_{1a} - K_T(C_a + C_m\Lambda_{ma}), $$
the last step by `eq:Ceff`. The marginal row, being slaved, keeps its loading through the update, $\hat\Lambda_{ma} = \Lambda_{ma}$ (`lem:loading`, Part (a)). Feeding both post-update loadings through the cross-block prediction identity $\underline\Sigma_{T+1}\!\mid_{1a} = A_{1\bullet}\,\mathcal U(\underline\Sigma_T)\!\mid_{\bullet a}\,A_a'$ (valid since $GQG'\!\mid_{1a}=0$; the same identity that drives `lem:structure`-3 on the diagonal) and dividing by $\underline\Sigma_{T+1}\!\mid_{aa} = A_a\,\mathcal U(\underline\Sigma_T)\!\mid_{aa}\,A_a'$:
$$ \Lambda_{1a}^+ = \big(A_1\hat\Lambda_{1a} + A_{1a} + A_{1m}\hat\Lambda_{ma}\big)A_a^{-1} = A_1\big[(I - K_T C_1)\Lambda_{1a} - K_T(C_a + C_m\Lambda_{ma})\big]A_a^{-1} + \big(A_{1a} + A_{1m}\Lambda_{ma}\big)A_a^{-1}, $$
which regroups to `eq:cf-rec`.

**Part 3.** Unrolling `eq:cf-rec`,
$$ \Lambda_{1a,T} = \Phi_L(T,0)\,\Lambda_{1a,0}\,A_a^{-T} + \sum_{j=0}^{T-1}\Phi_L(T,j+1)\,d_j\,A_a^{-(T-1-j)}. $$
Each summand is bounded on the left by $\|\Phi_L\|\le c_L$ (Part 1) and on the right by $\|A_a^{-(T-1-j)}\|\le c_a\gamma^{\,T-1-j}$, $\gamma := \rho(A_a^{-1})+\epsilon < 1$ (`eq:A2-inv`, `fact:schur-decay`); the drive is bounded, $\|d_j\|\le \bar d < \infty$, since $\Lambda_{ma}\to0$ and $K_T$ is bounded (Part 1). Hence $\|\Lambda_{1a,T}\| \le c_L c_a\|\Lambda_{1a,0}\|\gamma^T + c_L c_a\bar d\sum_{k\ge0}\gamma^k < \infty$, uniformly in $T$ — a two-sided sandwich, decaying on **both** ends. (The per-step ratio $\hat\Lambda_{1a}/\Lambda_{1a}$ may be arbitrarily large; it is not the transition operator, $\Phi_L$ is.) For convergence, $L_T\to L_\infty$ and $d_T\to d_\infty := [A_{1a} - A_1 K_\infty C_a]A_a^{-1}$ (using $\Lambda_{ma}\to0$), and the limiting Stein operator $\Lambda\mapsto L_\infty\Lambda A_a^{-1}$ has spectral radius $\rho(L_\infty)\rho(A_a^{-1}) < 1$, so the asymptotically-autonomous recursion `eq:cf-rec` converges to its unique fixed point $\Lambda_{1a}^\infty = (I - L_\infty(\cdot)A_a^{-1})^{-1}d_\infty$. ∎

<!-- lem:jtransform -->
### Lemma (lem:jtransform) — Antistable information homes, floor-free

On the slaved lower trajectory, the antistable information $J_1 = (\underline\Sigma_T\!\mid_{aa})^{-1}$ obeys the fixed $A_a^{-1}$-Stein recursion

<!-- eq:J1-rec -->
$$ J_1^+ = A_a^{-1\prime}\big[\,J_1 + \Xi_T\,\big]A_a^{-1}, \qquad \Xi_T := \big(\mathcal U(\underline\Sigma_T)\!\mid_{aa}\big)^{-1} - (\underline\Sigma_T\!\mid_{aa})^{-1} = C_{\mathrm{eff}}'\,\tilde S^{-1}\,C_{\mathrm{eff}} \;\succeq\;0, \tag{eq:J1-rec} $$

with $C_{\mathrm{eff}}$ of `eq:Ceff` and $\tilde S = R + C_1 P_T C_1'$. The source is bounded and convergent, and

<!-- eq:J1-home -->
$$ \Lambda_{ma}\to0, \qquad \Lambda_{1a}\to\Lambda_{1a}^\infty, \qquad J_1 \longrightarrow (\Sigma_\infty\!\mid_{aa})^{-1} \quad\text{(exp. fast, floor-free).} \tag{eq:J1-home} $$

*Proof.* **The recursion.** The unconditional $(a,a)$-block identity (`app:machinery`-2, $GQG'\!\mid_{aa}=0$, $A_2 = A_a\oplus A_m$ block-diagonal) is $\underline\Sigma_{T+1}\!\mid_{aa} = A_a\,\mathcal U(\underline\Sigma_T)\!\mid_{aa}\,A_a'$; inverting (both sides $\succ0$ by `lem:structure`-3, $A_a$ nonsingular by `eq:A2-inv`) gives the first form of `eq:J1-rec`, with $\Xi_T = (\mathcal U(\underline\Sigma_T)\!\mid_{aa})^{-1} - (\underline\Sigma_T\!\mid_{aa})^{-1}\succeq0$ (the update contracts the block, `fact:update-kernel`). The closed form $\Xi_T = C_{\mathrm{eff}}'\tilde S^{-1}C_{\mathrm{eff}}$ is the Woodbury dual of the antistable update block computed in `lem:condfilter`-2. Writing $S := C\underline\Sigma_T C' + R$, that block is $\mathcal U(\underline\Sigma_T)\!\mid_{aa} = \underline\Sigma_T\!\mid_{aa} - \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\,\underline\Sigma_T\!\mid_{aa}$; the matrix-inversion lemma gives
$$ \big(\underline\Sigma_T\!\mid_{aa} - \underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'S^{-1}C_{\mathrm{eff}}\,\underline\Sigma_T\!\mid_{aa}\big)^{-1} = (\underline\Sigma_T\!\mid_{aa})^{-1} + C_{\mathrm{eff}}'\big(S - C_{\mathrm{eff}}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}'\big)^{-1}C_{\mathrm{eff}}, $$
and the reduced innovation $S - C_{\mathrm{eff}}\underline\Sigma_T\!\mid_{aa}\,C_{\mathrm{eff}}' = R + C_1 P_T C_1' = \tilde S$ (the $C_{\mathrm{eff}}\underline\Sigma_T\!\mid_{aa}C_{\mathrm{eff}}'$ terms cancel, `lem:condfilter`-1), so the increment is $\Xi_T = C_{\mathrm{eff}}'\tilde S^{-1}C_{\mathrm{eff}}$.

**Source-boundedness (the antistable floor).** $\tilde S = R + C_1 P_T C_1'\succeq R\succ0$ is bounded below, and bounded above since $P_T$ is bounded (`lem:condfilter`-1); $C_{\mathrm{eff}} = C_a + C_1\Lambda_{1a} + C_m\Lambda_{ma}$ is bounded since both loadings are (`lem:condfilter`-3, `lem:loading`). Hence $\sup_T\|\Xi_T\| < \infty$: the source is bounded with **no floor on $\underline\Sigma_T\!\mid_{aa}$ assumed** — the would-be circularity ($\Xi_T$ bounded $\iff\underline\Sigma_T\!\mid_{aa}$ floored) is broken because the loadings are controlled by the conditional filter, whose recursion `eq:condric` never reads $\underline\Sigma_T\!\mid_{aa}$.

**Homing.** Unrolling `eq:J1-rec` is `eq:Jgram` restricted to the antistable corner,
$$ J_{1,T} = \big(A_a^{-T}\big)'J_{1,0}\,A_a^{-T} + \sum_{j=0}^{T-1}\big(A_a^{-(T-1-j)}\big)'\,W_j\,A_a^{-(T-1-j)}, \qquad W_j := A_a^{-1\prime}\Xi_j A_a^{-1}\succeq0. $$
The seed term vanishes ($A_a^{-1}$ Schur, `eq:A2-inv`). By `lem:condfilter`-3 and `lem:loading` the loadings converge, so $C_{\mathrm{eff}}\to C_a + C_1\Lambda_{1a}^\infty$ and $\tilde S\to R + C_1 P_\infty C_1'$, whence $\Xi_T\to\Xi_\infty$ and $W_j\to W_\infty$; the gramian of a convergent source against the Schur weight $A_a^{-1}$ converges (exp. fast, dominated by $\gamma^{2(T-j)}$). The limit solves the Stein equation $J_1^\infty = A_a^{-1\prime}(J_1^\infty + \Xi_\infty)A_a^{-1}$. Its coefficients match those at the fixed point: $P_\infty$ and $\Lambda_{1a}^\infty$ are the unique fixed points of `eq:condric` and `eq:cf-rec`, which are also solved by the values $\Sigma_\infty\!\mid_{1|a}$ and $\Sigma_\infty\!\mid_{1a}(\Sigma_\infty\!\mid_{aa})^{-1}$ read off the strong solution (the DARE fixed point satisfies both recursions), so by uniqueness $\Xi_\infty = C_{\mathrm{eff}}(\Sigma_\infty)'\tilde S(\Sigma_\infty)^{-1}C_{\mathrm{eff}}(\Sigma_\infty)$ is the steady antistable increment at $\Sigma_\infty$. But $(\Sigma_\infty\!\mid_{aa})^{-1}$ solves that same Stein equation (`eq:Sinf-gram`, `lem:structure`-1 / `lem:structure-marg`), so by uniqueness of the Stein solution ($A_a^{-1}$ Schur) $J_1^\infty = (\Sigma_\infty\!\mid_{aa})^{-1}$, which is `eq:J1-home`. The rate is geometric, set by $\max\{\rho(A_a^{-1})^2,\ \rho(L_\infty),\ \rho(A_a^{-1})\}$ — all $<1$, no marginal eigenvalue among them: the marginal enters only through $\Lambda_{ma}$, and there $|\lambda(A_m)|=1$ is multiplied by $\rho(A_a^{-1})<1$ (`lem:loading`). ∎

<!-- verify: LEAN (phase B): lem:condfilter Parts 1-2 = the conditional-chart step (Estimation/Dare/CondChart.lean): the decomposition Sigma = e1 P e1' + V Saa V' (V = e1 Lam1a + eA + eM Lamma) is preserved by the measurement update (chart_updM, via the generic twoblock_update whose push-through identities inv_bracket/pushthrough/uhat_mul_inv_form are all consequences of S = Stil + Ceff Saa Ceff') and by prediction (chart_dareStep: P -> the ISOLATED reduced Riccati eq:condric in which Saa never appears — the non-circular foothold, verified by construction of redP; Lam1a -> eq:cf-rec via lamNext; Saa -> the (a,a)-identity). Part 3 = lowLam1a_tendsto (LowSqueeze.lean): gain/loop/drive continuity + the fixed point from strong_chart_fixed + lam_unroll against the transition products + the geometric-kernel convolution. The analytic import is DISCHARGED (phase D): the reduced fact:dare-strong is a theorem — redP_exists_stabilizing (Estimation/Dare/Reduced.lean: zero-seed monotone-bounded convergence via monotone_psd_tendsto + eq:bounded, fixed point via dareStep_diff, Schur loop via the one-step PBH-Stein fixed_point_schur, uniqueness) — with the limit identified as the strong chart component (redP_tendsto_infP, Estimation/Dare/ReducedFacts.lean) and the product bound proved geometric (redProdF_geometric via fact:uniexp's verified half). The exponential-rate qualifier is now VERIFIED (phase E): lowLam1a_geometric (Estimation/Dare/LowRate.lean; lam_unroll against the geometric products redProdF_geometric with Lipschitz drive errors + the geometric convolution geom_conv_le), riding redP_geometric (the exact two-seed factorization of the reduced Riccati). -->
<!-- verify: LEAN (phase B): lem:jtransform: eq:J1-rec = lowJ_rec (CondChart.lean; the Woodbury dual is uhat_inv_eq, U-hat^-1 = Saa^-1 + Ceff' Stil^-1 Ceff, proved from S = Stil + Ceff Saa Ceff' alone); source-boundedness/convergence = ceff_tendsto + redStilInv_tendsto (the R-floor via Loewner inversion — no Saa-floor anywhere); homing eq:J1-home = lowSaa_tendsto (LowSqueeze.lean): conj_unroll of the information error against the Schur Aa^-1 powers (rho = rho(Aa^-1)^2) + inversion continuity under the eq:bounded ceiling; the RATE is now verified (phase E): lowJ_geometric (kernel rho(Aa^-1)^2 exactly as displayed) + lowSaa_geometric (resolvent transfer; Estimation/Dare/LowRate.lean). Limit identification: instead of the deck's uniqueness-of-fixed-points prose, the Lean gives Sigma_inf its own chart (strong_decomp, zero marginal loading by eq:marg-extinct) and reads the fixed-point identities off chart extraction (strong_chart_fixed) — same content, constructive. Axioms clean. -->
<!-- verify: GATE-2 all recursions on the slaved trajectory, delta in {1, 1e-3, 1e-6}, and on 300-400 random 3-block C3w-marginal systems. -->
<!-- eq:J1-rec: J_1^+ = A_a^-T'[J_1 + Xi]A_a^-1 with Xi = (U|aa)^-1 - (Sig|aa)^-1, resid 0 exactly (the inverted (a,a)-identity); check_A_corrected.py, check_full_conv.py. -->
<!-- eq:condric: P_T = Sigma_{1|a} obeys the ISOLATED e1 Kalman-Riccati P^+ = A1(I-KC1)P A1' + G1QG1', NO Sigma_aa; resid 4e-16 (check_condfilter.py). Non-circular foothold. -->
<!-- eq:cf-rec: Lambda_1a^+ = A1(I-K_TC1)Lambda_1a A_a^-1 + d_T, resid 1e-16 (check_condfilter.py). Post-update hatLam_1a = Lam_1a - K Ceff (push-through), resid 1e-4 modulo conditioning across 300 random systems; the +K sign in the first-pass was wrong (check_condfilter2.py). -->
<!-- Boundedness: naive per-step ratio ||hatLam||/||Lam|| hits 206-457x on adversarial systems, but sup_T||Lambda_1a|| bounded (65.8 worst) via the stable product Phi_L; the ratio is NOT the transition operator (check_postupdate_loading.py, check_condfilter2.py). -->
<!-- ADVERSARIAL GATE (Call D, check_condfilter_adversarial.py): on the witness stablistep-handoff §3 NAMES (strong antistable<->e_1 running-prior correlation, weighted antistable obs), the NAIVE bound W_T <= Wbar:=A_a^{-'}C_a'R^{-1}C_a A_a^{-1} FAILS on ~all steps (599999 violations / 200 trials) — we are squarely in the §3 trap regime — yet lem:condfilter holds: worst sup_T||Lambda_1a||=14.5 bounded, min eig(Sigma_T|aa)=1.4e-2>0 floored, 200/200 converge. The floor is closed with the handoff's own discipline (adversarial, not benign, witness) satisfied. -->
<!-- Homing/identification: Lambda_1a, P=Sig_1|a, J_1=1/Saa all -> their values AT Sigma_inf (diffs 1e-6 at 400 steps), so J_1 -> (Sigma_inf|aa)^-1 the CORRECT limit (check_limits_match.py). rho(L_inf)=0.234<1, loading rate rho(L)rho(A_a^-1)=0.117. -->
<!-- verify: hypotheses/DAG. lem:condfilter: C1 (restricted (A1,C1) detectable), (A1,G1) stabilizable, app:machinery ((a,a) and (1,a) block identities via GQG'|1a=GQG'|aa=0), eq:A2-inv, lem:loading (Lambda_ma slaved, hatLam_ma=Lambda_ma, ->0), fact:dare-strong (reduced e1 stabilizing solution), fact:schur-decay. NO Sigma_aa-floor, NO C3w. lem:jtransform: app:machinery-2, eq:A2-inv, fact:update-kernel, lem:structure-3 (Sig_aa>0), lem:condfilter + lem:loading (source bdd/convergent), eq:Sinf-gram + lem:structure-1/lem:structure-marg (limit identification). CONSUMER: 05-lowsqueeze (antistable half of the lower anchor). Confinement: MARGINAL branch, does not read C3w. -->
<!-- verify: CW correspondence. eq:J1-rec = discrete dual of CW eq:Jsys (dot J_1 = -J_1 A_-1* - A_-1 J_1 + (B_1+J_12 B_2)(...)*), with A_a^{-1} <-> Hurwitz -A_-1, Xi_T = Ceff' Stil^-1 Ceff <-> the (B_1+J_12 B_2)(...)* input-Gram, Lambda_ma <-> J_12 (both autonomous, ->0). The EXTRA piece Lambda_1a (=> lem:condfilter) has NO CW analog: CW's antistrong coordinates carry no stable block, so its source has one loading; the discrete strong solution keeps A_c=e_1, forcing the second. -->
<!-- END FILE: 04-evolution.md -->

<!-- BEGIN FILE: 05-lowsqueeze.md -->
<!-- 05-lowsqueeze — Scylla, the lower anchor of the GAS squeeze. A universal (every-prior), C2w-tight, slaved -->
<!-- seed whose trajectory converges to the strong solution FLOOR-FREE. Two results: lem:slaved-seed (the seed, -->
<!-- ported from riccastep 06) and lem:lowsqueeze (the convergence, assembled on 04-evolution). The convergence -->
<!-- is the discrete dual of CW lem:lowsqueeze (eq:lowsqueeze): the rank-minimal slaved seed forgets geometrically, -->
<!-- with the marginal riding the antistable (lem:loading) and e_1 conditionally filtered (lem:condfilter). -->

<!-- lem:slaved-seed -->
### Lemma (lem:slaved-seed) — A C2w-tight, rank-minimal lower initial condition

Work in the frame `eq:three-block`, $\Sigma_0=\operatorname{blkdiag}(\Sigma_1,\Sigma_2)$, with $\Sigma_2=\big[\begin{smallmatrix}\Sigma_{aa}&\Sigma_{am}\\\Sigma_{am}'&\Sigma_{mm}\end{smallmatrix}\big]\succeq0$ and $\Sigma_a:=\Sigma_{aa}$. Let $S:=\Sigma_2/\Sigma_{aa}=\Sigma_{mm}-\Sigma_{am}'\Sigma_{aa}^{\dagger}\Sigma_{am}\succeq0$ be the **marginal** (generalized) Schur complement, and define the **slaved antistable part** and the **seed**

<!-- eq:Sig2a -->
$$ \Sigma_2^{(a)} := \Sigma_2 - \operatorname{blkdiag}(0,\,S) = \begin{bmatrix}\Sigma_{aa} & \Sigma_{aa}\Lambda_0'\\ \Lambda_0\Sigma_{aa} & \Lambda_0\Sigma_{aa}\Lambda_0'\end{bmatrix} = \begin{bmatrix}I\\ \Lambda_0\end{bmatrix}\Sigma_{aa}\begin{bmatrix}I & \Lambda_0'\end{bmatrix},\qquad \Lambda_0:=\Sigma_{am}'\Sigma_{aa}^{\dagger}=\Sigma_{ma}\Sigma_{aa}^{\dagger}, \tag{eq:Sig2a} $$

<!-- eq:Ldef-slaved -->
$$ \underline\Sigma_0 := \operatorname{blkdiag}\big(0_{e_1},\ \delta\,\Sigma_2^{(a)}\big), \qquad \delta\in(0,1]. \tag{eq:Ldef-slaved} $$

Then, **for every prior** $\Sigma_0$:

<!-- lem:slaved-seed-1 -->
**1. (Universal lower bound.)** $\underline\Sigma_0 \preceq \Sigma_0$, with no condition on $\Sigma_0$.

<!-- lem:slaved-seed-2 -->
**2. (C2w characterization.)** $\underline\Sigma_0\!\mid_{aa} = \delta\Sigma_a$, so the antistable block is nondegenerate iff C2w:

<!-- eq:Lc2w -->
$$ \underline\Sigma_0\!\mid_{aa} = \delta\Sigma_a \succ 0 \quad\iff\quad \text{C2w}. \tag{eq:Lc2w} $$

<!-- lem:slaved-seed-3 -->
**3. (Rank-minimal and slaved.)** $\Sigma_2^{(a)}$ has zero marginal Schur complement and $\operatorname{rank}\Sigma_2^{(a)}=\operatorname{rank}\Sigma_{aa}$; under C2w, $\operatorname{rank}(\underline\Sigma_0\!\mid_{22})=n_a$ and the seed is **slaved** with loading $\Lambda_0=\Sigma_{ma}\Sigma_{aa}^{-1}$,

<!-- eq:seed-slaved -->
$$ \underline\Sigma_0\!\mid_{m,:} = \Lambda_0\,\underline\Sigma_0\!\mid_{a,:}. \tag{eq:seed-slaved} $$

*Proof.* **Part 1.** For PSD $\Sigma_2$, $\operatorname{range}\Sigma_{am}\subseteq\operatorname{range}\Sigma_{aa}$, so $\Sigma_{aa}\Sigma_{aa}^\dagger\Sigma_{am}=\Sigma_{am}$ and `eq:Sig2a` holds with $\Sigma_2^{(a)}=\big[\begin{smallmatrix}I\\\Lambda_0\end{smallmatrix}\big]\Sigma_{aa}\big[\begin{smallmatrix}I&\Lambda_0'\end{smallmatrix}\big]\succeq0$ (`fact:schur`). Then $\Sigma_0-\underline\Sigma_0=\operatorname{blkdiag}(\Sigma_1,\ \Sigma_2-\delta\Sigma_2^{(a)})$ with $\Sigma_2-\delta\Sigma_2^{(a)}=(1-\delta)\Sigma_2^{(a)}+\operatorname{blkdiag}(0,S)\succeq0$ ($\Sigma_1\succeq0$, $\Sigma_2^{(a)}\succeq0$, $S\succeq0$, $1-\delta\ge0$) — for **every** $\Sigma_0$, no threshold. **Part 2.** By `eq:Sig2a`, $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_{aa}=\delta\Sigma_a$; by `eq:prior-pos`(b) ($\Sigma_a\succ0\iff$ C2w) this gives `eq:Lc2w`. **Part 3.** The outer factor $[I;\Lambda_0]$ has full column rank $n_a$, so $\operatorname{rank}\Sigma_2^{(a)}=\operatorname{rank}\Sigma_{aa}$; its marginal Schur complement is $\Lambda_0\Sigma_{aa}\Lambda_0'-(\Lambda_0\Sigma_{aa})\Sigma_{aa}^\dagger(\Sigma_{aa}\Lambda_0')=0$. Under C2w, $\Sigma_{aa}\succ0$, so $\Lambda_0=\Sigma_{ma}\Sigma_{aa}^{-1}$ and the marginal row $\underline\Sigma_0\!\mid_{m,:}=[\,0,\ \delta\Lambda_0\Sigma_{aa},\ \delta\Lambda_0\Sigma_{aa}\Lambda_0'\,]=\Lambda_0[\,0,\ \delta\Sigma_{aa},\ \delta\Sigma_{aa}\Lambda_0'\,]=\Lambda_0\,\underline\Sigma_0\!\mid_{a,:}$, which is `eq:seed-slaved`. ∎

**Remark (the seed that makes the anchor geometric).** The lower anchor must inject the *smallest* antistable prior information compatible with $\Sigma_0$ and nothing else. The full seed $\operatorname{blkdiag}(0,\delta\Sigma_2)$ injects the marginal Schur complement $\delta S$ as *independent* marginal covariance, drained only through the marginal's divergent $A_m^{-1}$-gramian at the polynomial $1/T$ rate. The slaved seed `eq:Ldef-slaved` removes exactly $S$ — leaving the rank-$n_a$ antistable-supported $\Sigma_2^{(a)}$ — so the marginal carries no covariance of its own at $T=0$, `lem:loading` holds it slaved for all $T$, and the anchor forgets geometrically. **Condition hygiene:** Parts 1, 3 use no condition; C2w enters only in Part 2; C3w not at all. **Pseudoinverse hygiene:** $\Sigma_{aa}^\dagger$ is notational — all three parts use only *some* loading $\Lambda_0$ with $\Sigma_{ma} = \Lambda_0\Sigma_{aa}$, which exists for every PSD $\Sigma_2$ (range inclusion $\operatorname{range}\Sigma_{am} \subseteq \operatorname{range}\Sigma_{aa}$); under C2w the loading is unique and equals $\Sigma_{ma}\Sigma_{aa}^{-1}$. *(Port of riccastep 06-slaved-seed-v2, arc-2 antistable-first frame.)*

<!-- lem:lowsqueeze -->
### Lemma (lem:lowsqueeze) — The universal, C2w-tight lower anchor converges, floor-free

Let C1 and C2w hold. For every prior $\Sigma_0$, the slaved lower trajectory $\underline\Sigma_T$ seeded at `eq:Ldef-slaved` satisfies

<!-- eq:lowsqueeze -->
$$ \underline\Sigma_0 \preceq \Sigma_0 \quad\Longrightarrow\quad \underline\Sigma_T \preceq \Sigma_T \ \ (T\ge0), \qquad\text{and}\qquad \underline\Sigma_T \longrightarrow \Sigma_\infty \quad\text{(exp. fast, floor-free).} \tag{eq:lowsqueeze} $$

*Proof.* **Domination.** $\underline\Sigma_0\preceq\Sigma_0$ for every prior (`lem:slaved-seed`-1); the recursion is monotone in the initial condition (`eq:comparison`), so $\underline\Sigma_T=\mathcal R^T(\underline\Sigma_0)\preceq\mathcal R^T(\Sigma_0)=\Sigma_T$ for all $T$.

**The anchor collapses to its $(1a)(1a)$ block.** Full-row slaving (`eq:row-slaved`) makes the marginal row a $\Lambda_{ma}$-readout of the antistable row, so the whole matrix is carried by its leading $e_1\oplus e_a$ block $\underline\Sigma_T^{ea}:=\underline\Sigma_T\!\mid_{(1a)(1a)}$:

<!-- eq:pi-collapse -->
$$ \underline\Sigma_T = \Pi_T\,\underline\Sigma_T^{ea}\,\Pi_T', \qquad \Pi_T := \begin{bmatrix} I_{n_1} & 0 \\ 0 & I_{n_a} \\ 0 & \Lambda_{ma} \end{bmatrix}, \tag{eq:pi-collapse} $$

as read off block by block from `eq:row-slaved` ($\underline\Sigma_T\!\mid_{1m}=\underline\Sigma_T\!\mid_{1a}\Lambda_{ma}'$, $\underline\Sigma_T\!\mid_{am}=\underline\Sigma_T\!\mid_{aa}\Lambda_{ma}'$, $\underline\Sigma_T\!\mid_{mm}=\Lambda_{ma}\underline\Sigma_T\!\mid_{aa}\Lambda_{ma}'$).

**The $(1a)(1a)$ block homes.** Its three sub-blocks converge, each to the corresponding block of $\Sigma_\infty$:
- *antistable:* $J_1\to(\Sigma_\infty\!\mid_{aa})^{-1}$ (`lem:jtransform`, `eq:J1-home`), so $\underline\Sigma_T\!\mid_{aa}=J_1^{-1}\to\Sigma_\infty\!\mid_{aa}$, floor-free;
- *cross:* $\underline\Sigma_T\!\mid_{1a}=\Lambda_{1a}\,\underline\Sigma_T\!\mid_{aa}\to\Lambda_{1a}^\infty\,\Sigma_\infty\!\mid_{aa}=\Sigma_\infty\!\mid_{1a}$ (`lem:condfilter`-3 and the line above);
- *stabilizable:* $\underline\Sigma_T\!\mid_{11}=P_T+\Lambda_{1a}\,\underline\Sigma_T\!\mid_{aa}\,\Lambda_{1a}'\to P_\infty+\Lambda_{1a}^\infty\,\Sigma_\infty\!\mid_{aa}\,\Lambda_{1a}^{\infty\prime}=\Sigma_\infty\!\mid_{11}$ (`eq:condcov`, `lem:condfilter`-1,3).

The three limits are the strong-solution blocks: $P_\infty$ and $\Lambda_{1a}^\infty$ are the unique fixed points of `eq:condric` and `eq:cf-rec`, which the values $\Sigma_\infty\!\mid_{1|a}$, $\Sigma_\infty\!\mid_{1a}(\Sigma_\infty\!\mid_{aa})^{-1}$ read off $\Sigma_\infty$ also satisfy, so they coincide (uniqueness, as in `lem:jtransform`). Hence $\underline\Sigma_T^{ea}\to\Sigma_\infty\!\mid_{(1a)(1a)}$.

**Assembly.** $\Lambda_{ma}\to0$ (`eq:loading-conv`), so $\Pi_T\to\Pi_\infty=[\,I_{n_1};\,I_{n_a};\,0\,]$, and by `eq:pi-collapse`
$$ \underline\Sigma_T = \Pi_T\,\underline\Sigma_T^{ea}\,\Pi_T' \longrightarrow \Pi_\infty\big(\Sigma_\infty\!\mid_{(1a)(1a)}\big)\Pi_\infty' = \operatorname{blkdiag}\big(\Sigma_\infty\!\mid_{(1a)(1a)},\,0\big) = \Sigma_\infty, $$
the last equality by marginal extinction $\Sigma_\infty\!\mid_{\cdot\,m}=0$ (`eq:marg-extinct`). Every constituent rate is $<1$ — antistable $\rho(A_a^{-1})^2$, loadings $\rho(A_a^{-1})$, conditional $\rho(L_\infty)$ — and **no marginal unit-circle eigenvalue appears** (the marginal enters only through $\Lambda_{ma}$, where $|\lambda(A_m)|=1$ is multiplied by $\rho(A_a^{-1})<1$); so the approach is exponential, and **floor-free**: no lower bound on $\underline\Sigma_T\!\mid_{aa}$ was used — its information is bounded above by the convergent $A_a^{-1}$-gramian of `lem:jtransform`, whose source is bounded by the conditional filter (`lem:condfilter`), not by any assumed floor. ∎

**Remark (C2w-tightness and the role in the squeeze).** The anchor is nondegenerate exactly under C2w (`eq:Lc2w`): if C2w fails, $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_a$ is singular and the antistable chart `eq:jchart` degenerates on the uninformed direction — the seed cannot inject the antistable information the strong solution demands, and attraction fails there (the necessity direction, treated separately). Paired with the dominating upper anchor (Charybdis, `lem:supremal`), `eq:lowsqueeze` is the lower half of the GAS squeeze $\underline\Sigma_T\preceq\Sigma_T\preceq\overline\Sigma_T$ (`thm:sufficiency`). This is the discrete dual of CW's exponentially-converging lower bound (`eq:lowsqueeze` of riccaflow): the rank-minimal slaved seed, the marginal riding the antistable, the geometric forgetting — with the one discrete addition that $e_1$ is conditionally filtered rather than folded into an antistrong block.

<!-- verify: LEAN (phase B): lem:slaved-seed = Estimation/Dare/SlavedSeed.lean: Part 1 = slavedSeed_le_Sig0 (via the conditional completed square Sig₂_quadForm_decomp and smar_posSemidef), Part 2 = slavedSeed_corner(_posDef) via the verified criterion_w, Part 3 = slavedSeed_slaved. The dagger-general form is now ALSO verified (phase E5): exists_loading — every PSD prior admits a loading Λ₀ with Σₘₐ = Λ₀Σₐₐ (the pseudoinverse is notational; existence by the normal-equation rank argument exists_loading_of_posSemidef: ker Σₐₐ ⊆ ker Σₐₘ' forces rank[Σₐₐ Σₐₘ] = rank Σₐₐ) — and the general seed slavedSeedOf Λ₀ δ satisfies all three parts with no C2w anywhere: slavedSeedOf_le_Sig0 (Part 1, every prior), slavedSeedOf_corner (Part 2), slavedSeedOf_slaved (Part 3, unconditional); slavedSeedOf_lam0 ties it to the C2w seed consumed downstream. lem:lowsqueeze = lowsqueeze_tendsto (LowSqueeze.lean): the trajectory rides the explicit chart (lowTraj_decomp — the Lean's implementation of eq:pi-collapse: the decomposition IS the Pi-collapse, with P_T the conditional block), all four data converge (redP -> P_inf, now a THEOREM: redP_tendsto_infP, phase D; Lam1a by lem:condfilter-3, Lamma -> 0 by lem:loading, Saa -> Sigma_inf|aa by lem:jtransform), and the assembly converges in norm. lowsqueeze_tendsto keeps ReducedImport as a general-lemma hypothesis, discharged at every consumer by reducedImport_holds (phase D, Estimation/Dare/ReducedFacts.lean). Domination = slavedSeed_le_Sig0 + dareIter_mono. The exponential-rate claim is now VERIFIED (phase E): lowsqueeze_geometric (Estimation/Dare/LowRate.lean) — all four chart data decay geometrically (redP_geometric, lowLam1a_geometric, lowLamma closed form, lowSaa_geometric) and the assembly carries the rate, marginal block included. Axioms clean. -->
<!-- verify: GATE-2. Pi_T collapse eq:pi-collapse: ||Pi_T Sig^ea Pi_T' - Sig_T|| < 3.8e-16 over delta in {1,1e-3,1e-6}, T=0..399 (check_pi_collapse.py). Full convergence ||Sig_T - Sig_inf|| -> 0 delta-independent, all blocks (check_full_conv.py, check_pi_collapse.py): Sig|11->1.22, Sig|1a->1.10, Sig|aa->13.85, Sig|mm->0. Domination Sigma0 - underSigma0 >= -1e-8 over 2000 random priors (lem:slaved-seed, check_slaved_seed.py). Block-limit identification -> values at Sigma_inf, diffs 1e-6 at T=400 (check_limits_match.py). -->
<!-- verify: hypotheses/DAG. lem:slaved-seed: fact:schur, eq:three-block + eq:prior-pos(b) (Sig_a>0<=>C2w). NO floor, NO C3w. lem:lowsqueeze: lem:slaved-seed (domination, seed), eq:comparison (monotone-in-IC), lem:loading (eq:row-slaved slaving, eq:loading-conv Lambda_ma->0), lem:jtransform (eq:J1-home antistable homes floor-free), lem:condfilter (eq:condcov/eq:condric/eq:cf-rec: P_T, Lambda_1a bounded/convergent), lem:structure-marg (eq:marg-extinct Sigma_inf|.m=0). CONSUMER: 06-sufficiency (lower half of the squeeze). -->
<!-- verify: CONFINEMENT — MARGINAL (GAS) branch. Does NOT read C3w. Floor-free: the antistable floor is EARNED (lem:jtransform source-boundedness via lem:condfilter), not assumed; the retired riccastep floors (eq:Jaa-bound/eq:Lfloor), lem:reduced-forget, omega-limit, lem:robust-with-floor are all DROPPED. Discrete dual of CW eq:lowsqueeze. -->
<!-- END FILE: 05-lowsqueeze.md -->

<!-- BEGIN FILE: 06-sufficiency.md -->
<!-- 06-sufficiency — the GAS squeeze: C1 + C2w => Sigma_T -> Sigma_inf from EVERY prior. A sandwich between -->
<!-- the two anchors, both attracted to Sigma_inf: upper = lem:supremal (Charybdis, from above, fixed F_inf), -->
<!-- lower = lem:lowsqueeze (Scylla, from below, the slaved J-transform, FLOOR-FREE). C2w enters in exactly -->
<!-- one place: the antistable seed of the lower anchor (eq:Lc2w). Cleaner than riccastep thm:sufficiency -->
<!-- (no omega-limit, no reduction lemma) because the lower anchor is the marginal-slaved lem:lowsqueeze. -->
<!-- sec:sufficiency — main text -->
<!-- thm:sufficiency -->
### Theorem (thm:sufficiency) — Sufficiency of C2w

Let C1 and C2w hold, with semisimple marginal modes when a marginal block is present (`lem:marginal`; the defective case is open). Then the recursion is attracted to the strong solution from **every** prior $\Sigma_0$: $\Sigma_T \to \Sigma_\infty$ — at a geometric rate when C3w also holds; no rate is claimed in the marginal case.

*Proof.* A squeeze between two initial conditions, both attracted to $\Sigma_\infty$.

**The two anchors.** Take $\overline\Sigma_0 = \Sigma_0 + \Sigma_\infty$ — manifestly $\succeq \Sigma_0$ and $\succeq \Sigma_\infty$, with no threshold to choose — and let $\underline\Sigma_0$ be the slaved seed `eq:Ldef-slaved` (any $\delta\in(0,1]$). By `lem:slaved-seed`-1, $\underline\Sigma_0\preceq\Sigma_0$; by construction $\Sigma_0\preceq\overline\Sigma_0$; so the prior is framed,

<!-- eq:framed -->
$$ \underline\Sigma_0 \;\preceq\; \Sigma_0 \;\preceq\; \overline\Sigma_0. \tag{eq:framed} $$

Comparison (`eq:comparison`) propagates `eq:framed` to every horizon,

<!-- eq:squeeze -->
$$ \underline\Sigma_T \;\preceq\; \Sigma_T \;\preceq\; \overline\Sigma_T \qquad T\ge0. \tag{eq:squeeze} $$

**Both anchors converge to $\Sigma_\infty$.** The upper trajectory converges by `lem:supremal` (`eq:above`), $\overline\Sigma_T\to\Sigma_\infty$, using only $\overline\Sigma_0\succeq\Sigma_\infty$ and C1. The lower trajectory converges by `lem:lowsqueeze` (`eq:lowsqueeze`), $\underline\Sigma_T\to\Sigma_\infty$, **floor-free** — this is where C2w enters: by `lem:slaved-seed`-2 (`eq:Lc2w`), C2w is exactly the nondegeneracy $\underline\Sigma_0\!\mid_{aa}=\delta\Sigma_a\succ0$ of the antistable seed, which the discrete $J$-transform (`lem:jtransform`) then carries to $\Sigma_\infty\!\mid_{aa}\succ0$ without any assumed floor, the marginal riding the antistable (`lem:loading`).

**Squeeze.** Both bounds in `eq:squeeze` converge to the *same* fixed point $\Sigma_\infty$ — the unique strong solution (`fact:dare-strong`) — so $\Sigma_T\to\Sigma_\infty$. No separate limit identification is needed: each anchor converges *to $\Sigma_\infty$* by construction.

**Rate.** Under C3w there is no marginal block: $F_\infty$ is Schur outright (`eq:Finf-c3w`; classically $A_c$ and the reflected $A_a^{-1}$), the from-above gap (`eq:gap-ric`) and the from-below anchor (`lem:jtransform`, rate $\max\{\rho(A_a^{-1})^2,\rho(L_\infty)\}$) both contract geometrically, and $\Sigma_T\to\Sigma_\infty$ at the geometric rate. Otherwise the marginal block is present and converges by `lem:marginal` with no rate claimed (the previously asserted polynomial rate rested on `lem:marginal`'s retired route; the numerics show $\sim 1/T$). ∎

**Remark (the squeeze block by block).** The **antistable** block is held *above* collapse by the nondegenerate C2w seed forgotten through $A_a^{-1}$ (`lem:jtransform`, source-bounded by the conditional filter `lem:condfilter`, not by an assumed floor) and *below* $\Sigma_\infty\!\mid_{aa}$ by the upper trajectory's convergence from above (`eq:above`); the **marginal** block is driven to zero by unbounded observation information from above (`eq:marg-zero`) and rides the antistable from below (`lem:loading`); the **stabilizable** block follows the Schur closed loop $A_c$ from above and its conditional filter from below (`lem:condfilter`). C2w enters in exactly one place — making the antistable prior seed nondegenerate (`eq:Lc2w`) so the forgetting can take over. Drop C2w and the lower anchor loses its antistable seed; the run is no longer pinned from below, and indeed fails to converge (`thm:necessity`). This is cleaner than the marginal-zero route: because the lower anchor's marginal is *slaved* (`lem:lowsqueeze`), the squeeze needs no omega-limit and no reduction lemma.

<!-- verify: LEAN (phase B): thm:sufficiency = DareSystem.sufficiency_tendsto (Estimation/Dare/Sufficiency.lean): the framing eq:framed/eq:squeeze via dareIter_mono, both anchors verified (supremal_tendsto with seed Sig0 + Sigma_inf per finding 10, lowsqueeze_tendsto with delta = 1), and the Loewner sandwich carried to the norm by polarization (symm_norm_le_of_abs_quadForm_le). Hypotheses = C1 + C2w + the power-bounded marginal — the ONLY remaining import besides IsStrongSolution existence (phase D4): eq:Finf-spec is discharged by strong_Fs_schur (Spectrum.lean) and the ReducedImport by reducedImport_holds (ReducedFacts.lean; redP -> infP identified through fixed_point_schur + uniqueness, products geometric via fact:uniexp's verified half). The C3w rate refinement is VERIFIED (phase E): sufficiency_geometric (Estimation/Dare/MainRate.lean) — exactly the Rate paragraph's squeeze: the from-above gap contracts under the Schur strong loop (supremal_geometric via eq:gap-ric/loewner_iter and eq:Finf-c3w), the from-below anchor by lowsqueeze_geometric, glued by the polarization sandwich (dare_sandwich_norm). Axioms clean. -->
<!-- verify: GATE-2. Full squeeze eq:squeeze with both anchors -> Sigma_inf, end to end: underSig_T <= Sig_T <= barSig_T all T, all -> Sigma_inf, delta-independent (check_pi_collapse.py lower, check_dsgg_upper.py upper, domination min eig >= -1e-9). Under C2w holds => convergence; C2w fails => stuck (thm:necessity side). -->
<!-- verify: deps — eq:comparison (propagate framing), lem:slaved-seed-1 (underSig0 <= Sig0), lem:slaved-seed-2 (eq:Lc2w, C2w = antistable seed nondegenerate), lem:supremal (eq:above upper anchor), lem:lowsqueeze (eq:lowsqueeze lower anchor, floor-free), lem:jtransform/lem:condfilter/lem:loading (the lower-anchor engine + rate), fact:dare-strong (unique Sigma_inf), eq:Finf-spec + lem:marginal + fact:gramian/fact:poly-growth (rate). CONSUMER: thm:main (Part 1, with thm:necessity). -->
<!-- verify: CONFINEMENT — C2w is the strong-solution frontier (Part 1). C3w/geometric is only the rate refinement here; the exponential/GES theory is thm:main Part 2 (the verified arc1 layer). The lower anchor is FLOOR-FREE: no eq:Jaa-bound/eq:Lfloor, no lem:reduced-forget, no omega-limit -- retired. Discrete dual of CW's finite-horizon squeeze. -->
<!-- END FILE: 06-sufficiency.md -->

<!-- BEGIN FILE: 07-necessity.md -->
<!-- 07-necessity — Tiresias. C2w is NECESSARY for attraction to the strong solution. -->
<!-- Crux: an antistable-uncontrollable direction the prior already knows exactly stays known forever; -->
<!-- its zero-covariance direction is merely rotated by A_2^{-1}, so the antistable block stays singular -->
<!-- while Sigma_inf|aa > 0. Uses C1 only; no controllability, no squeeze. Port of riccastep 03-necessity-v2. -->
<!-- sec:necessity — main text -->
<!-- thm:necessity -->
### Theorem (thm:necessity) — Necessity of C2w

Let C1 hold. If the recursion `eq:cov-rec` is attracted to the strong solution, $\Sigma_T\to\Sigma_\infty$, then C2w holds:

<!-- eq:necessity -->
$$ \ker\Sigma_0 \cap \mathcal X_{a,uc}(A,G) = \{0\}. \tag{eq:necessity} $$

*Proof.* The contrapositive. Suppose C2w fails: there is $v\ne0$ in $\ker\Sigma_0\cap\mathcal X_{a,uc}$. In the frame `eq:three-block`, $\mathcal X_{a,uc}$ is the antistable coordinate block, so $v$ is an $e_a$-vector with $v\in\ker\Sigma_2$ (`eq:prior-pos`), hence $v\in\ker(\Sigma_0\!\mid_{22})$.

**Image confinement by $A_2$.** By `app:machinery`-2, $\Sigma_{T+1}\!\mid_{22} = A_2\,\mathcal U(\Sigma_T)\!\mid_{22}\,A_2'$. The update never increases the covariance, $\mathcal U(\Sigma)\preceq\Sigma$, so $\mathcal U(\Sigma_T)\!\mid_{22}\preceq\Sigma_T\!\mid_{22}$; a smaller PSD matrix has the larger kernel, so $\operatorname{im}\mathcal U(\Sigma_T)\!\mid_{22}\subseteq\operatorname{im}\Sigma_T\!\mid_{22}$. Therefore $\operatorname{im}\Sigma_{T+1}\!\mid_{22} = A_2\operatorname{im}\mathcal U(\Sigma_T)\!\mid_{22} \subseteq A_2\operatorname{im}\Sigma_T\!\mid_{22}$, and unrolling from $\Sigma_0\!\mid_{22}=\Sigma_2$,

<!-- eq:image-shadow -->
$$ \operatorname{im}\Sigma_T\!\mid_{22} \subseteq A_2^{\,T}\operatorname{im}\Sigma_2 \qquad T\ge0. \tag{eq:image-shadow} $$

**A persistent kernel direction.** Taking orthogonal complements, $\ker\Sigma_T\!\mid_{22}\supseteq(A_2')^{-T}\ker\Sigma_2$. Since $v\in\ker\Sigma_2$ and $A_2$ is nonsingular (`eq:A2-inv`),
$$ w_T := (A_2')^{-T}v = (A_a')^{-T}v \ne 0, \qquad w_T\in\ker\Sigma_T\!\mid_{22} $$
($A_2' = A_a'\oplus A_m'$ keeps $w_T$ antistable, as $v$ is an $e_a$-vector). Embedding $w_T$ by zero on $e_1$, $w_T'\Sigma_T w_T = w_T'(\Sigma_T\!\mid_{22})w_T = 0$ for every $T$.

**No convergence.** By `lem:structure-marg` (equally `lem:structure`-1), the strong solution is positive definite on the antistable block, $\Sigma_\infty\!\mid_{aa}\succ0$. Normalizing $\hat w_T := w_T/\|w_T\|$ — an antistable unit vector — gives $\hat w_T'\Sigma_\infty\hat w_T \ge \lambda_{\min}(\Sigma_\infty\!\mid_{aa})>0$ while $\hat w_T'\Sigma_T\hat w_T = 0$. Hence
$$ \|\Sigma_T - \Sigma_\infty\| \ge \hat w_T'(\Sigma_\infty - \Sigma_T)\hat w_T = \hat w_T'\Sigma_\infty\hat w_T \ge \lambda_{\min}(\Sigma_\infty\!\mid_{aa}) > 0 $$
for all $T$, so $\Sigma_T\not\to\Sigma_\infty$ — contradicting the hypothesis, and proving `eq:necessity`. ∎

**Remark (the mechanism).** A purely antistable, uncontrollable direction $v$ the prior already knows exactly ($v\in\ker\Sigma_0$) stays known exactly forever: uncontrollable, so no process noise injects fresh uncertainty; a measurement update only removes covariance. Its zero-covariance direction is merely rotated by $A_2^{-1}$ each step (`eq:image-shadow`), so the antistable block of $\Sigma_T$ stays singular while $\Sigma_\infty\!\mid_{aa}\succ0$ is full — the gap cannot close. C2w is exactly the demand that the prior leave no such direction; it is the mirror of the lower anchor, where the C2w seed is what the $J$-transform needs to floor the antistable block (`lem:criterion-w`, `lem:lowsqueeze`).

<!-- verify: GATE-2 (riccastep check_necessity.py check 8): C2w fails (Sigma_a singular) => ||Sigma_T - Sigma_inf|| stuck at 3.1e2, min eig(Sigma_T|aa)=0 all T; C2w holds => converges 2e-12. Uses C1 only (Sigma_inf existence + Sigma_inf|aa>0 via lem:structure-marg/lem:structure-1); image confinement elementary (U<=Sigma, A2 nonsingular eq:A2-inv). The kernel direction w_T=(A2')^{-T}v is nonzero and antistable (e_a-block A2'-invariant), so hat w_T'Sigma_inf hat w_T >= lambda_min(Sigma_inf|aa) is legitimate. -->
<!-- verify: deps — eq:cov-rec, eq:three-block, eq:prior-pos (X_{a,uc}=e_a block, ker Sigma_2), app:machinery-2, eq:A2-inv, lem:structure-marg (Sigma_inf|aa>0, marginal-inclusive). No controllability, no squeeze, no C3w. CONSUMER: thm:main (Part 1, with thm:sufficiency). PORT of riccastep 03-necessity-v2. -->
<!-- verify: LEAN (phase B): thm:necessity / eq:necessity = DareSystem.necessity (Estimation/Dare/Necessity.lean). Same mechanism, quadratic-form implementation: instead of image confinement + orthogonal complements, the phi-quadratic along the backward-transported witness w_T = (Aa')^{-T}v is shown nonincreasing from zero (dare_quadForm_transported_eq_zero, via margPhi_step + update contraction), which is the persistent-kernel statement in quadForm language; the floor is strong_corner_posDef + quadForm_le_card_norm. Hypotheses even weaker than the deck's: no C1 — IsStrongSolution Sinf is hypothesized directly (C1's only role here is Sigma_inf's existence). Axioms clean. -->
<!-- END FILE: 07-necessity.md -->

<!-- BEGIN FILE: 08-main.md -->
<!-- 08-main — Ithaca. The strong/stabilizing dichotomy: necessity + sufficiency (Part 1), and the C3w -->
<!-- refinement to the stabilizing/exponential regime (Part 2). Part 2 is SELF-CONTAINED (rate + poly-rate -->
<!-- contradiction), not an external import; the fuller GES/uniform-exponential theory is the companion -->
<!-- (arc1 / the exponential deck), cited there for the detailed rate. Port of riccastep 12-main-v4. -->
<!-- sec:main — main text -->
<!-- thm:main -->
### Theorem (thm:main) — The strong/stabilizing dichotomy

Let C1 hold. By `lem:structure-marg` the strong error map $F_\infty$ has spectrum `eq:Finf-spec` — Schur on the $e_1\oplus a$ compression, and the marginal spectrum $\operatorname{spec}(A_m)$ unmoved on the unit circle (classically the Schur part is $\operatorname{spec}(A_c)$ together with the reflected antistable spectrum $\{\lambda^{-1}:\lambda\in\operatorname{spec}(A_a)\}$ — `fact:dare-strong`'s pencil statement). Consequently:

<!-- thm:main-1 -->
**1. (Strong attraction.)**

<!-- eq:main-strong -->
$$ \text{C1} + \text{C2w} \quad\iff\quad \Sigma_T \to \Sigma_\infty \quad\big(\rho(F_\infty)\le1\big). \tag{eq:main-strong} $$

(The $\Leftarrow$ direction carries `lem:marginal`'s standing qualification: marginal modes semisimple; the defective case is open. The qualification is verified as sufficient — semisimple ⇒ power-bounded, `marg_powers_bounded` — so the theorem also lands with this wording: `main_strong_attraction_semisimple`, `main_marg_not_exponential_semisimple`.)

<!-- thm:main-2 -->
**2. (Stabilizing/exponential refinement.)** Under C1,

<!-- eq:main-stab -->
$$ \text{C3w} \quad\iff\quad \big(\Sigma_T \to \Sigma_\infty \ \text{exponentially from every prior satisfying C2}\big) \quad\big(\rho(F_\infty)<1\big). \tag{eq:main-stab} $$

The quantifier over priors is essential and cannot be dropped: for a **fixed** prior, exponential convergence does *not* imply C3w (see the Remark below). Under C3w there is no marginal block, so C2 $\iff$ C2w and the C2 on the right is the natural strong-attraction condition.

*Proof.*

**Spectrum.** $F_\infty = A(I - \Sigma_\infty C'(C\Sigma_\infty C'+R)^{-1}C)$ is block upper-triangular for the $(e_1\oplus a\,|\,m)$ split — not by the frame alone but by **extinction**: $\Sigma_\infty\!\mid_{m\,\cdot}=0$ zeroes the marginal rows of the gain, so the $m$-rows of $F_\infty$ are $[\,0\ 0\ A_m\,]$ (the $e_1\,|\,a$ coupling, by contrast, survives — the antistable rows couple back through the gain, which is why the $e_1$-diagonal block of $F_\infty$ is *not* a spectral part). On the antistable block $\Sigma_\infty\!\mid_{aa}\succ0$ with information the $A_a^{-1}$-gramian (`eq:Sinf-gram`), and the whole $e_1\oplus a$ compression of $F_\infty$ is Schur by the one-step PBH–Stein argument of `lem:structure-marg` (at $|\mu| = 1$ the transported Stein identity forces a left eigenvector of $A$ unexcited by $G$, killed by stabilizability and antistability; $|\mu| > 1$ embeds through the block-triangular invariance against $\rho(F_\infty)\le1$); on the marginal block $\Sigma_\infty\!\mid_{mm}=0$ (`eq:marg-extinct`), the mode is estimated exactly, the gain is zero, and $F_\infty$ leaves it as $A_m$ on the unit circle. Hence `eq:Finf-spec`, and $\rho(F_\infty)<1$ iff there is no marginal block, i.e. iff C3w.

**Part 1.** ($\Leftarrow$) is `thm:sufficiency`; ($\Rightarrow$) is `thm:necessity`. By `fact:dare-strong`/`def:strong`, $\rho(F_\infty)\le1$.

**Part 2.** ($\Rightarrow$) Assume C3w and take any C2 prior. The marginal block is absent, $\mathcal X_{u,uc}=\mathcal X_{a,uc}$, C2 $\iff$ C2w (`eq:prior-pos`); by Part 1, $\Sigma_T\to\Sigma_\infty$, and by `thm:sufficiency`'s rate paragraph the approach is geometric — both squeeze anchors contract under the Schur strong loop (`eq:Finf-c3w`), with no marginal block to slow them. By the spectrum, $\rho(F_\infty)<1$ — the stabilizing solution.

($\Leftarrow$) Suppose a marginal block is present ($\neg$C3w); we exhibit a C2 prior whose run is not exponentially attracted — the **marginal rate obstruction**. Take $\Sigma_0 := \Sigma_\infty + E_m E_m'$ ($E_m$ the marginal inclusion): its uncontrollable corner is $\operatorname{blkdiag}(\Sigma_\infty\!\mid_{aa}, I)\succ0$ (`lem:structure-marg`, `eq:marg-extinct`), so C2 holds. Along the **exact** from-above gap recursion `eq:gap-ric`, $\Delta_{T+1} = F_\infty(\Delta_T - \Delta_T C'S_{\Delta_T}^{-1}C\Delta_T)F_\infty'$, track the transported marginal energy $\varphi_T := y_T'\Delta_T y_T$, $y_T := E_m A_m^{-T\prime}u$ — a legitimate transport because the strong gain vanishes on the extinct marginal, $E_m'F_\infty = A_m E_m'$. The loss per step is the $S^{-1}$-energy of $C\Delta_T y_T$, and Cauchy–Schwarz in $\Delta_T$ bounds it by $c\,\|\Delta_T\|\,\varphi_T$ with $c$ a system constant: $\varphi$ is nonincreasing and $\varphi_T \ge \varphi_0\big(1 - c\sum_{j<T}\|\Delta_j\|\big)$. Now scale the seed: for $\varepsilon\in(0,1]$ the run from $\Sigma_\infty + \varepsilon E_mE_m'$ has $\Delta_j(\varepsilon)\preceq\Delta_j(1)$ (comparison) and $\Delta_j(\varepsilon)\preceq \varepsilon\,F_\infty^j E_mE_m'F_\infty^{j\prime}$ (iterated `eq:gap-ric`). If the $\varepsilon=1$ run were exponential, $\|\Delta_j(1)\|\le C\rho^j$, split the loss at a horizon $J$ with the geometric tail $< 1/4$ and shrink $\varepsilon$ until the finite head is $< 1/4$: then $\varphi_T(\varepsilon) \ge \varphi_0(\varepsilon)/2 = \varepsilon\|u\|^2/2 > 0$ for all $T$, while $\varphi_T(\varepsilon) \le \mathrm{const}\cdot\|\Delta_T(1)\|\to0$ — contradiction. So no run from this seed family is exponential, refuting the right side. With C3w established for the converse direction, $\rho(F_\infty)<1$ follows from the spectrum. (The semisimple qualification enters through the bounded backward marginal powers $\|A_m^{-T}\|$.) ∎

**Remark (why the quantifier is necessary — the exactly-known marginal).** For a fixed prior, exponential convergence does **not** force C3w: take any prior whose marginal rows vanish, $E_m'\Sigma_0 = 0$ — the marginal component known exactly. The recursion preserves zero marginal rows (the update acts on rows from the right, prediction multiplies by $A_m$ and adds no `e₂` noise), so the run coincides with the run of the marginal-free `e₁⊕a` subsystem, which converges exponentially under its own C2w+C3w — despite $n_m>0$. The obstruction of the converse is thus genuinely a property of priors that *inform* the marginal block, and `eq:main-stab` quantifies accordingly. (An earlier draft asserted the per-prior converse via a polynomial rate floor from the retired `lem:marginal` route; that statement was false as written — Lean verification finding 7, now resolved by the repaired statement above.)

**Remark (the two regimes).** C2w is the exact frontier of attraction to the strong solution: it asks only that the prior inform every **antistable** uncontrollable direction (`lem:criterion-w`). Marginal uncontrollable directions need not be informed — their covariance is driven to zero by the unbounded information of a persistent observed mode (`lem:marginal`) — but they survive in $F_\infty$ on the unit circle and slow the approach to a polynomial rate. Removing them (C3w) collapses C2w to C2, reflects the entire uncontrollable-unstable spectrum strictly inside the disk, and restores the exponential, stabilizing regime. Both regimes are settled here, floor-free — the GAS branch (polynomial, marginal-inclusive) and the GES branch (exponential, C3w) — and both transfer to the estimator in `thm:payoff`.

<!-- verify: LEAN (phase B): thm:main Part 1 / eq:main-strong = DareSystem.strong_attraction_iff_C2w (Estimation/Dare/Sufficiency.lean): attraction to the strong solution IFF C2w, under C1 with the power-bounded marginal as the sole remaining hypothesis-import for <= (the => direction needs none — necessity works from IsStrongSolution alone); ReducedImport is now a theorem (reducedImport_holds, phase D) and no longer appears in the signature. eq:Finf-spec is a THEOREM (phase D): strong_Fs_schur + strong_spec_split + strong_exists_unit_eigenvalue (Estimation/Dare/Spectrum.lean); eq:Finf-c3w = strong_isSchurStable_iff_C3w (Main.lean). ASSEMBLED FORM (phase D close): DareSystem.main_strong_attraction (Estimation/Dare/Main.lean) states Part 1 with existence internal -- hypotheses are C1 + power-bounded marginal ONLY; Part 2's converse assembled as main_marg_not_exponential; fact:dare-strong existence/uniqueness = exists_strong_solution (C1 alone) + strong_solution_unique (Existence.lean). rho(F_inf)<=1 is the IsStrongSolution.specLe bundle field. Part 2 is CLOSED (phase E): forward = main_stab_forward (Estimation/Dare/MainRate.lean; C1+C2+C3w => exponential attraction, existence internal, via sufficiency_geometric), converse = main_marg_not_exponential (finding 7's repair). Axioms clean. -->
<!-- verify: FINDING 7 RESOLVED (statement repaired + converse core verified). The old per-prior converse was FALSE (exactly-known-marginal counterexample, Remark above); eq:main-stab now quantifies over C2 priors. LEAN: converse core = DareSystem.marg_not_exponential (Estimation/Dare/RateFloor.lean): the run from Sigma_inf + Em Em' is not exponential when nm > 0 (backward power-bounded Am), via the exact gap-ric transported-energy argument with the eps-scaling contradiction — no polynomial floor needed; counterexample mechanism = marg_rows_stay_zero (zero marginal rows are invariant); the covector invariance Em' F_inf = Am Em' = embMt_mul_errMap. The FORWARD rate is now VERIFIED (phase E): sufficiency_geometric / main_stab_forward (Estimation/Dare/MainRate.lean), by thm:sufficiency's rate-paragraph squeeze exactly. Related: the repo's arc1/FIESystem layer proves the analogous VALUE-level floor exists_gap_floor_of_not_C3w and the error-side C3w_of_isGES. -->
<!-- verify: assembles thm:sufficiency + thm:necessity (Part 1) and the rate + poly-rate contradiction (Part 2). Spectrum eq:Finf-spec from lem:structure-marg, now verified (phase D, PBH-Stein); riccastep check_Fspec.py: C3w rho(F+)=0.667, marginal rho(F+)=1.0. -->
<!-- verify: deps — lem:structure-marg (eq:Finf-spec spectrum, Sigma_inf|aa>0, eq:marg-extinct), eq:Sinf-gram, eq:prior-pos (C2<=>C2w under C3w), thm:sufficiency (<= Part1 + rate), thm:necessity (=> Part1), lem:marginal + fact:gramian (poly rate, exponential=>C3w), fact:dare-strong/def:strong (rho(F_inf)<=1). CONSUMER: thm:payoff (estimator dichotomy). STANDALONE: Part 2 (GES) is self-contained (rate + poly-rate contradiction), not deferred; the full dichotomy lives here. PORT of riccastep 12-main-v4. -->
<!-- END FILE: 08-main.md -->

<!-- BEGIN FILE: 09-payoff.md -->
<!-- 09-payoff — the estimator payoff (headline). The covariance dichotomy thm:main transfers to the two -->
<!-- estimators that share the filtering Riccati: the Full-Information Estimator (FIE) and the Time-Varying -->
<!-- Kalman Filter (TVKF), which coincide for the linear-Gaussian model. GES iff C1+C2+C3w, GAS iff C1+C2 -->
<!-- (the error frontier is C2; C2w is the covariance frontier — the deliberate asymmetry with thm:main); -->
<!-- robustness (ISS under GES) via the error-map difference identity eq:diff-unroll (no standalone lem:robust). -->
<!-- Port + estimator-side extension of riccastep 13-payoff-v2; the error-side dichotomy core is the repo's -->
<!-- verified arc1 layer (GES/GAS/Arrival), cited rather than subsumed. -->
<!-- sec:payoff — main text -->
### The estimators and their common covariance

Two estimators of the state $x(T)$ from $\{y_0,\dots,y_T\}$ are of interest. The **Full-Information Estimator** (FIE) minimizes the full-horizon least-squares cost penalizing the prior deviation and every process/measurement residual; the **Time-Varying Kalman Filter** (TVKF) is the recursion `eq:filter`. For the linear-Gaussian model `eq:linsys` both return the conditional mean $\mathbb E[x(T)\mid y_{0:T}]$ — the minimum-variance estimate — so **they coincide**, with common error covariance $\Sigma_T$ (`fact:filter-opt`) and common error map $F_T$ (`eq:filter`). The dichotomy `thm:main` therefore governs both at once; we state the payoff for the pair.

<!-- thm:payoff -->
### Theorem (thm:payoff) — Stability of the FIE/TVKF

Let C1 hold, so the strong solution $\Sigma_\infty$ exists (`fact:dare-strong`), and let $e^\star(T) := x(T) - \hat x(T\mid T)$ be the estimation error. (The estimator-error statements below concern the error *dynamics*; the covariance results of `thm:main` they build on need no assumption on the marginal Jordan structure.)

<!-- thm:payoff-1 -->
**1. (Limiting error map — reflection.)** When C2w also holds, $\Sigma_T\to\Sigma_\infty$ (`thm:main`-1) and $F_T\to F_\infty$, whose spectrum reflects the uncontrollable–unstable modes into the closed disk (`eq:Finf-spec`): each antistable uncontrollable $\lambda$ ($|\lambda|>1$) appears as $\lambda^{-1}$ (inside), each marginal uncontrollable $\lambda$ ($|\lambda|=1$) is unmoved (on the circle), the stabilizable modes sit at $\operatorname{spec}(A_c)$ (inside).

<!-- thm:payoff-2 -->
**2. (The estimator dichotomy.)**

<!-- eq:payoff-dich -->
$$ \text{C1}+\text{C2}+\text{C3w} \iff \text{FIE/TVKF is GES}, \qquad\qquad \text{C1}+\text{C2} \iff \text{FIE/TVKF is GAS}, \tag{eq:payoff-dich} $$

both in the standard sense for the noise-free error ($\|e^\star(T)\| \le \sigma(T)\|e^\star(0)\|$ with $\sigma\to0$, geometric $\sigma$ for GES). Under C1+C2+C3w the error map is uniformly exponentially stable and the estimator is moreover **robust** (ISS): $\|e^\star(T)\| \le c\,\gamma^T\|e^\star(0)\| + \sum_{k<T} c\,\gamma^{T-1-k}\|d_k\|$ for bounded disturbances $d_k$, some $\gamma<1$.

**The two frontiers.** Note the deliberate asymmetry with `thm:main`: the *covariance* forgets its prior iff **C2w** (marginal uncontrollable directions need not be informed — their covariance is extinguished by observation), but the *error* forgets its initial condition iff **C2**: an *uninformed* marginal error direction is never corrected — the optimal gain is zero along it, and the error rotates undamped on the unit circle, so GAS fails. Informing it (C2) is enough: the filter then learns the marginal component exactly (its covariance $\to0$, `eq:marg-extinct`) and the error converges — without C3w only non-uniformly and non-exponentially.

*Proof.* Part 1: the split and the Schur compression are `lem:structure-marg` (verified); the per-eigenvalue reciprocal identification is `fact:dare-strong`'s pencil statement (Arc 1).

Part 2, **GES.** This is the exponential dichotomy of the companion development, proved variationally on the lumped two-block frame ($e_2 = $ all uncontrollable modes with $|\lambda|\ge1$): under C1+C2+C3w the full-information value converges geometrically and the optimizer error is GES; conversely GES forces C2 (an uninformed unstable-uncontrollable direction leaves a persistent error) and C3w — a unit-circle uncontrollable mode keeps a *harmonic* floor $c/(1+T)$ of the value budget out of reach at every horizon, contradicting a geometric rate. Robustness under GES: a perturbed run (prior, gain, or additive disturbance in the error recursion) is carried by the same uniformly exponentially bounded transition (`eq:diff-unroll`), giving the displayed ISS bound.

Part 2, **GAS.** Under C1+C2 the full-information value converges for every anchor and the optimizer error is GAS — again variationally, with no appeal to transition-product boundedness (an earlier draft argued "$F_\infty$ power-bounded, hence $\Phi(T,k)$ uniformly bounded"; that inference is invalid for time-varying products, whose factors converge to $F_\infty$ too slowly without C3w — Lean verification finding 12). Conversely GAS forces C1 (else no strong solution to home on) and C2, as above. The FIE and TVKF errors coincide (`fact:filter-opt`; verified as the optimizer/filter-error bridge), so both statements transfer to the recursive filter. Two clarifications replacing the earlier marginal discussion (finding 11): (i) C2w does **not** suffice for GAS — see the two-frontiers remark; (ii) the semisimple/defective distinction of the marginal block governs the *limit* map's powers $\|F_\infty^k\|$ (bounded vs. polynomially growing — the undamped ripples of a frozen-gain implementation), not the optimal filter's error convergence, which holds under C1+C2 regardless. ∎

<!-- cor:every-prior -->
### Corollary (cor:every-prior) — Every-prior stability is a controllability property

<!-- eq:every-prior -->
$$ \big(\Sigma_T\to\Sigma_\infty\ \text{for every prior }\Sigma_0\succeq0\big) \iff \mathcal X_{a,uc}(A,G)=\{0\}, \qquad \big(\text{FIE/TVKF GAS — equivalently GES — for every prior}\big) \iff \mathcal X_{u,uc}(A,G)=\{0\} \iff (A,G)\ \text{stabilizable}. \tag{eq:every-prior} $$

*Proof.* By `thm:main`-1 and `thm:payoff`, stability for a given prior is a kernel condition on $\Sigma_0$ (C2w for the covariance, C2 for the error). A kernel condition holds for **every** PSD prior iff the exceptional subspace is trivial: if $\mathcal X_{a,uc}\ne\{0\}$ a prior singular on an antistable uncontrollable direction violates C2w (`eq:prior-pos`), and dually for $\mathcal X_{u,uc}$ and C2; conversely trivial subspaces make the conditions vacuous. So every-prior covariance attraction is exactly $\mathcal X_{a,uc}=\{0\}$, and every-prior error GAS is exactly $\mathcal X_{u,uc}=\{0\}$ — i.e. $(A,G)$ stabilizable — which already entails C3w (no uncontrollable unit-circle modes), so every-prior GAS and every-prior GES **coincide**. (An earlier draft characterized every-prior "RGAS" by $\mathcal X_{a,uc}=\{0\}$; that describes the covariance side, not the error side — finding 13.) ∎

**Remark (the practical reading).** Detectability buys the strong solution and hence a stable estimator for any admissible prior; whether that estimator is *exponentially* stable is a separate, controllability-side question. If every uncontrollable mode is stable — $(A,G)$ stabilizable — the FIE/TVKF is GES for every prior. If some uncontrollable modes sit on the unit circle, the best attainable even with a perfectly chosen prior is the strong solution: the covariance still converges (no longer exponentially), and the estimator is GAS provided the prior informs those modes (C2) — the error along them is learned, only slowly — while an exponentially stabilizing gain must be sought outside the optimal filter. C2w is the sharp frontier for the *covariance* — a *semidefinite*-prior kernel condition, weaker than positive-definiteness or domination of $\Sigma_\infty$ — separating the filter whose covariance forgets its prior from the one whose never does; C2 is the corresponding frontier for the *error*. This is the discrete, estimation-side image of the critical-mode phenomenon of Callier and Winkin (1995); it sharpens the positive-definite-prior filtering results of de Souza, Gevers and Goodwin (1986) to semidefinite priors with an explicit rate.

<!-- verify: LEAN (phase C): the estimator dichotomy eq:payoff-dich = the repo's verified arc1 layer (two-block frame, FIESystem/GeneralSystem): GES iff C1+C2+C3w = FIESystem.isGES_iff_C1_C2_C3w with the harmonic value floor exists_gap_floor_of_not_C3w (Estimation/GES.lean); GAS iff C1+C2 = FIESystem.isGAS_iff_C1_and_C2 (Estimation/GAS.lean); both bundled in gas_ges_dichotomy; the FIE = TVKF error bridge = isGASkf_iff_isGAS (Estimation/Arrival.lean). These are per-prior statements on the error side — no quantifier subtlety, unlike the covariance-side eq:main-stab: error-GES forces C2, which rules out the exactly-known-marginal counterexample. Phase F closes all three former gaps. Frame transfer VERIFIED: DareSystem.toFIE (Estimation/Dare/Payoff.lean) lumps a⊕m into the FIE frame with condition correspondences toFIE_C1_iff/toFIE_C2_iff/toFIE_C3w_iff, and payoff_dichotomy states eq:payoff-dich in THIS deck's three-block frame (GAS iff C1∧C2, GES iff C1∧C2∧C3w, all conditions in-frame). Part 1's map convergence F_T → F_inf = payoff_errMap_tendsto; the spectrum display is phase D's verified strong_spec_split / strong_exists_unit_eigenvalue. ISS VERIFIED (Estimation/Dare/Robust.lean): fullProd_geometric (fact:uniexp at the full three-block level — transitionProd made index-generic) + errTraj_unroll (eq:diff-unroll) + payoff_iss (the displayed bound c·γ^T‖e0‖ + Σ c·γ^(T−1−k)‖d_k‖, under C1+C2+C3w only, as claimed). Axioms clean. -->
<!-- verify: LEAN (phase F3): cor:every-prior = Estimation/Dare/EveryPrior.lean — everyPrior_C2w_iff ((∀ prior) C2w ↔ na=0, the covariance side), everyPrior_attraction_iff (every-prior Σ_T → Σ_inf ↔ X_{a,uc}=0), everyPrior_C2_iff ((∀ prior) C2 ↔ na=nm=0), fullStab_iff (the Hautus bridge: (A,G) stabilizable ↔ na=nm=0, left-eigenvector lift through the frame), everyPrior_gas_iff / everyPrior_ges_iff (each ↔ stabilizability, via payoff_dichotomy) and everyPrior_gas_iff_ges (the coincidence — stabilizability already entails C3w). Vacuity guard: exampleDare (Estimation/Dare/Instance.lean) realizes the dichotomy with all three blocks nonempty: C1+C2 by construction, GAS, NOT GES, covariance attracted but not exponentially. -->
<!-- verify: FINDINGS 11-13 (this file, all REPAIRED in place): (11) "C1+C2w iff RGAS" misstated the error frontier — the verified frontier is C2 (isGAS_iff_C1_and_C2); C2w is the covariance frontier (thm:main-1); the old text's own "undamped ripples" conceded non-convergence. (12) "F_inf power-bounded => Phi(T,k) uniformly bounded" is a non sequitur for time-varying products; the variational route avoids transition products entirely. (13) every-prior "RGAS iff X_{a,uc}=0" was the covariance-side characterization; the error side is X_{u,uc}=0 = stabilizability, making every-prior GAS and GES coincide. Old numerics note: check_defective_marginal.py measured ||F_inf^k|| (the LIMIT map), which distinguishes semisimple/defective for a frozen-gain implementation but not for the optimal filter's error. -->
<!-- verify: deps — eq:filter/eq:linsys (00-problem), fact:filter-opt (FIE=TVKF=MMSE, common Sigma_T), fact:dare-strong, thm:main-1/-2 (covariance side), eq:Finf-spec/lem:structure-marg (Part 1 reflection), arc1 verified layer (GES/GAS/Arrival: the error dichotomy and the value floor), eq:diff-unroll (robustness/ISS — VERIFIED, errTraj_unroll + payoff_iss, phase F2), eq:prior-pos (every-prior). PORT+extension of riccastep 13-payoff-v2; the exponential-only treatment is the arc1 layer, now cited as the verified error-side core rather than subsumed. -->
<!-- END FILE: 09-payoff.md -->

<!-- BEGIN FILE: a00-facts.md -->

# Appendix

## Mathematical facts

<!-- fact:schur -->
### Fact (fact:schur) — Schur complement bound

If $\begin{bmatrix} A & B \\ B' & C \end{bmatrix} \succeq 0$ and $C \succ 0$, then $A - B C^{-1} B' \succeq 0$.

<!-- fact:no-decay -->
### Fact (fact:no-decay) — No decay for autonomous modes on or outside the unit circle

If every eigenvalue of $A$ satisfies $|\lambda| \geq 1$, then $A^k v \to 0$ implies $v = 0$.

<!-- fact:gramian -->
### Fact (fact:gramian) — Spectral mapping and divergence of the sampled state-energy Gramian

Let $A \in \mathbb{R}^{n \times n}$ have every eigenvalue with $|\lambda| \geq 1$. For every integer $m \geq 1$,

$$ \operatorname{spec}(A^m) = \{ \lambda^m : \lambda \in \operatorname{spec}(A) \} $$

so every eigenvalue of $A^m$ also satisfies $|\lambda| \geq 1$. Moreover,

$$ \lambda_{\min}\!\left( \sum_{j=0}^{\kappa-1} (A^{jm})' A^{jm} \right) \to \infty \quad \text{as } \kappa \to \infty $$

**Proof.** The spectral identity is the spectral mapping theorem. For the Gramian, set $G_\kappa := \sum_{j=0}^{\kappa-1} (A^{jm})' A^{jm}$, so $G_{\kappa+1} \succeq G_\kappa$ and $\lambda_{\min}(G_\kappa)$ is nondecreasing. Suppose for contradiction $\lambda_{\min}(G_\kappa) \not\to \infty$. Then there exist $M < \infty$ and unit vectors $v_\kappa$ with $v_\kappa' G_\kappa v_\kappa \leq M$. Pass to a subsequence with $v_\kappa \to v$, $\|v\| = 1$. For every $N$ and all $\kappa \geq N$,

$$ \sum_{j=0}^{N-1} \|A^{jm} v_\kappa\|^2 \leq v_\kappa' G_\kappa v_\kappa \leq M $$

Taking $\kappa \to \infty$ along the subsequence gives $\sum_{j=0}^{N-1} \|A^{jm} v\|^2 \leq M$ for every $N$, hence $\sum_{j=0}^\infty \|A^{jm} v\|^2 < \infty$ and $A^{jm} v \to 0$. Since every eigenvalue of $A^m$ has modulus at least one, `fact:no-decay` forces $v = 0$, contradicting $\|v\| = 1$. ∎

**Observable-injection form.** If, in addition, $H$ is a matrix with $(A, H)$ **observable**, then

$$ \lambda_{\min}\!\left( \sum_{j=0}^{\kappa-1} (A^{j})'\,H'H\,A^{j} \right) \to \infty \quad \text{as } \kappa \to \infty $$

(the per-step injection $H'H$ may be rank-deficient — the orbit fills the missing directions). **Proof.** Identical compactness argument with $\|HA^{j}v_\kappa\|^2$ in place of $\|A^{jm}v_\kappa\|^2$: a bounded limit forces $\sum_{j\ge0}\|HA^{j}v\|^2 < \infty$, hence $HA^{j}v \to 0$. For an eigenvector $w$ of $A$ at $\lambda$ ($|\lambda|\ge1$), $HA^{j}w = \lambda^{j}Hw$ with $\|HA^{j}w\| = |\lambda|^{j}\|Hw\|$, which tends to $0$ only if $Hw=0$; observability (PBH: no $A$-eigenvector lies in $\ker H$) rules this out, and the Jordan generalization adds only polynomial factors. So $v=0$, a contradiction. ∎

<!-- fact:psd-bounds -->
### Fact (fact:psd-bounds) — Spectral factorization and quadratic-form bounds for symmetric positive semidefinite matrices.

Every $P = P' \succeq 0$ admits an orthogonal factorization

$$
P = M \Lambda M'
\qquad M M' = I
\qquad \Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n)
\qquad \lambda_i \ge 0
$$

Consequently, for every $x$,

$$
\lambda_{\min}(P)\, \|x\|^2 \le x' P x \le \lambda_{\max}(P)\, \|x\|^2
$$

Equivalently,

$$
\lambda_{\min}(P)\, I \preceq P \preceq \lambda_{\max}(P)\, I
$$

If $P \succ 0$, then

$$
\|P^{-1}\| = \frac{1}{\lambda_{\min}(P)}
$$

<!-- fact:uniexp -->
### Fact (fact:uniexp) — Uniform exponential stability of a time-varying system (Zhou & Zhao 2017)

Given a linear time-varying system

$$ z(k+1) = F(k)\, z(k) \qquad k \geq 0 $$

in which the limit $\lim_{k \to \infty} F(k) = F$ exists, the time-varying system is uniformly exponentially stable if and only if $F$ is Schur stable.

<!-- fact:poly-growth -->
### Fact (fact:poly-growth) — Polynomial growth of powers for spectra in the closed unit disk

Let $A \in \mathbb{R}^{n \times n}$ have every eigenvalue satisfying $|\lambda| \leq 1$, and let $m$ with $1 \leq m \leq n$ be the size of the largest Jordan block associated with an eigenvalue on the unit circle ($m = 1$ if no eigenvalue lies on the unit circle). Then there exists $c > 0$ such that

$$ \|A^k\| \;\leq\; c\,(1 + k)^{m-1} \qquad k \geq 0. $$

<!-- fact:schur-decay -->
### Fact (fact:schur-decay) — Geometric decay of Schur matrix powers

Let $M\in\mathbb{R}^{n\times n}$ have $\rho(M) < 1$. Then for every $\gamma\in(\rho(M),1)$ there is $c\ge 1$ with

$$ \|M^k\| \;\le\; c\,\gamma^k \qquad k\ge 0. $$

**Proof.** In the Jordan form $M = S J S^{-1}$, each block of size $m$ at eigenvalue $\lambda$ has $\|(\lambda I+N)^k\| \le \sum_{i<m}\binom{k}{i}|\lambda|^{k-i}\|N\|^i \le p(k)\,|\lambda|^{k-(m-1)}$ for a polynomial $p$; since $|\lambda|\le\rho(M)<\gamma$, $p(k)|\lambda|^{k}/\gamma^k\to 0$, so the ratio is bounded. Taking the max over blocks and absorbing $\|S\|\|S^{-1}\|$ gives a finite $c$. (Equivalently, $\limsup_k\|M^k\|^{1/k}=\rho(M)<\gamma$ by Gelfand, so $\|M^k\|\gamma^{-k}$ is bounded.) ∎

The induced **Stein/Lyapunov operator** $\mathcal{L}_M(\delta) := M\delta M'$ on symmetric matrices has spectrum $\{\lambda_i\lambda_j : \lambda_i,\lambda_j\in\operatorname{spec}(M)\}$, hence $\rho(\mathcal{L}_M)=\rho(M)^2$; so $\rho(M)<1$ likewise gives $\|\mathcal{L}_M^{\,k}\| = \|\delta\mapsto M^k\delta M'^k\| \le c'\,\gamma^{2k}$.

<!-- fact:update-kernel -->
### Fact (fact:update-kernel) — The measurement update preserves the kernel

For $\Sigma = \Sigma' \succeq 0$ and $R \succ 0$, the measurement update $\mathcal{U}(\Sigma) := \Sigma - \Sigma C'(C\Sigma C'+R)^{-1}C\Sigma$ satisfies, with $D := C\Sigma^{1/2}$,

$$ \mathcal{U}(\Sigma) \;=\; \Sigma^{1/2}\,\big(I + D'R^{-1}D\big)^{-1}\,\Sigma^{1/2} $$

The middle factor $(I+D'R^{-1}D)^{-1} \succ 0$, so $\ker\mathcal{U}(\Sigma) = \ker\Sigma^{1/2} = \ker\Sigma$. Consequently, for any index set $J$,

$$ \Sigma\!\mid_{JJ} \succ 0 \quad\Longrightarrow\quad \mathcal{U}(\Sigma)\!\mid_{JJ} \succ 0 $$

**Proof.** The identity $I - D'(DD'+R)^{-1}D = (I+D'R^{-1}D)^{-1}$ (push-through) gives $\mathcal{U}(\Sigma) = \Sigma^{1/2}[I-D'(DD'+R)^{-1}D]\Sigma^{1/2} = \Sigma^{1/2}(I+D'R^{-1}D)^{-1}\Sigma^{1/2}$; the middle factor is $\succ 0$ since $D'R^{-1}D\succeq 0$. Hence $\ker\mathcal{U}(\Sigma)=\ker\Sigma^{1/2}=\ker\Sigma$. For the block: if $\mathcal{U}(\Sigma)\!\mid_{JJ}v_J = 0$ for $v_J\ne 0$, then the embedding $v=\iota_J v_J$ has $v'\mathcal{U}(\Sigma)v = v_J'\mathcal{U}(\Sigma)\!\mid_{JJ}v_J = 0$, so $v\in\ker\mathcal{U}(\Sigma)=\ker\Sigma$, whence $v_J'\Sigma\!\mid_{JJ}v_J = v'\Sigma v = 0$ — contradicting $\Sigma\!\mid_{JJ}\succ0$. ∎

<!-- fact:dare-strong -->
### Fact (fact:dare-strong) — Strong DARE solution: existence, uniqueness, spectrum, stabilization (Fact 1, foundational)

Let $(A,C)$ be detectable, $Q\succeq 0$, $R\succ 0$. Then the filtering DARE `eq:dare` has a **strong** solution $\Sigma_\infty = \Sigma_\infty'\succeq 0$ (`def:strong`): it is the **maximal** positive-semidefinite solution and the **unique** solution with $\rho(F_\infty)\le 1$, where $F_\infty := A(I-L_\infty C)$ and $L_\infty := \Sigma_\infty C'(C\Sigma_\infty C'+R)^{-1}$.

**(Spectrum.)** In the frame `eq:three-block`, the closed loop splits along the three blocks:

<!-- eq:Finf-spec -->
$$ \operatorname{spec}(F_\infty) \;=\; \Lambda_{\mathrm{in}}(A_1,G_1,C_1)\ \sqcup\ \{\,\lambda^{-1} : \lambda\in\operatorname{spec}(A_a)\,\}\ \sqcup\ \operatorname{spec}(A_m), \tag{eq:Finf-spec} $$

where $\Lambda_{\mathrm{in}}(A_1,G_1,C_1)$ is the open-unit-disk half of the $2n_1$ reciprocally paired ($\lambda\leftrightarrow 1/\bar\lambda$) generalized eigenvalues of the symplectic pencil of the stabilizable subsystem $(A_1,G_1,C_1)$ — equivalently, the $n_1$ eigenvalues of the stabilizing-solution closed loop of the $(A_1,G_1,C_1)$ filter, all of modulus $<1$. The **antistable** modes are *reflected* to their reciprocals (modulus $<1$); the **marginal** modes are *fixed* on the unit circle.

**(Corollary — stabilization under C3w.)** $\rho(F_\infty)\le 1$ always, and

<!-- eq:Finf-c3w -->
$$ \rho(F_\infty) < 1 \quad\Longleftrightarrow\quad \text{no uncontrollable unit-circle mode (C3w)} \quad\Longleftrightarrow\quad n_m = 0. \tag{eq:Finf-c3w} $$

Under C3w the strong solution is **stabilizing**. Without it, $\rho(F_\infty)=1$ exactly, carried by the marginal block $\operatorname{spec}(A_m)\subset\{|\lambda|=1\}$, which is never reflected inside; the stabilizable and antistable directions are Schur regardless, so $F_\infty\!\mid_{e_1\oplus a}$ — the closed loop restricted to the stabilizable-plus-antistable subspace — is **Schur in every case**.

**(Verified construction, phase D.)** Existence and uniqueness are now *proved* in the frame, by chart assembly: the reduced $(A_1,G_1,C_1)$ stabilizing solution $P_\infty$ (zero-seed monotone convergence, one-step PBH–Stein Schur loop), the loading $\Lambda_\infty$ (a discrete Sylvester fixed point with Schur factors $L_\infty$, $A_a^{-1}$), and the information gramian $J_\infty\succ0$ (PSD by its iterates; *definite* because a kernel eigenvector would lift through the loading identity to an undetectable antistable mode of $(A,C)$, against C1); the assembled $\Sigma_\infty = e_1P_\infty e_1' + V_\infty J_\infty^{-1}V_\infty'$ is a fixed point by the conditional-chart step read backwards, with $\rho(F_\infty)\le1$ by the strict one-step PBH–Stein kill. Existence needs **C1 alone**; uniqueness (among $\rho\le1$ solutions) follows from `lem:supremal` seeded at $\Sigma_\infty+\Sigma_\infty'$, under the power-bounded marginal. **Maximality is not consumed by this development and remains a classical citation.**

(Classical references: existence, uniqueness, and maximality under detectability alone — de Souza–Gevers–Goodwin 1986; see also Chan–Goodwin–Sin 1984. The reciprocal-pairing / reflection structure `eq:Finf-spec` is the symplectic-pencil theory of the discrete Hamiltonian, Lancaster–Rodman 1995. This is the discrete dual of Callier–Winkin 1995, Fact 1.) Formerly imported; the present development establishes the *structure* of $\Sigma_\infty$ (`lem:structure`), that the recursion is *attracted* to it, and — as of the phase-D verification — the load-bearing spectrum claims themselves (`lem:structure-marg`: the $(e_1\oplus a\,|\,m)$ split, $F_\infty\!\mid_{e_1\oplus a}$ Schur, the unit-modulus witness for $\rho(F_\infty)=1$), all from the bundle's $\rho(F_\infty)\le1$ alone. As of phase D4 existence and uniqueness are theorems as well (`exists_strong_solution` under C1 alone; `strong_solution_unique` / `existsUnique_strong_solution`); only maximality (not consumed) and the finer reciprocal pairing $\Lambda_{\mathrm{in}}\sqcup\{\lambda^{-1}\}$ (an Arc-1 consumer) remain imported.

<!-- verify: eq:Finf-spec confirmed numerically in scratch/check_fact1.py — spec(F_inf) of the maximal (from-above) solution matches Lambda_in(A1,G1,C1) ⊔ {1/lambda(A_a)} ⊔ spec(A_m) to 2e-2: antistable {1.5,2.0} -> {0.667,0.5} (reflected inside), marginal e^{±0.6i} on the circle, Lambda_in inside. rho(F_inf)=1.0 with the marginal present; dropping the marginal block gives rho=0.667<1 (eq:Finf-c3w), and the e1⊕a restriction is Schur in both runs. -->
<!-- verify: import side-conditions — detectability (C1) is the standing hypothesis; Q>=0, R>0; the strong/maximal solution exists under detectability ALONE (no stabilizability of the unstable modes), the regime here. Primary citation: de Souza-Gevers-Goodwin 1986. F_inf|e1+a Schur and the split are now proved (strong_Fs_schur/strong_spec_split, phase D), consumed by lem:structure-1/-marg and the main line; the reciprocal-pairing fine form of eq:Finf-spec is consumed by thm:formula and lem:sysinterp (Arc 1) (disjoint pencil spectra => complementary deflating subspaces V_+/V_-); confine C3w to the GES branch — eq:Finf-c3w must NOT enter the GAS/attraction argument. -->

<!-- fact:filter-opt -->
### Fact (fact:filter-opt) — Optimality and information-monotonicity of the Kalman filter (foundational)

For the model `eq:linsys` with $x(0)\sim N(x_0,\Sigma_0)$, $w\sim N(0,Q)$, $v\sim N(0,R)$ independent, the Kalman filter error covariance $\Sigma_T$ is the **minimum** error covariance among all estimators of $x(T)$ measurable with respect to $\{y_0,\dots,y_T\}$: for any such estimator $\hat x$, $\operatorname{cov}(x(T)-\hat x) \succeq \Sigma_T$. Moreover the optimal error covariance is **monotone non-increasing under enlargement of the conditioning data**: if an estimator is additionally given the exact values of a subset of the state coordinates over $\{0,\dots,T\}$, the resulting optimal error covariance is $\preceq \Sigma_T$ (restricted to the estimated coordinates). (Standard minimum-variance/MMSE optimality and the data-processing monotonicity of conditional covariance; foundational and imported, not proved here.)

<!-- verify: LEAN status (phase A) — fact:schur: mathlib (Matrix.PosDef.fromBlocks₂₂); thin wrapper lands with first consumer. fact:no-decay: VERIFIED = LinearSystems.no_decay (SpectralGrowth.lean); consumed twice in the repaired lem:structure-marg (correction kill, row kill). fact:gramian: VERIFIED for H = I = LinearSystems.gramian_growth (quantitative c*T floor); in-frame marginal instantiation marg_gramian_growth (phase F4) — the identified tool for the defective-marginal open problem; the observable-injection form has no remaining consumer (the marginal route was rewritten off fact:gramian — finding 5 / 03's remark). fact:psd-bounds: VERIFIED = LinearSystems/QuadForm.lean layer. fact:uniexp: VERIFIED in the consumed direction (F(k) -> F Schur => uniform exponential bound) = LinearSystems.transitionProd_norm_le_of_tendsto, now consumed on the reduced run (redProdF_geometric, phase D3) AND on the full three-block run (fullProd_geometric, phase F2 — transitionProd made index-generic); thm:payoff's ISS display consumes it (payoff_iss); the converse direction is not consumed and not formalized. fact:poly-growth: verified-weakened = LinearSystems.pow_mulVec_le_poly (exponent n-1, not the Jordan-sharp m-1; every consumer needs only some polynomial rate — deviation register D5). fact:schur-decay: VERIFIED = LinearSystems.IsSchurStable.exists_pow_norm_le. fact:update-kernel: VERIFIED = Dare.updM_mulVec_eq_zero_iff (+ block form Dare.updM_toBlocks₂₂_posDef, corner form Dare.updM_corner_posDef). fact:dare-strong: PROVED (phase D4): existence = DareSystem.exists_strong_solution (C1 alone; chart assembly with Sylvester fixed points + gramian_fixed_posDef, Estimation/Dare/Existence.lean), uniqueness = strong_solution_unique / existsUnique_strong_solution (power-bounded marginal, via lem:supremal; the semisimple qualification is a verified implication — MargSemisimple => both power bounds, marg_powers_bounded, phase F4); the IsStrongSolution bundle (PSD + fixed + rho<=1) is now instantiated, not hypothesized; maximality not consumed, still classical; on the REDUCED (A1,G1,C1) system it is fully PROVED (phase D2/D3: exists_stabilizing_solution — monotone-from-zero + one-step PBH-Stein fixed_point_schur + uniqueness; redP_tendsto_infP identifies the limit; Estimation/Dare/Reduced.lean, ReducedFacts.lean); the eq:Finf-spec/eq:Finf-c3w load-bearing content is VERIFIED (phase D) from the bundle alone — strong_spec_split, strong_Fs_schur, strong_exists_unit_eigenvalue (Estimation/Dare/Spectrum.lean); the reciprocal-pairing fine form remains imported (Arc-1 consumers only). fact:filter-opt: IMPORTED; after the finding-1 adoption, consumed only by 09-payoff's FIE=TVKF identification. -->
<!-- END FILE: a00-facts.md -->

<!-- BEGIN FILE: a01-frame.md -->
<!-- app:frame — the antistable-marginal frame, justified by DARE similarity-covariance. -->
<!-- app:frame -->
### The antistable–marginal frame

The development of `00-setup` works, without loss of generality, in the frame `eq:three-block`. This appendix supplies the reduction and its justification, which rests only on the covariance of the DARE `eq:dare` under state similarity.

**1. (Similarity-covariance of the DARE.)** Let $T$ be nonsingular and write $\tilde A := T A T^{-1}$, $\tilde G := T G$, $\tilde C := C T^{-1}$. Then for every $\Sigma = \Sigma' \succeq 0$,

<!-- eq:dare-cov -->
$$ \mathcal{R}_{\tilde A, \tilde G, \tilde C}\big( T\Sigma T' \big) = T\, \mathcal{R}_{A, G, C}(\Sigma)\, T' \qquad \tilde F = T F T^{-1} \tag{eq:dare-cov} $$

where $\mathcal{R}_{A,G,C}(\Sigma) := A[\Sigma - \Sigma C'(C\Sigma C' + R)^{-1}C\Sigma]A' + GQG'$ is the recursion map of `eq:cov-rec` and $F$ its error map `eq:filter`.

*Proof.* $\tilde C\, (T\Sigma T')\, \tilde C' = C T^{-1} T \Sigma T' T^{-\prime} C' = C\Sigma C'$, so the innovation block and $R$ are untouched; hence $T\Sigma T'\, \tilde C'(\tilde C T\Sigma T' \tilde C' + R)^{-1}\tilde C\, T\Sigma T' = T\big[\Sigma C'(C\Sigma C' + R)^{-1}C\Sigma\big]T'$. Conjugating by $\tilde A = TAT^{-1}$ and adding $\tilde G Q \tilde G' = T GQG' T'$ gives the first identity; factoring $T$ out of $\tilde A(I - \cdots \tilde C)$ gives $\tilde F = TFT^{-1}$. ∎

Consequently, seeding `eq:cov-rec` at $\tilde\Sigma_0 = T\Sigma_0 T'$ produces $\tilde\Sigma_T = T\Sigma_TT'$ for all $T$; the error map conjugates to $\tilde F_T = T F_T T^{-1}$ with $\rho(\tilde F_T) = \rho(F_T)$; and $\tilde\Sigma_T \to \Sigma_\infty$ iff $\Sigma_T \to T^{-1}\Sigma_\infty T^{-\prime}$. So **attraction, the spectrum of the error map, and the strong/stabilizing classification are all similarity-covariant**: the prior transforms by the congruence $\Sigma_0 \mapsto T\Sigma_0 T'$, and we may choose $T$ freely. The conditions C1/C2/C2w/C3w are spectral/subspace statements about $(A, G, C)$ and $\ker\Sigma_0$, hence similarity-invariant.

**2. (The frame, in three similarities.)** Compose:

- *(Stabilizability canonical form.)* A similarity puts $(A, G)$ in $A = \big[\begin{smallmatrix} A_1 & A_{12} \\ 0 & A_2 \end{smallmatrix}\big]$, $G = \big[\begin{smallmatrix} G_1 \\ 0 \end{smallmatrix}\big]$ with $(A_1, G_1)$ stabilizable and $A_2$ carrying exactly the uncontrollable modes with $|\lambda| \ge 1$ (stable uncontrollable modes are absorbed into $A_1$). By C1, $(A_1, C_1)$ is detectable, so the stabilizable block is closed to a Schur $A_c$ (its $e_1$-diagonal block of $F_\infty$) by the strong-solution gain (`eq:Finf-spec`) — no separate stabilizing feedback need be constructed.
- *(Antistable–marginal separation.)* Within $A_2$, the spectra outside and on the unit circle are disjoint, $\operatorname{spec}(A_a) \cap \operatorname{spec}(A_m) = \varnothing$, so the Sylvester equation $A_a X - X A_m = -A_{am}$ has a unique solution and the similarity $\big[\begin{smallmatrix} I & X \\ 0 & I \end{smallmatrix}\big]$ block-diagonalizes $A_2$ into $A_a \oplus A_m$ — $A_a$ antistable ($A_a^{-1}$ Schur), $A_m$ on the circle. This **decouples** the antistable dynamics from the marginal ones, so backward propagation by $A_a^{-1}$ later cannot drive the marginal block. The **antistable block is placed first** within $A_2$, so the reduced $e_1\oplus e_a$ system occupies the leading principal block of the frame.
- *(Prior congruence.)* A block-triangular congruence across the stabilizable cut block-diagonalizes the prior, $\Sigma_0 \mapsto \operatorname{diag}(\Sigma_1, \Sigma_2)$, while preserving the upper-triangular structure of $A$ and $G = \operatorname{col}(G_1, 0, 0)$. The $(a, m)$ coupling **inside** $\Sigma_2 = \big[\begin{smallmatrix} \Sigma_{aa} & \Sigma_{am} \\ \Sigma_{am}' & \Sigma_{mm} \end{smallmatrix}\big]$ is retained (only the dynamics decouple, not the prior).

The composite similarity yields `eq:three-block`, and by Part 1 the entire development may be read there.

**3. (Prior positivity from C2 / C2w.)** Writing $\Sigma_a := \Sigma_{aa}$ for the antistable diagonal block of the lumped prior,

<!-- eq:prior-pos -->
$$ \textbf{(a)}\quad \text{C2} \iff \Sigma_2 \succ 0 \qquad\qquad \textbf{(b)}\quad \text{C2w} \iff \Sigma_a \succ 0 \tag{eq:prior-pos} $$

*Proof.* In the frame, $\mathcal{X}_{u,uc} = \{0\}^{n_1} \times \mathbb{R}^{n_2}$ and a vector $v = \operatorname{col}(0, v_2)$ lies in $\ker\Sigma_0 = \ker\Sigma_1 \times \ker\Sigma_2$ iff $\Sigma_2 v_2 = 0$, so $\ker\Sigma_0 \cap \mathcal{X}_{u,uc} \cong \ker\Sigma_2$, trivial iff $\Sigma_2 \succ 0$ — this is **(a)**. For **(b)**, $\mathcal{X}_{a,uc} = \{0\}^{n_1} \times \mathbb{R}^{n_a} \times \{0\}^{n_m}$, and $v = \operatorname{col}(0, v_a, 0) \in \ker\Sigma_0$ iff $\Sigma_2 \operatorname{col}(v_a, 0) = 0$; since $\Sigma_2 \succeq 0$, a vector lies in its kernel iff it annihilates the quadratic form, so this is $v_a' \Sigma_a v_a = 0$. Hence $\ker\Sigma_0 \cap \mathcal{X}_{a,uc} = \{0\}$ iff $\Sigma_a \succ 0$ — this is **(b)**. ∎

Part (b) is the prior-positivity form of the attraction criterion: the antistable prior block carries strictly positive information. The coupling matters — $\ker\Sigma_2$ may contain *mixed* antistable–marginal directions even when $\Sigma_a \succ 0$ — so C2w forbids only a *purely* antistable kernel direction. Under C3w the marginal block is empty, $\mathcal{X}_{a,uc} = \mathbb{R}^{n_2}$, and `eq:prior-pos`(b) becomes $\Sigma_2 \succ 0$, recovering (a) as C2 $\iff$ C2w.

<!-- verify: Part 1 (eq:dare-cov) licenses the frame using only DARE similarity-covariance. Part 3 (eq:prior-pos) is consumed by the criterion slice (C2w <=> Sigma_a > 0). Ordering: antistable e_a FIRST within A_2, marginal e_m LAST, so e_1(+)e_a is the leading principal block (reduced problem in the top-left corner). -->
<!-- verify: LEAN (phase A): eq:three-block = structure DareSystem (Estimation/Dare/System.lean; C1/C2/C2w in kernel form); eq:prior-pos(a) = DareSystem.criterion, (b) = DareSystem.criterion_w; eq:A2-inv = DareSystem.isUnit_A₂_det. Part 1 (eq:dare-cov similarity covariance): declared deck-level — the Lean development works in-frame; the analogous two-block reduction is verified end-to-end (GeneralSystem.redSys, Estimation/Reduction.lean), and the a⊕m lumping OUT of this frame is verified as phase F1's DareSystem.toFIE; a three-block staircase INTO the frame would mirror them. -->
<!-- END FILE: a01-frame.md -->

<!-- BEGIN FILE: a02-machinery.md -->
<!-- app:machinery — the engines of the squeeze: comparison, the e2-information A2^{-1} reversal, and the -->
<!-- gap engine (difference identity + gap-Riccati). The gap engine is promoted here because all three -->
<!-- consumers (upper anchor, lower forgetting, robustness) use it. -->
<!-- app:machinery -->
### Comparison principle, the $A_2^{-1}$ information recursion, and the gap engine

Write the recursion `eq:cov-rec` as $\Sigma_{T+1} = \mathcal{R}(\Sigma_T)$ with

<!-- eq:Rmap -->
$$ \mathcal{R}(\Sigma) := A\, \mathcal{U}(\Sigma)\, A' + GQG' \qquad \mathcal{U}(\Sigma) := \Sigma - \Sigma C'\big(C\Sigma C' + R\big)^{-1} C\Sigma \tag{eq:Rmap} $$

$\mathcal{U}$ is the measurement update; for $\Sigma \succ 0$, $\mathcal{U}(\Sigma) = (\Sigma^{-1} + C'R^{-1}C)^{-1}$ (information form). We work in the frame `eq:three-block`, $A = \big[\begin{smallmatrix} A_1 & A_{12} \\ 0 & A_2 \end{smallmatrix}\big]$ in the $(e_1, e_2)$ split, $G = \operatorname{col}(G_1, 0)$, $A_2 = A_a \oplus A_m$ nonsingular (`eq:A2-inv`).

<!-- app:machinery-1 -->
**1. (Comparison principle — monotonicity in the initial condition.)** $\mathcal{R}$ is monotone in the Löwner order, and hence so is every iterate:

<!-- eq:comparison -->
$$ L_1 \preceq L_2 \quad\Longrightarrow\quad \mathcal{R}^T(L_1) \preceq \mathcal{R}^T(L_2) \qquad T \ge 0 \tag{eq:comparison} $$

This is the one result we import rather than re-derive: the monotone dependence of the Riccati recursion on its initial condition (Poubelle, Petersen, Gevers and Bitmead 1986; Bitmead, Gevers and Petersen 1985; De Nicolao and Gevers 1992, Lemma 1). We include its short proof for completeness; everything downstream — both anchors of the squeeze — is built on it and re-derived in-deck.

<!-- app:machinery-2 -->
**2. (The $e_2$-information reverses by $A_2^{-1}$.)** Suppose $\Sigma_T\!\mid_{22} \succ 0$ for $T \ge T_0$ (supplied by the antistable seed, `lem:structure`-3). The $e_2$-block information $J_T := (\Sigma_T\!\mid_{22})^{-1}$ obeys the **linear** recursion

<!-- eq:Jrec -->
$$ J_{T+1} = A_2^{-1\prime}\, J_T\, A_2^{-1} + W_T \qquad W_T = W_T' \succeq 0 \tag{eq:Jrec} $$

so, unrolling from $T_0$,

<!-- eq:Jgram -->
$$ J_T = \big(A_2^{-(T-T_0)}\big)'\, J_{T_0}\, A_2^{-(T-T_0)} + \sum_{j=T_0}^{T-1} \big(A_2^{-(T-1-j)}\big)'\, W_j\, A_2^{-(T-1-j)} \tag{eq:Jgram} $$

an $A_2^{-1}$-driven gramian — the discrete object on which the whole development turns.

<!-- app:machinery-3 -->
**3. (The gap engine — difference identity and gap-Riccati.)** For $A_\sharp, B_\sharp = A_\sharp', B_\sharp' \succeq 0$, with $F(\Sigma) := A(I - L(\Sigma)C)$, $L(\Sigma) = \Sigma C'(C\Sigma C'+R)^{-1}$ (the error map `eq:filter`),

<!-- eq:diff-id -->
$$ \mathcal{R}(A_\sharp) - \mathcal{R}(B_\sharp) = F(A_\sharp)\,\big(A_\sharp - B_\sharp\big)\,F(B_\sharp)' \tag{eq:diff-id} $$

Unrolling along two trajectories $P_T^X := \mathcal{R}^T(X)$, $P_T^Y := \mathcal{R}^T(Y)$, with error-map products $\Phi_T^X := F(P_{T-1}^X)\cdots F(P_0^X)$ (newest factor first) and likewise $\Phi_T^Y$,

<!-- eq:diff-unroll -->
$$ P_T^X - P_T^Y = \Phi_T^X\,(X - Y)\,(\Phi_T^Y)' \tag{eq:diff-unroll} $$

Writing $F_\infty := F(\Sigma_\infty)$ and $S_V := C(\Sigma_\infty + V)C' + R \succ 0$, the gain expands about $\Sigma_\infty$ as $F(\Sigma_\infty + V) = F_\infty(I - VC'S_V^{-1}C)$; hence for $V \succeq 0$,

<!-- eq:gap-ric -->
$$ \mathcal{R}(\Sigma_\infty + V) - \Sigma_\infty = F_\infty\, V\, F_\infty' \;-\; F_\infty\, V\, C'\, S_V^{-1}\, C\, V\, F_\infty' \;\preceq\; F_\infty\, V\, F_\infty' \tag{eq:gap-ric} $$

the subtracted term being $\succeq 0$. **Above $\Sigma_\infty$ the gap is dominated by the fixed strong loop $F_\infty$** (a two-sided Stein contraction, rate $\rho(F_\infty)^2$); **below $\Sigma_\infty$**, `eq:diff-id` at the fixed point $B_\sharp = \Sigma_\infty$ carries the *fixed* $F_\infty$ on one side and a time-varying error map on the other (a one-sided contraction, rate $\rho(F_\infty)$) — the asymmetry the two anchors exploit.

*Proof.*

**Part 1.** $\mathcal{U}$ is monotone: completing the square, $\mathcal{U}(\Sigma) = \min_K\big[(I - KC)\Sigma(I - KC)' + KRK'\big]$ (the Joseph form, minimized over the gain $K$, optimum $K = \Sigma C'(C\Sigma C' + R)^{-1}$). For fixed $K$ the bracket is affine and monotone in $\Sigma$; a pointwise minimum of monotone maps is monotone, so $L_1 \preceq L_2 \Rightarrow \mathcal{U}(L_1) \preceq \mathcal{U}(L_2)$. Then $\Sigma \mapsto A\Sigma A' + GQG'$ is monotone, so $\mathcal{R}$ is monotone; iterating gives `eq:comparison`.

**Part 2.** Because $G = \operatorname{col}(G_1, 0)$ and $A$ has $e_2$-row $[\,0\ \ A_2\,]$, the $(2,2)$ block of $\mathcal{R}(\Sigma)$ is $\mathcal{R}(\Sigma)\!\mid_{22} = A_2\, \mathcal{U}(\Sigma)\!\mid_{22}\, A_2'$, so $\Sigma_{T+1}\!\mid_{22} = A_2\, \mathcal{U}(\Sigma_T)\!\mid_{22}\, A_2'$, and since $A_2$ is nonsingular (`eq:A2-inv`), $J_{T+1} = A_2^{-1\prime}\, (\mathcal{U}(\Sigma_T)\!\mid_{22})^{-1}\, A_2^{-1}$. Set $W_T := A_2^{-1\prime}\big[\,(\mathcal{U}(\Sigma_T)\!\mid_{22})^{-1} - (\Sigma_T\!\mid_{22})^{-1}\,\big] A_2^{-1}$, so `eq:Jrec` holds by construction. The update never increases the covariance, $\mathcal{U}(\Sigma) \preceq \Sigma$, and a principal block inherits the order, so $\mathcal{U}(\Sigma_T)\!\mid_{22} \preceq \Sigma_T\!\mid_{22}$; both $\succ 0$, inversion reverses, $(\mathcal{U}(\Sigma_T)\!\mid_{22})^{-1} \succeq (\Sigma_T\!\mid_{22})^{-1}$; congruence by $A_2^{-1}$ preserves $\succeq 0$, so $W_T \succeq 0$. Unrolling gives `eq:Jgram`.

**Part 3.** For `eq:diff-id`: the update obeys $\mathcal{U}(A_\sharp) - \mathcal{U}(B_\sharp) = (I - L(A_\sharp)C)(A_\sharp - B_\sharp)(I - L(B_\sharp)C)'$ — the Kalman update-difference, the bilinear remainder collapsing by the resolvent identity $S_\sharp^{-1} - S_\flat^{-1} = -S_\sharp^{-1}C(A_\sharp-B_\sharp)C'S_\flat^{-1}$ ($S_\sharp := CA_\sharp C'+R$); conjugating by $A$ and cancelling $GQG'$ gives `eq:diff-id`, and iterating gives `eq:diff-unroll`. For `eq:gap-ric`: $L(\Sigma_\infty + V) - L(\Sigma_\infty) = (I - L(\Sigma_\infty)C)VC'S_V^{-1}C$ gives the gain expansion; substituting into $\mathcal{R}(\Sigma_\infty+V) = F(\Sigma_\infty+V)(\Sigma_\infty+V)F(\Sigma_\infty+V)' + \cdots$ and using $\mathcal{R}(\Sigma_\infty)=\Sigma_\infty$ yields the displayed identity, whose subtracted term is a congruence of $S_V^{-1}\succ0$, hence $\succeq 0$. ∎

**Remark (why $A_2^{-1}$, and only $A_2$).** The measurement information propagates through the *inverse* of the dynamics on the uncontrollable–unstable block, legal precisely because $A_2$ is nonsingular (`eq:A2-inv`) — the open-loop $A$ and the stabilizable block $A_1$ are never inverted. On the antistable part $A_a^{-1}$ is Schur, so `eq:Jgram` converges (finite gramian, finite steady covariance); on the marginal part $A_m^{-1}$ sits on the unit circle, so it diverges (unbounded information, vanishing covariance). Under C3w the marginal block is absent and `eq:Jgram` is the convergent antistable gramian throughout.

<!-- verify: comparison (eq:comparison) and the linear A2^{-1} recursion (eq:Jrec, W_T>=0) validated in scratch/check_a03.py [D],[B]. Gap engine eq:diff-id resid 2e-16 (check_forget.py[1]); eq:gap-ric resid 1e-15/5e-10 (check_gapric.py). Ordering: A_2 = A_a (+) A_m (antistable first). W_T>=0 from U(Sigma)|22 <= Sigma|22. -->
<!-- verify: LIVE consumers — eq:Rmap feeds thm:formula (04, the Mobius/gap engine); app:machinery-2 (e2 identity, eq:Jrec/eq:Jgram) feeds lem:structure (antistable gramian eq:Sinf-gram); eq:diff-id/eq:diff-unroll feed lem:robust (08) / thm:payoff (robustness). eq:gap-ric (two-sided Stein) and eq:comparison are no longer on the arc-1 sufficiency path (their consumers were the retired squeeze anchors) — retained as standard tools / rate confirmation and for Arc 2. -->
<!-- verify: LEAN (phase A): eq:comparison = Dare.dareIter_mono (Estimation/Dare/Update.lean, via the Joseph-form gain minimization joseph_sub_updM); eq:Jrec = Dare.jRec + jRec_increment_posSemidef (Estimation/Dare/BlockInfo.lean; increment PSD via the new Löwner inversion-antitone lemma); eq:Jgram = Dare.jGram (phase F5: the generic unroll of eq:Jrec, backward-gramian form; the recursion hypothesis is jRec along a C2 run); eq:diff-id = Dare.dareStep_diff, eq:diff-unroll = Dare.dareIter_diff, eq:gap-ric = Dare.gapRic / gapRic_le (Estimation/Dare/GapEngine.lean). Axioms clean. -->
<!-- END FILE: a02-machinery.md -->

<!-- BEGIN FILE: a03-formula.md -->
<!-- thm:formula — the symplectic-pencil closed form. THE Arc-1 engine. Subsumes lem:supremal (from-above), -->
<!-- lem:lowerbound (from-below), and thm:necessity: the gap is one two-sided fixed-F_inf sandwich with a -->
<!-- homographic slide in the forward F_inf-gramian. Inversion-free, so singular A is absorbed (its null modes -->
<!-- are the pencil's infinite eigenvalues, kept uninverted). C3w-bound: needs F_inf Schur; the marginal case -->
<!-- (Arc 2) fails the gramian/sandwich and keeps the squeeze. -->
<!-- sec:formula -->
### The symplectic pencil and the gap formula

The whole Arc-1 gap $\Sigma_T - \Sigma_\infty$ has a single closed form: it sits between two copies of the fixed strong loop $F_\infty$, with a homographic slide between them. This is the discrete image of the stabilizing-solution formula of Callier, Winkin and Willems (1994). In continuous time the derivation exponentiates the Hamiltonian; in discrete time that step meets a singular $A$, and the naive symplectic *matrix* cannot survive it — it would invert $A$. We keep the associated *pencil* uninverted: the null modes of $A$ become eigenvalues at infinity of a regular pencil, ordinary points of its deflating structure, and the formula comes through built entirely from the Schur closed loop $F_\infty$ and the innovation weight — never from $A^{-1}$.

Write $H_C := C'R^{-1}C$ and $Q_w := GQG'$ for the innovation and process weights.

<!-- sec:formula-1 -->
**1. (The filter pencil.)** The recursion `eq:cov-rec` linearizes: the covariance quotient $\Sigma_T = Y_T X_T^{-1}$ rides the linear two-point flow

<!-- eq:pencil -->
$$ \mathcal{M} \begin{bmatrix} X_{T+1} \\ Y_{T+1} \end{bmatrix} = \mathcal{L} \begin{bmatrix} X_T \\ Y_T \end{bmatrix} \qquad \mathcal{L} = \begin{bmatrix} I & H_C \\ 0 & A \end{bmatrix} \quad \mathcal{M} = \begin{bmatrix} A' & 0 \\ -Q_w & I \end{bmatrix} \qquad \begin{bmatrix} X_0 \\ Y_0 \end{bmatrix} = \begin{bmatrix} I \\ \Sigma_0 \end{bmatrix} \tag{eq:pencil} $$

Neither $\mathcal{L}$ nor $\mathcal{M}$ carries an inverse of $A$; $\det\mathcal{M} = \det A'$, so $\mathcal{M}$ is singular exactly when $A$ is, sending the null modes of $A$ to eigenvalues at infinity. Under C1 the pencil is regular, with spectrum $\operatorname{spec}(F_\infty) \sqcup \operatorname{spec}(F_\infty)^{-\prime}$ paired reciprocally about the unit circle (`fact:dare-strong`, `eq:Finf-spec`).

<!-- sec:formula-2 -->
**2. (Block-triangularization by $\Sigma_\infty$.)** Conjugate on the right by the strong solution,

<!-- eq:Tsig -->
$$ T_\Sigma := \begin{bmatrix} I & 0 \\ \Sigma_\infty & I \end{bmatrix} \qquad T_\Sigma^{-1} \begin{bmatrix} X_T \\ Y_T \end{bmatrix} = \begin{bmatrix} X_T \\ (\Sigma_T - \Sigma_\infty)X_T \end{bmatrix} \tag{eq:Tsig} $$

which sends the covariance quotient to the **gap** quotient — the lower block becomes $(\Sigma_T-\Sigma_\infty)X_T$. Pairing $T_\Sigma$ with the left factor $P := \big[\begin{smallmatrix} I & 0 \\ -F_\infty\Sigma_\infty & I \end{smallmatrix}\big]$ triangularizes **both** pencil matrices at once, with no inverse anywhere:

<!-- eq:pencil-block -->
$$ P\, \mathcal{M}\, T_\Sigma = \begin{bmatrix} A' & 0 \\ 0 & I \end{bmatrix} \qquad P\, \mathcal{L}\, T_\Sigma = \begin{bmatrix} I + H_C\Sigma_\infty & H_C \\ 0 & F_\infty \end{bmatrix} \tag{eq:pencil-block} $$

Each lower-left block vanishes by substitution, not division. The $\mathcal{M}$-corner is $\Sigma_\infty - Q_w - F_\infty\Sigma_\infty A'$, zero by the strong identity $\Sigma_\infty - Q_w = F_\infty\Sigma_\infty A'$ **(id2)**; the $\mathcal{L}$-corner is $A\Sigma_\infty - F_\infty\Sigma_\infty(I + H_C\Sigma_\infty)$, zero by $A = F_\infty(I + \Sigma_\infty H_C)$ **(id1)**, and id1 also collapses the $\mathcal{L}$-diagonal to $A - F_\infty\Sigma_\infty H_C = F_\infty$. Both id1 and id2 are the strong DARE read off `eq:dare` (`fact:dare-strong`), and neither uses $A^{-1}$. So the lower block is the Schur loop $F_\infty$ (`lem:structure`-1), which drives the gap; the corner is the innovation weight $H_C$, which enters the gramian below through the **symmetric**
$$ \Omega \;=\; (I + H_C\Sigma_\infty)^{-1}H_C \;=\; (I - L_\infty C)'\,H_C \;=\; C'S_\infty^{-1}C \;=\; \Omega', \qquad L_\infty := \Sigma_\infty C'S_\infty^{-1}, \quad S_\infty := C\Sigma_\infty C' + R. $$

<!-- thm:formula -->
### Theorem (thm:formula) — Closed form for the gap

Let C1 and C3w hold. For every prior $\Sigma_0$ and every $T \ge 0$,

<!-- eq:formula -->
$$ \Sigma_T - \Sigma_\infty = F_\infty^{\,T}\, (\Sigma_0 - \Sigma_\infty)\, \big[\, I + \mathcal{G}_T(\Sigma_0 - \Sigma_\infty) \,\big]^{-1}\, (F_\infty')^{\,T} \tag{eq:formula} $$

where the middle factor is the forward $F_\infty$-gramian of the innovation weight,

<!-- eq:gramian -->
$$ \mathcal{G}_T := \sum_{k=0}^{T-1} (F_\infty')^k\, \Omega\, F_\infty^k \qquad \Omega = (I - L_\infty C)'\, C'R^{-1}C = \Omega' \tag{eq:gramian} $$

The gramian is finite, increasing to the Stein solution $\mathcal{G}_\infty = F_\infty'\mathcal{G}_\infty F_\infty + \Omega$; the denominator $I + \mathcal{G}_T(\Sigma_0-\Sigma_\infty)$ is nonsingular for every finite $T$. The formula uses only $\Sigma_\infty$, $F_\infty$, and $\Omega$ — no inverse of $A$ — so it holds verbatim when $A$ is singular.

*Proof.* Write $D := \Sigma_0 - \Sigma_\infty$, $F := F_\infty$, $\Gamma_T := CF^{\,T}$, and $\Omega_T := (F')^{\,T}\Omega F^{\,T} = \Gamma_T' S_\infty^{-1}\Gamma_T$; set $N_T := I + \mathcal{G}_T D$ and $G_T := F^{\,T} D\, N_T^{-1}(F')^{\,T}$, the right side of `eq:formula`. Every object is built from $F$, $\Omega$, $S_\infty$, and the slide $N_T^{-1}$ — no $A^{-1}$ — so each identity below holds verbatim at $\det A = 0$; there is no density argument and no forward pencil flow through the singular block. We prove by induction the joint claim: **$N_T$ is nonsingular and $\Sigma_\infty + G_T = \Sigma_T$**, with $\Sigma_T$ the iterate of `eq:cov-rec` from $\Sigma_0$. The second half is `eq:formula`.

**Base.** $N_0 = I$ and $\Sigma_\infty + G_0 = \Sigma_\infty + D = \Sigma_0$.

**Nonsingular denominator.** From `eq:gramian`, $\mathcal{G}_{T+1} = \mathcal{G}_T + \Omega_T$, so $N_{T+1} = N_T + \Omega_T D = (I + \Omega_T D N_T^{-1})N_T$ (using $N_T$ nonsingular). Under the induction hypothesis $\Sigma_T = \Sigma_\infty + G_T \succeq 0$ is a covariance, so $S_T := C\Sigma_T C' + R \succ 0$; and $\Gamma_T D N_T^{-1}\Gamma_T' = C G_T C'$, so $S_\infty + \Gamma_T D N_T^{-1}\Gamma_T' = S_\infty + C G_T C' = S_T$. The Sylvester determinant identity then gives
$$ \det\!\big(I + \Omega_T D N_T^{-1}\big) = \det\!\big(I + S_\infty^{-1}\Gamma_T D N_T^{-1}\Gamma_T'\big) = \frac{\det S_T}{\det S_\infty} > 0, $$
so $N_{T+1}$ is nonsingular. This is the closed-loop-transition nonsingularity of the flow — an equality of positive innovation determinants, not an appeal to a finite fraction.

**One Riccati step.** The gap form of the recursion (`app:machinery`, `eq:gap-ric`) reads $\mathcal{R}(\Sigma_\infty + V) - \Sigma_\infty = F\big[\,V - V C' S_V^{-1} C V\,\big]F'$ with $S_V = C(\Sigma_\infty + V)C' + R$. At $V = G_T$ (so $S_V = S_T$), substitute $G_T = F^{\,T} D N_T^{-1}(F')^{\,T}$ and factor $F^{\,T}(\cdot)(F')^{\,T}$ out of the bracket:
$$ G_T - G_T C' S_T^{-1} C G_T = F^{\,T}\Big[\, D N_T^{-1} - D N_T^{-1}\Gamma_T'\big(S_\infty + \Gamma_T D N_T^{-1}\Gamma_T'\big)^{-1}\Gamma_T D N_T^{-1} \,\Big](F')^{\,T}. $$
The push-through $\Gamma_T'\big(S_\infty + \Gamma_T X\Gamma_T'\big)^{-1} = \big(I + \Omega_T X\big)^{-1}\Gamma_T' S_\infty^{-1}$ at $X = D N_T^{-1}$ turns the bracket into
$$ D N_T^{-1}\big[\, I - (I + \Omega_T D N_T^{-1})^{-1}\Omega_T D N_T^{-1} \,\big] = D N_T^{-1}\big(I + \Omega_T D N_T^{-1}\big)^{-1} = D N_T^{-1}\, N_T N_{T+1}^{-1} = D N_{T+1}^{-1}, $$
the last two equalities using $N_{T+1} = (I + \Omega_T D N_T^{-1})N_T$. Hence $\mathcal{R}(\Sigma_\infty + G_T) - \Sigma_\infty = F^{\,T+1} D N_{T+1}^{-1}(F')^{\,T+1} = G_{T+1}$, i.e. $\Sigma_\infty + G_{T+1} = \mathcal{R}(\Sigma_T) = \Sigma_{T+1}$, closing the induction.

**Finiteness.** Under C3w, $F$ is Schur (`lem:structure`-1), so $\|(F')^k\Omega F^k\| \le c\,\gamma^{2k}\|\Omega\|$ (`fact:schur-decay`) and $\mathcal{G}_T \uparrow \mathcal{G}_\infty = F'\mathcal{G}_\infty F + \Omega$, the finite Stein solution. Both flanks of `eq:formula` are the Schur $F$; the middle is the bounded slide $N_T^{-1}$; nothing sees a singular $A$. ∎

<!-- cor:attract -->
**Corollary (rate of attraction) — cor:attract.** The two flanking Schur factors of `eq:formula` set the rate: *whenever* the homographic slide is uniformly bounded, $b' := \sup_{T}\big\|[I+\mathcal{G}_TD]^{-1}\big\| < \infty$,

$$ \|\Sigma_T - \Sigma_\infty\| \;\le\; \|F_\infty^{\,T}\|^2\, \|\Sigma_0 - \Sigma_\infty\|\, b' \;\le\; c\, \gamma^{2T} \;\longrightarrow\; 0 \qquad \gamma \in (\rho(F_\infty), 1) $$

so the attraction is exponential at rate $\rho(F_\infty)^2$ (`def:rate`, `eq:Finf-c3w`) — held *from above and below at once* by the one identity, with no separate domination and no floor. The slide is bounded precisely under C2, where the limiting denominator is nonsingular (`lem:sysinterp`); that boundedness and the resulting unconditional homecoming are assembled in `thm:sufficiency`.

<!-- cor:phi -->
**Corollary (the running product) — cor:phi.** The error-map product of the run factors through the fixed loop,

<!-- eq:phi-closed -->
$$ \Phi_T := F(\Sigma_{T-1}) \cdots F(\Sigma_0) = F_\infty^{\,T}\, \big[\, I + (\Sigma_0 - \Sigma_\infty)\mathcal{G}_T \,\big]^{-1} \tag{eq:phi-closed} $$

a fixed $F_\infty^{\,T}$ against a bounded homographic factor, so $\|\Phi_T\| \le c\,\gamma^T$ directly — the running products are geometrically bounded by closed form, needing no uniform-stability import.

<!-- cor:necessity -->
**Corollary (the convergence criterion) — cor:necessity.** The formula reduces homecoming to one linear-algebra question — nonsingularity of the limiting denominator:

$$ \Sigma_T \to \Sigma_\infty \quad\Longleftarrow\quad I + \mathcal{G}_\infty(\Sigma_0 - \Sigma_\infty) \ \text{nonsingular} \quad\Longleftarrow\quad \text{C2}\ (\Sigma_a \succ 0,\ \texttt{lem:criterion}). $$

The first implication is `thm:sufficiency` (a bounded slide makes `eq:formula` decay); the second is `lem:sysinterp` (under C2 the denominator is nonsingular, since $\ker(\Sigma_0 X_- - Y_-) \subseteq \ker\Sigma_0 \cap \mathcal{X}_{a,uc} = \{0\}$). The converse chain — $\neg$C2 $\Rightarrow$ singular denominator $\Rightarrow$ gap pinned off zero, no homecoming without an informed antistable prior — is the **necessity** direction (the reverse inclusion of `eq:kernel-id`), currently flagged OPEN. So the criterion is established in the direction the GES branch of `eq:dichotomy` consumes; the converse awaits the necessity write-up.

<!-- verify: pencil eq:pencil linearizes eq:cov-rec (graph quotient rides M[next]=L[now], no A^-1). TWO-SIDED block-tri eq:pencil-block: P M T_S == [[A',0],[0,I]] resid 0-3.6e-15 (EXACTLY 0 at singular A), P L T_S == [[I+HcS,Hc],[0,F]] resid 5.3-8.5e-15 (check_A15_rewrite.py). id1 (A=F(I+S Hc)) and id2 (S-Qw=F S A') are the strong DARE off eq:dare; Omega=(I+HcS)^-1 Hc=(I-LC)'Hc=C'S_inf^-1 C symmetric to 1e-16. This is the form 04a already consumes (id1 transposed, P M/L T_S blocks) — the rewrite retires the one-sided S=M^-1 L / F_inf^-' / W=A^-' Hc statement (undefined at det A=0). -->
<!-- verify: GAP FORMULA eq:formula PROVED by joint induction (N_T nonsingular AND Sinf+G_T=Sigma_T), inversion-free, NO forward pencil flow, NO density. (1) A4 nonsingularity N_{T+1}=(I+Om_T D N_T^-1)N_T, det(I+Om_T D N_T^-1)=detS_T/detS_inf>0 (min 0.52) resid 1.8e-15 (check_A4_nonsing.py) — replaces "fraction of a finite matrix". (2) A3 Riccati step via eq:gap-ric + push-through: bracket collapses to D N_{T+1}^-1, resid 1.8e-15..5.8e-12 (BRACE), giving R(Sinf+G_T)-Sinf==G_{T+1} resid 5.3e-15..3.8e-14 (check_A15_rewrite.py). eq:formula itself exact 6e-15..1.6e-13 over 5 priors x 60 steps on nonsingular A, SINGULAR A (zero mode in A_1), SINGULAR A + defective antistable Jordan. ||G_inf|| finite (1.7-2.9). Every step F-power / Omega / S_inf / N_T-slide / gap-Riccati / push-through — no A^-1, no F_inf^-1, exact at det A=0 (A5). -->
<!-- verify: cor:phi eq:phi-closed Phi_T = F_inf^T[I+D G_T]^-1 exact, resid 1.6e-15 on singular A (check_payoffs.py) — retires the uniform-filter-stability import (eq:Phi-bound). -->
<!-- verify: cor:necessity — C2: |det(I+G_inf D)|=0.41, gap->0; not-C2 (singular antistable prior): |det|=2e-15, gap stuck at 5.46 (check_payoffs.py, check_endtoend.py). SUFFICIENCY direction (C2 => nonsingular => converges) now PROVED: lem:sysinterp (04a, subset inclusion) + thm:sufficiency (06). NECESSITY direction (¬C2 => singular) = reverse inclusion of eq:kernel-id — now VERIFIED at the kernel level (sysinterp_singular, 04a; eq:info-fix = info_fix); the stuck-gap reading remains a prose signpost. This corollary is a downstream signpost (audited prose cross-ref to lem:sysinterp/thm:sufficiency); it proves nothing in 04. -->
<!-- verify: C3w-bound. Marginal mode (C2w, not C3w): rho(F_inf)=1, ||G_T|| diverges (3.4->79), ||F_inf^T|| ~2.4 does not decay (check_c2w_boundary.py) — gramian and sandwich both fail; the marginal case (Arc 2) keeps the squeeze. -->
<!-- verify: SUBSUMES / RETIRES — the from-above anchor (retired-04-supremal.md, lem:supremal) is the upper flank F_inf^T(.)(F_inf')^T of eq:formula; the from-below anchor (retired-05-lowerbound.md, lem:lowerbound) and its import eq:Phi-bound are replaced by lem:sysinterp's "M_inf nonsingular under C2". Both files RETIRED out of the live sequence. LIVE consumers: thm:main (unwritten) reads thm:sufficiency + cor:necessity; thm:payoff (robustness) reads eq:formula + cor:phi. Deps of thm:formula: lem:structure-1 (F_inf Schur, eq:bounded), app:machinery (eq:Rmap, eq:gap-ric), a00-facts (fact:schur-decay, fact:dare-strong). NOTE: cor:attract and cor:necessity forward-point to lem:sysinterp/thm:sufficiency (allowlisted prose cross-refs) — not proof-deps, so no 04<->04a/06 cycle. -->
<!-- verify: DECK-WIDE eq:pencil-block sync — 04a (sec:formula-2, id1, P M/L T_Sigma) now matches this file's two-sided display exactly; no other file references the retired F_inf^-'/W form. -->
<!-- verify: LEAN (phase E4a): thm:formula + cor:phi = Estimation/Dare/Formula.lean. eq:formula = formula — the deck's own joint induction (det-unit of N_T AND the closed form), via slide_step (the A4 push-through slide), pencil_block_M/pencil_block_L (the two-sided block-tri eq:pencil-block), strong_id1/strong_id2 (id1/id2 off the strong DARE), innovWeight_eq_oneSubKC + shear_mul_innovWeight (the Omega/shear identities), and gapRic with its hypothesis generalized to PSD sums; the A4 determinant step is Weinstein-Aronszajn (Matrix.det_one_add_mul_comm), inversion-free throughout, exact at det A = 0. G_T = fwdGram: fwdGram_posSemidef, fwdGram_eq_sylvIter, fwdGram_tendsto_stein (G_inf finite as the Stein limit); the geometric-rate display = formula_rate. cor:phi eq:phi-closed = errProd_closed (det-unit of I+D*G_T and Phi_T(I+D*G_T) = F_inf^T) with display form errProd_eq, via slide_swap. Axioms clean on all heads. -->
<!-- verify: rate DECISION deferred to thm:payoff. -->
<!-- (Gate-2 scratch: /home/claude/arc1scratch/check_A15_rewrite.py, check_A4_nonsing.py, check_pencil_formula3.py, check_payoffs.py, check_endtoend.py, check_c2w_boundary.py.) -->
<!-- END FILE: a03-formula.md -->

<!-- BEGIN FILE: a04-subspace.md -->
<!-- lem:sysinterp — the geometry that decides whether the gap dies. Discrete dual of CWW lem:sysinterp, -->
<!-- carried in the deflating-subspace basis [X_-;Y_-] instead of the (for singular A nonexistent) -->
<!-- antistabilizing solution Sigma_-. The attraction denominator I+G_inf D is nonsingular iff the prior -->
<!-- plane is transverse to the antistable deflating subspace V_-, iff C2. Both directions; sufficiency uses -->
<!-- the (subset) inclusion. A^{-1}-hygiene: no inverse of A, M, L, F_inf, X_-; no Sigma_-. The one benign -->
<!-- inverse is the frame W (complementary deflating subspaces) and the p×p innovation block in Omega. -->
<!-- codenames (comments only): Charybdis=lem:supremal, Scylla=lem:lowerbound. -->
<!-- lem:sysinterp -->
### Lemma (lem:sysinterp) — The attraction denominator and the uninformed antistable prior

Let C1 and C3w hold, and work in the frame `eq:three-block`, where the uncontrollable block is antistable-only ($e_2 = e_a$) and $\Sigma_0 = \operatorname{diag}(\Sigma_1, \Sigma_a)$. Write $D := \Sigma_0 - \Sigma_\infty$ and $M_\infty := I + \mathcal{G}_\infty D$ for the limiting denominator of the gap formula `eq:formula`, and let $[X_-; Y_-]$ be a basis of the antistable deflating subspace $\mathcal{V}_-$ of the pencil `eq:pencil` (below). Then the criterion object $\Sigma_0 X_- - Y_-$ carries the denominator's kernel,

<!-- eq:kernel-id -->
$$ \ker M_\infty \;\cong\; \ker\big(\Sigma_0 X_- - Y_-\big) \;=\; \ker\Sigma_0 \cap \mathcal{X}_{a,uc}, \tag{eq:kernel-id} $$

so $M_\infty$ is nonsingular **iff** C2, which under C3w coincides with C2w $\iff\Sigma_a\succ0$ (`lem:criterion-w`, `eq:prior-pos`). In particular, under C1 + C2 + C3w the denominator of `eq:formula` is nonsingular; and under C1 + C3w, $\Sigma_T \to \Sigma_\infty$ fails whenever C2 fails, since then $M_\infty$ is singular and the gap `eq:formula` is pinned off zero. Both inclusions are proved below: $\subseteq$ (the attraction/sufficiency half) and $\supseteq$ (the necessity half).

*Proof.* The whole argument is the discrete dual of the continuous system-interpretation lemma of Callier, Winkin and Willems (1994), carried in the deflating-subspace basis $[X_-; Y_-]$ rather than through a graph. The one discrete obstruction is that the antistabilizing solution $\Sigma_-$ — the graph of $\mathcal{V}_-$ — need not exist: for singular $A$ the leading block $X_-$ is singular and $\Sigma_- = Y_- X_-^{-1}$ is undefined (its innovation covariance $C\Sigma_- C' + R$ collapses). We therefore never form the graph; every object is built from the pair $(X_-, Y_-)$, which is well defined for every $A$.

**The two deflating subspaces.** Under C1 the pencil `eq:pencil` is regular with spectrum $\operatorname{spec}(F_\infty) \sqcup \operatorname{spec}(F_\infty)^{-\prime}$ (`fact:dare-strong`, `eq:Finf-spec`). Under C3w the $n$ eigenvalues $\operatorname{spec}(F_\infty)$ lie strictly inside the unit disk and their $n$ reciprocals strictly outside or at infinity (the null modes of $A$, since $\det\mathcal{M} = \det A'$), the two sets disjoint. The pencil then has complementary deflating subspaces for the two spectral halves (Lancaster–Rodman 1995): the **inside** half is the graph of the strong solution,

$$ \mathcal{V}_+ = \operatorname{range}\begin{bmatrix} I \\ \Sigma_\infty \end{bmatrix}, $$

and the **outside-or-infinite** half is $\mathcal{V}_- = \operatorname{range}[X_-; Y_-]$, on which the pencil acts through the reflected block $E_-$,

<!-- eq:deflate -->
$$ \mathcal{L}\begin{bmatrix} X_- \\ Y_- \end{bmatrix} = \mathcal{M}\begin{bmatrix} X_- \\ Y_- \end{bmatrix} E_-, \qquad \rho(E_-) < 1, \tag{eq:deflate} $$

$E_-$ Schur because its spectrum is $\operatorname{spec}(F_\infty)$ reflected back inside together with the zeros standing for $A$'s null modes. Being deflating subspaces for disjoint spectra, $\mathcal{V}_+$ and $\mathcal{V}_-$ are complementary, so

<!-- eq:frame -->
$$ W := \begin{bmatrix} I & X_- \\ \Sigma_\infty & Y_- \end{bmatrix} \quad\text{is nonsingular.} \tag{eq:frame} $$

This is the one benign inverse of the argument — the deflating-subspace frame, never $A^{-1}$, $X_-^{-1}$, or $\Sigma_-$. Writing the blocks of `eq:deflate` out with $\mathcal{L} = \big[\begin{smallmatrix} I & H_C \\ 0 & A \end{smallmatrix}\big]$, $\mathcal{M} = \big[\begin{smallmatrix} A' & 0 \\ -Q_w & I \end{smallmatrix}\big]$,

<!-- eq:deflate-rows -->
$$ \text{(i)}\quad X_- + H_C Y_- = A' X_- E_- \qquad\qquad \text{(ii)}\quad A Y_- = Y_- E_- - Q_w X_- E_-. \tag{eq:deflate-rows} $$

**The gap object and the link.** Put $Z := \Sigma_\infty X_- - Y_-$, the inversion-free avatar of $(\Sigma_\infty - \Sigma_-)X_-$. Conjugating `eq:deflate` by the gap similarity $T_\Sigma$ (`eq:Tsig`) block-triangularizes it (`sec:formula`-2): with $T_\Sigma^{-1}[X_-; Y_-] = [X_-; -Z]$ and $P\mathcal{M}T_\Sigma = \big[\begin{smallmatrix} A' & 0 \\ 0 & I \end{smallmatrix}\big]$, $P\mathcal{L}T_\Sigma = \big[\begin{smallmatrix} I+H_C\Sigma_\infty & H_C \\ 0 & F_\infty \end{smallmatrix}\big]$, the two block rows of the conjugated relation read

$$ (I + H_C\Sigma_\infty)X_- - H_C Z = A' X_- E_-, \qquad F_\infty Z = Z E_-. $$

The lower row is the **intertwining** $F_\infty Z = Z E_-$. In the upper row substitute the structural identity $A' = (I + H_C\Sigma_\infty)F_\infty'$ (`eq:pencil-block`, id1 transposed) and cancel the nonsingular factor $I + H_C\Sigma_\infty$; using the innovation-form identity $(I + H_C\Sigma_\infty)^{-1}H_C = (I - L_\infty C)'H_C = \Omega$ (`eq:gramian`) this becomes the **Sylvester relation**

<!-- eq:sylv -->
$$ X_- - F_\infty' X_- E_- = \Omega Z. \tag{eq:sylv} $$

Both hold with no inverse of $A$: the only inverse used is that of $I + H_C\Sigma_\infty$, a $\Sigma_\infty$-shear, discharged by the $p\times p$ innovation block of $\Omega$. Telescoping `eq:sylv` through the intertwining — $\Omega Z E_-^k = \Omega F_\infty^k Z$ by $F_\infty^k Z = Z E_-^k$, and both $F_\infty, E_-$ Schur —

$$ \mathcal{G}_\infty Z = \sum_{k\ge0}(F_\infty')^k \Omega F_\infty^k Z = \sum_{k\ge0}(F_\infty')^k \Omega Z E_-^k = \sum_{k\ge0}\Big[(F_\infty')^k X_- E_-^k - (F_\infty')^{k+1} X_- E_-^{k+1}\Big] = X_-, $$

the sum collapsing since $(F_\infty')^m X_- E_-^m \to 0$. This is the **link** $\mathcal{G}_\infty Z = X_-$; equivalently, since $M_\infty X_- = X_- + \mathcal{G}_\infty(\Sigma_0 - \Sigma_\infty)X_- = X_- - \mathcal{G}_\infty Z + \mathcal{G}_\infty(\Sigma_0 X_- - Y_-)$ and $X_- = \mathcal{G}_\infty Z$,

<!-- eq:link -->
$$ M_\infty X_- = \mathcal{G}_\infty\big(\Sigma_0 X_- - Y_-\big). \tag{eq:link} $$

**Transversality — the isomorphism of `eq:kernel-id`.** A vector $[w; \Sigma_0 w]$ of the prior plane lies in $\mathcal{V}_- = \operatorname{range}[X_-; Y_-]$ iff $w = X_- t$, $\Sigma_0 w = Y_- t$ for some $t$, i.e. iff $t \in \ker(\Sigma_0 X_- - Y_-)$; since $[X_-; Y_-]$ has full column rank this identifies $[I;\Sigma_0]\cap\mathcal{V}_- \cong \ker(\Sigma_0 X_- - Y_-)$. To match this with $\ker M_\infty$, take $v \in \ker M_\infty$ and expand $[v; \Sigma_0 v] = W[\alpha;\beta] = [\alpha + X_-\beta;\ \Sigma_\infty\alpha + Y_-\beta]$ in the frame `eq:frame`. The two blocks give $X_-\beta = v - \alpha$ and $Y_-\beta = \Sigma_0 v - \Sigma_\infty\alpha$, so $(\Sigma_0 X_- - Y_-)\beta = \Sigma_0(v - \alpha) - (\Sigma_0 v - \Sigma_\infty\alpha) = -D\alpha$. Applying $\mathcal{G}_\infty$ and using `eq:link` on the left, $M_\infty X_-\beta = M_\infty(v - \alpha) = -M_\infty\alpha$ (as $M_\infty v = 0$), while the right is $-\mathcal{G}_\infty D\alpha$; hence $M_\infty\alpha = \mathcal{G}_\infty D\alpha$, i.e. $(I + \mathcal{G}_\infty D)\alpha = \mathcal{G}_\infty D\alpha$, forcing $\alpha = 0$. Thus $[v; \Sigma_0 v] = [X_-\beta; Y_-\beta] \in \mathcal{V}_-$ with $\beta \in \ker(\Sigma_0 X_- - Y_-)$ and $v = X_-\beta$. Conversely `eq:link` sends any $t \in \ker(\Sigma_0 X_- - Y_-)$ to $M_\infty X_- t = 0$. So $v \mapsto \beta$, $t \mapsto X_- t$ are mutually inverse between $\ker M_\infty$ and $\ker(\Sigma_0 X_- - Y_-)$, giving the isomorphism of `eq:kernel-id`.

**The reverse-time energy certificate.** The kernel identity now reduces to a statement about $\ker(\Sigma_0 X_- - Y_-)$, and the tool is the discrete dual of the antistabilizing energy $-\Sigma_- \succeq 0$ (Callier–Winkin–Willems 1994, from the reverse-time cost $\int(\|Cx^\star\|^2 + \|u^\star\|^2)$), carried on $\mathcal{V}_-$ with no $\Sigma_-$. From `eq:deflate-rows`, using $(X_- E_-)'A = (A' X_- E_-)' = X_-' + Y_-' H_C$ (row i) and $Y_- E_- = A Y_- + Q_w X_- E_-$ (row ii),

$$ E_-'(X_-'Y_-)E_- = (X_- E_-)'(Y_- E_-) = (X_- E_-)'A Y_- + (X_- E_-)'Q_w(X_- E_-) = X_-'Y_- + Y_-'H_C Y_- + (X_- E_-)'Q_w(X_- E_-), $$

so the per-step drop is manifestly a sum of the innovation and process energies,

<!-- eq:perstep -->
$$ \Pi := E_-'(X_-'Y_-)E_- - X_-'Y_- = Y_-'H_C Y_- + (X_- E_-)'Q_w(X_- E_-) \;\succeq\; 0. \tag{eq:perstep} $$

Since $\Pi$ is symmetric while $E_-'(X_-'Y_-)E_- - X_-'Y_-$ is built from the possibly-nonsymmetric $X_-'Y_-$, the antisymmetric part $K := X_-'Y_- - Y_-'X_-$ obeys $E_-'K E_- = K$; with $E_-$ Schur this Stein relation forces $K = 0$, so $X_-'Y_- = Y_-'X_-$ is symmetric (the Lagrangian property of $\mathcal{V}_-$). Unrolling `eq:perstep` with $E_-$ Schur,

<!-- eq:energy -->
$$ -X_-'Y_- = \sum_{k\ge0}(E_-^k)'\,\Pi\,E_-^k \;\succeq\; 0, \tag{eq:energy} $$

the convergent $E_-$-gramian of the per-step energy. This is the certificate that replaces $-\Sigma_- \succeq 0$; it is exact for singular $A$.

**The kernel identity ($\subseteq$).** Let $u \in \ker(\Sigma_0 X_- - Y_-)$, so $\Sigma_0 X_- u = Y_- u$, and set $v := X_- u$. Left-multiplying by $X_-'$ and pairing with $u$, then using $X_-'Y_- = Y_-'X_-$,

$$ u'(X_-'\Sigma_0 X_-)u \;+\; u'(-X_-'Y_-)u \;=\; u'X_-'\Sigma_0 X_- u - u'X_-'Y_- u \;=\; 0. $$

Both terms are nonnegative — the first by $\Sigma_0 \succeq 0$, the second by `eq:energy` — so each vanishes. From $u'X_-'\Sigma_0 X_- u = 0$ and $\Sigma_0 \succeq 0$, $\Sigma_0 v = 0$; in particular $Y_- u = \Sigma_0 X_- u = 0$. From $u'(-X_-'Y_-)u = 0$ and `eq:energy`, $\Pi\, E_-^k u = 0$ for every $k$, so by `eq:perstep` both energies vanish along the reflected orbit:

$$ C\,Y_- E_-^k u = 0\ (k \ge 0), \qquad G'\,X_- E_-^{k} u = 0\ (k \ge 1). $$

Write $p_k := X_- E_-^k u$, $q_k := Y_- E_-^k u$. Since $G' p_k = 0$ gives $Q_w p_k = 0$ for $k \ge 1$, row (ii) of `eq:deflate-rows` along the orbit reads $A q_k = q_{k+1}$, and $q_0 = Y_- u = 0$ gives $q_k = A^k q_0 = 0$ for all $k$; then row (i) reads $p_k = A' p_{k+1}$. Thus the state orbit obeys

<!-- eq:orbit -->
$$ p_k = A' p_{k+1}\ (k \ge 0), \qquad G' p_k = 0\ (k \ge 1), \qquad p_k \to 0, \tag{eq:orbit} $$

the last because $E_-$ is Schur. We claim `eq:orbit` forces $v = p_0 \in \mathcal{X}_{a,uc}$. In the frame `eq:three-block` write $p_k = [a_k; b_k]$ over $e_1 \oplus e_a$, so $A' = \big[\begin{smallmatrix} A_1' & 0 \\ A_{1a}' & A_a' \end{smallmatrix}\big]$, $G' = [G_1'\ \ 0]$, and `eq:orbit` gives $a_k = A_1' a_{k+1}$, $G_1' a_k = 0\ (k\ge1)$, $a_k \to 0$; the goal is $a_0 = 0$. By stabilizability of $(A_1, G_1)$ — detectability of the dual pair $(G_1', A_1')$ — choose an output injection $L_{\mathrm{inj}}$ with $A_1' - L_{\mathrm{inj}} G_1'$ Schur. Since $G_1' a_{k+1} = 0$ for every $k \ge 0$, the backward orbit rewrites as $a_k = A_1' a_{k+1} = (A_1' - L_{\mathrm{inj}} G_1')\,a_{k+1}$, so $a_j = (A_1' - L_{\mathrm{inj}} G_1')^{m}\, a_{j+m}$ for every $m$; letting $m \to \infty$ with $a_{j+m} \to 0$ and the injected powers Schur-bounded gives $a_j = 0$ for every $j \ge 0$. Therefore $p_0 = [0; b_0] \in e_a = \mathcal{X}_{a,uc}$. Together with $\Sigma_0 v = 0$ this places $v \in \ker\Sigma_0 \cap \mathcal{X}_{a,uc}$.

**The kernel identity ($\supseteq$) — the necessity direction.** Reverse the inclusion: let $v \in \ker\Sigma_0 \cap \mathcal{X}_{a,uc}$, so $v \in e_a$ and $\Sigma_0 v = 0$; we show $v \in \ker M_\infty$. Since $\Sigma_0 v = 0$, $M_\infty v = v + \mathcal{G}_\infty(\Sigma_0 - \Sigma_\infty)v = v - \mathcal{G}_\infty\Sigma_\infty v$, so it suffices that the steady information invert the steady covariance on $\mathcal{X}_{a,uc}$,

<!-- eq:info-fix -->
$$ \mathcal{G}_\infty\Sigma_\infty v = v \qquad (v \in \mathcal{X}_{a,uc}). \tag{eq:info-fix} $$

Two facts on $e_a$ drive this, both from the frame `eq:three-block` ($A$ upper-triangular with $e_a$-diagonal $A_a$, so $A'$ leaves $e_a$ invariant and acts there as $A_a'$; $G = \operatorname{col}(G_1, 0)$, so $Q_w = GQG'$ kills $e_a$). First, the DARE in the form $\Sigma_\infty = F_\infty\Sigma_\infty A' + Q_w$ (from $A\,\mathcal{U}(\Sigma_\infty) = F_\infty\Sigma_\infty$, using $\mathcal{U}(\Sigma_\infty) = (I - \Sigma_\infty\Omega)\Sigma_\infty$ and $F_\infty = A(I - \Sigma_\infty\Omega)$), evaluated at $(A_a')^{-1}v \in e_a$, gives $\Sigma_\infty(A_a')^{-1}v = F_\infty\Sigma_\infty v + Q_w(A_a')^{-1}v = F_\infty\Sigma_\infty v$, whence

$$ F_\infty\Sigma_\infty v = \Sigma_\infty(A_a')^{-1}v, \qquad\text{so}\qquad F_\infty^k\Sigma_\infty v = \Sigma_\infty(A_a')^{-k}v. $$

Second, transposing $F_\infty = A(I - \Sigma_\infty\Omega)$ (`eq:gramian`) and using $A'|_{e_a} = A_a'$,

$$ F_\infty'(A_a')^{-1}u = (I - \Omega\Sigma_\infty)u \qquad (u \in e_a). $$

Now telescope, writing $u_k := (A_a')^{-k}v \in e_a$:
$$ \mathcal{G}_\infty\Sigma_\infty v = \sum_{k\ge0}(F_\infty')^k\,\Omega\,F_\infty^k\Sigma_\infty v = \sum_{k\ge0}(F_\infty')^k\,\Omega\Sigma_\infty\,u_k = \sum_{k\ge0}\Big[(F_\infty')^k u_k - (F_\infty')^{k+1}u_{k+1}\Big] = v, $$
the summand collapsing by the second fact ($\Omega\Sigma_\infty u_k = u_k - F_\infty'(A_a')^{-1}u_k = u_k - F_\infty' u_{k+1}$) and the sum by $(F_\infty')^k u_k = (F_\infty')^k(A_a')^{-k}v \to 0$ ($F_\infty$ and $A_a^{-1}$ both Schur). This is `eq:info-fix`, so $M_\infty v = 0$: every uninformed antistable prior direction sits in $\ker M_\infty$. Hence $\ker\Sigma_0 \cap \mathcal{X}_{a,uc} \subseteq \ker M_\infty$.

**Conclusion — the sharp criterion.** The two inclusions and the isomorphism close `eq:kernel-id` to the equality $\ker M_\infty = \ker\Sigma_0 \cap \mathcal{X}_{a,uc}$. By `lem:criterion-w` (C2 $\iff$ C2w under C3w, `eq:prior-pos`), $\Sigma_a \succ 0 \iff \ker\Sigma_0 \cap \mathcal{X}_{a,uc} = \{0\}$, so $M_\infty = I + \mathcal{G}_\infty D$ is **nonsingular iff C2**. The $\subseteq$ direction is what `thm:sufficiency` consumes ($M_\infty$ nonsingular under C1 + C2 + C3w); the $\supseteq$ direction is the necessity lever — under C1 + C3w, $\neg$C2 forces $M_\infty$ singular and the gap `eq:formula` off zero, so $\Sigma_T \not\to \Sigma_\infty$. ∎

<!-- The reverse inclusion ker Sig0 ∩ X_auc ⊆ ker(Sig0 X_- - Y_-) is the NECESSITY half: an uninformed -->
<!-- The reverse inclusion ker Sig0 ∩ X_auc ⊆ ker M_inf is the NECESSITY half, now PROVEN above via the -->
<!-- info-fixed-point identity eq:info-fix: G_inf Sinf v = v for v in X_auc, so M_inf v = v - G_inf Sinf v = 0 -->
<!-- when Sig0 v = 0. Mechanism: an uninformed antistable prior direction (¬C2) leaves M_inf singular and the -->
<!-- gap pinned off zero (Sigma_T ̸→ Sigma_inf since Sigma_inf|aa ≻ 0). Completes eq:kernel-id to EQUALITY and -->
<!-- gives the criterion "M_inf nonsingular ⟺ C2" (C1 + C3w branch). -->
<!-- verify: GATE-2 (check_reverse2.py). eig-1 eigenspace of G_inf Sinf == e_a (resid 1.3e-15); (I-G_inf Sinf)v=0 -->
<!-- on e_a (~1e-15). Telescoping steps: (1) F_inf Sinf v = Sinf (A_a')^{-1}v resid 2e-15; (2) F_inf'(A_a')^{-1}u -->
<!-- = (I - Om Sinf)u resid 6e-16; (3) sum_k (F_inf')^k Om Sinf (A_a')^{-k}v = v resid 9e-16. Also M_inf v = 0 for -->
<!-- uninformed antistable v, M_inf v != 0 under C2 (check_reverse_incl.py, 1.6e-15 vs 0.29). ⊆-side dim -->
<!-- ker(Sig0 X_- - Y_-) = n_a under ¬C2 / = 0 under C2 (check_subspace_coords.py). NOTE the plug-in is via M_inf -->
<!-- (eq:info-fix), NOT [v;0]∈V_- (that is false: check_reverse2.py CLAIM A residual ~0.9). -->


**Remark (why the subspace, not the graph).** Every step above is exact at $\det A = 0$ because it lives on $\mathcal{V}_-$, a genuine deflating subspace of the regular pencil, and never on its graph $\Sigma_- = Y_- X_-^{-1}$. The obstruction is precise: the reciprocal pairing sends an antistable closed-loop eigenvalue to infinity, so $S_- = C\Sigma_- C' + R$ is singular and $\Sigma_-$ is not a DARE solution. The scalar witness $a = 0$, $g = 0$, $c = r = q = 1$ makes it plain — the DARE $\Sigma = a^2\Sigma/(\Sigma + 1)$ has the unique solution $\Sigma_\infty = 0$, and the value $\Sigma = -1$ is the spurious root from clearing $(\Sigma+1)$, exactly where that denominator vanishes. The pair $(X_-, Y_-)$ and the certificate `eq:energy` are finite and correct throughout.

<!-- verify: eq:deflate L V- = M V- E_- with rho(E_-)<1 (=0.8), and rows (i),(ii) of eq:deflate-rows: resid 3e-16/1e-15 on nonsingular, singular A, singular+defective antistable Jordan, stable-unobservable (check_final.py, check_closing.py). W=[V+ V-] invertible incl. singular A (detW off zero). -->
<!-- verify: link — sub-identities (a) eq:sylv X_- - F'X_-E_- = Omega Z and (b) F Z = Z E_- resid 3e-16..3e-14; telescope G_inf Z = X_- resid 8e-16..1e-14; eq:link M_inf X_- = G_inf(Sig0 X_- - Y_-) resid 1e-15 (check_telescope.py, check_final.py, check_bridge.py). Innovation-form identity (I+Hc Sinf)^{-1}Hc = Omega = C'Sinn^{-1}C verified (H_C-Omega = H_C Sinf Omega, algebraic). -->
<!-- verify: transversality — dim ker M_inf = dim ker(Sig0 X_- - Y_-) in all cases; for v in ker M_inf the V+ component alpha = 0 to 1e-16 so [v;Sig0 v] in V_- (check_bridge.py). -->
<!-- verify: reverse-energy certificate — eq:perstep Pi = Y'HcY + (XE)'Qw(XE) matches E'(X'Y)E - X'Y to 1e-16, min eig Pi >= 0; X'Y symmetric (Stein K = E'KE => K=0); eq:energy -X'Y = sum (E^k)'Pi E^k resid 3e-16, min eig(-X'Y)=0 with n_a-dim kernel (check_closing.py, check_XmYm.py, check_energy.py). Equals the pseudoinverse crux X_-'(G_inf^# - Sinf)X_- = -X_-'Y_-, and crux' G_inf - G_inf Sinf G_inf >= 0 <=> rho(G_inf Sinf)<=1 (=1, n_a eigs at 1) (check_dual_crux.py, check_crux_prime.py). -->
<!-- verify: kernel identity — dim ker(Sig0 X_- - Y_-) = dim(ker Sig0 ∩ e_a): 0 under C2, n_a under ¬C2, both nonsingular and singular A; the kernel vector maps X_- u -> e_a direction in ker Sig0 (check_subspace_coords.py, discover_kernel.py). Landing: q_k=0, p_k=A'p_{k+1}, G'p_k=0 (k>=1), v=X_-u in e_a (||v_e1||=0) on singular A + Jordan (check_closing.py). -->
<!-- verify: consumers — thm:sufficiency reads eq:kernel-id ⊆ (M_inf nonsingular under C2); 06b-necessity (B, C3w branch) reads the ⊇ / equality (M_inf singular under ¬C2 => no convergence). Deps: eq:pencil, eq:pencil-block (id1, T_Sigma block-tri), eq:gramian (Omega, G_inf, F_inf=A(I-Sinf Omega)), lem:criterion-w (C2<=>C2w under C3w <=> Sigma_a>0), lem:structure-1 (F_inf Schur), fact:dare-strong (pencil spectrum eq:Finf-spec). The ⊇ direction (eq:info-fix) folds the former standalone thm:necessity into this lemma. C3w enters ONLY via F_inf Schur / disjoint pencil spectra (frame W invertible, E_- Schur) — confined to this GES branch; the GAS/marginal argument does not read it. -->
<!-- verify: LEAN (phase E4b): lem:sysinterp = Estimation/Dare/Subspace.lean. The Lancaster-Rodman deflating-pair frame enters as the single structural import `structure DeflatingPair` (Xm/Ym/Em with Em Schur, the pencil rows eq:deflate-rows as row1/row2, and surjectivity of the W-frame as surj); everything downstream of it is verified: intertwine/sylv/link (eq:sylv, eq:link — every telescoping series replaced by Sylvester uniqueness, sylvester_unique), link_M, perstep(_posSemidef) (eq:perstep), lagrangian (X'Y symmetric via the Stein equation K = E'KE => K = 0), energy_fix/energy_posSemidef (eq:energy), kernel_sub (the ⊆ inclusion of eq:kernel-id — orbit collapse via the stabilizing output injection detect_inj, finding 16), transversal, info_fix (eq:info-fix, Sylvester uniqueness again in place of the series), sysinterp_nonsingular (M_inf nonsingular under C2, IsUnit det form) and sysinterp_singular (not-C2w => explicit kernel vector: the ⊇/necessity half at the kernel level). Axioms clean on all heads; the DeflatingPair fields are the only unverified input (fact:dare-strong's pencil geometry). -->
<!-- verify: A^{-1} hygiene — no inverse of A, M, L, F_inf, X_-; no Sigma_-. Inverses used: W (frame, benign, complementary deflating subspaces), I+H_C Sinf (Sigma-shear, discharged into the p×p Omega block), S_inf (p×p innovation cov). No partial inverses: the former (A_1'|_{L>=})^{-1} reversal is retired — the orbit collapse goes through a stabilizing output injection (finding 16). -->
<!-- END FILE: a04-subspace.md -->

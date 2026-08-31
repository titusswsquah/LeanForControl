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

- $(A_1, G_1)$ stabilizable and $(A_1, C_1)$ detectable (C1); its closed loop under the strong-solution gain, $A_c$ (the $e_1$-diagonal block of $F_\infty$), is Schur, $\rho_c := \rho(A_c) < 1$ (`eq:Finf-spec`) — the block that converges **forward**, needing no reversal;
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

The attraction is **exponential** if there is $\gamma \in (0, 1)$ such that for every prior $\Sigma_0 \succeq 0$ there is $c < \infty$ with $\|\Sigma_T - \Sigma_\infty\| \le c\, \gamma^T$ for all $T$; otherwise (e.g. $\|\Sigma_T - \Sigma_\infty\| \sim c\, T^{-r}$) it is **polynomial**. Marginal uncontrollable modes ($A_m$) force the polynomial regime; their absence (C3w) gives the exponential one.

## The dichotomy

The development culminates in the strong/stabilizing dichotomy `eq:dichotomy`, assembled last in the main theorem (forthcoming), and stated exponential-branch first:

<!-- eq:dichotomy -->
$$ \text{C1} + \text{C2} + \text{C3w} \iff \Sigma_T \to \Sigma_\infty\ \text{exponentially}\ (\rho(F_\infty) < 1) \qquad\qquad \text{C1} + \text{C2w} \iff \Sigma_T \to \Sigma_\infty\ (\rho(F_\infty) \le 1) \tag{eq:dichotomy} $$

The first line is the exponentially-attracting, **stabilizing** regime: with no uncontrollable unit-circle mode the reduced $e_1 \oplus e_a$ system is the whole state, $F_\infty$ is Schur, and the approach is geometric (the discrete-time counterpart of Callier, Winkin and Willems 1994). The second relaxes C2 + C3w to C2w alone: the marginal modes survive in the limit, $F_\infty$ sits on the unit circle, and the approach is polynomial — marginal uncontrollable modes slow the recursion but do not stop it (the discrete counterpart of the critical-mode phenomenon of Callier and Winkin 1995).

**Remark (boundary cases).** If $(A, G)$ is controllable, $\mathcal{X}_{uc} = \{0\}$ and C2/C2w hold for every prior. If $(A, C)$ is observable, C1 is automatic. With the marginal block empty, `eq:three-block` is the two-block C3w form and `eq:dichotomy` reduces to its first line. Each such case is read by setting the corresponding block to be absent.

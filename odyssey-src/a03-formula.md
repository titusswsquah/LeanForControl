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
<!-- verify: cor:necessity — C2: |det(I+G_inf D)|=0.41, gap->0; not-C2 (singular antistable prior): |det|=2e-15, gap stuck at 5.46 (check_payoffs.py, check_endtoend.py). SUFFICIENCY direction (C2 => nonsingular => converges) now PROVED: lem:sysinterp (04a, subset inclusion) + thm:sufficiency (06). NECESSITY direction (¬C2 => singular => stuck) = reverse inclusion of eq:kernel-id, FLAGGED OPEN. This corollary is a downstream signpost (audited prose cross-ref to lem:sysinterp/thm:sufficiency); it proves nothing in 04. -->
<!-- verify: C3w-bound. Marginal mode (C2w, not C3w): rho(F_inf)=1, ||G_T|| diverges (3.4->79), ||F_inf^T|| ~2.4 does not decay (check_c2w_boundary.py) — gramian and sandwich both fail; the marginal case (Arc 2) keeps the squeeze. -->
<!-- verify: SUBSUMES / RETIRES — the from-above anchor (retired-04-supremal.md, lem:supremal) is the upper flank F_inf^T(.)(F_inf')^T of eq:formula; the from-below anchor (retired-05-lowerbound.md, lem:lowerbound) and its import eq:Phi-bound are replaced by lem:sysinterp's "M_inf nonsingular under C2". Both files RETIRED out of the live sequence. LIVE consumers: thm:main (unwritten) reads thm:sufficiency + cor:necessity; thm:payoff (robustness) reads eq:formula + cor:phi. Deps of thm:formula: lem:structure-1 (F_inf Schur, eq:bounded), app:machinery (eq:Rmap, eq:gap-ric), a00-facts (fact:schur-decay, fact:dare-strong). NOTE: cor:attract and cor:necessity forward-point to lem:sysinterp/thm:sufficiency (allowlisted prose cross-refs) — not proof-deps, so no 04<->04a/06 cycle. -->
<!-- verify: DECK-WIDE eq:pencil-block sync — 04a (sec:formula-2, id1, P M/L T_Sigma) now matches this file's two-sided display exactly; no other file references the retired F_inf^-'/W form. -->
<!-- verify: rate DECISION deferred to thm:payoff. -->
<!-- (Gate-2 scratch: /home/claude/arc1scratch/check_A15_rewrite.py, check_A4_nonsing.py, check_pencil_formula3.py, check_payoffs.py, check_endtoend.py, check_c2w_boundary.py.) -->

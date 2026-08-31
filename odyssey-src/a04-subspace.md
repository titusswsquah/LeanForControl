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

the last because $E_-$ is Schur. We claim `eq:orbit` forces $v = p_0 \in \mathcal{X}_{a,uc}$. In the frame `eq:three-block` write $p_k = [a_k; b_k]$ over $e_1 \oplus e_a$, so $A' = \big[\begin{smallmatrix} A_1' & 0 \\ A_{1a}' & A_a' \end{smallmatrix}\big]$, $G' = [G_1'\ \ 0]$, and `eq:orbit` gives $a_k = A_1' a_{k+1}$, $G_1' a_k = 0\ (k\ge1)$, $a_k \to 0$; the goal is $a_0 = 0$. Split $e_1 = L^-(A_1') \oplus L^{\ge}(A_1')$ into the stable ($|\lambda|<1$) and unstable-or-critical ($|\lambda|\ge1$) $A_1'$-invariant subspaces. For fixed $j$, the stable component $a_j^- = (A_1'|_{L^-})^{k-j} a_k^-$ has norm $\le c\gamma^{k-j}\|a_k^-\| \to 0$ as $k \to \infty$, so $a_j^- = 0$ for every $j$: the orbit lives in $L^{\ge}(A_1')$, where $A_1'$ is invertible. There $G_1' a_k = 0\ (k\ge1)$ reads $G_1'(A_1'|_{L^\ge})^{-j}a_1 = G_1' a_{1+j} = 0$ for all $j \ge 0$, so $a_1$ lies in the unobservable subspace of $(G_1', (A_1'|_{L^\ge})^{-1})$, which equals that of $(G_1', A_1'|_{L^\ge})$ since inverse-related maps share invariant subspaces. By stabilizability of $(A_1, G_1)$ the uncontrollable subspace $NO(G_1', A_1')$ lies in $L^-(A_1')$, so it meets $L^{\ge}(A_1')$ only at $0$; hence $a_1 = 0$ and $a_0 = A_1' a_1 = 0$. Therefore $p_0 = [0; b_0] \in e_a = \mathcal{X}_{a,uc}$. Together with $\Sigma_0 v = 0$ this places $v \in \ker\Sigma_0 \cap \mathcal{X}_{a,uc}$.

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
<!-- verify: A^{-1} hygiene — no inverse of A, M, L, F_inf, X_-; no Sigma_-. Inverses used: W (frame, benign, complementary deflating subspaces), I+H_C Sinf (Sigma-shear, discharged into the p×p Omega block), (A_1'|_{L>=})^{-1} (reversal on the |lambda|>=1 modes only, legal as in eq:A2-inv), S_inf (p×p innovation cov). -->

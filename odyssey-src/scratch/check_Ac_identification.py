# Finding 15 refutation: A_c is NOT the e1-diagonal block of F_inf.
# The (a,e1) coupling of F_inf is nonzero (the antistable rows couple
# back through the gain), so F_inf is not (e1|a)-triangular and
# spec((F_inf)_11) is not a subset of spec(F_inf). The correct A_c
# (Lambda_in's realization) is the reduced (A1,G1,C1) stabilizing loop.
import numpy as np
exec(open('check_spectrum_split.py').read().split('# 1. block')[0])
F11 = F[:n1, :n1]
print("spec((Finf)_11)         :", np.sort(np.abs(np.linalg.eigvals(F11))))
print("spec(Finf) (moduli)     :", np.sort(np.abs(np.linalg.eigvals(F))))
print("||F_{a,e1}|| (coupling) :", np.linalg.norm(F[n1:n1+na, :n1]))
A1r = A[:n1,:n1]; C1r = C[:,:n1]; G1r = G[:n1,:]
P = np.zeros((n1,n1))
for _ in range(2000): P = dare_step(P, A1r, C1r, Q, R, G1r)
Kr = P@C1r.T@np.linalg.solve(C1r@P@C1r.T+R, np.eye(C1r.shape[0]))
Lred = A1r@(np.eye(n1)-Kr@C1r)
print("spec(Lred) (reduced loop):", np.sort(np.abs(np.linalg.eigvals(Lred))))
sF = np.sort_complex(np.linalg.eigvals(F))
sL = np.sort_complex(np.linalg.eigvals(Lred))
print("spec(Lred) subset of spec(Finf)?",
      all(min(abs(l-f) for f in sF) < 5e-3 for l in sL))

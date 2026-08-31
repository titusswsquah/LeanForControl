import numpy as np
rng = np.random.default_rng(31)
def randpsd(n): X = rng.standard_normal((n,n)); return X @ X.T
def randpd(n):  return randpsd(n) + 0.5*np.eye(n)
ok=True
def check(name,l,r,tol=1e-8):
    global ok; d=np.max(np.abs(l-r)); ok &= d<tol; print(f"{name}: {d:.2e} {'OK' if d<tol else 'FAIL'}")

# Build a DARE fixed point with a singular Sigma_inf by construction:
# uncontrollable antistable mode with zero-prior direction never gains cov?
# Easier: verify the three identities at ANY psd Sigma with the fixed point
# replaced by the step (identities (i)-(iii) hold at a fixed point; test the
# implications on a system where we can iterate to a singular fixed point).
# System: A = diag(0.5, 2), G = [1;0], C = [1 1]; antistable mode 2 is
# uncontrollable; seed Sigma0 with zero in the antistable direction ->
# Sigma_T stays singular there (necessity mechanism), and the limit is a
# non-strong fixed point Sig* with ker; check (i) A^T-invariance of ker,
# (ii) G^T kills ker, (iii) F(Sig*)^T w = A^T w on ker, (iv) F has eig 2.
A = np.array([[0.5, 0.3],[0, 2.0]])
G = np.array([[1.0],[0.0]])
C = np.array([[1.0, 1.0]])
Q = np.array([[1.0]]); Rr = np.array([[1.0]])
Qw = G@Q@G.T
def step(S):
    Sinn = C@S@C.T+Rr
    U = S - S@C.T@np.linalg.inv(Sinn)@C@S
    return A@U@A.T + Qw
S = np.diag([1.0, 0.0])
for _ in range(300): S = step(S)
check("fixed point", step(S), S, 1e-9)
# kernel of S
w, V = np.linalg.eigh(S)
kvecs = V[:, w < 1e-9]
print("dim ker Sig* =", kvecs.shape[1])
for k in range(kvecs.shape[1]):
    v = kvecs[:,k]
    check(f"Sig* v = 0 [{k}]", S@v, 0*v)
    check(f"A^T-invariance [{k}]", S@(A.T@v), 0*v)      # A^T v in ker
    check(f"G^T kills ker [{k}]", G.T@v, 0*np.zeros(1))
    Sinn = C@S@C.T+Rr
    K = S@C.T@np.linalg.inv(Sinn)
    F = A@(np.eye(2)-K@C)
    check(f"F^T = A^T on ker [{k}]", F.T@v, A.T@v)
print("spec F =", np.linalg.eigvals(A@(np.eye(2)-S@C.T@np.linalg.inv(C@S@C.T+Rr)@C)))
print("ALL OK" if ok else "FAILED")

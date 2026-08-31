import numpy as np
rng = np.random.default_rng(23)
def randpsd(n): X = rng.standard_normal((n,n)); return X @ X.T
def randpd(n):  return randpsd(n) + 0.5*np.eye(n)
ok=True
def check(name,l,r,tol=1e-9):
    global ok; d=np.max(np.abs(l-r)); ok &= d<tol; print(f"{name}: {d:.2e} {'OK' if d<tol else 'FAIL'}")
for _ in range(20):
    n,p,mm=4,2,3
    A=rng.standard_normal((n,n)); C=rng.standard_normal((p,n)); Rr=randpd(p)
    Sg=randpsd(n); Qw=randpsd(n); L=rng.standard_normal((n,p))
    S=C@Sg@C.T+Rr
    U=Sg - Sg@C.T@np.linalg.inv(S)@C@Sg
    dstep=A@U@A.T+Qw
    Ls=A@Sg@C.T@np.linalg.inv(S)
    pj=(A-L@C)@Sg@(A-L@C).T + L@Rr@L.T + Qw
    check("pjoseph excess", pj - dstep, (L-Ls)@S@(L-Ls).T)
print("ALL OK" if ok else "FAILED")

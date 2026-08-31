import numpy as np
rng = np.random.default_rng(41)
ok=True
def check(name,l,r,tol=1e-7):
    global ok; d=np.max(np.abs(np.asarray(l)-np.asarray(r))); ok &= d<tol
    print(f"{name}: {d:.2e} {'OK' if d<tol else 'FAIL'}")
def randpsd(n): X=rng.standard_normal((n,n)); return X@X.T
def randpd(n): return randpsd(n)+0.5*np.eye(n)

# marginal system: n1=2 stab, na=1 antistable (2.0), nm=2 marginal (rotation),
# C sees everything through coupling; Sig2 PD (C2 holds)
th=0.7; Am=np.array([[np.cos(th),-np.sin(th)],[np.sin(th),np.cos(th)]])
A1=np.array([[0.5,0.1],[0,0.3]]); Aa=np.array([[2.0]])
A12=rng.standard_normal((2,3))
A=np.block([[A1,A12],[np.zeros((3,2)),np.block([[Aa,np.zeros((1,2))],[np.zeros((2,1)),Am]])]])
G=np.vstack([rng.standard_normal((2,1)),np.zeros((3,1))])
C=rng.standard_normal((1,5)); Q=np.array([[1.0]]); Rr=np.array([[1.0]])
Qw=G@Q@G.T
def step(S_):
    Si=C@S_@C.T+Rr
    U=S_-S_@C.T@np.linalg.inv(Si)@C@S_
    return A@U@A.T+Qw
S=np.eye(5)
for _ in range(60000): S=step(S)
check("fixed point", step(S), S, 1e-6)
EmbM=np.zeros((5,2)); EmbM[3,0]=1; EmbM[4,1]=1
P=EmbM.T@S@EmbM
Si=C@S@C.T+Rr; U=S-S@C.T@np.linalg.inv(Si)@C@S
D=EmbM.T@(S-U)@EmbM
# Stein relation D = P - Am^-1 P Am^-T
check("stein", D, P-np.linalg.inv(Am)@P@np.linalg.inv(Am).T, 1e-5)
# telescoping unroll bounded
B2=np.linalg.inv(Am.T)
for N in [5,50]:
    tot=sum(np.linalg.matrix_power(np.linalg.inv(Am),k)@D@np.linalg.matrix_power(np.linalg.inv(Am),k).T for k in range(N))
    check(f"telescope N={N}", tot, P-np.linalg.matrix_power(np.linalg.inv(Am),N)@P@np.linalg.matrix_power(np.linalg.inv(Am),N).T, 1e-5)
print("||D|| =", np.linalg.norm(D), " (should be ~0: extinction of correction)")
# PSD Cauchy-Schwarz floor on a random PSD
Dt=randpsd(3); x=rng.standard_normal(3); y=rng.standard_normal(3)
check("psd CS", min(0.0, (y@Dt@x)**2*0 + ( (y@Dt@y)*(x@Dt@x)-(y@Dt@x)**2 )), 0.0)  # nonneg check
print("CS slack:", (y@Dt@y)*(x@Dt@x)-(y@Dt@x)**2, ">=0")
# Z-columns: Bm ~ 0, Z = A Z Am^T, (A-LC)Z = Z (Am^T)^-1, rows die under no-decay
Z=S@EmbM
Bm=C@S@EmbM
print("||Bm|| =", np.linalg.norm(Bm), " ||Z|| =", np.linalg.norm(Z), "(both ~0 at the strong soln)")
# verify the fixed-point identity Z = A Z Am^T holds structurally at approx fixed point
check("Z fixed pt", Z, A@(U@EmbM)@Am.T, 1e-5)
print("ALL OK" if ok else "FAILED")

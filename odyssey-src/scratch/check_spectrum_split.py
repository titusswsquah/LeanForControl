import numpy as np
rng = np.random.default_rng(7)
def make_sys(n1=3, na=2, nm=2, p=2, m=2, defective=False):
    A1 = rng.normal(size=(n1,n1))*0.4
    A12 = rng.normal(size=(n1,na+nm))*0.5
    Aa = np.diag([1.6, -2.1]) + np.triu(rng.normal(size=(na,na))*0.2,1)
    th = 1.1
    Am = np.array([[np.cos(th), -np.sin(th)],[np.sin(th), np.cos(th)]])
    A2 = np.block([[Aa, np.zeros((na,nm))],[np.zeros((nm,na)), Am]])
    A = np.block([[A1, A12],[np.zeros((na+nm,n1)), A2]])
    G = np.vstack([rng.normal(size=(n1,m)), np.zeros((na+nm,m))])
    C = rng.normal(size=(p, n1+na+nm))
    Q = np.eye(m); R = np.eye(p)
    return A, G, C, Q, R, n1, na, nm
def dare_step(S, A, C, Q, R, G):
    Sm = C @ S @ C.T + R
    U = S - S @ C.T @ np.linalg.solve(Sm, C @ S)
    return A @ U @ A.T + G @ Q @ G.T
A,G,C,Q,R,n1,na,nm = make_sys()
n = n1+na+nm
# strong solution via long iteration from a C2w prior
S = np.eye(n)
for _ in range(30000): S = dare_step(S,A,C,Q,R,G)
Sinf = S
K = Sinf @ C.T @ np.linalg.solve(C@Sinf@C.T+R, np.eye(C.shape[0]))
F = A @ (np.eye(n) - K @ C)
# 1. block triangularity: embM' F embS = 0
embS = np.zeros((n, n1+na)); embS[:n1,:n1]=np.eye(n1); embS[n1:n1+na,n1:]=np.eye(na)
embM = np.zeros((n, nm)); embM[n1+na:,:]=np.eye(nm)
print("||embM' F embS|| =", np.linalg.norm(embM.T@F@embS))
Fs = embS.T@F@embS
# 2. spec split
sF = np.sort_complex(np.linalg.eigvals(F)); sFs = np.linalg.eigvals(Fs); sAm = np.linalg.eigvals(embM.T@F@embM)
print("spec(F) =", np.round(sF,4))
print("spec(Fs)∪spec(Am) =", np.round(np.sort_complex(np.concatenate([sFs,sAm])),4))
print("max|spec Fs| =", np.abs(sFs).max(), "(<1 expected)")
# 3. Stein kill: unit-circle eigvec of F' is m-supported
w = np.linalg.eig(F.T)
for lam, v in zip(w.eigenvalues, w.eigenvectors.T):
    if abs(abs(lam)-1) < 1e-6:
        print("unit eig", np.round(lam,3), " |e1,a-part|=", np.linalg.norm(v[:n1+na]), " (0 expected)")
# 4. reduced-run product bounds + geometric P-convergence
A1 = A[:n1,:n1]; C1 = C[:,:n1]; G1 = G[:n1,:]
P = np.zeros((n1,n1)); Ps=[P]
for _ in range(400):
    P = dare_step(P,A1,C1,Q,R,G1); Ps.append(P)
Pinf = Ps[-1]
Ls=[]
for P in Ps[:-1]:
    Kt = P@C1.T@np.linalg.solve(C1@P@C1.T+R, np.eye(C1.shape[0]))
    Ls.append(A1@(np.eye(n1)-Kt@C1))
prods=[]
for j in range(0, 60, 7):
    Phi = np.eye(n1); mx = 0
    for t in range(j, 200):
        Phi = Ls[t] @ Phi; mx = max(mx, np.linalg.norm(Phi))
    prods.append(mx)
print("sup product norms over starts:", np.round(max(prods),3))
errs=[np.linalg.norm(Ps[t]-Pinf) for t in (5,10,20,40)]
print("P-convergence ratios:", [round(errs[i+1]/max(errs[i],1e-300),4) for i in range(3)])
# 5. chart-assembled Sinf vs iterated
Linf = A1@(np.eye(n1)-Pinf@C1.T@np.linalg.solve(C1@Pinf@C1.T+R,C1))
Aa = A[n1:n1+na, n1:n1+na]
A1a = A[:n1, n1:n1+na]; A1m = A[:n1, n1+na:]
Ca = C[:, n1:n1+na]
Kinf = Pinf@C1.T@np.linalg.solve(C1@Pinf@C1.T+R, np.eye(C1.shape[0]))
dinf = (A1a - A1@Kinf@Ca) @ np.linalg.inv(Aa)
Lam = np.zeros((n1,na))
for _ in range(2000): Lam = Linf@Lam@np.linalg.inv(Aa) + dinf
Ceff = C1@Lam + Ca
Stil = R + C1@Pinf@C1.T
Xi = Ceff.T@np.linalg.solve(Stil, Ceff)
J = np.zeros((na,na)); Ainv = np.linalg.inv(Aa)
for _ in range(2000): J = Ainv.T@(J+Xi)@Ainv
V = embS@np.vstack([Lam, np.eye(na)])
Sass = embS[:, :n1]@Pinf@embS[:, :n1].T + V@np.linalg.inv(J)@V.T
print("||assembled - Sinf|| =", np.linalg.norm(Sass - Sinf))
print("min eig J =", np.linalg.eigvalsh((J+J.T)/2).min(), "(>0 expected)")

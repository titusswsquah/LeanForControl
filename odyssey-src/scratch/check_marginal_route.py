import numpy as np
rng = np.random.default_rng(53)
ok=True
def check(name,val,tol=1e-8,cmp='small'):
    global ok
    if cmp=='small': good = val<tol
    else: good = val>tol
    ok &= good; print(f"{name}: {val:.3e} {'OK' if good else 'FAIL'}")

def run(Am, label, T=4000):
    global ok
    nm=Am.shape[0]
    n1,na=2,1
    A1=np.array([[0.5,0.1],[0,0.3]]); Aa=np.array([[2.0]])
    A12=rng.standard_normal((n1,na+nm))*0.5
    A2=np.block([[Aa,np.zeros((na,nm))],[np.zeros((nm,na)),Am]])
    A=np.block([[A1,A12],[np.zeros((na+nm,n1)),A2]])
    G=np.vstack([rng.standard_normal((n1,1)),np.zeros((na+nm,1))])
    C=rng.standard_normal((1,n1+na+nm)); Q=np.eye(1); Rr=np.eye(1)
    Qw=G@Q@G.T
    E2=np.vstack([np.zeros((n1,na+nm)),np.eye(na+nm)])
    def step(S_):
        Si=C@S_@C.T+Rr
        U=S_-S_@C.T@np.linalg.inv(Si)@C@S_
        return A@U@A.T+Qw, Si, U
    S=np.eye(n1+na+nm)
    Sbar_innov_sum=0.0; phi_mono_viol=0.0
    u=rng.standard_normal(na+nm)
    A2iT=np.eye(na+nm)  # A2^{-T'} accumulator: (A2.T)^{-T}
    A2Tinv=np.linalg.inv(A2.T)
    phi_prev=None
    cy_sq=[]
    for t in range(T):
        # phi_t(u) = quadForm S|22 ((A2')^{-t} u)
        w=A2iT@u
        phi=w@(E2.T@S@E2)@w
        if phi_prev is not None: phi_mono_viol=max(phi_mono_viol, phi-phi_prev-1e-12)
        phi_prev=phi
        Y=S@E2@A2iT   # S * E2 * (A2')^{-t}
        cy_sq.append(np.linalg.norm(C@Y)**2)
        S,Si,U=step(S)
        A2iT=A2iT@A2Tinv
    check(f"[{label}] phi monotone (max violation)", phi_mono_viol)
    print(f"[{label}] sum||CY||^2 (partial) = {sum(cy_sq):.4f}  tail@{T}: {cy_sq[-1]:.2e}")
    Y=S@E2@A2iT
    print(f"[{label}] ||Y_T|| = {np.linalg.norm(Y):.3e}")
    Smm=S[n1+na:,n1+na:]
    print(f"[{label}] ||Sigma_T|mm|| = {np.linalg.norm(Smm):.3e}  (T={T})")
    return np.linalg.norm(Smm)

th=0.7
Am_ss=np.array([[np.cos(th),-np.sin(th)],[np.sin(th),np.cos(th)]])  # semisimple
Am_def=np.array([[1.0,1.0],[0.0,1.0]])                              # defective
r1=run(Am_ss,"semisimple")
r2=run(Am_def,"defective")
check("semisimple Sigma|mm -> 0", r1, 5e-2)
print("defective Sigma|mm (route gives no proof; numerics):", f"{r2:.3e}")
print("ALL-KEY OK" if ok else "FAILED")

"""Deterministic stdlib-only consistency checks for the analytic p<1 theorem.

Numerical integration is NOT a rigorous proof; manuscript Appendix app:sublinear-severe
contains the mathematical construction and uniform resource estimates.
"""
import math

def simpson(fun,a,b,n=1024):
    assert n % 2 == 0 and b >= a
    if b == a: return 0.
    h=(b-a)/n
    return h/3*(fun(a)+fun(b)+4*sum(fun(a+j*h) for j in range(1,n,2))
                +2*sum(fun(a+j*h) for j in range(2,n,2)))

def construct(p,c,eps):
    N=3;m=2;nu=2-p;rho=.4;T=8.;bbar=.2
    def AH(b):
        a=(1-b**nu-(m-1)*c**nu)**(1/nu)
        H=a**(nu-1)+(m-1)*c**(nu-1)+(b**(nu-1) if b else 0.)
        return a,H
    def R(b,t):
        H=AH(b)[1]
        return H+(N**(1/nu)-H)*math.exp(-rho*t)
    def comp(b):
        end=(R(b,T)**nu-m*eps**nu-1)/nu
        rec=rho*simpson(lambda t:(b*R(b,t))**(nu-1)*(b*R(b,t)-1),0,T) if b else 0.
        return end+rec
    assert comp(0)>0 and comp(bbar)<0,(p,comp(0),comp(bbar))
    lo=0.;hi=bbar
    for _ in range(100):
        mid=(lo+hi)/2
        if comp(mid)>0: lo=mid
        else: hi=mid
    b=(lo+hi)/2
    a,H=AH(b)
    def W(t):
        r=R(b,t)
        return r**(nu-1)*((a**nu-c**nu)*r-(a**(nu-1)-c**(nu-1)))
    assert a>max(b,c) and b*H<1 and c*H<1
    assert min(W(0),W(T))>0
    area=simpson(W,0,T)
    lo=0.;hi=T
    for _ in range(60):
        mid=(lo+hi)/2
        if simpson(W,0,mid)<area/2: lo=mid
        else: hi=mid
    middle=(lo+hi)/2
    times=[0.,middle,T]
    lastComp=(R(b,T)**nu-m*eps**nu)**(1/nu)
    ledger=[]
    for i in range(N):
        integral=0.
        for j in range(m):
            u=b if i==m else (a if i==j else c)
            integral+=simpson(lambda t:(u*R(b,t))**(nu-1)*(u*R(b,t)-1),
                              times[j],times[j+1])
        end=lastComp if i==m else eps
        ledger.append((end**nu-1)/nu+rho*integral)
    assert max(abs(v) for v in ledger)<1e-7,(p,ledger)
    for j in range(m):
        u=[c]*m+[b];u[j]=a
        assert abs(sum(v**nu for v in u)-1)<1e-12
        assert abs(sum(v**(nu-1)*(v*H-1) for v in u))<1e-11
    assert 1<lastComp<N**(1/nu)+1e-12
    loss=(m*math.log(1/eps)-math.log(lastComp))/N
    assert loss>0
    M0=N**3/(2*nu)+rho*N*T
    H0=N*N**((nu-1)/nu)/(nu-1)+rho*T*min(c,b/2)**(-p)*(1+N**(1/nu))
    assert M0>0 and H0>0
    return b,loss,max(abs(v) for v in ledger)

def main():
    for p,c in ((0.,.002),(.25,.002),(.5,.002),(.75,.002),(.9,.0002)):
        near=construct(p,c,1e-5)
        far=construct(p,c,1e-10)
        assert far[1]>near[1]+5
        assert abs(far[0]-near[0])<2e-4,(p,near,far)
        print("PASS p=",p,"eps=1e-10; root=",format(far[0],".9g"),
              "mean-log=",format(far[1],".6f"),
              "dollar-ledger residual=",format(far[2],".3g"))
    print("PASS: independent radial controls, dollar closure and fixed resource envelopes")

if __name__=="__main__":
    main()

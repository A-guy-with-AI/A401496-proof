# Vérifie la caractérisation : R=(t^v u, f) avec 1<=v<m est solution  <=>  val(f+t) >= ceil((m-v)/2)
# et la formule a(n) = 2 + sum_{r=1}^{n-2} 2^(r+floor(r/2))  (n>=2)
import sys
def mul(a,b,m):
    r=0
    for i in range(m):
        if a>>i&1: r^=b<<i
    return r&((1<<m)-1)
def matrix(g,f,m):
    cols=[];p=g
    for j in range(m):
        cols.append(p>>j<<j&((1<<m)-1)); p=mul(p,f,m)
    return tuple(cols)
def val(x):
    if x==0: return 10**9
    return (x&-x).bit_length()-1
for m in range(1,int(sys.argv[1])+1):
    S={}
    for g in range(1<<m):
        for f in range(0,1<<m,2): S.setdefault(matrix(g,f,m),(g,f))
    L=tuple(((1<<m)-1)>>j<<j for j in range(m))
    sol={M for M in S if tuple(a^b for a,b in zip(M,L)) in S}
    ok=True; nI=0
    for g in range(1<<m):
        v=val(g)
        if not (1<=v<m): continue
        for f in range(0,1<<(m-v),2):   # f mod t^(m-v), f(0)=0 : representant canonique
            M=matrix(g,f,m)
            pred = val(f^2) >= -(-(m-v)//2)   # f+t, t = bit 1 -> 2
            if pred != (M in sol): ok=False
            nI+=pred
    n=m+1
    formula = 2+sum(2**(r+r//2) for r in range(1,n-1))
    conj = 1+sum(2**((3*(k-1))//2) for k in range(1,n))
    print(f"n={n} a={len(sol)} 2|I|+2={2*nI+2} formule={formula} conjecture={conj} caractérisation_ok={ok}")

"""Exact checks for the sharpened braid-length bound (l = 11 strands)."""
from fractions import Fraction as F
from math import comb
import itertools, numpy as np

# ---- 1. Braid identities in the (unreduced) Burau representation at t=2, exact ----
def burau(l,i,t=F(2),inv=False):
    M=[[F(int(a==b)) for b in range(l)] for a in range(l)]
    k=i-1
    blk=[[1-t,t],[F(1),F(0)]] if not inv else [[F(0),F(1)],[1/t,1-1/t]]
    for a in range(2):
        for b in range(2): M[k+a][k+b]=F(blk[a][b])
    return M
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def word(l,w):
    M=[[F(int(a==b)) for b in range(l)] for a in range(l)]
    for i in w: M=mul(M,burau(l,i))
    return M
def Lword(j): return [] if j==1 else [j-1]+Lword(j-1)+[j-1]
def Zword(r): return [i for j in range(1,r+1) for i in Lword(j)]
l=11
S={i:word(l,[i]) for i in range(1,l)}
for i in range(1,l-1): assert mul(mul(S[i],S[i+1]),S[i])==mul(mul(S[i+1],S[i]),S[i+1])
for r in range(2,l+1):
    Z=word(l,Zword(r)); assert len(Zword(r))==2*comb(r,2)
    for i in range(1,r): assert mul(Z,S[i])==mul(S[i],Z), (r,i)
assert word(l,Zword(3))==word(l,[1,2]*3)
print("Burau checks: braid relations, Z_r commutes with s_i (i<r), |Z_r|=2N_r letters, Z_3=(s1s2)^3: OK")

# ---- 2. Exact linear algebra of the bound; linear forms a0 + a1*x + a2*c ----
def Q(r): return (F(1),F(r-2),F(comb(r-2,2)))           # <g,Z_r>/D^2
def lin(*terms):
    out=[F(0)]*3
    for k,v in terms:
        for i in range(3): out[i]+=k*v[i]
    return tuple(out)
N=lambda r: F(comb(r,2))
for l in range(5,60):
    # |W|^2/D^2 for W = Z_{l-1}^l Z_l^{-(l-2)}, using |Z_r|^2=N_r Q_r, <Z_{l-1},Z_l>=N_{l-1} Q_l
    W=lin((l*l*N(l-1),Q(l-1)),(-2*l*(l-2)*N(l-1),Q(l)),((l-2)**2*N(l),Q(l)))
    A=lin((F(l),Q(l-1)),(F(-(l-2)),Q(l)))
    assert W==tuple(F((l-1)*l*(l-2),2)*a for a in A)
    assert A==(F(2),F(l-4),F(-2*(l-3)))
    comb_=lin((F(1),Q(l)),(F(l-2,4),A))       # nonneg combination: c cancels
    assert comb_==(F(l,2),F(l*(l-2),4),F(0))
    R3=(1+F(-2,l-2))/3
    assert R3==F(l-4,3*(l-2))
    assert (R3>F(1,4))==(l>10)
print("Bound R_3 >= (l-4)/(3(l-2)) verified symbolically for 5<=l<60; strict >1/4 iff l>=11")
print("l=11: R_3 >=",F(7,27),"> 1/4; old paper l=40 bound",F(143,513))

# ---- 3. Tightness: the two constraints are simultaneously attained, so the chain cannot beat this ----
for l in (10,11,12):
    x=F(-2,l-2); c=F(2,(l-2)*(l-3))
    q=lambda r: Q(r)[0]+Q(r)[1]*x+Q(r)[2]*c
    assert q(l)==0 and q(l-1)==0
print("Extremal point x=-2/(l-2), c0=2/((l-2)(l-3)) makes Q_{l-1}=Q_l=0 (both constraints tight)")

# ---- 4. Generator count of the modified matrix ----
def gens(l): return 5+3*(l-3)
assert gens(40)==116 and gens(11)==29
print("Generators: l=40 ->",gens(40),"; l=11 ->",gens(11))

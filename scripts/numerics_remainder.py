import numpy as np, math
N=20000; K=3*N+10
idx=np.arange(-K,K+1)
G=(idx>=0).astype(float)
laws=[{-3:0.25,1:0.75},{-1:0.75,3:0.25}]  # 2*X, grid step 1/2
c=2/(3*math.sqrt(2*math.pi*math.e))
def shift(a,s):
    out=np.empty_like(a)
    if s>0: out[s:]=a[:-s]; out[:s]=0.0
    elif s<0: out[:s]=a[-s:]; out[s:]=1.0
    else: out[:]=a
    return out
H=G.copy()
for n in range(1,N+1):
    A=[sum(p*shift(G,s) for s,p in L.items()) for L in laws]
    G=np.minimum(A[0],A[1])
    if n in (1,10,100,1000,2000,5000,10000,20000):
        e=(H-G).sum()*0.5
        print(n, round(e,6), round(e-c*math.log(n),6), flush=True)

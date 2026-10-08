import sys; sys.dont_write_bytecode=True
import numpy as np
from math import gcd
IRR={5:0b100101,7:0b10000011,9:0b1000010001,11:0b100000000101,13:0b10000000011011,15:0b1000000000000011}
class GF:
    def __init__(s,m):
        s.m=m; s.q=1<<m; f=IRR[m]; q=s.q
        exp=[0]*(2*q); x=1
        for i in range(q-1):
            exp[i]=x; x<<=1
            if x&q: x^=f
        assert x==1
        for i in range(q-1,2*q): exp[i]=exp[i-(q-1)]
        log=[0]*q
        for i in range(q-1): log[exp[i]]=i
        assert len(set(exp[:q-1]))==q-1
        s.exp=np.array(exp,dtype=np.int64); s.log=np.array(log,dtype=np.int64)
        s.X=np.arange(q,dtype=np.int64)
    def mul(s,a,b):
        a=np.asarray(a);b=np.asarray(b)
        r=s.exp[(s.log[a]+s.log[b])%(s.q-1)]
        return np.where((a==0)|(b==0),0,r)
    def pw(s,a,e):
        a=np.asarray(a)
        if e==0: return np.ones_like(a)
        r=s.exp[(s.log[a]*e)%(s.q-1)]
        return np.where(a==0,0,r)
    def poly(s,terms):  # terms: set of exponents, F2 coeffs
        v=np.zeros(s.q,dtype=np.int64)
        for e in terms: v^=s.pw(s.X,e)
        return v
    def tr(s,a):
        a=np.asarray(a); t=a.copy(); x=a.copy()
        for _ in range(s.m-1):
            x=s.mul(x,x); t=t^x
        return t

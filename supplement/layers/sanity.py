# sanity: compare rowspec's F with Python ring evaluation via a penultimate-layer M4 check and direct python DDT on tiny case
import subprocess,sys,random
from grlib import *
m=5;K=4
T=read_terms('../P53sp.txt',m)
R=Ring(m,K)
# python DDT on one row of the v2 layer (penultimate for K=4)
a=R.smul(4,R.lift(3))
open('al.txt','w').write(f"{R.pack(a)}\n")
out=subprocess.run(['./rowspec',str(m),str(K),'37','../P53sp.txt','al.txt'],capture_output=True,text=True).stdout
print(out)
# python full count (2^20 evaluations is slow in python; sample 3000 x and compare F values against C? just print a couple)

# R05b (Claude): no reduced quadratic APN permutation of F_8 satisfies (H) (paper Section 3: why m >= 5).
# Exhaustive over the DO coefficients c3,c5,c6 and linear coefficients c1,c2,c4 (the constant is irrelevant).
P=0b1011; q=8
def mul(a,b):
    r=0
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
        if a&q: a^=P
    return r
def pw(a,e):
    r=1
    for _ in range(e): r=mul(r,a)
    return r
cnt=0; apnperm=0
for c3 in range(8):
 for c5 in range(8):
  for c6 in range(8):
   K=[mul(c3,pw(x,2))^mul(c5,pw(x,4)) for x in range(8)]
   ker=[x for x in range(8) if K[x]==0]
   for c1 in range(8):
    for c2 in range(8):
     for c4 in range(8):
      f=[mul(c1,x)^mul(c2,pw(x,2))^mul(c3,pw(x,3))^mul(c4,pw(x,4))^mul(c5,pw(x,5))^mul(c6,pw(x,6)) for x in range(8)]
      if len(set(f))<8: continue
      ok=True
      for a in range(1,8):
        if len(set(f[x^a]^f[x] for x in range(8)))<4: ok=False;break
      if not ok: continue
      apnperm+=1
      if len(ker)==2 and c1 not in set(K): cnt+=1
print('APN permutations (no constant):',apnperm,' satisfying (H):',cnt)
assert apnperm==1344 and cnt==0
print('M3_NO_H OK')

# Independent recount (Python, different field implementation) of the affine points of
# Q(z,w) = (h(z)+h(w))/(z+w) = 0 over F_{2^17}, h(z) = z^15+z^14+z^12+z^8, f = x^17+x^3+1.
from collections import Counter
m = 17; f = (1 << 17) | (1 << 3) | 1; q = 1 << m
def mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> m: a ^= f
    return r
cnt = Counter()
for z in range(q):
    z2 = mul(z, z); z4 = mul(z2, z2); z8 = mul(z4, z4); z12 = mul(z8, z4); z14 = mul(z12, z2); z15 = mul(z14, z)
    cnt[z15 ^ z14 ^ z12 ^ z8] += 1
pts = sum(n * (n - 1) for n in cnt.values()) + 1   # off-diagonal pairs + the point (0,0) (Q(z,z) = z^14)
print({'m': m, 'affine_points_Q': pts, 'bound_if_no_F2_component': 98, 'conclusion': pts > 98})

"""Exact-integer independent replay for the parity-correlated sufficient bound."""
from itertools import product

P = 3_955_200

def trigger(n, q, o):
    j = max(0, max(0, n + 2*q - 5) - max(0, o - 1))
    m = max(1, min(q, n)-1)
    return 40*m*m*max(0, 30*j+25-30*m)+36*m*m*(n+1)

def seed(s):
    return 4096*s**6*(9+3*(s-1).bit_length())

def packing(s, l):
    return 200*s**3*(2*(s-1)+2*l+1)

def endpoint(n):
    return 200*(2*n-1)**4*(n-1)**2*(1236*n-1364)

def verify(n, q, o):
    s = n+o
    t = trigger(n,q,o)
    assert t%2 == 0
    if q>=2:
        assert t == (q-1)**2*(1236*n+1200*q-3764-1200*max(0,o-1))
    l = (q-1)*(t-2)
    if n>=6:
        assert packing(s,l)<=endpoint(n)
    assert seed(s)+packing(s,l)<=(P+1)*n**7

checked=0
for n in range(1,95):
    for q in range(1,n+1):
        for o in range(q):
            verify(n,q,o)
            checked+=1
for e in [8,16,20,21,22,32,64,100,255,500]:
    for n in range(2**e-2,2**e+3):
        for q in (1,2,3,n//2,n-1,n):
            for o in sorted({0,min(1,q-1),q//2,q-1}):
                verify(n,q,o)
                checked+=1
reserves=0
for q in range(2,13):
    for roots in product((0,1), repeat=q-1):
        o=sum(roots)
        for v in range(q-1):
            # Ignore the root's bit; bank 2 removes one off-root bit.
            r=sum(2-x for i,x in enumerate(roots) if i!=v)
            assert r+o==2*(q-2)+roots[v]
            for n in (q,q+1,2*q):
                j=n+2*q-5-max(0,o-1)
                assert n-1+r<=j
                assert 45*(q-1)<=30*j+25
                w=4*(q-1)**2*(30*j+25-30*(q-1))
                assert 30*(n-1+r)+23<=w
                reserves+=1
assert trigger(6,3,0)==29008 and trigger(6,3,2)==24208
assert (P+1)*6**7==1_107_203_147_136
print(f'{checked} exact cutoffs; {reserves} reserve and capacity cases')

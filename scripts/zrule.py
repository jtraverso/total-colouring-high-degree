import sys, itertools
from collections import Counter
def connected(vs, adj):
    vs=set(vs)
    if not vs: return False
    s=next(iter(vs)); seen={s}; st=[s]
    while st:
        v=st.pop()
        for w in adj[v]:
            if w in vs and w not in seen: seen.add(w); st.append(w)
    return seen==vs
st=Counter()
for line in open(sys.argv[1]):
    n, rest = line.split(' ',1); n=int(n)
    hb=[tuple(sorted(e)) for e in eval(rest)]
    na=[set() for _ in range(n)]
    for u,v in hb: na[u].add(v); na[v].add(u)
    adj=[set(range(n))-na[v]-{v} for v in range(n)]
    if not connected(range(n),adj): continue
    zs=[z for z in range(n) if len(na[z])==3]
    allz=True; anyz=False
    for z in zs:
        Q=sorted(na[z]); okz=False
        for q1,q2,q3 in itertools.permutations(Q):
            for y in na[q1]-{z}:
                for t in na[q2]-{z,y}:
                    if n%2==0:
                        b = bool(adj[q3]-{q1,q2,y,t})
                        p = t in na[y]
                        pp = (q2 in na[y]) and bool(adj[q2]-set(Q)-{y,t})
                        if b or p or pp: okz=True
                    else:
                        ii = bool(adj[q1]-set(Q)-{t})
                        if ii: okz=True
        allz &= okz; anyz |= okz
    st[(n,allz,anyz)]+=1
print(st)

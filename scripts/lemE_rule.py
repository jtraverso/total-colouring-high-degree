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
    def ok(x,y,s,t,w):
        K=set(range(n))-{x,y,s,t}-({w} if w is not None else set())
        return connected(K,adj) and adj[x]&K and adj[y]&K
    res={}
    for (x,y) in hb:
        good=False
        for (s,t) in hb:
            if {s,t}&{x,y}: continue
            if n%2==0:
                if ok(x,y,s,t,None): good=True
            else:
                for (a,b) in ((s,t),(t,s)):
                    for w in adj[a]:
                        if w in (x,y,s,t): continue
                        if ok(x,y,a,b,w): good=True
        res[(x,y)]=good
    st[(n, all(res.values()), any(res.values()))]+=1
print(st)

# rule tests
st2=Counter()
for line in open(sys.argv[1]):
    n, rest = line.split(' ',1); n=int(n)
    hb=[tuple(sorted(e)) for e in eval(rest)]
    na=[set() for _ in range(n)]
    for u,v in hb: na[u].add(v); na[v].add(u)
    adj=[set(range(n))-na[v]-{v} for v in range(n)]
    if not connected(range(n),adj): continue
    def ok(x,y,s,t,w):
        K=set(range(n))-{x,y,s,t}-({w} if w is not None else set())
        return bool(connected(K,adj) and adj[x]&K and adj[y]&K)
    def good(x,y):
        for (s,t) in hb:
            if {s,t}&{x,y}: continue
            if n%2==0:
                if ok(x,y,s,t,None): return True
            else:
                for (a,b) in ((s,t),(t,s)):
                    for w in adj[a]:
                        if w in (x,y,s,t): continue
                        if ok(x,y,a,b,w): return True
        return False
    dh=[len(na[v]) for v in range(n)]
    sums=[dh[x]+dh[y] for x,y in hb]
    rmin=all(good(x,y) for (x,y),sm in zip(hb,sums) if sm==min(sums))
    rmax=all(good(x,y) for (x,y),sm in zip(hb,sums) if sm==max(sums))
    bad=[(dh[x],dh[y]) for x,y in hb if not good(x,y)]
    st2[(n,rmin,rmax)]+=1
    if bad: print(n, sorted(dh), bad)
print(st2)

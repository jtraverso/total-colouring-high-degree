import itertools, sys
from collections import Counter
def ham_path(vs, adj, start, end):
    vs=set(vs); target=len(vs)
    def go(cur, seen):
        if len(seen)==target: return cur==end
        for w in adj[cur]:
            if w in vs and w not in seen and (w!=end or len(seen)==target-1):
                seen.add(w)
                if go(w,seen): return True
                seen.discard(w)
        return False
    return go(start,{start})
# general question: K alpha<=2, x !~ y. When is there a Ham x-y path?  classify failures by (X,Y,Z) structure
stats=Counter(); fails=Counter()
for line in open(sys.argv[1]):
    n, rest = line.split(' ',1); n=int(n)
    if n%2: continue
    hb=[tuple(sorted(e)) for e in eval(rest)]
    na=[set() for _ in range(n)]
    for u,v in hb: na[u].add(v); na[v].add(u)
    adj=[set(range(n))-na[v]-{v} for v in range(n)]
    # connected?
    seen={0}; st=[0]
    while st:
        v=st.pop()
        for w in adj[v]:
            if w not in seen: seen.add(w); st.append(w)
    if len(seen)<n: continue
    good=0; tot=0; anyxy_allss=False
    per_xy={}
    for (x,y) in hb:
        cnt=0; c2=0
        for (s,t) in hb:
            if {s,t}&{x,y}: continue
            c2+=1
            K=[v for v in range(n) if v not in (s,t)]
            if ham_path(K,adj,x,y): cnt+=1
            else:
                X=[v for v in K if v in adj[x] and v not in adj[y]]
                Y=[v for v in K if v in adj[y] and v not in adj[x]]
                Z=[v for v in K if v in adj[x] and v in adj[y]]
                XY=any(b in adj[a] for a in X for b in Y)
                badZ=[z for z in Z if not (adj[z]&(set(X)|set(Y)))]
                fails[(len(X),len(Y),len(Z),XY,len(badZ))]+=1
        per_xy[(x,y)]=(cnt,c2)
    stats[(n, all(c>0 for c,_ in per_xy.values()), any(c==c2 for c,c2 in per_xy.values()))]+=1
print(stats)
for k,v in sorted(fails.items()): print(k,v)

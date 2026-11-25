import itertools, sys
from collections import Counter
def canon(m, adjm):
    best=None
    for p in itertools.permutations(range(m)):
        key=tuple(adjm[p[i]][p[j]] for i in range(m) for j in range(i+1,m))
        if best is None or key<best: best=key
    return best
def hp_nonadj_ends(m, adj):
    full=(1<<m)-1
    # dp over subsets: reach[mask][v] set of starts
    reach=[[0]*m for _ in range(1<<m)]
    for v in range(m): reach[1<<v][v]=1<<v
    for mask in range(1,1<<m):
        for v in range(m):
            st=reach[mask][v]
            if not st: continue
            for w in adj[v]:
                if not mask>>w&1:
                    reach[mask|1<<w][w]|=st
    for v in range(m):
        st=reach[full][v]
        for u in range(m):
            if st>>u&1 and u!=v and u not in adj[v]: return True
    return False
def connected(m, adj):
    seen={0}; st=[0]
    while st:
        v=st.pop()
        for w in adj[v]:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen)==m
m=int(sys.argv[1])
pairs=list(itertools.combinations(range(m),2))
exc=set()
# enumerate triangle-free H by backtracking over pairs
def rec(i, hedges, hadj):
    if i==len(pairs):
        adj=[set(range(m))-hadj[v]-{v} for v in range(m)]
        if not hedges: return
        if not connected(m,adj): return
        if not hp_nonadj_ends(m,adj):
            adjm=[[1 if j in adj[k] else 0 for j in range(m)] for k in range(m)]
            exc.add(canon(m,adjm))
        return
    u,v=pairs[i]
    rec(i+1,hedges,hadj)
    if not (hadj[u]&hadj[v]):
        hadj[u].add(v); hadj[v].add(u)
        rec(i+1,hedges+1,hadj)
        hadj[u].discard(v); hadj[v].discard(u)
rec(0,0,[set() for _ in range(m)])
print(m, len(exc))
for e in exc:
    E=[pairs[k] for k,b in enumerate(e) if b]
    print(E)

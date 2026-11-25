import sys
from collections import Counter
st=Counter()
for line in open(sys.argv[1]):
    n, rest = line.split(' ',1); n=int(n)
    hb=[tuple(sorted(e)) for e in eval(rest)]
    na=[set() for _ in range(n)]
    for u,v in hb: na[u].add(v); na[v].add(u)
    bip=None
    # bipartite check of H
    col={}
    ok=True
    for s in range(n):
        if s in col: continue
        col[s]=0; stack=[s]
        while stack:
            v=stack.pop()
            for w in na[v]:
                if w not in col: col[w]=1-col[v]; stack.append(w)
                elif col[w]==col[v]: ok=False
    minR=min(n-len(na[x])-len(na[y]) for x,y in hb)
    st[(n,ok,minR)]+=1
for k,v in sorted(st.items()): print(k,v)

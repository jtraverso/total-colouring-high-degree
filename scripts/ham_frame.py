import itertools, sys
from collections import Counter

def ham_paths(vs, adj, start, end):
    # does G[vs] have a Hamiltonian path from start to end?
    vs = set(vs); target = len(vs)
    def go(cur, seen):
        if len(seen) == target: return cur == end
        for w in adj[cur]:
            if w in vs and w not in seen and (w != end or len(seen) == target - 1):
                seen.add(w)
                if go(w, seen): return True
                seen.discard(w)
        return False
    return go(start, {start})

stats = Counter()
for line in open(sys.argv[1]):
    n, rest = line.split(' ', 1); n = int(n)
    hb = [tuple(sorted(e)) for e in eval(rest)]
    na = [set() for _ in range(n)]
    for u, v in hb: na[u].add(v); na[v].add(u)
    adj = [set(range(n)) - na[v] - {v} for v in range(n)]
    ok = False
    if n % 2 == 0:
        # (b): nonedge {s,s'}, Ham path in G-{s,s'} between H-adjacent x,y
        for (s, t) in hb:
            rest_v = [v for v in range(n) if v not in (s, t)]
            for (x, y) in hb:
                if x in (s, t) or y in (s, t): continue
                if ham_paths(rest_v, adj, x, y): ok = True; break
            if ok: break
    else:
        # (a): H-path x-y-s'-s ; Ham path of G-{y,s'} from x to s
        for y in range(n):
            for sp in na[y]:
                rest_v = [v for v in range(n) if v not in (y, sp)]
                for x in na[y]:
                    if x == sp: continue
                    for s in na[sp]:
                        if s in (y, x): continue
                        if ham_paths(rest_v, adj, x, s): ok = True; break
                    if ok: break
                if ok: break
            if ok: break
    stats[(n, ok)] += 1
    if not ok: print("FAIL", n, hb)
print(stats)

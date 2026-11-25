"""Test the strict two-class frame: disjoint non-edges S1,S2, matchings M1 (avoid S1), M2 (avoid S2),
M1 & M2 disjoint, every vertex of W covered by both, and some S-vertex covered."""
import itertools, sys
from collections import Counter

def matchings_covering(vs, adj, must, forbid_edges):
    # all matchings on vertex list vs covering all of `must`
    vs = sorted(vs); res = []
    def go(i, used, cur):
        if i == len(vs):
            res.append(list(cur)); return
        v = vs[i]
        if v in used: go(i+1, used, cur); return
        if v not in must: go(i+1, used, cur)
        for w in vs[i+1:]:
            if w not in used and w in adj[v] and frozenset((v,w)) not in forbid_edges:
                used.add(v); used.add(w); cur.append(frozenset((v,w)))
                go(i+1, used, cur)
                cur.pop(); used.discard(v); used.discard(w)
    go(0, set(), [])
    return res

def solve(n, adj, nonedges):
    sols = []
    for S1, S2 in itertools.permutations(nonedges, 2):
        if set(S1) & set(S2): continue
        W = set(range(n)) - set(S1) - set(S2)
        for M1 in matchings_covering([v for v in range(n) if v not in S1], adj, W, set()):
            for M2 in matchings_covering([v for v in range(n) if v not in S2], adj, W, set(M1)):
                cov = {v for e in M1 + M2 for v in e}
                if cov & (set(S1) | set(S2)):
                    return (S1, S2, M1, M2)
    return None

stats = Counter()
for line in open(sys.argv[1]):
    n, rest = line.split(' ', 1); n = int(n)
    hb = [tuple(sorted(e)) for e in eval(rest)]
    na = [set() for _ in range(n)]
    for u, v in hb: na[u].add(v); na[v].add(u)
    adj = [set(range(n)) - na[v] - {v} for v in range(n)]
    s = solve(n, adj, hb)
    stats[(n, s is not None)] += 1
    if s is None: print("FAIL", n, hb)
print(stats)

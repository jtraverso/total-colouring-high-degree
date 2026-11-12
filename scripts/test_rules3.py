"""Test candidate constructions for TCC when alpha(G) <= 2 and Delta(G) = n - 4.

Input: lines "n [edges of Hbar]" (Hbar = complement of G, triangle-free, min degree 3).
Construction (two levels): disjoint non-edges S1, S2; matchings M1 in G - S1, M2 in G - M1 - S2;
G' = G - M1 - M2 + apex joined to W = V \ (S1 u S2).  Success: Delta(G') <= Delta and the
vertices of degree Delta(G') induce a forest (Fournier) or Delta(G') < Delta (Vizing).
"""
import itertools
import sys
USE_D = len(sys.argv) < 3
BAD=[]


def matchings(vs, adj):
    vs = sorted(vs)
    res = []

    def go(i, used, cur):
        if i == len(vs):
            res.append(list(cur))
            return
        v = vs[i]
        if v in used:
            go(i + 1, used, cur)
            return
        go(i + 1, used, cur)  # leave v unmatched
        for w in vs[i + 1:]:
            if w not in used and w in adj[v]:
                used.add(v); used.add(w); cur.append((v, w))
                go(i + 1, used, cur)
                cur.pop(); used.discard(v); used.discard(w)

    go(0, set(), [])
    return res


def acyclic(nodes, edges):
    parent = {x: x for x in nodes}

    def f(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in edges:
        ra, rb = f(a), f(b)
        if ra == rb:
            return False
        parent[ra] = rb
    return True


def check(n, adj, D, S1, S2, M1, M2):
    W = [v for v in range(n) if v not in S1 and v not in S2]
    F = set(frozenset(e) for e in M1) | set(frozenset(e) for e in M2)
    deg = {}
    for v in range(n):
        d = sum(1 for u in adj[v] if frozenset((u, v)) not in F)
        deg[v] = d + (1 if v in W else 0)
    deg['c'] = len(W)
    md = max(deg.values())
    if md > D:
        return False
    if md < D:
        return True
    core = [x for x in deg if deg[x] == md]
    cs = set(core)
    edges = []
    for a, b in itertools.combinations(core, 2):
        if a == 'c' or b == 'c':
            o = b if a == 'c' else a
            if o in W:
                edges.append((a, b))
        elif b in adj[a] and frozenset((a, b)) not in F:
            edges.append((a, b))
    return acyclic(core, edges)


def main():
    stats = {}
    for line in open(sys.argv[1]):
        n, rest = line.split(' ', 1)
        n = int(n)
        hb = eval(rest)
        nonadj = [set() for _ in range(n)]
        for u, v in hb:
            nonadj[u].add(v); nonadj[v].add(u)
        adj = [set(range(n)) - nonadj[v] - {v} for v in range(n)]
        degs = [len(adj[v]) for v in range(n)]
        D = max(degs)
        assert D == n - 4
        majors = {v for v in range(n) if degs[v] == D}
        nonedges = [tuple(sorted(e)) for e in hb]
        # Rule: for every S1 and every max-coverage M1, there is S2 (containing U1) and for every
        # max-coverage M2 (priority: A2 coverage, then D-coverage) the result works.
        rule_ok_some_S1 = False
        ALLS1 = [True]
        exists_ok = False
        for S1 in nonedges:
            H = [v for v in range(n) if v not in S1]
            Ms = matchings(H, adj)
            cov = lambda M: (len(majors & {v for e in M for v in e}), len(M))
            best = max(cov(M) for M in Ms)
            opt1 = [M for M in Ms if cov(M) == best]
            all_M1_ok = True
            for M1 in opt1:
                cov1 = {v for e in M1 for v in e}
                U1 = [v for v in H if v in majors and v not in cov1]
                cands = [S2 for S2 in nonedges if not set(S2) & set(S1) and set(U1) <= set(S2)]
                if len(U1) == 1:
                    pass
                found = False
                for S2 in cands:
                    m1set = set(frozenset(e) for e in M1)
                    H2 = [v for v in range(n) if v not in S2]
                    adj2 = [set(u for u in adj[v] if frozenset((u, v)) not in m1set) for v in range(n)]
                    Ms2 = matchings(H2, adj2)
                    W = [v for v in range(n) if v not in S1 and v not in S2]
                    def p(v):
                        m1 = 1 if v in cov1 else 0
                        return len(adj[v]) - m1 + (1 if v in W else 0)
                    A2 = {v for v in H2 if p(v) >= D}
                    Dset = {v for v in A2 if any(u in adj2[v] for u in U1)}
                    cov2 = lambda M: ((len(Dset & {v for e in M for v in e}) if USE_D else 0), len(A2 & {v for e in M for v in e}), len(M))
                    must = {v for v in H2 if p(v) > D}
                    Ms2 = [M for M in Ms2 if must <= {v for e in M for v in e}]
                    if not Ms2:
                        BAD.append(('nomust',S1,M1,S2)); found=False; break
                    b2 = max(cov2(M) for M in Ms2)
                    if all(check(n, adj, D, S1, S2, M1, M2) for M2 in Ms2 if cov2(M2) == b2):
                        found = True
                    else:
                        BAD.append((S1,M1,S2)); found=False; break
                if not found:
                    all_M1_ok = False
                    break
            if all_M1_ok:
                rule_ok_some_S1 = True
            else:
                ALLS1[0] = False
        key = (n, rule_ok_some_S1, ALLS1[0])
        stats[key] = stats.get(key, 0) + 1
        if not rule_ok_some_S1:
            print("RULE FAILS", n, hb, flush=True)
    print(stats); print(BAD[:5])


if __name__ == "__main__":
    main()

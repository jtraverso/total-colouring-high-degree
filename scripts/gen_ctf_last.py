"""Generate, up to isomorphism, all graphs G on n vertices with alpha(G) <= 2 and
Delta(G) = n - 4, i.e. complements H of triangle-free graphs with minimum degree exactly 3.

Orderly-ish generation: triangle-free graphs are built vertex by vertex (new vertex joined to an
independent set), deduplicated by a canonical form computed by brute force over permutations
compatible with an equitable partition refinement.  Output: one line per graph, the edge list of
the complement Hbar (triangle-free, min degree 3).
"""
import itertools
import sys


def refine(n, adj):
    # colour refinement starting from degrees
    col = [len(adj[v]) for v in range(n)]
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in adj[v]))) for v in range(n)]
        keys = sorted(set(sig))
        new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(col)):
            return new
        col = new


def canon(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    col = refine(n, adj)
    classes = {}
    for v in range(n):
        classes.setdefault(col[v], []).append(v)
    keys = sorted(classes)
    best = None
    # iterate over products of permutations of each class (small for our sizes)
    for perms in itertools.product(*[itertools.permutations(classes[k]) for k in keys]):
        order = [v for p in perms for v in p]
        pos = {v: i for i, v in enumerate(order)}
        code = tuple(sorted(tuple(sorted((pos[u], pos[v]))) for u, v in edges))
        if best is None or code < best:
            best = code
    return best


def independent_sets(n, adj):
    res = []
    for r in range(n + 1):
        for S in itertools.combinations(range(n), r):
            if all(b not in adj[a] for a, b in itertools.combinations(S, 2)):
                res.append(S)
    return res


def main():
    nmax = int(sys.argv[1])
    level = {canon(1, []): (1, [])}
    out = {}
    for n in range(2, nmax + 1):
        nxt = {}
        for code, (m, edges) in level.items():
            adj = [set() for _ in range(m)]
            for u, v in edges:
                adj[u].add(v); adj[v].add(u)
            for S in independent_sets(m, adj):
                ne = list(edges) + [(s, m) for s in S]
                if n == nmax:
                    dg = [0] * (m + 1)
                    for a, b in ne:
                        dg[a] += 1; dg[b] += 1
                    if min(dg) != 3:
                        continue
                c = canon(m + 1, ne)
                if c not in nxt:
                    nxt[c] = (m + 1, ne)
        level = nxt
        good = []
        for code, (m, edges) in level.items():
            deg = [0] * m
            for u, v in edges:
                deg[u] += 1; deg[v] += 1
            if min(deg) == 3:
                good.append(list(code))
        out[n] = good
        print(f"n={n}: {len(level)} triangle-free graphs, {len(good)} with min degree 3", file=sys.stderr)
    for n, gs in out.items():
        for g in gs:
            print(n, g)


if __name__ == "__main__":
    main()

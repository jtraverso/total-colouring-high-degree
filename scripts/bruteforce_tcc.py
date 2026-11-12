"""Brute-force sanity check of the Hilton-Hind statement on small graphs.

For every labelled simple graph on n <= NMAX vertices with 4*Delta >= 3*n we search
for a total colouring with Delta + 2 colours (vertices and edges; adjacent vertices,
adjacent edges and incident vertex-edge pairs get different colours).
We also record the graphs needing exactly Delta + 2 colours (tightness, e.g. K_4).
"""
import itertools
import sys


def total_colourable(n, edges, k):
    # elements: vertices 0..n-1, edges n..n+m-1; build conflict graph
    m = len(edges)
    N = n + m
    nb = [set() for _ in range(N)]
    for idx, (u, v) in enumerate(edges):
        e = n + idx
        nb[u].add(v); nb[v].add(u)
        nb[e].add(u); nb[u].add(e)
        nb[e].add(v); nb[v].add(e)
        for jdx, (a, b) in enumerate(edges):
            if jdx != idx and len({u, v} & {a, b}) > 0:
                nb[e].add(n + jdx)
    order = sorted(range(N), key=lambda x: -len(nb[x]))
    col = [-1] * N

    def go(i, used):
        if i == N:
            return True
        x = order[i]
        forb = {col[y] for y in nb[x] if col[y] >= 0}
        # symmetry breaking: allow at most one new colour
        for c in range(min(k, used + 1)):
            if c not in forb:
                col[x] = c
                if go(i + 1, max(used, c + 1)):
                    return True
                col[x] = -1
        return False

    return go(0, 0)


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for n in range(0, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        checked = tight = 0
        for mask in range(1 << len(pairs)):
            edges = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
            deg = [0] * n
            for u, v in edges:
                deg[u] += 1; deg[v] += 1
            D = max(deg) if n else 0
            if 4 * D < 3 * n:
                continue
            checked += 1
            if not total_colourable(n, edges, D + 2):
                print("COUNTEREXAMPLE", n, edges)
                return 1
            if not total_colourable(n, edges, D + 1):
                tight += 1
        print(f"n={n}: {checked} labelled graphs with 4*Delta>=3n, all (Delta+2)-total-colourable; "
              f"{tight} need exactly Delta+2")
    # complete graphs and stars up to 8
    for n in range(1, 9):
        Kn = list(itertools.combinations(range(n), 2))
        D = n - 1
        print(f"K_{n}: Delta+2 ok={total_colourable(n, Kn, D + 2)}, Delta+1 ok={total_colourable(n, Kn, D + 1)}")
        star = [(0, i) for i in range(1, n)]
        print(f"K_1,{n-1}: Delta+1 ok={total_colourable(n, star, D + 1)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""Brute-force check: every graph G with alpha(G) <= 2 and Delta(G) = n - 4, n <= 10
(complements of the triangle-free graphs with minimum degree 3 listed in ctf10.txt),
has a total colouring with Delta + 2 colours."""
import sys
from bruteforce_tcc import total_colourable
cnt = {}
for line in open(sys.argv[1]):
    n, rest = line.split(' ', 1)
    n = int(n); hb = set(tuple(sorted(e)) for e in eval(rest))
    edges = [(u, v) for u in range(n) for v in range(u + 1, n) if (u, v) not in hb]
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1; deg[v] += 1
    D = max(deg); assert D == n - 4
    ok = total_colourable(n, edges, D + 2)
    cnt[(n, ok)] = cnt.get((n, ok), 0) + 1
    if not ok:
        print("FAIL", n, sorted(hb))
print(cnt)

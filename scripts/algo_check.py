"""Check the planned uniform construction on all 232 graphs (alpha<=2, Delta=n-4)."""
import sys, itertools
from collections import Counter
def ham(vs, adj, s, e):
    vs=set(vs); T=len(vs)
    def go(path, seen):
        cur=path[-1]
        if len(seen)==T: return list(path) if cur==e else None
        for w in adj[cur]:
            if w in vs and w not in seen and (w!=e or len(seen)==T-1):
                seen.add(w); path.append(w)
                r=go(path,seen)
                if r: return r
                path.pop(); seen.discard(w)
        return None
    return go([s],{s})
def alt(l):
    P=set(); Q=set()
    for i in range(len(l)-1):
        (P if i%2==0 else Q).add(frozenset((l[i],l[i+1])))
    return P,Q
def frame_ok(n,adj,x,y,s,t,M1,M2,r):
    D=n-4
    S={x,y,s,t}; W=set(range(n))-S
    assert len(S)==4 and y not in adj[x] and t not in adj[s]
    for M,av in ((M1,{x,y}),(M2,{s,t})):
        vs=[v for e in M for v in e]
        assert len(vs)==len(set(vs)), "not matching"
        assert not set(vs)&av, "not avoiding"
        for e in M:
            a,b=tuple(e); assert b in adj[a]
    assert not M1&M2
    cov1={v for e in M1 for v in e}; cov2={v for e in M2 for v in e}
    for v in W:
        if v!=r: assert v in cov1 and v in cov2, ("W",v)
    if r in W: assert r in cov1 or r in cov2
    U=[u for u in S if u not in cov1 and u not in cov2 and u!=r]
    for u,v in itertools.combinations(U,2): assert v not in adj[u], "U"
    return True
st=Counter()
for line in open(sys.argv[1]):
    n, rest = line.split(' ',1); n=int(n)
    hb=[tuple(sorted(e)) for e in eval(rest)]
    na=[set() for _ in range(n)]
    for u,v in hb: na[u].add(v); na[v].add(u)
    adj=[set(range(n))-na[v]-{v} for v in range(n)]
    for z in [v for v in range(n) if len(adj[v])==n-4]:
        Q=sorted(na[z]); O=set(range(n))-set(Q)-{z}
        N=lambda q: na[q]-{z}
        outs=[(q,u) for q in Q for u in adj[q] if u not in Q]
        if not outs:
            q1,q2,q3=Q; R=sorted(set(range(n))-set(Q)); c1,c2=[c for c in R if c!=z][:2]
            mid=[c for c in R if c not in (c1,c2)]
            l=[c1]+mid+([c2] if n%2==0 else [])
            P,QQ=alt(l)
            M2=P|{frozenset((q1,q3))}; M1=QQ|{frozenset((q3,q2))}
            r = l[-1] if n%2 else q1
            frame_ok(n,adj,q1,c1,q2,c2,M1,M2,r); st[(n,'D')]+=1; continue
        q,u=outs[0]
        if n%2==1:
            q1=q; q2=[a for a in Q if a!=q1][0]; q3=[a for a in Q if a not in (q1,q2)][0]
            y1,y2=sorted(N(q1))[:2]
            ts=sorted(N(q2)-{y1,u})
            if ts: y,t=y1,ts[0]
            else: y,t=y2,y1
            K=set(range(n))-set(Q)-{y,t}
            l=ham(K|{q1,y},adj,q1,y); assert l
            P,QQ=alt(l); M2=P; M1=QQ|{frozenset((q2,q3))}
            frame_ok(n,adj,q1,y,q2,t,M1,M2,q3); st[(n,'odd')]+=1
        else:
            a,b=[w for w in Q if w!=q]; v=u
            ys=sorted(N(a)-{v}); found=None
            for y in ys:
                ts=sorted(N(b)-{v,y})
                if ts: found=(a,b,q,y,ts[0],v); break
            if not found:
                y0=ys[0]; assert N(a)=={v,y0} and N(b)=={v,y0}
                yp=v; tp=sorted(N(q)-{yp})[0]
                vp=sorted(O-{v,y0,tp})[0]; assert vp in adj[a]
                found=(b,q,a,yp,tp,vp)
            q1,q2,q3,y,t,v=found
            assert v in adj[q3] and v not in (y,t) and v in O
            K=set(range(n))-{q1,q2,y,t}
            l=ham(K|{q1,y},adj,q1,y); assert l, "no ham"
            P,QQ=alt(l); frame_ok(n,adj,q1,y,q2,t,QQ,P,q1); st[(n,'even')]+=1
print(st)

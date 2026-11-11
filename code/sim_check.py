"""Simulation of preferential attachment with fixed out-degree m and attachment function f.

Vertex t sends m edges to 1..t-1 one at a time; an endpoint is chosen with probability proportional to
f(in-degree), and in-degrees are updated after every edge. The new vertex is not eligible, parallel edges are
allowed, there are no loops. The simulated graph is compared with the formulas of the paper:
  - the in-degree law of the two-level rule f(0)=a, f(k)=b (k>=1);
  - the mean relative age of the first parent, from the density [b+(a-b)u^(lambda a)]/c on (0,1);
  - one ball of radius 2: a root of in-degree 0 whose m parents each have in-degree exactly 1 (the root is
    their only child) and whose m^2 grandparents are distinct with no edge among them; its limiting
    probability is (a z/c)^m / (1 + lambda a + m lambda b);
  - for f(k)=sqrt(k+1): c_f solves sum_k prod_{j<k} m f(j)/(c+m f(j)) = m, and the in-degree law is
    p_0=c/(c+m f(0)), p_k = m f(k-1) p_{k-1}/(c+m f(k)).
usage: python sim_check.py N SEED OUT.json
"""
import json
import math
import random
import sys


class Fenwick:
    def __init__(self, n):
        self.n = n
        self.t = [0.0] * (n + 1)

    def add(self, i, v):
        i += 1
        while i <= self.n:
            self.t[i] += v
            i += i & -i

    def find(self, x):
        """smallest index k with prefix(k) > x"""
        pos = 0
        step = 1 << (self.n.bit_length())
        while step:
            nxt = pos + step
            if nxt <= self.n and self.t[nxt] <= x:
                pos = nxt
                x -= self.t[nxt]
            step >>= 1
        return pos


def simulate(n, m, f, rng, dcap=8192):
    indeg = [0] * (n + 1)
    outs = [[] for _ in range(n + 1)]
    members = [[] for _ in range(dcap)]   # degree class -> vertices
    where = [0] * (n + 1)                 # index of vertex inside its class list
    fw = Fenwick(dcap)
    total = 0.0
    fv = [f(k) for k in range(dcap)]

    def insert(v, k):
        nonlocal total
        where[v] = len(members[k])
        members[k].append(v)
        fw.add(k, fv[k])
        total += fv[k]

    def remove(v, k):
        nonlocal total
        lst = members[k]
        i = where[v]
        last = lst.pop()
        if last != v:
            lst[i] = last
            where[last] = i
        fw.add(k, -fv[k])
        total -= fv[k]

    insert(1, 0)
    for t in range(2, n + 1):
        for _ in range(m):
            x = rng.random() * total
            k = fw.find(x)
            if k >= dcap or not members[k]:      # float drift guard: fall back to a linear scan
                acc = 0.0
                for kk in range(dcap):
                    acc += fv[kk] * len(members[kk])
                    if acc > x and members[kk]:
                        k = kk
                        break
            lst = members[k]
            v = lst[int(rng.random() * len(lst))]
            remove(v, k)
            insert(v, k + 1)
            indeg[v] = k + 1
            outs[t].append(v)
        insert(t, 0)
        if t % 50000 == 0:   # refresh the running total against drift
            total = sum(fv[kk] * len(members[kk]) for kk in range(dcap) if members[kk])
    return indeg, outs


def degree_law(indeg, n, kmax):
    cnt = [0] * (kmax + 1)
    for v in range(1, n + 1):
        if indeg[v] <= kmax:
            cnt[indeg[v]] += 1
    return [c / n for c in cnt]


def two_level_theory(m, a, b, kmax):
    # z solves (a-b) z^2 + (2b + m a - a) z - b = 0 in (0,1)
    A, B, C = (a - b), (2 * b + m * a - a), -b
    if abs(A) < 1e-15:
        z = -C / B
    else:
        disc = math.sqrt(B * B - 4 * A * C)
        roots = [(-B + disc) / (2 * A), (-B - disc) / (2 * A)]
        z = [r for r in roots if 0 < r < 1][0]
    c = b + (a - b) * z
    lam = m / c
    p = [z, lam * a * z / (1 + lam * b)]
    q = lam * b / (1 + lam * b)
    while len(p) <= kmax:
        p.append(p[-1] * q)
    mean_parent_age = (b / 2 + (a - b) / (2 + lam * a)) / c
    ball2 = (a * z / c) ** m / (1 + lam * a + m * lam * b)
    return {"z": z, "c": c, "lambda": lam, "p": p[:kmax + 1], "mean_parent_age": mean_parent_age, "ball2": ball2}


def ball2_fraction(indeg, outs, n, m, lo):
    hits = 0
    tot = 0
    for v in range(lo, n + 1):
        tot += 1
        if indeg[v] != 0:
            continue
        ps = outs[v]
        if len(set(ps)) != m or any(indeg[p] != 1 for p in ps):
            continue
        gs = [g for p in ps for g in outs[p]]
        if len(gs) != m * m or len(set(gs)) != m * m:
            continue
        gset = set(gs)
        if any(h in gset for g in gs for h in outs[g]):
            continue
        hits += 1
    return hits / tot


def mean_first_parent_age(outs, n, lo):
    s = 0.0
    k = 0
    for t in range(lo, n + 1):
        s += outs[t][0] / t
        k += 1
    return s / k


def sublinear_theory(m, f, kmax):
    def M(d):
        tot, prod = 0.0, 1.0
        for k in range(1, 20000):
            prod *= m * f(k - 1) / (d + m * f(k - 1))
            tot += prod
            if prod < 1e-16:
                break
        return tot
    lo, hi = 1e-6, 1e6
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        if M(mid) > m:
            lo = mid
        else:
            hi = mid
    c = math.sqrt(lo * hi)
    p = [c / (c + m * f(0))]
    for k in range(1, kmax + 1):
        p.append(m * f(k - 1) * p[-1] / (c + m * f(k)))
    return {"c_f": c, "p": p}


def main():
    n, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    rng = random.Random(seed)
    m, a, b = 2, 1.0, 2.0
    res = {"n": n, "seed": seed, "m": m}
    th = two_level_theory(m, a, b, 8)
    indeg, outs = simulate(n, m, lambda k: a if k == 0 else b, rng)
    res["two_level"] = {"theory": th, "sim_degree_law": degree_law(indeg, n, 8),
                        "sim_mean_first_parent_age_late_half": mean_first_parent_age(outs, n, n // 2),
                        "sim_ball2_fraction_all_roots": ball2_fraction(indeg, outs, n, m, 2),
                        "sim_ball2_fraction_late_half": ball2_fraction(indeg, outs, n, m, n // 2)}
    fs = lambda k: math.sqrt(k + 1.0)
    th2 = sublinear_theory(m, fs, 10)
    indeg2, outs2 = simulate(n, m, fs, rng)
    s_n = sum(fs(indeg2[v]) for v in range(1, n + 1)) / n
    res["sqrt_rule"] = {"theory": th2, "sim_degree_law": degree_law(indeg2, n, 10), "sim_S_n_over_n": s_n,
                        "sim_max_indegree": max(indeg2)}
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(res, fh, indent=1)
    print(json.dumps(res)[:3000])


if __name__ == "__main__":
    main()

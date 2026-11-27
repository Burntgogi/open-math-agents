"""Independent finite controls for the Green 39 incidence and exposure arguments."""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import cos, exp, log, pi, sin


def subsets(p, n):
    return combinations(range(p), n)


def reps(p, a, t):
    return Counter((x + y) % p for x in a for y in t)


def proportion(p, k, t):
    good = total = 0
    for a in subsets(p, k):
        good += any(len(reps(p, a, s)) == p for s in subsets(p, t))
        total += 1
    return Fraction(good, total)


def check_incidence(p, k, t):
    count = 0
    for a in subsets(p, k):
        dif = Counter((v - w) % p for v in a for w in a)
        for centers in subsets(p, t):
            rows = {u: {(u + v) % p for v in a} for u in centers}
            mult = reps(p, a, centers)
            loss = k * t - len(mult)
            nonprivate = {u: [v for v in a if mult[(u + v) % p] > 1]
                          for u in centers}
            assert sum(map(len, nonprivate.values())) <= 2 * loss
            for u in centers:
                observed = sum(len(rows[u] & rows[z]) >= 2
                               for z in centers if z != u)
                rectangles = sum(len(list(combinations(rows[u] & rows[z], 2)))
                                 for z in centers if z != u)
                budget = sum(dif[(v - w) % p] - 1
                             for v, w in combinations(nonprivate[u], 2))
                assert observed <= rectangles <= budget
            for n in range(1, t + 1):
                partial = [k * n - len(reps(p, a, s))
                           for s in combinations(centers, n)]
                assert t * sum(partial) <= n * loss * len(partial)
            count += 1
    return count


def check_exposure(p, k, s):
    count = 0
    for seed in subsets(p, s):
        spectrum = [sum(complex(cos(2*pi*h*v/p), sin(2*pi*h*v/p))
                        for v in seed) for h in range(1, p)]
        spectral_square = max(abs(z)**2 for z in spectrum)
        for first in subsets(p, k // 2):
            covered = set(reps(p, first, seed))
            hits = [sum((z + v) % p in covered for v in seed) for z in range(p)]
            mean = Fraction(s * len(covered), p)
            assert sum(hits) == p * mean
            variance = sum((y - mean)**2 for y in hits) / p
            assert float(variance) <= spectral_square * len(covered) / p + 1e-9
            for rest in combinations(sorted(set(range(p)) - set(first)), k - len(first)):
                loss = k * s - len(reps(p, first + rest, seed))
                assert sum(hits[v] for v in rest) <= loss
                count += 1
    return count


def check_weighted_sum(p, n, s):
    """Count the same witnesses by input differences and by output translates."""
    count = 0
    for first in subsets(p, n):
        dif = Counter((v - w) % p for v in first for w in first)
        for seed in subsets(p, s):
            sd = Counter((v - w) % p for v in seed for w in seed)
            weights = [sd[v] if v else 0 for v in range(p)]
            expansion = sum(weights[v] * weights[w] * dif[(v - w) % p]
                            for v in range(p) for w in range(p))
            smooth = [sum(weights[(x - v) % p] for v in first) for x in range(p)]
            assert sum(z * z for z in smooth) == expansion
            covered = set(reps(p, first, seed))
            hits = [sum((x + v) % p in covered for v in seed) for x in range(p)]
            assert all(z <= w + s * (x in first)
                       for x, (z, w) in enumerate(zip(hits, smooth)))
            classes = {min((v - w) % p, (w - v) % p)
                       for v, w in combinations(seed, 2)}
            if len(classes) == s * (s - 1) // 2:
                edges = sum(min((v-w) % p, (w-v) % p) in classes
                            for v, w in combinations(first, 2))
                assert edges == sum(dif[(v-w) % p] for v, w in combinations(seed, 2))
            count += 1
    return count


def check_asymmetric():
    p = 7
    weights = (0, 1, 1, 2, 3, 0, 1)
    mass = sum(weights)
    count = 0
    for first in subsets(p, 2):
        g = [sum(weights[(a-z) % p] for a in first) for z in range(p)]
        for last in combinations(sorted(set(range(p)) - set(first)), 2):
            a = first + last
            for centers in subsets(p, 3):
                full = reps(p, a, centers)
                bad = {t: sum(full[(v+t) % p] > 1 for v in a) for t in centers}
                for region in combinations(centers, 2):
                    covered = set(reps(p, first, region))
                    assert len(covered) >= len(first)*len(region) - sum(bad[t] for t in region)
                    for seed in combinations(centers, 1):
                        hits = sum((z+t) % p in covered for z in last for t in seed)
                        assert hits <= sum(bad[t] for t in seed)
                        baseline = [len(seed)*sum(weights[(u-z) % p] for u in covered)
                                    for z in range(p)]
                        assert sum(baseline[z] for z in last) == len(seed)*sum(
                            weights[(u-z) % p] for u in covered for z in last)
                        # Arbitrary cutoff on g, avoiding the very slack asymptotic constants.
                        cut = 2
                        upper_tail = max(sum(max(0, g[(z-v) % p]-cut) for z in last)
                                         for v in range(p))
                        for n in range(len(last)+1):
                            for exceptional in combinations(last, n):
                                assert sum(baseline[z] for z in exceptional) <= (
                                    len(seed)*len(region)*(cut*n + upper_tail))
                        # Fourier residual against a nonuniform, nonsymmetric model.
                        err2 = sum((mass * sum((z+t) % p in covered for t in seed)
                                    - baseline[z])**2 for z in range(p))
                        coeff = [mass * (t in seed) - len(seed)*weights[t] for t in range(p)]
                        largest = max(abs(sum(v*complex(cos(2*pi*j*t/p), sin(2*pi*j*t/p))
                                              for t, v in enumerate(coeff)))**2
                                      for j in range(1, p))
                        assert err2 <= largest * len(covered) + 1e-7
                        count += 1
    return count


def check_fit(heavy_limit):
    # Finite analog of the fitting loop. A small threshold exercises both outcomes.
    p, eta = 11, 0.4
    chars = [[sign * trig(2*pi*j*t/p) for t in range(p)]
             for j in range(1, p) for trig in (cos, sin) for sign in (1, -1)]
    totals = Counter()
    for target in subsets(p, 4):
        remain = set(target)
        while remain:
            law = [1/p] * p
            for _ in range(2 + int(16*log(p)/eta**2)):
                heavy = [value > heavy_limit for value in law]
                mh = sum(value for value, yes in zip(law, heavy) if yes)
                nh = sum(heavy[v] for v in remain)/len(remain)
                if mh > eta and nh >= eta/2:
                    remain = {v for v in remain if not heavy[v]}
                    totals['peel'] += 1
                    break
                if mh > eta:
                    feat = [-int(yes) for yes in heavy]
                else:
                    def gap(f):
                        return (sum(f[v] for v in remain)/len(remain)
                                - sum(a*b for a, b in zip(law, f)))
                    feat = max(chars, key=gap)
                    if gap(feat) <= eta/2:
                        fitted = [0 if yes else value/(1-mh) for yes, value in zip(heavy, law)]
                        assert max(fitted) <= 2*heavy_limit
                        assert abs(sum(fitted) - 1) < 1e-10
                        assert all(abs(sum(f[v] for v in remain)/len(remain)
                                           - sum(a*b for a, b in zip(fitted, f))) <= 3*eta
                                   for f in chars)
                        totals['fit'] += 1
                        remain = set()
                        break
                tilt = [v*exp(eta*f/4) for v, f in zip(law, feat)]
                norm = sum(tilt)
                after = [v/norm for v in tilt]
                drop = sum(log(after[v]/law[v]) for v in remain)/len(remain)
                assert drop >= eta**2/16
                law = after
                totals['update'] += 1
            else:
                raise AssertionError("entropy iteration bound exceeded")
    return totals


if __name__ == "__main__":
    controls = [(7, 4, 2, Fraction(3, 5)), (11, 3, 4, Fraction(1, 3)),
                (11, 4, 3, Fraction(1, 6))]
    for p, k, t, expected in controls:
        result = proportion(p, k, t)
        assert result == expected
        print(f"proportion({p}, {k}, {t}) = {result}")
    for p, k, t in [(7, 3, 3), (11, 3, 3)]:
        print(f"incidence and thinning, p={p}: {check_incidence(p, k, t)} pairs")
    print("exposure, p=7:", check_exposure(7, 4, 3), "ordered splits with seed")
    print("weighted differences and Sidon sampling, p=11:",
          check_weighted_sum(11, 4, 3), "pairs")
    print("asymmetric incidence, clipped baseline and Fourier residual:", check_asymmetric())
    fit_counts = check_fit(0.13) + check_fit(0.5)
    assert all(fit_counts[name] for name in ('fit', 'peel', 'update'))
    print("finite fitting loop:", dict(fit_counts))
    sigma = Fraction(1, 10**13)
    assert Fraction(1, 10**24) < sigma * Fraction(1, 128*10**7)
    assert float(sigma)*(5001+log(1/float(sigma))) < 1e-7/32
    assert 24*log(10)+1000+5000/20+log(5+2*log(2*5000**2)) < 2500
    h, a = Fraction(1, 10**7), Fraction(1, 10**9)
    assert a < h / 32 and Fraction(1, 10**20) / a < h / 512
    assert h < Fraction(1, 64 * 10**5)
    assert Fraction(1, 8) < Fraction(2, 3) / 5
    assert Fraction(1, 2) - Fraction(180, 640) > Fraction(1, 5)
    assert (Fraction(1, 16) - Fraction(1, 640)) / 8 > Fraction(1, 180)
    # The fixed-size Singer control has one high point and no double-overlap edges.
    singer = (0, 1, 3, 9)
    mult = reps(13, singer, [-v for v in singer])
    assert Counter(mult.values()) == {1: 12, 4: 1}
    print("rational margins and Singer incidence control passed")

"""Independent checks of the constants, exchange extension and ordered-slice laws."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb, exp, log


def subsets(n, k):
    return [frozenset(c) for c in combinations(range(n), k)]


def score(A, P, t, n):
    holes = set(range(n)) - {(a + v) % n for a in A for v in P}
    return sum((a + t) % n in holes for a in A)


def check_slices():
    n, k = 7, 3
    samples = subsets(n, k)
    tests = 0
    for m in (0, 1, 2, 3):
        for P in subsets(n, m):
            rho = Q(comb(n - m, k), comb(n, k))
            for t in range(n):
                scores = {A: score(A, P, t, n) for A in samples}
                want = 0 if t in P else k * rho * Q(n, n - m)
                assert Q(sum(scores.values()), len(samples)) == want
                translates = [{(v + u) % n for u in P} for v in range(n)]
                for L in (1, 2):
                    good = [A for A in samples if all(len(A & C) <= L for C in translates)]
                    if not good:
                        continue
                    ext = {A: min(k, min(scores[B] + (1 + L)*len(A - B) for B in good))
                           for A in samples}
                    assert all(ext[A] == scores[A] for A in good)
                    assert all(abs(ext[A] - ext[B]) <= 1 + L for A in samples
                               for B in samples if len(A - B) == 1)
                tests += 1
    return tests


def check_orientations():
    # An asymmetric law helps detect an accidental reflection in either convolution.
    n = 7
    weights = [1, 4, 7, 2, 3, 1, 2]
    tests = 0
    for A1 in subsets(n, 2):
        for A2 in subsets(n, 2):
            if A1 & A2:
                continue
            for R in subsets(n, 2):
                U = {(a + v) % n for a in A1 for v in R}
                y0 = [sum(weights[(u-z) % n] for u in U) for z in range(n)]
                g = [sum(weights[(a-z) % n] for a in A1) for z in range(n)]
                assert all(y0[z] <= sum(g[(z-v) % n] for v in R) for z in range(n))
                assert sum(y0[z] for z in A2) == sum(sum(weights[(u-z) % n]
                                                        for z in A2) for u in U)
                tests += 1
    return tests


def check_constants():
    q = lambda s: Q(str(s))
    assert 1 - q(.02) / q(.0225) == Q(1, 9)
    assert q(.0114) - q(.0225)/2 == q(.00015)
    assert Q(1, 9) - Q(4, 3*5000**2) > q(.11)
    # Uniform for k >= 10,000, including all floors and p < (k+1)^2.
    a, r, pmax = Q(1, 2)-Q(1, 20000), q(.0999), (1+Q(1, 10000))**2
    lower = (a-q(.0114))/(2*pmax) - Q(1, 10**8)/r
    upper = q(.0114)/r
    assert lower > q(.244) and upper < q(.115)
    f = (q(.244)-q(.115)-2*q(.001))/q(.51)
    assert f > q(.24)
    assert 7/(q(.099)*q(.001)) < 71000
    slope = q(.101)-2*q(.24)*q(.22)
    intercept = .1*(1+log(10))+.001*(1+log(1000))+log(2)+.24*log(2*71000**2)-480
    slack = 2500 - (24*log(10)+1000+.22*5000+log(5+2*log(2*5000**2)))
    assert slope == -q(.0046) and intercept < -470 and slack > 300
    assert .001-2*(exp(1)-1)*1e-8 > .0009999
    return dict(lower=float(lower), upper=float(upper), fraction=str(f), slope=str(slope),
                intercept=intercept, shrink_slack=slack)


if __name__ == "__main__":
    print("score means:", check_slices(), "asymmetric incidence checks:", check_orientations())
    print(check_constants())

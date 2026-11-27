"""Independent finite checks for the review. Uses Python's standard library."""

from itertools import combinations
from math import ceil, comb, e, log, sqrt


def subsets(p, size=None):
    if size is None:
        return range(1 << p)
    return [sum(1 << i for i in indices) for indices in combinations(range(p), size)]


def shift(mask, by, p):
    by %= p
    return ((mask << by) | (mask >> (p - by))) & ((1 << p) - 1)


def sumset(a, p_set, p):
    result = 0
    for v in range(p):
        if a & (1 << v):
            result |= shift(p_set, v, p)
    return result


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def check_holes():
    p, k = 7, 3
    samples = subsets(p, k)
    full = (1 << p) - 1
    mean_checks = lipschitz_checks = extension_checks = 0
    for centers in subsets(p):
        m = centers.bit_count()
        holes = [full ^ sumset(a, centers, p) for a in samples]
        assert sum(h.bit_count() for h in holes) == p * choose(p - m, k)
        shifts = [shift(centers, v, p) for v in range(p)]
        regularity = [max((a & block).bit_count() for block in shifts) for a in samples]
        distances = [[(a & ~b).bit_count() for b in samples] for a in samples]
        for t in range(p):
            scores = [(shift(a, t, p) & h).bit_count() for a, h in zip(samples, holes)]
            expected_sum = 0 if centers & (1 << t) else p * choose(p - 1 - m, k - 1)
            assert sum(scores) == expected_sum
            mean_checks += 1
            for i, j in combinations(range(len(samples)), 2):
                difference = scores[i] - scores[j]
                assert difference <= (1 + regularity[i]) * distances[i][j]
                assert -difference <= (1 + regularity[j]) * distances[i][j]
                lipschitz_checks += 1
            for cap in range(min(regularity), max(regularity) + 1):
                regular = [j for j in range(len(samples)) if regularity[j] <= cap]
                extension = [
                    min(k, min(scores[j] + (1 + cap) * row[j] for j in regular))
                    for row in distances
                ]
                assert all(extension[j] == scores[j] for j in regular)
                for i, j in combinations(range(len(samples)), 2):
                    assert abs(extension[i] - extension[j]) <= (1 + cap) * distances[i][j]
                extension_checks += 1
    return mean_checks, lipschitz_checks, extension_checks


def check_graphs():
    # Test the large-component truncation, even when the undershoot is 1 or 2.
    n = 6
    pairs = list(combinations(range(n), 2))
    thresholds = 0
    for mask in range(1 << len(pairs)):
        adj = [set() for _ in range(n)]
        for j, (a, b) in enumerate(pairs):
            if mask & (1 << j):
                adj[a].add(b)
                adj[b].add(a)
        components = []
        unseen = set(range(n))
        while unseen:
            root = min(unseen)
            connected_order = [root]
            unseen.remove(root)
            for vertex in connected_order:
                for child in sorted(unseen & adj[vertex]):
                    unseen.remove(child)
                    connected_order.append(child)
            if len(connected_order) >= 3:
                components.append(connected_order)
        total = sum(map(len, components))
        for cutoff in range(1, total + 1):
            used = set()
            for component in components:
                need = cutoff - len(used)
                selected = component[:max(3, need)]
                assert len(selected) >= 3 and used.isdisjoint(selected)
                for j in range(1, len(selected)):
                    assert adj[selected[j]].intersection(selected[:j])
                used.update(selected)
                if len(used) >= cutoff:
                    break
            assert cutoff <= len(used) <= cutoff + 2
            thresholds += 1
    return 1 << len(pairs), thresholds


def check_difference_graph():
    p = 11
    checked = 0
    for centers in subsets(p, 3):
        sites = [i for i in range(p) if centers & (1 << i)]
        differences = [min((i-j) % p, (j-i) % p) for i, j in combinations(sites, 2)]
        if len(set(differences)) != len(differences):
            continue
        for sample in subsets(p, 4):
            points = [i for i in range(p) if sample & (1 << i)]
            edges = sum(min((i-j) % p, (j-i) % p) in differences
                        for i, j in combinations(points, 2))
            assert edges == sum((sample & shift(sample, d, p)).bit_count() for d in differences)
            checked += 1
    return checked


def check_margins():
    # Worst active-level slope and intercept. Enlarge floors in the safe direction.
    alpha = 1e-5
    old_slope = 2 * alpha - 1 / 200
    old_intercept = (2 * alpha * log(2 * e / alpha) + log(2)
                     + log(2 * (1400 / alpha) ** 2) / 20 - 100)
    assert old_intercept + old_slope * 5000 < -1 and old_slope < 0
    assert 1e-13 * (5001 + log(1e13)) < 1e-7 / 32
    assert 1e-24 < (1e-7 / 128) * 1e-13
    assert 1 / (64 * 1e5) > 1e-7
    assert (0.5 - 1e-24) * 0.5 - 1e-8 / alpha > 0.22
    assert 2 / sqrt(1e24) < 1e-8

    last_retained = 1 - 0.02 / 0.0225 - 4 / (3 * 5000**2)
    assert last_retained > 0.11
    assert 0.0225 / 2 < 0.0114
    assert 0.5 * (0.5 - 0.0114) - 1e-8 / 0.1 > 0.244
    assert 0.0114 / 0.1 < 0.115
    hit_fraction = (0.244 - 0.115 - 0.001 - 0.001) / 0.51
    assert hit_fraction > 0.24
    assert 7 / (0.001 * 0.099) < 71000
    assert 0.001 > 2 * (e - 1) * 1e-8
    slope = 0.101 - 2 * 0.24 * 0.22
    intercept = (0.1 * log(10 * e) + 0.001 * log(1000 * e) + log(2)
                 + 0.24 * log(2 * 71000**2) - 480)
    assert slope < 0 and intercept < -470
    for a in (0.05, 0.22):
        x = 5000
        slack = x/2 - (log(1e24) + 1000 + a*x + log(5 + 2*log(2*x*x)))
        assert slack > 300
        assert 0.5 - a - (4/x) / (5 + 2*log(2*x*x)) > 0
    assert 0.98 + 0.11 > 1.01
    print(f"old exponent at x=5000: {old_intercept + old_slope * 5000:.6f}")
    print(f"1% retained fraction >= {last_retained:.9f}, hits >= {hit_fraction:.9f}")
    print(f"1% intercept {intercept:.6f}, slope {slope:.6f}")


if __name__ == "__main__":
    check_margins()
    means, pairs, extensions = check_holes()
    print(f"{means} exact score means, {pairs} score pair bounds, {extensions} global extensions")
    graphs, cutoffs = check_graphs()
    print(f"{graphs} simple graphs, {cutoffs} connected-truncation cases")
    print(f"{check_difference_graph()} distinct-difference edge identities")

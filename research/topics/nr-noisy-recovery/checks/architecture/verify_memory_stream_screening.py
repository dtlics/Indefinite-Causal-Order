"""Finite exact guards for the memory-stream-screening component.

The all-size C6 reduction, simplex-volume law, concentration, spectral
perturbation and physical interface are analytic. This checker reconstructs
finite probability ledgers and complete logical matrix-unit code actions.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("Exact proof checks require assertions; do not use -O.")

from fractions import Fraction as F
from itertools import product
import json
from math import isqrt


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def address_ledgers() -> tuple[int, int]:
    records = 0
    families = 0
    for m in (2, 3, 4):
        # A finite null distribution over all these classical address histories
        # and terminal outputs; arbitrary memory is not being simulated here.
        runs = [(h, out) for length in range(5)
                for h in product(range(m), repeat=length)
                for out in range(-1, m)]
        probability = F(1, len(runs))
        for q in (1, 2, 3):
            alpha = [F(0)] * m
            tail = [F(0)] * m
            optimistic = [F(0)] * m
            means = [F(0)] * m
            for history, out in runs:
                counts = [history.count(j) for j in range(m)]
                for j, n in enumerate(counts):
                    original = int(out == j)
                    reaches = int(n > q)
                    capped = int(original or reaches)
                    require(capped >= original and capped-original <= reaches,
                            "optimistic local cap event containment")
                    require(q*reaches <= n, "per-run query-tail Markov ledger")
                    alpha[j] += probability*original
                    tail[j] += probability*reaches
                    optimistic[j] += probability*capped
                    means[j] += probability*n
                    records += 1
            require(sum(alpha) <= 1, "one terminal candidate index per run")
            for j in range(m):
                require(optimistic[j] <= alpha[j]+tail[j]
                        and q*tail[j] <= means[j],
                        "averaged local accept/tail ledger")
            require(sum(tail) <= sum(means)/q,
                    "direct-sum tail ledger with retained address history")
            families += 1
    return records, families


def expected_cost_rounding() -> int:
    checked = 0
    d = F(215, 10000)
    for m in range(2, 20):
        for q in range(1, 14):
            for s in (F(2, 3), F(3, 4), F(9, 10), F(1)):
                a = s-d-F(1, m)
                if a <= 0:
                    continue
                mq = m*q
                cap = (a*mq/2).__floor__()
                if cap < 1:
                    continue
                bound = cap*(a-F(cap, mq))
                require(bound >= a*a*mq/4-F(1, mq),
                        "integer optimistic selection-cost bound")
                require(bound >= 0 and cap <= a*mq/2,
                        "positive finite global query cap")
                checked += 1
    return checked


def pool_summary(m: int, good: int, r: int, plus: F) -> tuple[F, F, F, F]:
    # good=-1 means all LOW. Recursing over packages stops at the first
    # certificate; all rejecting trials and all earlier devices are counted.
    correct, wrong, none, trials = F(0), F(0), F(1), F(0)
    for j in reversed(range(m)):
        if j == good:
            correct, wrong, none, trials = F(1), F(0), F(0), F(r)
        else:
            certifies = plus**r
            rejected = 1-certifies
            local_mean = sum((plus**k for k in range(r)), F(0))
            correct, wrong, none, trials = (
                rejected*correct, certifies+rejected*wrong,
                rejected*none, local_mean+rejected*trials)
    return correct, wrong, none, trials


def native_pool_ledgers() -> int:
    checked = 0
    for m in range(1, 9):
        for r in range(1, 10):
            for plus in (F(1, 2), F(5, 8), F(3, 4)):
                local_mean = sum((plus**k for k in range(r)), F(0))
                local_mass = plus**r + sum(
                    ((1-plus)*plus**(k-1) for k in range(1, r+1)), F(0))
                require(local_mass == 1 and local_mean <= min(F(r), F(4)),
                        "truncated geometric trial mass and all-attempt mean")
                for good in range(-1, m):
                    correct, wrong, none, trials = pool_summary(m, good, r, plus)
                    require(correct+wrong+none == 1, "complete pool output flags")
                    require(wrong <= m*plus**r, "all-device false certificate bound")
                    require(trials <= 4*m+r and trials <= m*r,
                            "all rejecting and certifying trial costs")
                    if good >= 0:
                        require(correct >= 1-m*plus**r,
                                "unique-HIGH selection success ledger")
                    else:
                        require(correct == 0 and trials <= 4*m,
                                "all-LOW mean includes every rejected package")
                    checked += 1
    return checked


def stopped_likelihood(q: F, h: F, ell: F, upper: F, lower: F,
                       horizon: int) -> tuple[F, F, F, F, F]:
    f1, f0 = h/ell, (1-h)/(1-ell)
    live = {F(1): F(1)}
    accepted = rejected = stopped_lr = stopped_inverse = expected = F(0)
    for _ in range(horizon):
        expected += sum(live.values(), F(0))
        following: dict[F, F] = {}
        for ratio, weight in live.items():
            for multiplier, probability in ((f1, q), (f0, 1-q)):
                next_ratio, mass = ratio*multiplier, weight*probability
                if next_ratio >= upper:
                    accepted += mass
                    stopped_lr += mass*next_ratio
                    stopped_inverse += mass/next_ratio
                elif next_ratio <= lower:
                    rejected += mass
                    stopped_lr += mass*next_ratio
                    stopped_inverse += mass/next_ratio
                else:
                    following[next_ratio] = following.get(next_ratio, F(0))+mass
        live = following
    ongoing = sum(live.values(), F(0))
    require(accepted+rejected+ongoing == 1, "finite stopped likelihood flags")
    lr_mean = stopped_lr+sum((mass*ratio for ratio, mass in live.items()), F(0))
    inverse_mean = stopped_inverse+sum(
        (mass/ratio for ratio, mass in live.items()), F(0))
    require(expected <= horizon, "finite expected stopping ledger")
    return accepted, rejected, ongoing, lr_mean, inverse_mean


def sequential_noise_ledgers() -> int:
    h, ell = F(1, 8), F(1, 4)
    f1, f0 = h/ell, (1-h)/(1-ell)
    checked = 0
    for upper in (F(4), F(16)):
        for lower in (F(1, 4), F(1, 8)):
            for horizon in (1, 4, 8, 16):
                for q in (ell, F(1, 2), F(1)):
                    require(q*f1+(1-q)*f0 <= 1,
                            "composite LOW likelihood multiplier")
                    accepted, _, _, lr, _ = stopped_likelihood(
                        q, h, ell, upper, lower, horizon)
                    require(lr <= 1 and accepted <= 1/upper,
                            "LOW finite stopped-supermartingale acceptance bound")
                    checked += 1
                for q in (F(0), h/2, h):
                    require(q/f1+(1-q)/f0 <= 1,
                            "composite HIGH reciprocal multiplier")
                    _, rejected, _, _, inv = stopped_likelihood(
                        q, h, ell, upper, lower, horizon)
                    require(inv <= 1 and rejected <= lower,
                            "HIGH finite stopped-supermartingale rejection bound")
                    checked += 1
    return checked


def ordered_partitions(total: int, length: int, ceiling: int | None = None):
    if length == 0:
        if total == 0:
            yield ()
        return
    ceiling = total if ceiling is None else min(ceiling, total)
    for first in range(ceiling, -1, -1):
        if total-first > (length-1)*first:
            continue
        for rest in ordered_partitions(total-first, length-1, first):
            yield (first,)+rest


def pointer_gap_guards() -> tuple[int, int]:
    volume_maps = inequalities = 0
    for d in (3, 4, 5):
        for total in range(d, d+8):
            ordered = list(ordered_partitions(total, d))
            for k in (1, 2):
                source = {p for p in ordered if p[k-1]-p[k] >= 1}
                target = set(ordered_partitions(total-k, d))
                image = {tuple(v-int(i < k) for i, v in enumerate(p))
                         for p in source}
                require(image == target,
                        "subtract-from-top-k ordered-simplex bijection on rational grids")
                for p in target:
                    inverse = tuple(v+int(i < k) for i, v in enumerate(p))
                    require(inverse in source, "inverse volume-map support")
                volume_maps += len(source)+len(target)
    for d in range(3, 33):
        for numerator in range(1, 21):
            gamma = F(numerator, 100*d)
            union = 2-(1-gamma)**(d-1)-(1-2*gamma)**(d-1)
            require(0 <= union <= 3*(d-1)*gamma,
                    "exact top-two gap volume union and Bernoulli bound")
            eta = F(1, 100)
            chosen = eta/(3*d)
            failure = 2-(1-chosen)**(d-1)-(1-2*chosen)**(d-1)
            require(failure <= eta, "chosen pointer isolation confidence")
            inequalities += 1
    return volume_maps, inequalities


def five_use_code() -> tuple[int, F]:
    # X-basis labels make the physical repetition isometry exact. The full
    # decoding label map is bijective, so it defines a unitary before syndrome
    # disposal, and all logical coherences are checked explicitly.
    physical_labels = list(product((0, 1), repeat=5))
    images = set()
    for bits in physical_labels:
        syndrome = tuple(bits[i] ^ bits[0] for i in range(1, 5))
        relative = (0,)+syndrome
        majority = int(sum(relative) >= 3)
        images.add((bits[0] ^ majority, syndrome))
    require(len(images) == 32, "complete repetition decoding basis isometry")
    correct = F(0)
    matrix_units = 0
    total = F(0)
    for error in physical_labels:
        syndrome = tuple(error[i] ^ error[0] for i in range(1, 5))
        majority = int(sum((0,)+syndrome) >= 3)
        residual = error[0] ^ majority
        require(residual == int(sum(error) >= 3), "minimum-weight phase correction")
        weight = F(1, 4)**sum(error)*F(3, 4)**(5-sum(error))
        total += weight
        if residual == 0:
            correct += weight
        for a, b in product((0, 1), repeat=2):
            require(tuple((a ^ error[i]) ^ (a ^ error[0])
                          for i in range(1, 5)) == syndrome
                    and tuple((b ^ error[i]) ^ (b ^ error[0])
                              for i in range(1, 5)) == syndrome,
                    "syndrome is independent of both logical matrix-unit indices")
            require((a ^ error[0] ^ majority, b ^ error[0] ^ majority)
                    == (a ^ residual, b ^ residual),
                    "reference-complete corrected logical matrix unit")
            matrix_units += 1
    require(total == 1 and correct == F(459, 512), "complete CPTP five-use fidelity")
    theta = F(1, 4000)
    minimum = correct-20*theta
    threshold = (minimum+F(7, 8))/2
    half_gap = (minimum-F(7, 8))/2
    require(minimum > F(89, 100) > F(7, 8), "robust pointer/gate score margin")
    require(threshold-F(7, 8) == minimum-threshold == half_gap > 0,
            "validation separates target quality from constructed quality")
    require(20*theta == F(1, 200), "five-use conservative half-diamond ledger")
    require(F(1, 100)+F(1, 100)+2*F(1, 100)+F(1, 200) < F(1, 3),
            "explicit robust overall failure budget")
    return matrix_units, correct


def qstar(d: int) -> int:
    for _ in range(4):
        d = isqrt(d)
    return d//100


def verify() -> dict:
    address_records, address_families = address_ledgers()
    rounding = expected_cost_rounding()
    pools = native_pool_ledgers()
    sequential = sequential_noise_ledgers()
    volume_maps, gap_inequalities = pointer_gap_guards()
    matrix_units, fidelity = five_use_code()
    require(qstar(100**16-1) == 0 and qstar(100**16) == 1,
            "asymptotic C6 threshold is not a finite-device guarantee")
    require(qstar(2**106) == 0 and qstar(2**107) == 1,
            "qubit-dimension floor guard")
    return {
        "status": "passed",
        "optimistic_cap_records": address_records,
        "address_distribution_families": address_families,
        "expected_cost_rounding_cases": rounding,
        "native_pool_all_history_cases": pools,
        "sequential_noise_prefix_cases": sequential,
        "ordered_simplex_grid_points": volume_maps,
        "pointer_gap_inequality_cases": gap_inequalities,
        "five_use_logical_matrix_units": matrix_units,
        "five_use_bell_fidelity": str(fidelity),
        "scope": (
            "Finite exact probability/cap, native pool, likelihood-prefix, "
            "simplex-map and reference-complete repetition-code guards. "
            "C6, the all-size selection reduction, continuous simplex volume, "
            "concentration, spectral perturbation, synthesis/runtime and native "
            "physical interfaces remain analytic; no coherent-index or "
            "finite-architecture advantage is certified.")
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))


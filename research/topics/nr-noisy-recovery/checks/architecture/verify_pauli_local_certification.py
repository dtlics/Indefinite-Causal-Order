"""Finite exact guards for ordinary product-probe capacity certificates.

General concentration, entropy and capacity statements remain analytic.
No third-party dependencies, file writes or import-time output.
"""
from fractions import Fraction as F
from itertools import product
import json

if not __debug__:
    raise RuntimeError("Run local-certification guards without -O.")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def local_chi(a, b):
    return 1 if a == 0 or b == 0 or a == b else -1


def chi(a, b):
    result = 1
    for x, y in zip(a, b):
        result *= local_chi(x, y)
    return result


def detected_mask(a, axes):
    return sum((local_chi(x, k) == -1) << i
               for i, (x, k) in enumerate(zip(a, axes)))


def overlap(a, b):
    return sum(x != 0 and y != 0 for x, y in zip(a, b))


def law(size, indices):
    indices = list(indices)
    return [F(1, len(indices)) if i in indices else F(0) for i in range(size)]


def mean_variance(values):
    mean = sum((p * x for p, x in values), F(0))
    second = sum((p * x * x for p, x in values), F(0))
    return mean, second - mean * mean


def readout_law(ideal_a, ideal_b, ea, eb):
    n = len(ideal_a)
    for observed in product((0, 1), repeat=2 * n):
        probability = F(1)
        for i in range(n):
            probability *= ea if observed[i] != ideal_a[i] else 1 - ea
            probability *= eb if observed[n + i] != ideal_b[i] else 1 - eb
        yield probability, observed[:n], observed[n:]


def verify():
    conditional_pairs = identity_probes = correlated_laws = 0
    spam_cases = corrected_sum_cases = 0
    for n in (1, 2):
        labels = list(product(range(4), repeat=n))
        axes = list(product((1, 2, 3), repeat=n))
        masks = {a: [detected_mask(a, k) for k in axes] for a in labels}
        for a in labels:
            z = sum((F(-1, 2) ** m.bit_count() for m in masks[a]), F(0)) / len(axes)
            require(z == int(not any(a)), "FO individual identity-population estimator")
            identity_probes += 1
            for b in labels:
                pairs = [(x, y) for x in masks[a] for y in masks[b]]
                j = F(sum(bool(x & y) for x, y in pairs), len(pairs))
                t = F(sum((x & y).bit_count() for x, y in pairs), len(pairs))
                k = overlap(a, b)
                require(j == 1 - F(5, 9) ** k, "full conditional OR response")
                require(t == F(4, 9) * k and j <= t, "sum versus OR response")
                require(j >= F(4, 9) * int(chi(a, b) == -1),
                        "OR controls global anticommutation")
                conditional_pairs += 1
    for n in (2, 3):
        labels = list(product(range(4), repeat=n))
        size = len(labels)
        laws = [
            law(size, [0]), law(size, range(size)),
            law(size, [i for i, a in enumerate(labels) if all(x in (0, 3) for x in a)]),
            law(size, [0, size - 1]),
            [F(i + 1, size * (size + 1) // 2) for i in range(size)]
        ]
        for p in laws:
            require(sum(p) == 1, "normalized correlated law")
            eta = sum((pa * pb * chi(a, b)
                       for a, pa in zip(labels, p) for b, pb in zip(labels, p)), F(0))
            j = sum((pa * pb * (1 - F(5, 9) ** overlap(a, b))
                     for a, pa in zip(labels, p) for b, pb in zip(labels, p)), F(0))
            t = sum((pa * pb * F(4, 9) * overlap(a, b)
                     for a, pa in zip(labels, p) for b, pb in zip(labels, p)), F(0))
            w = [sum((pa for a, pa in zip(labels, p) if a[i]), F(0))
                 for i in range(n)]
            require(t == F(4, 9) * sum(x * x for x in w), "spatial dilution identity")
            require(eta >= 1 - F(9, 2) * j >= 1 - F(9, 2) * t,
                    "correlated-law sufficient certificates")
            z = sum((pa * int(not any(a)) for a, pa in zip(labels, p)), F(0))
            require(z == p[0], "correlated-law identity coefficient")
            correlated_laws += 1
    # Exact n32 sparse-event population calculation, using only its 97 supported labels.
    n = 32
    entries = [((-1, 0), F(19, 50))]
    entries += [((i, a), F(31, 50 * 3 * n))
                for i in range(n) for a in (1, 2, 3)]
    j = eta = F(0)
    for (i, a), pa in entries:
        for (k, b), pb in entries:
            same_site = i == k and i >= 0
            j += pa * pb * (F(4, 9) if same_site else 0)
            eta += pa * pb * (-1 if same_site and a != b else 1)
    lower = 1 - F(9, 2) * j
    require(lower == 1 - 2 * F(31, 50) ** 2 / n, "single-site OR population certificate")
    require(eta == 1 - F(4, 3) * F(31, 50) ** 2 / n, "single-site exact eta")
    root = F(31, 200)
    require(root * root == 1 - lower, "population square root")
    capacity = (F(19, 50) - root) * n - 1 - 3 * F(31, 50)
    require(capacity == F(217, 50), "4.34 population certificate")
    # Full readout trajectories check unbiased inverses, not just a copied formula.
    for n in (1, 2, 3):
        zero = (0,) * n
        for ea, eb in ((F(0), F(1, 10)), (F(1, 100), F(1, 10)),
                       (F(1, 10), F(1, 10))):
            ta = ea * (1 - ea) / (1 - 2 * ea) ** 2
            tb = eb * (1 - eb) / (1 - 2 * eb) ** 2
            observed_j, corrected_j, observed_z, corrected_z = [], [], [], []
            for probability, oa, ob in readout_law(zero, zero, ea, eb):
                u = [(x - ea) / (1 - 2 * ea) for x in oa]
                v = [(x - eb) / (1 - 2 * eb) for x in ob]
                complement = z = F(1)
                for x, y in zip(u, v):
                    complement *= 1 - x * y
                    z *= 1 - F(3, 2) * x
                observed_j.append((probability, int(any(x and y for x, y in zip(oa, ob)))))
                corrected_j.append((probability, 1 - complement))
                observed_z.append((probability, F(-1, 2) ** sum(oa)))
                corrected_z.append((probability, z))
            require(mean_variance(observed_j)[0] == 1 - (1 - ea * eb) ** n,
                    "identity-channel false-coincidence floor")
            mj, vj = mean_variance(corrected_j)
            require(mj == 0 and vj == (1 + ta * tb) ** n - 1,
                    "specific corrected-OR product variance")
            require(mean_variance(observed_z)[0] == (1 - F(3, 2) * ea) ** n,
                    "uncorrected identity-population SPAM bias")
            mz, vz = mean_variance(corrected_z)
            require(mz == 1 and vz == (1 + F(9, 4) * ta) ** n - 1,
                    "specific corrected-identity product variance")
            spam_cases += 1
    # Corrected additive overlap provides a polynomial, not exponential, alternative.
    n, ea, eb = 2, F(1, 100), F(1, 10)
    ta = ea * (1 - ea) / (1 - 2 * ea) ** 2
    tb = eb * (1 - eb) / (1 - 2 * eb) ** 2
    for ia in product((0, 1), repeat=n):
        for ib in product((0, 1), repeat=n):
            values = []
            for probability, oa, ob in readout_law(ia, ib, ea, eb):
                corrected = sum(((x - ea) * (y - eb)
                                 / ((1 - 2 * ea) * (1 - 2 * eb))
                                 for x, y in zip(oa, ob)), F(0))
                values.append((probability, corrected))
            mean, variance = mean_variance(values)
            require(mean == sum(x * y for x, y in zip(ia, ib)),
                    "corrected additive overlap mean")
            require(variance == ta * sum(ib) + tb * sum(ia) + n * ta * tb,
                    "conditional corrected-additive variance")
            corrected_sum_cases += 1
    require(1 - F(99, 100) ** 32 > F(2, 9),
            "fixed readout floor can make identity OR certificate nonpositive")
    return {
        "status": "passed", "conditional_error_pairs": conditional_pairs,
        "identity_probe_cases": identity_probes, "correlated_laws": correlated_laws,
        "full_spam_trajectory_cases": spam_cases,
        "corrected_additive_cases": corrected_sum_cases,
        "population_example": {"n": 32, "eta_lower": str(lower),
                               "capacity_lower_qubits": str(capacity),
                               "finite_sample_claim": False},
        "scope": ("Finite exact probe, correlated-law and readout-model guards; "
                  "general concentration/entropy/coding proofs remain analytic. "
                  "No optimal noisy-estimator or ordinary-query lower bound.")
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))

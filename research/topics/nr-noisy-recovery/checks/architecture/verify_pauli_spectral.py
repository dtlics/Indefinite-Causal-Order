"""Finite exact guards for NR-R06 spectral and dense-noise scalar bounds.

This does not implement or verify the external population-recovery
algorithm. Its list/error/query theorem remains a cited analytic input.
The finite lists below test the subsequent reconstruction argument.
"""

from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact Pauli-spectral checks without -O.")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def bracket(a, b, n):
    mask = (1 << n) - 1
    return (((a & mask) & (b >> n)).bit_count() + ((b & mask) & (a >> n)).bit_count()) & 1


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), F(0))


def transform(h, vector):
    return [dot(row, vector) for row in h]


def spike(h, label, amplitude):
    size = len(h)
    result = [(1 + amplitude * h[label][a]) / size for a in range(size)]
    require(sum(result) == 1 and min(result) >= 0, "valid spike law")
    return result


def clipped_list(q, theta, pattern):
    # Synthetic estimates satisfying the external theorem's hypotheses.
    chosen = {a for a, value in enumerate(q) if value > theta}
    cap = int(4 / theta)
    for a in range(len(q)):
        if len(chosen) >= cap:
            break
        if (a + pattern) % 3 == 0:
            chosen.add(a)
    raw = {a: q[a] + (theta if (a + pattern) % 2 else -theta) for a in chosen}
    clipped = [min(F(1), max(F(0), raw[a])) if a in chosen else F(0)
               for a in range(len(q))]
    require(len(chosen) <= 4 / theta, "finite list-size hypothesis")
    require(max(abs(clipped[a] - q[a]) for a in range(len(q))) <= theta,
            "coordinate error, including unlisted values")
    return chosen, clipped, any(raw[a] != clipped[a] for a in chosen)


def verify_pauli_spectral():
    h2_entries = reconstruction = spike_cases = dense_cases = clipped_cases = omitted_cases = 0
    unnormalized_cases = 0
    square_chi_cases = 0
    for n in (1, 2, 3):
        d, size = 1 << n, 1 << (2 * n)
        h = [[1 - 2 * bracket(a, b, n) for b in range(size)] for a in range(size)]
        for a in range(size):
            for b in range(size):
                require(sum(h[a][j] * h[j][b] for j in range(size)) == (size if a == b else 0), "H squared")
                h2_entries += 1
        uniform = [F(1, size)] * size
        dense = [F(2, 5), F(1, 4), F(1, 5)] + [F(3, 20 * (size - 3))] * (size - 3)
        point = [F(1)] + [F(0)] * (size - 1)
        other = [F(0), F(1)] + [F(0)] * (size - 2)
        auxiliary = (uniform, dense, point, other)
        sparse_fourier = [(1 + F(1, 4) * h[1][a] - F(1, 5) * h[2][a]
                           + F(1, 10) * h[3][a]) / size for a in range(size)]
        pair_law = [F(1, 2) if a in (0, 1) else F(0) for a in range(size)]
        for p in (sparse_fourier, pair_law):
            require(min(p) >= 0 and sum(p) == 1, "valid reconstruction Pauli law")
            eigenvalues = transform(h, p)
            mass = sum(abs(value) for value in eigenvalues[1:])
            for q in auxiliary:
                eta = dot(q, eigenvalues)
                for theta in (F(1, 10), F(1, 5) / (4 * (mass + 1))):
                    alpha = F(1, 50)
                    for pattern in range(3):
                        listed, qhat, clipped = clipped_list(q, theta, pattern)
                        clipped_cases += int(clipped)
                        omitted_cases += int(len(listed) < size)
                        unnormalized_cases += int(sum(qhat) != 1)
                        nonidentity = listed - {0}
                        list_mass = sum((qhat[b] for b in nonidentity), F(0))
                        require(list_mass <= 1 + len(nonidentity) * theta <= 5, "unnormalized list mass")
                        nu = {b: min(F(1), max(F(-1), eigenvalues[b] + (-1 if b % 2 else 1) * alpha))
                              for b in nonidentity}
                        require(all(abs(nu[b] - eigenvalues[b]) <= alpha for b in nonidentity), "probe error hypothesis")
                        eta_hat = qhat[0] + sum((qhat[b] * nu[b] for b in nonidentity), F(0))
                        coordinate_part = dot([qhat[b] - q[b] for b in range(size)], eigenvalues)
                        probe_part = sum((qhat[b] * (nu[b] - eigenvalues[b]) for b in nonidentity), F(0))
                        require(eta_hat - eta == coordinate_part + probe_part, "NL7 exact error decomposition")
                        require(abs(coordinate_part) <= (mass + 1) * theta, "spectral mass coordinate bound")
                        require(abs(probe_part) <= list_mass * alpha <= 5 * alpha, "weighted probe bound")
                        require(abs(eta_hat - eta) <= (mass + 1) * theta + 5 * alpha, "NL7 full bound")
                        reconstruction += 1
        for label in range(1, min(size, 5)):
            for amplitude in (F(-1, 2), F(1, 2), F(1)):
                p = spike(h, label, amplitude)
                eigenvalues = transform(h, p)
                require(eigenvalues == [F(1) if b == 0 else amplitude if b == label else F(0)
                                       for b in range(size)], "spike Fourier support")
                for q in auxiliary:
                    require(dot(q, eigenvalues) == q[0] + amplitude * q[label], "spike with arbitrary auxiliary law")
                    spike_cases += 1
        for p in auxiliary:
            for q in auxiliary:
                hp, hq = transform(h, p), transform(h, q)
                eta = dot(p, hq)
                r, s = [value - uniform[0] for value in p], [value - uniform[0] for value in q]
                cp, cq = size * dot(r, r), size * dot(s, s)
                cross = dot(r, transform(h, s))
                require(eta == p[0] + q[0] - F(1, size) + cross, "chi-square decomposition")
                require(eta * eta <= size * dot(p, p) * dot(q, q), "collision norm signal bound")
                require(r[0]**2 <= cp / size and s[0]**2 <= cq / size, "chi-square coordinate bounds")
                require(cross * cross <= cp * cq / size, "chi-square cross bound")
                dense_cases += 1
        # Perfect-square chi-square divergences check the combined bound without radicals.
        for beta in (F(-1, 2), F(1, 3)):
            for gamma in (F(-1, 4), F(2, 3)):
                p, q = spike(h, 1, beta), spike(h, 2, gamma)
                r, s = [x - uniform[0] for x in p], [x - uniform[0] for x in q]
                require(size * dot(r, r) == beta * beta and size * dot(s, s) == gamma * gamma,
                        "specified chi-square divergences")
                eta = dot(p, transform(h, q))
                require(abs(eta) <= F(1, size) + (abs(beta) + abs(gamma) + abs(beta * gamma)) / d,
                        "combined NL12 bound")
                square_chi_cases += 1
    require(clipped_cases > 0 and omitted_cases > 0 and unnormalized_cases > 0,
            "nontrivial clipping, omission and unnormalized-list coverage")
    return {
        "status": "passed", "arithmetic": "exact Fraction and binary symplectic characters",
        "data_qubits": [1, 2, 3], "h_squared_entries": h2_entries,
        "spectral_mass_reconstruction_cases": reconstruction,
        "clipped_list_cases": clipped_cases, "omitted_list_cases": omitted_cases,
        "unnormalized_list_cases": unnormalized_cases,
        "spike_auxiliary_cases": spike_cases, "dense_norm_decomposition_cases": dense_cases,
        "combined_chi_square_cases": square_chi_cases,
        "scope": (
            "Finite character, synthetic-list reconstruction, spike and norm guards. "
            "No implementation or verification of external population recovery; its theorem, "
            "all-n sampling/runtime proofs and physical assumptions remain analytic dependencies."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(verify_pauli_spectral(), sort_keys=True))

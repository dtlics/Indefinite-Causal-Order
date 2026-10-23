"""Exact NR-R06 guards for the one-sided Bell/Pauli-check eta estimator.

Pauli operators are represented by their exact monomial action and powers
of i, not numerical matrices. The all-n access and sampling proofs remain
analytic in architecture-baselines.md.
"""

from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run exact Pauli-statistic memory checks without -O.")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


ROOTS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def action(a, x, n):
    mask = (1 << n) - 1
    ax, az = a & mask, a >> n
    phase = ((ax & az).bit_count() + 2 * (az & x).bit_count()) % 4
    return x ^ ax, phase


def bracket(a, b, n):
    mask = (1 << n) - 1
    return (((a & mask) & (b >> n)).bit_count() + ((b & mask) & (a >> n)).bit_count()) & 1


def product_eigenvector(b, n):
    # Unnormalized product eigenvector: |0> on I/Z, |+> on X, |+i> on Y.
    result = {}
    for x in range(1 << n):
        phase = 0
        possible = True
        for j in range(n):
            bx, bz, bit = (b >> j) & 1, (b >> (n + j)) & 1, (x >> j) & 1
            if not bx and bit:
                possible = False
                break
            if bx and bz and bit:
                phase += 1
        if possible:
            result[x] = phase % 4
    return result


def pure_expectation(vector, a, n):
    real = imag = 0
    for x, phase in vector.items():
        dest, added = action(a, x, n)
        if dest in vector:
            value = ROOTS[(phase + added - vector[dest]) % 4]
            real += value[0]
            imag += value[1]
    return F(real, len(vector)), F(imag, len(vector))


def law(size, offset):
    weights = [1 + ((j * j + offset * j + offset) % 7) for j in range(size)]
    total = sum(weights)
    return [F(w, total) for w in weights]


def spectrum(probabilities, characters):
    return [sum((p * sign for p, sign in zip(probabilities, row)), F(0)) for row in characters]


def convolve(p, q):
    size = len(p)
    return [sum((p[b] * q[b ^ x] for b in range(size)), F(0)) for x in range(size)]


def verify_pauli_statistic_memory():
    bell_pairs = pcs_columns = product_probes = mixtures = global_noise_cases = spike_cases = 0
    for n in (1, 2, 3):
        d, size = 1 << n, 1 << (2 * n)
        characters = [[1 - 2 * bracket(a, b, n) for b in range(size)] for a in range(size)]
        for a in range(size):
            for b in range(size):
                real = imag = 0
                for x in range(d):
                    dest_a, phase_a = action(a, x, n)
                    dest_b, phase_b = action(b, x, n)
                    if dest_a == dest_b:
                        value = ROOTS[(phase_b - phase_a) % 4]
                        real += value[0]
                        imag += value[1]
                    # Complete operator columns of C(P_b) P_a C(P_b).
                    for control in (0, 1):
                        z, exponent = x, 0
                        if control:
                            z, increment = action(b, z, n)
                            exponent += increment
                        z, increment = action(a, z, n)
                        exponent += increment
                        if control:
                            z, increment = action(b, z, n)
                            exponent += increment
                        expected_z, expected_phase = action(a, x, n)
                        expected_phase += 2 * control * bracket(a, b, n)
                        require((z, exponent % 4) == (expected_z, expected_phase % 4), "PCS full operator identity")
                        pcs_columns += 1
                require((real, imag) == ((d if a == b else 0), 0), "Bell-label orthogonality")
                bell_pairs += 1
                vector = product_eigenvector(b, n)
                require(pure_expectation(vector, b, n) == (F(1), F(0)), "known product eigenvector")
                errored = {}
                for x, exponent in vector.items():
                    dest, increment = action(a, x, n)
                    errored[dest] = (exponent + increment) % 4
                require(pure_expectation(errored, b, n) == (F(characters[a][b]), F(0)), "product-probe error character")
                product_probes += 1
        for offset in (1, 3):
            p, q = law(size, offset), law(size, offset + 1)
            lambda_p, lambda_q = spectrum(p, characters), spectrum(q, characters)
            eta = sum((p[a] * lambda_q[a] for a in range(size)), F(0))
            hybrid = sum((q[b] * lambda_p[b] for b in range(size)), F(0))
            require(hybrid == eta, "one-sided hybrid mean")
            require(sum(lambda_p, F(0)) / size == p[0], "uniform Pauli-check p0")
            mixtures += 1
            for f in (F(1, 5), F(3, 4), F(1)):
                reference = [F(1 - f, size) for _ in range(size)]
                reference[0] += f
                lambda_reference = spectrum(reference, characters)
                require(lambda_reference == [F(1)] + [f] * (size - 1), "global reference spectrum")
                noisy_q = convolve(q, reference)
                observed = sum((noisy_q[b] * lambda_p[b] for b in range(size)), F(0))
                character_sum = sum((p[a] * lambda_q[a] * lambda_reference[a] for a in range(size)), F(0))
                require(observed == character_sum == f * eta + (1 - f) * p[0], "global noise affine correction")
                require((observed - (1 - f) * p[0]) / f == eta, "exact calibrated recovery")
                global_noise_cases += 1
        for amplitude in (F(1, 2), F(1)):
            a = 1
            spike = [(1 + amplitude * characters[a][b]) / size for b in range(size)]
            eigenvalues = spectrum(spike, characters)
            expected = [F(1) if b == 0 else amplitude if b == a else F(0) for b in range(size)]
            require(eigenvalues == expected, "hidden spike spectrum")
            spike_eta = sum((spike[b] * eigenvalues[b] for b in range(size)), F(0))
            require(spike_eta == (1 + amplitude)**2 / size, "shrinking spike self-switch mean")
            if amplitude == 1:
                require((spike_eta - F(1, size)) / 2 == F(3, 2 * size), "unit-spike control-only gap")
            spike_cases += 1

    # At n=2 local depolarization attenuates weight one and two differently.
    n, f = 2, F(1, 2)
    size = 1 << (2 * n)
    characters = [[1 - 2 * bracket(a, b, n) for b in range(size)] for a in range(size)]
    single = [(1 + 3 * f) / 4] + [(1 - f) / 4] * 3
    reference = []
    for a in range(size):
        local = []
        for j in range(n):
            local.append(((a >> j) & 1) + 2 * ((a >> (n + j)) & 1))
        reference.append(single[local[0]] * single[local[1]])
    lambda_reference = spectrum(reference, characters)
    x1, x1x2, z1 = 1, 3, 1 << n
    require(characters[x1][z1] == characters[x1x2][z1] == -1, "matched true eta")
    require(lambda_reference[x1] == f and lambda_reference[x1x2] == f * f, "local weight counterexample")
    observed_pair = (-lambda_reference[x1], -lambda_reference[x1x2])
    require(observed_pair == (F(-1, 2), F(-1, 4)), "distinct observed equal-eta means")

    # Correlated B/reference faults can erase the label even with known marginals.
    a, labels = 1, (0, 2)  # At n=1: A=X, B uniform I/Z.
    true_eta = sum((F(1, 2) * (1 - 2 * bracket(a, b, 1)) for b in labels), F(0))
    independent_observed = sum((F(1, 4) * (1 - 2 * bracket(a, b ^ e, 1))
                                for b in labels for e in labels), F(0))
    correlated_observed = sum((F(1, 2) * (1 - 2 * bracket(a, b ^ b, 1))
                               for b in labels), F(0))
    require(true_eta == independent_observed == 0 and correlated_observed != 0, "independence counterexample")
    return {
        "status": "passed", "arithmetic": "exact Pauli phase and Fraction mixtures",
        "data_qubits": [1, 2, 3], "bell_orthogonality_pairs": bell_pairs,
        "reference_complete_pcs_operator_columns": pcs_columns,
        "product_eigenstate_probes": product_probes,
        "hybrid_mixture_cases": mixtures, "global_reference_noise_cases": global_noise_cases,
        "hidden_spike_control_mean_cases": spike_cases,
        "local_reference_equal_eta_observed_means": [str(x) for x in observed_pair],
        "correlated_reference_counterexample": True,
        "scope": (
            "Finite full Pauli operator/Bell-label identities, exact mixture character sums and "
            "calibrated global-noise correction. All-n sampling, physical noise factorization, "
            "gate/memory cost and literature tradeoffs remain analytic; no eta lower bound or native advantage."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(verify_pauli_statistic_memory(), sort_keys=True))

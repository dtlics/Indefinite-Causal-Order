"""Finite exact replay for NR-R06 calibrated faults, bosonic compilers and passive probes.

Only the Python standard library is used. Gaussian-rational matrices verify
complete process bases, Bell decoding of correlated labels, and equality of
the full normalized control-target Choi matrices. No report files are written.
Bosonic matrix-unit coefficients and Weyl phases are also checked exactly.
The general trajectory, infinite-dimensional and physical-access arguments
remain analytic inputs.
"""

from fractions import Fraction as F
from itertools import product, permutations
from math import factorial
import json


if not __debug__:
    raise RuntimeError("Exact fault-simulation checks require Python without -O.")


ZERO = (F(0), F(0))
ONE = (F(1), F(0))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def gaussian(real=0, imag=0):
    return (F(real), F(imag))


def add(a, b):
    if a == ZERO:
        return b
    if b == ZERO:
        return a
    return (a[0] + b[0], a[1] + b[1])


def multiply(a, b):
    if a == ZERO or b == ZERO:
        return ZERO
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def conjugate(a):
    return (a[0], -a[1])


def times(a, scalar):
    return (a[0] * scalar, a[1] * scalar)


def zeros(rows, cols):
    return [[ZERO for _ in range(cols)] for _ in range(rows)]


def identity(d):
    out = zeros(d, d)
    for i in range(d):
        out[i][i] = ONE
    return out


def adjoint(a):
    return [[conjugate(a[j][i]) for j in range(len(a))]
            for i in range(len(a[0]))]


def matmul(a, b):
    require(len(a[0]) == len(b), "Matrix dimensions disagree.")
    out = zeros(len(a), len(b[0]))
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if x == ZERO:
                continue
            for j, y in enumerate(b[k]):
                if y != ZERO:
                    out[i][j] = add(out[i][j], multiply(x, y))
    return out


def tensor(a, b):
    return [[multiply(a[i][j], b[k][ell])
             for j in range(len(a[0])) for ell in range(len(b[0]))]
            for i in range(len(a)) for k in range(len(b))]


def diagonal_blocks(a, b):
    d = len(a)
    require(len(b) == d, "Control branches have different dimensions.")
    out = zeros(2 * d, 2 * d)
    for i, j in product(range(d), repeat=2):
        out[i][j] = a[i][j]
        out[d + i][d + j] = b[i][j]
    return out


def vectorize(a):
    # Column-major vec: row index is output + input * output_dimension.
    return [a[i][j] for j in range(len(a[0])) for i in range(len(a))]


def inner(a, b):
    out = ZERO
    for x, y in zip(a, b):
        out = add(out, multiply(conjugate(x), y))
    return out


def add_outer(out, vector, weight):
    occupied = [(i, x) for i, x in enumerate(vector) if x != ZERO]
    for i, x in occupied:
        for j, y in occupied:
            out[i][j] = add(out[i][j], times(multiply(x, conjugate(y)), weight))


def pauli_basis(n):
    i = identity(2)
    x = [[ZERO, ONE], [ONE, ZERO]]
    y = [[ZERO, gaussian(0, -1)], [gaussian(0, 1), ZERO]]
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    out = []
    for word in product((i, x, y, z), repeat=n):
        matrix = [[ONE]]
        for factor in word:
            matrix = tensor(matrix, factor)
        out.append(matrix)
    return out


def rational_rotation(pauli, numerator, imaginary_numerator, denominator):
    # (a I - i b P)/c with a^2+b^2=c^2; no square roots are introduced.
    d = len(pauli)
    out = zeros(d, d)
    for i, j in product(range(d), repeat=2):
        out[i][j] = multiply(gaussian(0, F(-imaginary_numerator, denominator)),
                             pauli[i][j])
        if i == j:
            out[i][j] = add(out[i][j], gaussian(F(numerator, denominator)))
    require(matmul(adjoint(out), out) == identity(d), "Calibration is not unitary.")
    return out


def non_clifford_check(unitary, probe, paulis):
    image = vectorize(matmul(matmul(unitary, probe), adjoint(unitary)))
    d = len(unitary)
    coefficients = [times(inner(vectorize(p), image), F(1, d)) for p in paulis]
    require(all(c[1] == 0 for c in coefficients), "Hermitian Pauli coefficient is nonreal.")
    nonzero = [c[0] for c in coefficients if c != ZERO]
    require(len(nonzero) == 2 and sum(c * c for c in nonzero) == 1,
            "Chosen calibration did not give the intended non-Clifford witness.")
    return [str(c) for c in nonzero]


def process_basis(gates):
    d = len(gates[0])
    require(len(gates) == d * d, "Example is not a complete process basis.")
    require(all(matmul(adjoint(gate), gate) == identity(d) for gate in gates),
            "An orthogonal fault operation is not unitary.")
    vectors = [vectorize(gate) for gate in gates]
    gram = [[times(inner(a, b), F(1, d)) for b in vectors] for a in vectors]
    require(gram == identity(d * d), "Normalized process states are not orthogonal.")
    resolution = zeros(d * d, d * d)
    for vector in vectors:
        add_outer(resolution, vector, F(1, d))
    require(resolution == identity(d * d), "Process projectors do not resolve identity.")
    # Squared overlaps are the actual Bell/process-state measurement kernel.
    return [[z[0] * z[0] + z[1] * z[1] for z in row] for row in gram]


def correlated_law(labels, support, diagonal_only=False):
    p = [[F(0) for _ in range(labels)] for _ in range(labels)]
    if diagonal_only:
        for a, index in enumerate(support):
            p[index][index] = F(a + 1, 10)
    else:
        for a, index_a in enumerate(support):
            for b, index_b in enumerate(support):
                p[index_a][index_b] = F((a + 1) * (4 - b) + (a + 1) * (a == b), 110)
    require(sum(map(sum, p)) == 1, "Fault law is not normalized.")
    a, b = support[:2]
    minor = p[a][a] * p[b][b] - p[a][b] * p[b][a]
    require(minor != 0, "Fault law accidentally factorizes.")
    return p, minor


def decode_joint_labels(p, kernel_e, kernel_f):
    labels = len(p)
    occupied = [(a, b, p[a][b]) for a, b in product(range(labels), repeat=2) if p[a][b]]
    out = [[F(0) for _ in range(labels)] for _ in range(labels)]
    for a, b in product(range(labels), repeat=2):
        out[a][b] = sum(weight * kernel_e[a][i] * kernel_f[b][j]
                        for i, j, weight in occupied)
    require(out == p, "Bell measurement did not reproduce the correlated joint law.")
    return out


def direct_switch_choi(es, fs, p):
    d = len(es[0])
    out = zeros((2 * d) ** 2, (2 * d) ** 2)
    for a, b in product(range(len(es)), range(len(fs))):
        if p[a][b]:
            # Direct definition: the two coherent order blocks are FE and EF.
            w = diagonal_blocks(matmul(fs[b], es[a]), matmul(es[a], fs[b]))
            add_outer(out, vectorize(w), p[a][b] / (2 * d))
    return out


def ordinary_simulator_choi(es, fs, decoded):
    d = len(es[0])
    n = 2 * d
    out = zeros(n * n, n * n)
    for a, b in product(range(len(es)), range(len(fs))):
        if not decoded[a][b]:
            continue
        # Known feedforward is two controlled gates after decoding. Construct
        # it independently of the direct FE/EF block formula above.
        first = diagonal_blocks(es[a], fs[b])
        second = diagonal_blocks(fs[b], es[a])
        w = matmul(second, first)
        weight = decoded[a][b] / n
        # Evaluate every input matrix unit |i><j|; this includes arbitrary
        # control coherence and arbitrary reference-entangled input states.
        for i, j in product(range(n), repeat=2):
            for row in range(n):
                if w[row][i] == ZERO:
                    continue
                for col in range(n):
                    if w[col][j] != ZERO:
                        r, s = row + n * i, col + n * j
                        value = multiply(w[row][i], conjugate(w[col][j]))
                        out[r][s] = add(out[r][s], times(value, weight))
    return out


def check_choi(choi, d):
    n = 2 * d
    require(choi == adjoint(choi), "Full Choi matrix is not Hermitian.")
    marginal = [[ZERO for _ in range(n)] for _ in range(n)]
    for i, j in product(range(n), repeat=2):
        for output in range(n):
            marginal[i][j] = add(marginal[i][j], choi[output + n * i][output + n * j])
    expected = [[times(x, F(1, n)) for x in row] for row in identity(n)]
    require(marginal == expected, "Output partial trace is not I/(2d).")
    # Explicitly retain coherence between the two order blocks. A fixed |+>
    # slice, a scalar acceptance check, or a classical order mixture is not
    # the object checked here.
    order_zero = [row + n * col for row, col in product(range(d), repeat=2)]
    order_one = [d + row + n * (d + col) for row, col in product(range(d), repeat=2)]
    coherent_entries = sum(choi[i][j] != ZERO for i in order_zero for j in order_one)
    require(coherent_entries > 0, "Example failed to test cross-order Choi coherence.")
    return coherent_entries


def example(n, diagonal_only=False):
    d = 2 ** n
    paulis = pauli_basis(n)
    if n == 1:
        generator_u, generator_v, probe_u, probe_v = 1, 3, 3, 1
        support = [0, 1, 2, 3]
    else:
        # Genuine two-qubit calibrated entanglers and spatial Pauli faults.
        generator_u, generator_v, probe_u, probe_v = 5, 13, 12, 4  # XX, ZX, ZI, XI
        support = [0, 5, 11, 12]  # II, XX, YZ, ZI
    u = rational_rotation(paulis[generator_u], 3, 4, 5)
    v = rational_rotation(paulis[generator_v], 5, 12, 13)
    witnesses = [non_clifford_check(u, paulis[probe_u], paulis),
                 non_clifford_check(v, paulis[probe_v], paulis)]
    es = [matmul(p, u) for p in paulis]
    fs = [matmul(p, v) for p in paulis]
    kernel_e, kernel_f = process_basis(es), process_basis(fs)
    p, minor = correlated_law(len(paulis), support, diagonal_only)
    decoded = decode_joint_labels(p, kernel_e, kernel_f)
    direct = direct_switch_choi(es, fs, p)
    ordinary = ordinary_simulator_choi(es, fs, decoded)
    require(direct == ordinary, "Full switched-output and ordinary Choi matrices differ.")
    coherence = check_choi(direct, d)
    return {
        "data_dimension": d,
        "control_target_input_dimension": 2 * d,
        "complete_process_basis_size_per_module": d * d,
        "process_gram_entries_checked": 2 * d ** 4,
        "correlated_label_law": "weighted equal labels" if diagonal_only else "asymmetric nonproduct rational law",
        "nonproduct_minor": str(minor),
        "nonzero_joint_label_pairs": sum(weight != 0 for row in p for weight in row),
        "calibration_non_clifford_pauli_coefficients": witnesses,
        "full_choi_shape": [(2 * d) ** 2, (2 * d) ** 2],
        "full_choi_entries_compared": (2 * d) ** 4,
        "input_matrix_units_checked": (2 * d) ** 2,
        "nonzero_cross_order_choi_entries": coherence,
        "normalized_choi_output_partial_trace": "I/(2d)",
        "exact_full_choi_residual": "0",
    }


def bosonic_falling(n,k):
    return F(factorial(n),factorial(n-k)) if n>=k else F(0)


def bosonic_loss_checks(x,y,cutoff=6):
    eta1,eta2=x*x,y*y; tau=eta1*eta2; z=(x+y)/(1+x*y)
    assert 0<=z<=1
    def weight(eta,k):return (1-eta)**k/factorial(k)
    def history(n,l,m,order):
        q=l+m
        if n<q:return F(0)
        if order==0:
            return bosonic_falling(n,l)*x**(n-l)*bosonic_falling(n-l,m)*y**(n-q)
        return bosonic_falling(n,m)*y**(n-m)*bosonic_falling(n-m,l)*x**(n-q)
    checked=0
    for a,b,n,m,q in product(range(2),range(2),range(cutoff+1),
                           range(cutoff+1),range(cutoff+1)):
        actual=sum(weight(eta1,l)*weight(eta2,q-l)*
                   history(n,l,q-l,a)*history(m,l,q-l,b)
                   for l in range(q+1))
        expected=F(0)
        if min(n,m)>=q:
            expected=weight(tau,q)*bosonic_falling(n,q)*bosonic_falling(m,q)*(x*y)**(n+m-2*q)
            if a!=b:expected*=z**q
        assert actual==expected,(x,y,a,b,n,m,q,actual,expected)
        checked+=1
    return checked


def bosonic_amplifier_checks(s,t,cutoff=4,max_added=8):
    # s=sqrt(G1),t=sqrt(G2); raising an unnormalized Fock ket has no factorial.
    g1,g2=s*s,t*t; total=g1*g2; z=(s+t)/(1+s*t)
    assert 0<=z<=1
    def weight(g,k):return (g-1)**k/(g**(k+1)*factorial(k))
    def history(n,l,m,order):
        return s**(-n)*t**(-n-l) if order==0 else t**(-n)*s**(-n-m)
    checked=0
    for a,b,n,m,q in product(range(2),range(2),range(cutoff+1),
                           range(cutoff+1),range(max_added+1)):
        actual=sum(weight(g1,l)*weight(g2,q-l)*
                   history(n,l,q-l,a)*history(m,l,q-l,b)
                   for l in range(q+1))
        expected=weight(total,q)*(s*t)**(-n-m)
        if a!=b:expected*=z**q
        assert actual==expected,(s,t,a,b,n,m,q,actual,expected)
        checked+=1
    return checked


def bosonic_power(a,n):
    out=(F(1),F(0))
    for _ in range(n):out=multiply(out,a)
    return out


def bosonic_phase_matrix_unit_checks():
    checked=0
    for u in [(F(3,5),F(4,5)),(F(5,13),F(12,13)),(F(0),F(1))]:
        assert multiply(u,conjugate(u))==(1,0)
        for a,b,n,m,q in product(range(2),range(2),range(8),range(8),range(8)):
            if q>min(n,m):continue
            # Controlled pre/post rotation on the ket and bra separately.
            ket=multiply(bosonic_power(u,n*a),conjugate(bosonic_power(u,(n-q)*a)))
            bra=multiply(bosonic_power(u,m*b),conjugate(bosonic_power(u,(m-q)*b)))
            actual=multiply(ket,conjugate(bra))
            expected=multiply(bosonic_power(u,q*a),conjugate(bosonic_power(u,q*b)))
            assert actual==expected
            checked+=1
    return checked


def bosonic_symplectic(a,b):return a[1]*b[0]-a[0]*b[1]
def bosonic_weyl_product(a,b):
    # (real alpha, imag alpha, central phase), with exact formal phases.
    return(a[0]+b[0],a[1]+b[1],a[2]+b[2]+bosonic_symplectic(a,b))


def bosonic_gaussian_checks():
    checked=0
    for va,vb in [(F(1,3),F(2,5)),(F(7,11),F(3,13)),(F(1),F(1))]:
        v=va+vb;c=va/v;w=va*vb/v
        # delta=alpha-c*(alpha+beta) is independent of gamma for Gaussians:
        # exact zero cross covariance, with each quadrature variance w/2.
        assert (1-c)*va/2-c*vb/2==0
        assert (1-c)**2*va/2+c*c*vb/2==w/2
        for gamma,zeta in product([(F(1),F(0),F(0)),(F(0),F(1),F(0)),
                                   (F(2,3),F(-4,5),F(0))],repeat=2):
            neg=(-zeta[0],-zeta[1],F(0))
            actual=bosonic_weyl_product(bosonic_weyl_product(neg,gamma),zeta)
            assert actual[:2]==gamma[:2]
            assert actual[2]==2*bosonic_symplectic(gamma,zeta)
            alpha=(c*gamma[0]+zeta[0],c*gamma[1]+zeta[1],F(0))
            beta=(gamma[0]-alpha[0],gamma[1]-alpha[1],F(0))
            forward=bosonic_weyl_product(beta,alpha);reverse=bosonic_weyl_product(alpha,beta)
            assert forward[:2]==reverse[:2]==gamma[:2]
            assert forward[2]==-reverse[2]==bosonic_symplectic(gamma,zeta)
            for a,b in product(range(2),repeat=2):
                # Coefficient of each control matrix unit; the common
                # target map Ad_D(gamma) is identical on both sides.
                # Sign of the centered Gaussian linear form is immaterial.
                phases=[forward[2],reverse[2]]
                assert phases[a]-phases[b]==-(a-b)*actual[2]
                # Independently compute the two linear forms' variances:
                # switch residual=(1-c)alpha-c beta, helper=sampled zeta.
                switch_cov=((a-b)*2)**2*((1-c)**2*va/2+c*c*vb/2)
                helper_cov=((a-b)*2)**2*w/2
                assert switch_cov==helper_cov
                exponent=-switch_cov*(gamma[0]**2+gamma[1]**2)/2
                assert exponent==-(a-b)**2*w*(gamma[0]**2+gamma[1]**2)
                checked+=1
    return checked


def bosonic_compiler_checks():
    losses = sum(bosonic_loss_checks(x, y) for x, y in
                 [(F(4, 5), F(1, 2)), (F(0), F(3, 5)), (F(1), F(4, 5)),
                  (F(0), F(0)), (F(1), F(1))])
    amplifiers = sum(bosonic_amplifier_checks(s, t) for s, t in
                     [(F(5, 4), F(3, 2)), (F(1), F(7, 5)), (F(1), F(1))])
    phases = bosonic_phase_matrix_unit_checks()
    gaussian_coefficients = bosonic_gaussian_checks()
    return {
        "full_control_fock_matrix_unit_loss_coefficients": losses,
        "full_control_fock_matrix_unit_amplifier_coefficients": amplifiers,
        "controlled_number_phase_matrix_unit_checks": phases,
        "weyl_and_gaussian_control_coefficients": gaussian_coefficients,
        "scope": ("Exact finite coefficients on unnormalized Fock matrix units, including loss "
                  "endpoints and all four control blocks. Weyl phases and Gaussian conditional "
                  "quadratic coefficients are exact. All-Fock binomial sums, Poisson-kernel "
                  "Fourier moments, continuous Gaussian conditioning/integration and native "
                  "implementation costs remain analytic; no truncated displacement-operator "
                  "approximation or unknown-parameter Fisher-information simulation is asserted."),
    }


def passive_trace(a):
    out = ZERO
    for i in range(len(a)):
        out = add(out, a[i][i])
    return out


def passive_channel(ks, rho):
    out = zeros(len(rho), len(rho))
    for weight, k in ks:
        term = matmul(matmul(k, rho), adjoint(k))
        for i, j in product(range(len(rho)), repeat=2):
            out[i][j] = add(out[i][j], times(term[i][j], weight))
    return out


def passive_choi(ks):
    d = len(ks[0][1])
    out = zeros(d*d, d*d)
    for weight, k in ks:
        add_outer(out, vectorize(k), weight/d)
    return out


def passive_reordering_checks():
    # The four-particle seed vectors are rational: (|01>+|10>)^tensor2/2.
    seed_vectors = [{(0, 0, 0, 0): F(1)},
                    {word: F(1, 2) for word in product(range(2), repeat=4)
                     if word[0] != word[1] and word[2] != word[3]}]
    for vector, expected in zip(seed_vectors, [F(1), F(2, 3)]):
        actual = sum(amplitude*vector.get(tuple(word[p] for p in perm), F(0))
                     for perm in permutations(range(4))
                     for word, amplitude in vector.items())/24
        require(actual == expected, "Four-particle seed symmetrizer weight failed.")
    for m in range(2, 65):
        d = m*(m+1)//2
        d4 = F(m*(m+1)*(m+2)*(m+3), 24)
        d22 = F(m*m*(m*m-1), 12)
        kappa = F(2*(m+1), m*m+m+2)
        a, b = 2*kappa-1, 2*(1-kappa)
        s = abs(a)+abs(b)
        require(d4+d22 == F(d*(d+1), 2) and a+b == 1,
                "Passive sector dimensions/normalization failed.")
        require(a+F(2, 3)*b == 2*d4/(d*(d+1)),
                "Signed seed weights do not match the Haar second moment.")
        require((1+F(1, d))*s <= 3 and (1+F(1, d))*s+1 <= 4,
                "Dimension-independent estimator coefficient bound failed.")
        if m >= 4:
            require((1+F(1, d))*s == 3-F(4*m+1, d),
                    "Exact signed variance conversion identity failed.")

    # An explicit qutrit projective 2-design, evaluated as density matrices,
    # checks the Haar trace contraction without a simulated Haar integral.
    d = 3
    probes = []
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        for phase in [ONE, gaussian(-1), gaussian(0, 1), gaussian(0, -1)]:
            rho = zeros(d, d)
            rho[i][i] = rho[j][j] = gaussian(F(1, 2))
            rho[i][j], rho[j][i] = times(conjugate(phase), F(1, 2)), times(phase, F(1, 2))
            probes.append(rho)
    a = [[gaussian(F(3, 5)), gaussian(F(-4, 5)), ZERO],
         [gaussian(F(4, 5)), gaussian(F(3, 5)), ZERO], [ZERO, ZERO, ONE]]
    b = [[ONE, ZERO, ZERO], [ZERO, gaussian(F(5, 13)), gaussian(F(-12, 13))],
         [ZERO, gaussian(F(12, 13)), gaussian(F(5, 13))]]
    ba, ab = matmul(b, a), matmul(a, b)
    projection = [[ONE, ZERO, ZERO], [ZERO, ONE, ZERO], [ZERO, ZERO, ZERO]]
    cases = [([(F(1), ba)], [(F(1), ab)]),
             ([(F(1, 3), identity(d)), (F(2, 3), a)],
              [(F(1, 4), identity(d)), (F(3, 4), b)]),
             ([(F(1, 2), projection), (F(1, 5), a)], [(F(2, 3), b)])]
    for index, (left, right) in enumerate(cases):
        same = sum(passive_trace(matmul(passive_channel(left, rho),
                                        passive_channel(right, rho)))[0]
                   for rho in probes)/len(probes)
        hilbert_schmidt, choi_formula = F(0), F(0)
        for (wl, l), (wr, r) in product(left, right):
            w = matmul(adjoint(l), r)
            tw = passive_trace(w)
            hilbert_schmidt += wl*wr*passive_trace(matmul(w, adjoint(w)))[0]
            choi_formula += wl*wr*(tw[0]**2+tw[1]**2)
        require(same == (hilbert_schmidt+choi_formula)/(d*(d+1)),
                "Explicit two-copy design disagrees with the Haar trace identity.")
        mixed = [[times(value, F(1, d)) for value in row] for row in identity(d)]
        independent = passive_trace(matmul(passive_channel(left, mixed),
                                           passive_channel(right, mixed)))[0]
        overlap = passive_trace(matmul(passive_choi(left), passive_choi(right)))[0]
        require(independent == hilbert_schmidt/(d*d)
                and (1+F(1, d))*same-independent == overlap == choi_formula/(d*d),
                "Launch-normalized CP Choi-overlap subtraction failed.")
        if index == 0:
            require(((d+1)*same-1)/d == overlap,
                    "Unitary reordering-fidelity conversion failed.")
        if index == 2:
            require(passive_trace(passive_choi(left))[0] < 1,
                    "Trace-decreasing example accidentally became trace preserving.")

    # The noisy-channel comparison and switch visibility are different targets.
    i2, x, _, z = pauli_basis(1)
    ea, eb = [(F(1, 2), i2), (F(1, 2), z)], [(F(1, 2), i2), (F(1, 2), x)]
    forward = [(wa*wb, matmul(bj, ai)) for (wa, ai), (wb, bj) in product(ea, eb)]
    reverse = [(wa*wb, matmul(ai, bj)) for (wa, ai), (wb, bj) in product(ea, eb)]
    jf, jr = passive_choi(forward), passive_choi(reverse)
    visibility = sum(wa*wb*passive_trace(matmul(adjoint(matmul(bj, ai)),
                                               matmul(ai, bj)))[0]/2
                     for (wa, ai), (wb, bj) in product(ea, eb))
    require(jf == jr and passive_trace(matmul(jf, jr))[0] == F(1, 4)
            and visibility == F(1, 2), "Noisy target-statistic distinction failed.")
    return {"four_particle_seed_weights": 2, "mode_coefficient_cases": 63,
            "explicit_qutrit_second_design_states": len(probes),
            "unitary_tp_and_trace_decreasing_channel_pairs": len(cases),
            "noisy_statistic_counterexamples": 1,
            "scope": "Exact finite seed symmetrizer, dimension/coefficient, explicit qutrit second-design, CP Choi-overlap and target-statistic identities. Representation decomposition, Haar twirling, all-mode variance proof and physical source/SWAP/routing costs remain analytic; no approximate finite passive design or hardware certificate."}


def main():
    from verify_cat_reservoir_parity import verify_cat_reservoir_parity
    from verify_cat_physical_interface import verify_cat_physical_interface
    from verify_pauli_statistic_memory import verify_pauli_statistic_memory
    from verify_local_overlap import verify_local_overlap
    from verify_lindblad_statistic import verify_lindblad_statistic
    from verify_pauli_spectral import verify_pauli_spectral
    from verify_pauli_cross_pair import verify_pauli_cross_pair
    from gaussian_readout_guards import verify_gaussian_readout_guards
    from verify_su11_ports import verify_su11_full_ports
    from verify_conditional_readout import (
        verify_known_gaussian_control, verify_conditional_noise_readout,
    )
    examples = [example(1), example(1, diagonal_only=True), example(2)]
    print(json.dumps({
        "status": "passed",
        "result": "NR-R06",
        "arithmetic": "Python standard-library Gaussian rationals; no floating point",
        "examples": examples,
        "bosonic_compilers": bosonic_compiler_checks(),
        "cat_reservoir_parity": verify_cat_reservoir_parity(),
        "cat_physical_interface": verify_cat_physical_interface(),
        "pauli_statistic_memory": verify_pauli_statistic_memory(),
        "local_overlap": verify_local_overlap(),
        "lindblad_statistic": verify_lindblad_statistic(),
        "pauli_spectral": verify_pauli_spectral(),
        "pauli_cross_pair": verify_pauli_cross_pair(),
        "passive_reordering": passive_reordering_checks(),
        "gaussian_readout_noise_floor": verify_gaussian_readout_guards(),
        "su11_complete_ports": verify_su11_full_ports(),
        "known_gaussian_control": verify_known_gaussian_control(),
        "conditional_noise_readout": verify_conditional_noise_readout(),
        "scope": ("Finite exact d=2,4 algebra replay of known orthogonal-unitary process bases, "
                  "correlated Bell-label decoding, and the full coherent switched-output ordinary simulation. "
                  "Persistent-trajectory induction, matched physical fault laws, noiseless memory, allowed "
                  "known-control synthesis and hardware costs remain assumptions/analytic proof inputs. "
                  "The separately scoped bosonic coefficient and passive-reordering checks are reported above; "
                  "no general quantum-memory or input-dependent-noise simulation is asserted."),
    }, indent=2))


if __name__ == "__main__":
    main()

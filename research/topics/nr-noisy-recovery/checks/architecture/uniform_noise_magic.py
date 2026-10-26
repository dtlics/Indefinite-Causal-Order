"""Exact NR-R17 H/S magic-source ingredient; no discovery or optimization.

Gaussian rational matrices reconstruct the SWITCH, physical decoder and
matched ordinary CS histories. Triaffinity extends the eight-vertex moment
identities to every declared visibility. Distillation and stabilizer closure
have analytic proofs in the canonical owner; finite replay is not a device
threshold or a priority certificate.
"""
from fractions import Fraction as F
from itertools import product
import json

if not __debug__:
    raise RuntimeError('Exact checks reject -O execution.')


def q(real=0, imag=0):
    return F(real), F(imag)


def add(z, w):
    return z[0]+w[0], z[1]+w[1]


def mul(z, w):
    return z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0]


def conj(z):
    return z[0], -z[1]


def total(values):
    answer = q()
    for value in values:
        answer = add(answer, value)
    return answer


def mm(a, b):
    return [[total(mul(a[i][k], b[k][j]) for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def scale(a, factor):
    return [[mul(z, q(factor)) for z in row] for row in a]


def adj(a):
    return [[conj(z) for z in col] for col in zip(*a)]


def tensor(a, b):
    return [[mul(z, w) for z in rowa for w in rowb]
            for rowa in a for rowb in b]


def diagonal(values):
    return [[q(value if i == j else 0) for j in range(len(values))]
            for i, value in enumerate(values)]


def outer(v):
    return [[mul(z, conj(w)) for w in v] for z in v]


def tracep(p, rho):
    value = total(mul(p[i][j], rho[j][i])
                  for i, j in product(range(len(p)), repeat=2))
    assert value[1] == 0
    return value[0]


I = diagonal([1, 1])
X = [[q(), q(1)], [q(1), q()]]
Y = [[q(), q(0, -1)], [q(0, 1), q()]]
Z = diagonal([1, -1])
H0 = [[q(1), q(1)], [q(1), q(-1)]]
S = [[q(1), q()], [q(), q(0, 1)]]
SD = adj(S)
CNOT = [[q(value) for value in row] for row in
        [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]]]
CZ = diagonal([1, 1, 1, -1])
PAULIS = {a+b: tensor(p, r)
          for (a, p), (b, r) in
          product(zip('IXYZ', (I, X, Y, Z)), repeat=2)}
D0 = mm(tensor(H0, I), mm(CNOT, tensor(I, SD)))


def verify():
    joint, decoded, histories = 0, 0, 0
    # A_e and B_f have their exact sqrt(2) normalization deferred to rho.
    vecs = {}
    for e, f in product((0, 1), repeat=2):
        a = mm((I, Z)[e], H0)
        b = mm((I, Z)[f], S)
        vecs[e, f] = [total(row) for row in mm(b, a)] + [total(row) for row in mm(a, b)]
    for alpha, beta, gamma in product((F(0), F(1)), repeat=3):
        rho = [[q() for _ in range(4)] for _ in range(4)]
        for e, f in product((0, 1), repeat=2):
            raw = outer(vecs[e, f])
            weight = (1+(-1)**e*alpha)*(1+(-1)**f*beta)/32
            for i, j in product(range(4), repeat=2):
                coherence = gamma if i//2 != j//2 else 1
                rho[i][j] = add(rho[i][j], mul(raw[i][j], q(weight*coherence)))
        assert tracep(PAULIS['II'], rho) == 1 and rho == adj(rho)
        expected = {
            'II': 1, 'IX': 0, 'IY': -alpha*beta/2, 'IZ': F(1, 2),
            'XI': gamma/2, 'XX': gamma*alpha/2, 'XY': -gamma*alpha*beta/2,
            'XZ': gamma/2, 'YI': gamma*beta/2, 'YX': -gamma*alpha*beta/2,
            'YY': -gamma*alpha/2, 'YZ': gamma*beta/2,
            'ZI': 0, 'ZX': 0, 'ZY': alpha*beta/2, 'ZZ': F(1, 2),
        }
        for label, pauli in PAULIS.items():
            assert tracep(pauli, rho) == expected[label], (alpha, beta, gamma, label)
            joint += 1
        decoded_rho = scale(mm(D0, mm(rho, adj(D0))), F(1, 2))
        accepted = [[mul(decoded_rho[i+2][j+2], q((-1)**(i+j)))
                     for j in range(2)] for i in range(2)]
        expected_out = ((2+gamma*alpha*beta)/4, (gamma+alpha*beta)/4,
                        gamma*beta/4, (1+gamma*alpha*beta)/4)
        for pauli, value in zip((I, X, Y, Z), expected_out):
            assert tracep(pauli, accepted) == value
            decoded += 1
        p, nx, ny, nz = expected_out
        x = (nx+nz)/(2*p)
        assert x == (1+gamma)*(1+alpha*beta)/(2*(2+gamma*alpha*beta))
        assert x-F(1, 2) == (gamma+alpha*beta-1)/(2*(2+gamma*alpha*beta))

    # Both vectors below omit a common denominator 2. H0 cancels the
    # source's sqrt(2) denominator with the final H normalization.
    cs = [[q(1)], [q(1)], [q(1)], [q(0, 1)]]
    for e, f, g in product((0, 1), repeat=3):
        native_vec = [[mul(z, q((-1)**(g*(i//2))))]
                      for i, z in enumerate(vecs[e, f])]
        native_after_h = scale(mm(tensor(I, H0), native_vec), F(1, 2))
        ordinary = mm(tensor((I, Z)[g], I),
                      mm(CNOT if e else PAULIS['II'],
                         mm(CZ if f else PAULIS['II'], cs)))
        assert native_after_h == ordinary
        histories += 1

    # A symbolic Pauli-action coefficient check uses h=nu/sqrt(2):
    # the random Clifford weights are 1/2,h,1/2-h. Both transverse
    # components equal h and I,Z stay fixed for the entire interval.
    for pauli, target in ((X, [[q(0), q(1, -1)], [q(1, 1), q(0)]]),
                          (Y, [[q(0), q(-1, -1)], [q(-1, 1), q(0)]])):
        const = [[add(a, b) for a, b in zip(rowa, rowb)]
                 for rowa, rowb in zip(scale(pauli, F(1, 2)),
                                       scale(mm(Z, mm(pauli, Z)), F(1, 2)))]
        slope = [[add(a, mul(b, q(-1))) for a, b in zip(rowa, rowb)]
                 for rowa, rowb in zip(mm(S, mm(pauli, SD)), mm(Z, mm(pauli, Z)))]
        assert const == scale(I, 0) and slope == target
    for pauli in (I, Z):
        assert mm(S, mm(pauli, SD)) == mm(Z, mm(pauli, Z)) == pauli

    nu = F(2, 3)
    p = (2+nu**3)/4
    assert p == F(31, 54) and 1/p == F(54, 31)
    assert ((nu+nu**2)/(4*p), nu**2/(4*p), (1+nu**3)/(4*p)) == (F(15, 31), F(6, 31), F(35, 62))
    assert (1+nu)*(1+nu**2)/(2*(2+nu**3)) == F(65, 124)
    assert nu+nu**2 > 1 and nu**2 < F(1, 2)
    # Exact witness e<.13 and the worst endpoint of the analytic F15 sign proof.
    assert F(2)-(F(37*124, 50*65))**2 > 0
    upper_w = F(1369, 2500)+F(2500, 1369)
    assert upper_w**3+upper_w**2-2*upper_w-16 < 0
    assert 4*F(1, 2)*1*(1-2*F(3, 5)**2)*(1-F(3, 5)**2)/(1+14*F(3, 5)**4) == F(224, 1759)
    assert (1+14*F(1, 2)**4)/64 == F(15, 512)
    return {'joint_pauli_moments': joint, 'decoded_branch_moments': decoded,
            'matched_CS_histories': histories, 'visibility_vertices': 8,
            'witness_acceptance': str(p), 'witness_H_coordinate': '65/124',
            'ordinary_mixture': 'symbolic exact Pauli action',
            'arithmetic': 'Gaussian rational fractions',
            'scope': 'Fixed atomic-source identities and exact entry arithmetic; general stabilizer closure, distillation, processor/interface premises and novelty remain analytic.'}


if __name__ == '__main__':
    print(json.dumps({'status': 'passed', **verify()}, indent=2))

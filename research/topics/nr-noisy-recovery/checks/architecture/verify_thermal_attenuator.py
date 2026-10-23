"""Exact finite-bath and polynomial checks; no Fock-cutoff certificate.

The infinite-dimensional Gaussian integral, QND access and faithful-output
density argument are analytic inputs, not experimentally fitted conclusions.
"""

from fractions import Fraction as F
from itertools import product
import json


if not __debug__:
    raise RuntimeError("Exact partial-thermal checks require Python without -O.")


def _verify_contacts_and_polynomials():
    zero, one = (F(0), F(0)), (F(1), F(0))

    def require(test, message):
        if not test:
            raise RuntimeError(message)

    def add(a, b):
        return (a[0] + b[0], a[1] + b[1])

    def mul(a, b):
        return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0])

    def conj(a):
        return (a[0], -a[1])

    def scale(a, s):
        return (a[0]*s, a[1]*s)

    def accumulate(out, key, value):
        value = add(out.get(key, zero), value)
        if value != zero:
            out[key] = value
        else:
            out.pop(key, None)

    def contact(vector, port, c, s):
        out = {}
        for key, amp in vector.items():
            swapped = list(key)
            swapped[1], swapped[port] = swapped[port], swapped[1]
            accumulate(out, key, scale(amp, c))
            accumulate(out, tuple(swapped), mul(amp, (F(0), s)))
        return out

    def qswap(vector):
        out = {}
        for (control, target, e1, e2), amp in vector.items():
            key = ((control, target, e2, e1) if control
                   else (control, target, e1, e2))
            accumulate(out, key, amp)
        return out

    columns = choi_entries = 0
    for dim in (2, 3):
        weights = [F(i + 1, dim*(dim + 1)//2) for i in range(dim)]
        require(sum(weights) == 1, "Bath normalization failed.")
        for c, s in ((F(1), F(0)), (F(0), F(1)),
                     (F(3, 5), F(4, 5)), (F(5, 13), F(12, 13))):
            require(c*c + s*s == 1, "Contact is not unitary.")
            for control, target, e1, e2 in product(range(2), range(dim), range(dim), range(dim)):
                initial = {(control, target, e1, e2): one}
                compiled = qswap(contact(contact(qswap(initial), 2, c, s), 3, c, s))
                first, second = ((2, 3) if control == 0 else (3, 2))
                expected = contact(contact(initial, first, c, s), second, c, s)
                require(compiled == expected, "Full controlled bath-exchange identity failed.")
                columns += 1

            size = dim*dim
            serial = [[zero for _ in range(size)] for _ in range(size)]
            cross = [[zero for _ in range(size)] for _ in range(size)]
            minus = [[zero for _ in range(size)] for _ in range(size)]

            def reduce_outer(out, left, right, weight):
                # Here key[0] stores the inert reference, not a helper.
                for (r, a, e1, e2), xamp in left.items():
                    for (q, b, f1, f2), yamp in right.items():
                        if (e1, e2) == (f1, f2):
                            row, col = a*dim + r, b*dim + q
                            out[row][col] = add(out[row][col],
                                               scale(mul(xamp, conj(yamp)), weight))

            for e1, e2 in product(range(dim), repeat=2):
                initial = {(r, r, e1, e2): one for r in range(dim)}
                forward = contact(contact(initial, 2, c, s), 3, c, s)
                reverse = contact(contact(initial, 3, c, s), 2, c, s)
                difference = dict(forward)
                for key, value in reverse.items():
                    accumulate(difference, key, scale(value, -1))
                weight = weights[e1]*weights[e2]/dim
                reduce_outer(serial, forward, forward, weight)
                reduce_outer(cross, forward, reverse, weight)
                reduce_outer(minus, difference, difference, weight/4)
            for a, r, b, q in product(range(dim), repeat=4):
                reset = weights[a]/dim if a == b and r == q else F(0)
                sandwich = weights[a]*weights[b]/dim if a == r and b == q else F(0)
                gap = reset - sandwich
                row, col = a*dim+r, b*dim+q
                require(minus[row][col] == (s**4*gap/2, F(0)),
                        "Minus full-reference Choi identity failed.")
                expected_cross = add(serial[row][col], (-s**4*gap, F(0)))
                require(cross[row][col] == expected_cross,
                        "Off-diagonal full-reference Choi identity failed.")
                choi_entries += 1

    # Exact multivariate polynomial arithmetic in x,b,z.
    def pconst(value):
        return {} if value == 0 else {(0, 0, 0): F(value)}

    def padd(*terms):
        out = {}
        for term in terms:
            for key, value in term.items():
                out[key] = out.get(key, F(0)) + value
        return {key: value for key, value in out.items() if value}

    def pscale(poly, scalar):
        return {key: value*scalar for key, value in poly.items() if value*scalar}

    def pmul(*terms):
        out = pconst(1)
        for term in terms:
            nxt = {}
            for key, value in out.items():
                for key2, value2 in term.items():
                    key3 = tuple(a+b for a, b in zip(key, key2))
                    nxt[key3] = nxt.get(key3, F(0)) + value*value2
            out = {key: value for key, value in nxt.items() if value}
        return out

    def ppow(poly, n):
        return pmul(*([poly]*n))

    onep = pconst(1)
    x, b, z = ({(1, 0, 0): F(1)}, {(0, 1, 0): F(1)}, {(0, 0, 1): F(1)})
    omx = padd(onep, pscale(x, -1))
    h = padd(onep, ppow(x, 2))
    t = padd(onep, pmul(h, b))
    opb = padd(onep, b)
    d = padd(ppow(opb, 2), pscale(pmul(b, x), -2))
    diagonal = padd(opb, pscale(pmul(b, x, z), -1))
    determinant = padd(ppow(diagonal, 2),
                       pmul(ppow(b, 2), z, padd(pscale(x, 2), pscale(pmul(z, ppow(x, 2)), -1))))
    require(determinant == padd(ppow(opb, 2), pscale(pmul(b, x, z), -2)),
            "Thermal vacuum generating determinant failed.")
    require(padd(ppow(opb, 2), pscale(t, -1)) ==
            pmul(b, padd(onep, pscale(ppow(x, 2), -1), b)),
            "Initial probability-ratio polynomial failed.")
    require(padd(pmul(h, ppow(opb, 2)), pscale(pmul(x, t), -2)) ==
            padd(ppow(omx, 2), pscale(pmul(b, h, omx), 2), pmul(ppow(b, 2), h)),
            "Successive probability-ratio polynomial failed.")
    numerator = padd(pmul(padd(d, pconst(-1)), ppow(t, 2), ppow(opb, 4)),
                     pscale(pmul(h, b, d, ppow(opb, 4)), -2),
                     pscale(pmul(b, x, d, ppow(t, 2)), 4))
    c2_bracket = padd(pconst(3), pscale(x, 8), pscale(ppow(x, 2), -4),
                      pscale(ppow(x, 3), 6), pscale(ppow(x, 4), -1))
    cs = [pscale(pmul(x, omx), 2),
          padd(onep, pscale(pmul(x, ppow(omx, 2)), 8)),
          pscale(pmul(omx, c2_bracket), 2),
          padd(pconst(15), pscale(ppow(x, 2), 2), pscale(ppow(x, 3), 8),
               pscale(ppow(x, 4), -7), pscale(ppow(x, 6), -8)),
          padd(pconst(4), pscale(x, -2), pscale(ppow(x, 2), -2),
               pmul(padd(pconst(16), pscale(x, -8)), ppow(h, 2))),
          padd(onep, pmul(padd(pconst(14), pscale(x, -8)), ppow(h, 2))),
          pmul(padd(pconst(6), pscale(x, -2)), ppow(h, 2)), ppow(h, 2)]
    expansion = padd(*(pmul(coeff, ppow(b, j+1)) for j, coeff in enumerate(cs)))
    require(numerator == expansion, "Fock-one minus-fidelity coefficient expansion failed.")
    # The two less immediate coefficient bounds have explicit nonnegative forms.
    require(padd(c2_bracket, pscale(padd(pconst(3), pscale(x, 4), pscale(ppow(x, 3), 5)), -1)) ==
            pmul(omx, padd(pscale(x, 4), ppow(x, 3))), "C2 lower bound failed.")
    require(padd(cs[3], pscale(padd(pconst(15), pscale(ppow(x, 2), -5)), -1)) ==
            padd(pscale(pmul(ppow(x, 2), padd(onep, pscale(ppow(x, 2), -1))), 7),
                 pscale(pmul(ppow(x, 3), padd(onep, pscale(ppow(x, 3), -1))), 8)),
            "C3 lower bound failed.")
    return {"status": "passed", "full_joint_columns": columns,
            "full_reference_choi_entries": choi_entries,
            "vacuum_polynomial_identities": 6,
            "scope": "Finite-bath exact identities and analytic-polynomial coefficients; no finite-Fock physical fit."}


def _matrix_unit_boundary_guards():
    """Check the annihilation algebra, not a truncated thermal channel."""
    def require(test, message):
        if not test:
            raise RuntimeError(message)

    def branch_vector(target_dim, code_dim, a, b):
        # A=|a0><a1|, B=|b0><b1|, unnormalized embedded Bell input.
        out = [F(0)] * (2 * target_dim * code_dim)
        if b[1] == a[0] and a[1] < code_dim:
            out[b[0] * code_dim + a[1]] += 1
        if a[1] == b[0] and b[1] < code_dim:
            out[target_dim * code_dim + a[0] * code_dim + b[1]] += 1
        return out

    def rank(vectors):
        basis = {}
        for values in vectors:
            values = list(values)
            for pivot, row in sorted(basis.items()):
                if values[pivot]:
                    coefficient = values[pivot]
                    values = [a - coefficient*b for a, b in zip(values, row)]
            pivot = next((j for j, value in enumerate(values) if value), None)
            if pivot is not None:
                coefficient = values[pivot]
                basis[pivot] = [value/coefficient for value in values]
        return len(basis)

    guarded_ranks = []
    universal_kernel_contractions = 0
    for target_dim in (2, 3, 4):
        units = list(product(range(target_dim), repeat=2))
        for code_dim in (target_dim - 1, target_dim):
            vectors = [branch_vector(target_dim, code_dim, a, b)
                       for a, b in product(units, repeat=2)]
            actual_rank = rank(vectors)
            expected_rank = 2*target_dim*code_dim - (code_dim == target_dim)
            require(actual_rank == expected_rank,
                    'Matrix-unit support rank disagrees with the boundary algebra.')
            guarded_ranks.append([target_dim, code_dim, actual_rank])
            if code_dim == target_dim:
                # The finite-dimensional |minus> tensor Bell kernel must remain.
                for vector in vectors:
                    contraction = sum(vector[j*code_dim+j] -
                                      vector[target_dim*code_dim+j*code_dim+j]
                                      for j in range(code_dim))
                    require(contraction == 0, 'Finite-D trace-commutator kernel lost.')
                    universal_kernel_contractions += 1
            else:
                # An unused physical output direction breaks that compressed trace.
                p, k = 0, code_dim
                vector = branch_vector(target_dim, code_dim, (k, p), (p, k))
                contraction = sum(vector[j*code_dim+j] -
                                  vector[target_dim*code_dim+j*code_dim+j]
                                  for j in range(code_dim))
                require(contraction == 1, 'Unused-direction counterexample failed.')
    return guarded_ranks, universal_kernel_contractions


def _vacuum_retained_flag_guards():
    def require(test, message):
        if not test:
            raise RuntimeError(message)

    number_blocks = modulo_records = 0
    for x, b in product((F(0), F(1, 3), F(3, 5), F(4, 5)),
                        (F(1, 10), F(1, 2), F(2))):
        m = (1+x*x)*b
        r = m/(1+m)
        d = (1+b)**2 - 2*b*x
        helper_overlap = 1/d
        cross_ratio = 2*b*x/(1+b)**2
        p_plus, p_minus = (1+helper_overlap)/2, (1-helper_overlap)/2
        require(p_plus+p_minus == 1 and p_minus > 0,
                'Complete flag probabilities failed.')
        serial_sum = cross_sum = F(0)
        for k in range(13):
            probability = m**k/(1+m)**(k+1)
            cross = (2*b*x)**k/(1+b)**(2*k+2)
            require(0 <= cross <= probability, 'Source ratio is not physical.')
            a_plus = (1+cross/probability)/2
            a_minus = (1-cross/probability)/2
            # Number-controlled preparation followed by helper X dephasing.
            computational_diagonal = probability*(a_plus+a_minus)/2
            computational_cross = probability*(a_plus-a_minus)/2
            require(computational_diagonal == probability/2 and
                    computational_cross == cross/2,
                    'Retained helper state does not equal the switch output.')
            require(probability*a_plus == (probability+cross)/2 and
                    probability*a_minus == (probability-cross)/2,
                    'Accepted/rejected target blocks disagree.')
            serial_sum += probability
            cross_sum += cross
            number_blocks += 1
        require(serial_sum+r**13 == 1, 'Exact serial tail identity failed.')
        require(cross_sum+helper_overlap*cross_ratio**13 == helper_overlap,
                'Exact cross-map tail identity failed.')
        p_one = m/(1+m)**2
        j_one = 2*b*x/(1+b)**4
        for sign in (-1, 1):
            require((p_one+sign*j_one)/2 <= p_one,
                    'Raw single-photon yield comparison failed.')
        for bits in (1, 2, 3, 4):
            modulus = 2**bits
            accepted = p_one/(1-r**modulus)
            fidelity = 1-r**modulus
            require(accepted*fidelity == p_one,
                    'Modulo predicate joint photon probability failed.')
            # Closed geometric tail after finitely many accepted aliases.
            aliases = sum((1-r)*r**(1+modulus*j) for j in range(6))
            require(aliases+accepted*r**(6*modulus) == accepted,
                    'Modulo instrument alias tail failed.')
            modulo_records += 1
    return number_blocks, modulo_records


def verify():
    result = _verify_contacts_and_polynomials()
    ranks, kernels = _matrix_unit_boundary_guards()
    number_blocks, modulo_records = _vacuum_retained_flag_guards()
    result.update(matrix_unit_boundary_ranks=ranks,
                  finite_dimension_kernel_contractions=kernels,
                  retained_source_number_blocks=number_blocks,
                  modulo_source_records=modulo_records,
                  scope=('Exact finite-bath/Choi, polynomial, retained-source and '
                         'matrix-unit boundary checks. Infinite-oscillator '
                         'faithfulness, bounded strong density, Gaussian integration, '
                         'infinite tails and native access are analytic or measured inputs.'))
    return result


if __name__ == '__main__':
    print(json.dumps(verify(), sort_keys=True))




"""Exact ordinary Raman witnesses and balanced-cavity polynomial identities.

Canonical proofs and physical limits are in communication.md, NR-R11.
No solver, discovery dependency or measured hardware model is used.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from verify_fault_simulation import (
    ZERO, ONE, gaussian, add, multiply, conjugate, times, zeros, identity,
    adjoint, matmul,
)

if not __debug__:
    raise RuntimeError("Exact Raman checks require assertions; do not use -O.")

def scale(matrix, scalar):
    return [[times(value, scalar) for value in row] for row in matrix]

def raman_local_ancilla_examples():
    """Ordinary flat-Lambda Bell generation with one local ancilla per node.

    Exact state/instrument identities; physical Q-preserving ports and
    clean local preparation/filter/decode costs remain assumptions.
    """
    def norm2(values):
        total = ZERO
        for value in values:
            total = add(total, multiply(value, conjugate(value)))
        assert total[1] == 0
        return total[0]

    def bit(value, site):
        return (value >> (5-site)) & 1

    def scatter(vector, site, beta):
        answer = [F(0)]*64
        for index, value in enumerate(vector):
            if bit(index, 0) == bit(index, site):
                target = index
            else:
                target = index ^ (1 << 5) ^ (1 << (5-site))
            answer[index] += (1-beta)*value
            answer[target] += beta*value
        return answer

    # Unnormalized Bell basis; Gram=2I. Physical source/bra normalizations
    # multiply to 1/4 in the final four-qubit branch, avoiding sqrt(2).
    e = ([ONE, ZERO, ZERO, ONE],
         [ZERO, ONE, ONE, ZERO],
         [ZERO, gaussian(0, -1), gaussian(0, 1), ZERO],
         [ONE, ZERO, ZERO, gaussian(-1)])
    for i, j in product(range(4), repeat=2):
        value = ZERO
        for x, y in zip(e[i], e[j]):
            value = add(value, multiply(conjugate(x), y))
        assert value == gaussian(2 if i == j else 0)

    source = [F(0)]*64
    # Six-qubit order P,Q,a,a',b,b'; each of the three pairs is local.
    for p, aa, bb in product(range(2), repeat=3):
        source[48*p+12*aa+3*bb] = F(1)
    betas = (F(0), F(1, 10), F(3, 10), F(1, 2), F(7, 10),
             F(4, 5), F(5, 6), F(9, 10), F(19, 20), F(45, 46), F(1))
    branch_units = filter_effect_cases = 0
    records = []
    for beta in betas:
        t = 1-beta
        a, b, c = (2-beta)**2/4, beta**2/4, beta*(2-beta)/4
        q = 1-beta+beta*beta
        state = scatter(scatter(source, 2, beta), 4, beta)
        assert sum(value*value for value in state)/8 == q*q
        branches = []
        for m, n in product(range(2), repeat=2):
            raw = [F(0)]*16
            for p, matter in product(range(2), range(16)):
                raw[matter] += F((-1)**(n*p), 4)*state[32*p+16*(p ^ m)+matter]
            # Corrected a output uses Z^n X^m, as in teleportation.
            actual = [ZERO]*16
            for aa, ap, bb, bp in product(range(2), repeat=4):
                input_index = 8*aa+4*ap+2*bb+bp
                out_a = aa ^ m
                output_index = 8*out_a+4*ap+2*bb+bp
                actual[output_index] = gaussian((-1)**(n*out_a)*raw[input_index])
            mu = 0 if (m, n) == (0, 0) else (3 if m == 0 else (1 if n == 0 else 2))
            coefficients = ([a, b, b, b] if mu == 0 else
                            [c if k in (0, mu) else b for k in range(4)])
            expected = [ZERO]*16
            for k, row, col in product(range(4), repeat=3):
                expected[4*row+col] = add(expected[4*row+col],
                    times(multiply(e[k][row], e[k][col]), coefficients[k]/2))
            assert actual == expected
            weight = norm2(actual)
            assert weight == sum(value*value for value in coefficients)
            for i, j in product(range(16), repeat=2):
                assert multiply(actual[i], conjugate(actual[j])) == multiply(
                    expected[i], conjugate(expected[j]))
                branch_units += 1
            branches.append(weight)
        assert sum(branches) == q*q
        # Explicit I-branch edge-filter POVM on its Schmidt basis.
        lam = [a*a, b*b, b*b, b*b]
        edges = {}
        if a*a >= 3*b*b:
            for j in range(1, 4):
                edges[(0, j)] = b*b
        else:
            for j in range(1, 4):
                edges[(0, j)] = a*a/3
            for i in range(1, 4):
                for j in range(i+1, 4):
                    edges[(i, j)] = (b*b-a*a/3)/2
        degree = [F(0)]*4
        for (i, j), weight in edges.items():
            assert weight >= 0
            degree[i] += weight
            degree[j] += weight
            # The local diagonal effect has entries w/lambda at i,j;
            # the output Schmidt weights are both w, so it is a Bell.
            for vertex in (i, j):
                if lam[vertex]:
                    effect = weight/lam[vertex]
                    assert 0 <= effect <= 1 and lam[vertex]*effect == weight
                else:
                    assert weight == 0
            filter_effect_cases += 1
        assert all(0 <= degree[k] <= lam[k] for k in range(4))
        failure = sum(lam)-sum(degree)
        assert failure == max(F(0), a*a-3*b*b)
        if a*a <= 3*b*b:
            assert degree == lam
        first_flag_yield = 2*sum(edges.values())
        assert first_flag_yield == min(a*a+3*b*b, 6*b*b)
        # Other three flags factor into a Bell and a two-level junk pair.
        other_yield = 6*(c*c+b*b)
        ordinary = first_flag_yield+other_yield
        low = F(3, 8)*beta*beta*(4-4*beta+3*beta*beta)
        assert ordinary == min(q*q, low)
        switched = beta*beta*(1+t*t)
        assert low-switched == beta*beta*(beta*beta+4*beta-4)/8
        assert q*q-switched == t*t
        assert ordinary+failure+(1-q*q) == 1
        records.append({'beta': str(beta), 'ordinary_Bell_yield': str(ordinary),
                        'switch_Bell_yield': str(switched),
                        'ordinary_minus_switch': str(ordinary-switched),
                        'local_filter_failure': str(failure),
                        'rejected_photon_loss': str(1-q*q)})
    return {'local_ancilla_beta_cases': len(betas),
            'six_qubit_Bell_branch_CP_coefficients': branch_units,
            'local_edge_filter_effect_cases': filter_effect_cases,
            'records': records,
            'scope': ('Achievable ordinary flat symmetric Raman Bell generation '
                      'with a photonic Bell helper and one pre-entangled local '
                      'stationary ancilla at each node. Exact branch and filter '
                      'identities do not assert an ordinary optimum or a native '
                      'rate advantage after local preparation/decoding costs.')}


def raman_uniform_ancilla_examples():
    """Fixed local projections remove unknown I/single-SWAP amplitudes."""
    def norm2(values):
        total = ZERO
        for value in values:
            total = add(total, multiply(value, conjugate(value)))
        assert total[1] == 0
        return total[0]

    def plus(*values):
        total = ZERO
        for value in values:
            total = add(total, value)
        return total

    def scatter(vector, site, a, b):
        answer = [ZERO]*64
        for index, value in enumerate(vector):
            target = index
            if ((index >> 5) & 1) != ((index >> (5-site)) & 1):
                target ^= (1 << 5) ^ (1 << (5-site))
            answer[index] = add(answer[index], multiply(a, value))
            answer[target] = add(answer[target], multiply(b, value))
        return answer

    e = ([ONE, ZERO, ZERO, ONE], [ZERO, ONE, ONE, ZERO],
         [ZERO, gaussian(0, -1), gaussian(0, 1), ZERO],
         [ONE, ZERO, ZERO, gaussian(-1)])
    source = [ZERO]*64
    for p, a, b in product(range(2), repeat=3):
        source[48*p+12*a+3*b] = ONE
    nodes = ((gaussian(F(3, 10), F(2, 5)), gaussian(F(3, 10), F(-1, 5))),
             (gaussian(0, F(1, 4)), gaussian(F(1, 2))),
             (gaussian(F(1, 2), F(3, 10)), gaussian(F(1, 5), F(-2, 5))),
             (gaussian(F(1, 10)), gaussian(F(9, 10))),
             (ONE, ZERO), (ZERO, ONE))
    coefficient_units = projection_cases = 0
    records = []
    for a_a, b_a in nodes:
        for a_b, b_b in nodes:
            # Necessary/sufficient scalar contraction test for I,F family.
            for a, b in ((a_a, b_a), (a_b, b_b)):
                assert norm2([add(a, b)]) <= 1
                assert norm2([add(a, times(b, -1))]) <= 1
            state = scatter(scatter(source, 2, a_a, b_a), 4, a_b, b_b)
            double = multiply(b_a, b_b)
            d = times(double, F(1, 4))
            success = F(0)
            for m, n in product(range(2), repeat=2):
                actual = [ZERO]*16
                for p, aa, ap, bb, bp in product(range(2), repeat=5):
                    matter = 8*aa+4*ap+2*bb+bp
                    out_a = aa ^ m
                    target = 8*out_a+4*ap+2*bb+bp
                    value = times(state[32*p+16*(p ^ m)+matter],
                                  F((-1)**(n*(p+out_a)), 4))
                    actual[target] = add(actual[target], value)
                mu = 0 if (m, n) == (0, 0) else (3 if m == 0 else (1 if n == 0 else 2))
                coefficients = [d]*4
                if mu == 0:
                    coefficients[0] = plus(multiply(a_a, a_b),
                        times(plus(multiply(b_a, a_b), multiply(a_a, b_b)), F(1, 2)), d)
                else:
                    coefficients[0] = add(times(multiply(b_a, a_b), F(1, 2)), d)
                    coefficients[mu] = add(times(multiply(a_a, b_b), F(1, 2)), d)
                expected = [ZERO]*16
                for k, row, col in product(range(4), repeat=3):
                    expected[4*row+col] = add(expected[4*row+col],
                        times(multiply(coefficients[k], multiply(e[k][row], e[k][col])), F(1, 2)))
                assert actual == expected
                # A local projector in the orthonormal e basis removes
                # unknown coefficients. Compute retained vectors directly.
                kept = [k for k in range(4) if k != 0 and (mu == 0 or k != mu)]
                projected = [ZERO]*16
                for k, row, col in product(kept, range(4), range(4)):
                    projected[4*row+col] = add(projected[4*row+col],
                        times(multiply(d, multiply(e[k][row], e[k][col])), F(1, 2)))
                retained_probability = norm2(projected)
                assert retained_probability == len(kept)*norm2([d])
                assert len(kept) == (3 if mu == 0 else 2)
                success += retained_probability
                # Fixed qutrit pair effects each cover two Schmidt labels
                # with 1/2 weight; their sum is the identity on this support.
                if len(kept) == 3:
                    degrees = {k: F(0) for k in kept}
                    for i in range(3):
                        for j in range(i+1, 3):
                            degrees[kept[i]] += F(1, 2)
                            degrees[kept[j]] += F(1, 2)
                    assert all(value == 1 for value in degrees.values())
                for i, j in product(range(16), repeat=2):
                    assert multiply(actual[i], conjugate(actual[j])) == multiply(
                        expected[i], conjugate(expected[j]))
                    coefficient_units += 1
                projection_cases += 1
            assert success == F(9, 16)*norm2([double])
            switched_minus = F(1, 2)*norm2([double])
            assert success-switched_minus == F(1, 16)*norm2([double])
            assert success <= sum(norm2([value]) for value in state)/8 <= 1
            records.append({'ordinary_Bell_yield': str(success),
                            'switch_minus_Bell_yield': str(switched_minus)})
    return {'unknown_complex_node_pairs': len(records),
            'full_Bell_branch_CP_coefficients': coefficient_units,
            'fixed_local_projection_cases': projection_cases,
            'scope': ('Fixed ordinary local-ancilla projections give 9/16 '
                      'times the double-SWAP weight, versus switch minus '
                      '1/2, for unknown accepted scalar I/SWAP families. '
                      'Full physical costs, nonpreserved mode labels and '
                      'additional switch plus outputs are not compared.')}


def raman_operator_ancilla_examples():
    """Fixed local projections factor arbitrary ordered auxiliary kernels."""
    def msum(*matrices):
        dimension = len(matrices[0])
        output = zeros(dimension, dimension)
        for matrix in matrices:
            for i, j in product(range(dimension), repeat=2):
                output[i][j] = add(output[i][j], matrix[i][j])
        return output

    def gscale(matrix, scalar):
        return [[multiply(scalar, value) for value in row] for row in matrix]

    def scatter(vector, site, a, b):
        dimension = len(a)
        answer = [zeros(dimension, dimension) for _ in range(64)]
        for index, value in enumerate(vector):
            target = index
            if ((index >> 5) & 1) != ((index >> (5-site)) & 1):
                target ^= (1 << 5) ^ (1 << (5-site))
            answer[index] = msum(answer[index], matmul(a, value))
            answer[target] = msum(answer[target], matmul(b, value))
        return answer

    e = ([ONE, ZERO, ZERO, ONE], [ZERO, ONE, ONE, ZERO],
         [ZERO, gaussian(0, -1), gaussian(0, 1), ZERO],
         [ONE, ZERO, ZERO, gaussian(-1)])
    x = [[ZERO, ONE], [ONE, ZERO]]
    z = [[ONE, ZERO], [ZERO, gaussian(-1)]]
    y = [[ZERO, gaussian(0, -1)], [gaussian(0, 1), ZERO]]
    cycle = zeros(3, 3)
    reverse = zeros(3, 3)
    for index in range(3):
        cycle[(index+1) % 3][index] = ONE
        reverse[2-index][index] = ONE
    phase = [[ONE, ZERO, ZERO], [ZERO, gaussian(0, 1), ZERO],
             [ZERO, ZERO, gaussian(-1)]]
    rotation = [[gaussian(F(3, 5)), gaussian(F(-4, 5)), ZERO],
                [gaussian(F(4, 5)), gaussian(F(3, 5)), ZERO],
                [ZERO, ZERO, ONE]]
    examples = ((identity(2), x, z, y), (cycle, phase, rotation, reverse))
    factor_entries = gram_entries = noncommuting_cases = 0
    for u_a, v_a, u_b, v_b in examples:
        dimension = len(u_a)
        ident = identity(dimension)
        for unitary in (u_a, v_a, u_b, v_b):
            assert matmul(adjoint(unitary), unitary) == ident
        a_a = scale(msum(u_a, v_a), F(1, 2))
        b_a = scale(msum(u_a, scale(v_a, -1)), F(1, 2))
        a_b = scale(msum(u_b, v_b), F(1, 2))
        b_b = scale(msum(u_b, scale(v_b, -1)), F(1, 2))
        assert matmul(b_a, b_b) != matmul(b_b, b_a)
        noncommuting_cases += 1
        double = matmul(b_b, b_a)
        source = [zeros(dimension, dimension) for _ in range(64)]
        for p, aa, bb in product(range(2), repeat=3):
            source[48*p+12*aa+3*bb] = ident
        state = scatter(scatter(source, 2, a_a, b_a), 4, a_b, b_b)
        # Each node is controlled-U/V on SWAP +/- sectors, hence unitary.
        total_gram = zeros(dimension, dimension)
        for operator in state:
            total_gram = msum(total_gram, matmul(adjoint(operator), operator))
        assert scale(total_gram, F(1, 8)) == ident
        success_gram = zeros(dimension, dimension)
        for m, n in product(range(2), repeat=2):
            actual = [zeros(dimension, dimension) for _ in range(16)]
            for p, aa, ap, bb, bp in product(range(2), repeat=5):
                matter = 8*aa+4*ap+2*bb+bp
                out_a = aa ^ m
                target = 8*out_a+4*ap+2*bb+bp
                actual[target] = msum(actual[target],
                    scale(state[32*p+16*(p ^ m)+matter],
                          F((-1)**(n*(p+out_a)), 4)))
            mu = 0 if (m, n) == (0, 0) else (3 if m == 0 else (1 if n == 0 else 2))
            kept = [k for k in range(4) if k != 0 and (mu == 0 or k != mu)]
            local_projector = zeros(4, 4)
            for k, i, j in product(kept, range(4), range(4)):
                local_projector[i][j] = add(local_projector[i][j],
                    times(multiply(e[k][i], conjugate(e[k][j])), F(1, 2)))
            assert matmul(local_projector, local_projector) == local_projector
            projected = [zeros(dimension, dimension) for _ in range(16)]
            for i, j, old in product(range(4), repeat=3):
                projected[4*i+j] = msum(projected[4*i+j],
                    gscale(actual[4*old+j], local_projector[i][old]))
            projected_gram = zeros(dimension, dimension)
            for i, j in product(range(4), repeat=2):
                factor = ZERO
                for k in kept:
                    factor = add(factor, times(multiply(e[k][i], e[k][j]), F(1, 8)))
                expected = gscale(double, factor)
                assert projected[4*i+j] == expected
                factor_entries += dimension*dimension
                projected_gram = msum(projected_gram,
                    matmul(adjoint(projected[4*i+j]), projected[4*i+j]))
            expected_gram = scale(matmul(adjoint(double), double), F(len(kept), 16))
            assert projected_gram == expected_gram
            gram_entries += dimension*dimension
            success_gram = msum(success_gram, projected_gram)
        assert success_gram == scale(matmul(adjoint(double), double), F(9, 16))
    return {'noncommuting_auxiliary_dimensions': [len(case[0]) for case in examples],
            'noncommuting_operator_cases': noncommuting_cases,
            'full_auxiliary_factor_matrix_entries': factor_entries,
            'retained_branch_Gram_entries': gram_entries,
            'scope': ('Reference-complete finite ordered operator-kernel '
                      'factorization for common auxiliary dimensions two and '
                      'three. No coefficient commutation is assumed. Physical '
                      'common-SWAP tensor ports and Bell-program costs remain '
                      'hypotheses; scalar switch-minus yields do not extend '
                      'automatically to noncommuting coefficient operators.')}


def verify_raman_source_clock_frontier():
    from fractions import Fraction as F
    import verify_fault_simulation as g

    def add(a,b):
        return [[g.add(x,y) for x,y in zip(ar,br)] for ar,br in zip(a,b)]

    def multiply_scalar(a,value):
        return [[g.multiply(x,value) for x in row] for row in a]

    def half_sum(a,b,sign):
        return [g.times(g.add(x,g.times(y,sign)),F(1,2)) for x,y in zip(a,b)]

    def act(a,v):
        return [row[0] for row in g.matmul(a,[[x] for x in v])]

    def absolute_square(z):
        q=g.multiply(z,g.conjugate(z));assert q[1]==0
        return q[0]

    def norm(v):
        q=g.inner(v,v);assert q[1]==0
        return q[0]

    eye=g.identity(8);wa=g.zeros(8,8);wb=g.zeros(8,8)
    for index in range(8):
        p,a,b=(index>>2)&1,(index>>1)&1,index&1
        wa[(a<<2)+(p<<1)+b][index]=g.ONE
        wb[(b<<2)+(a<<1)+p][index]=g.ONE
    assert g.matmul(wa,wa)==g.matmul(wb,wb)==eye
    initial=[g.ZERO]*8;initial[4]=g.ONE
    spectators=[g.ONE,g.gaussian(F(3,5),F(4,5)),
                g.gaussian(F(-9,11)),g.gaussian(F(4,5))]
    bright=[g.gaussian(-1),g.gaussian(0,1),g.gaussian(F(18,23)),
            g.gaussian(F(3,5),F(-4,5)),g.ZERO]
    fixtures=[(s,z) for s in spectators for z in bright]+[(g.ONE,g.ONE)]
    branch_count=yield_count=visit_count=repeat_count=0
    for s,z in fixtures:
        assert absolute_square(s)<=1 and absolute_square(z)<=1
        a=g.times(g.add(s,z),F(1,2))
        b=g.times(g.add(s,g.times(z,-1)),F(1,2))
        q=absolute_square(b);h=absolute_square(a)+q;sv=absolute_square(s)
        assert h<=1
        ta=add(multiply_scalar(eye,a),multiply_scalar(wa,b))
        tb=add(multiply_scalar(eye,a),multiply_scalar(wb,b))
        first_a,first_b=act(ta,initial),act(tb,initial)
        order0,order1=act(tb,first_a),act(ta,first_b)
        p_switch=F(0);p_one=F(0)
        for sign in [1,-1]:
            sw=half_sum(order0,order1,sign)[:4]
            ordinary=half_sum(first_a,first_b,sign)[:4]
            for v in [sw,ordinary]:
                assert v[0]==v[3]==g.ZERO
                assert v[1]==g.times(v[2],sign)
                branch_count+=1
            p_switch+=norm(sw);p_one+=norm(ordinary)
        assert p_switch==q*(sv+absolute_square(a))
        assert p_one==q
        yield_count+=2
        assert norm(first_a)==norm(first_b)==h
        c_switch=1+h
        assert q*c_switch-p_switch==q*(1+q-sv)
        assert q*c_switch-p_switch>=q*q
        visit_count+=2
        p_two=2*q-q*q
        assert p_two-p_switch==q*(2-sv-h)>=0
        if q<1:
            probability=min(F(1),h/(1-q))
            cost=1+probability*(1-q)
            success=q*(1+probability*(1-q))
            assert cost<=c_switch and success>=p_switch
        else:
            assert q==1 and p_switch==1
        repeat_count+=2
    return dict(status='passed',balanced_passive_node_fixtures=len(fixtures),
                complete_Bell_branch_vectors=branch_count,
                switch_and_one_pass_yield_identities=yield_count,
                first_loss_and_mean_visit_identities=visit_count,
                two_attempt_and_adaptive_budget_identities=repeat_count,
                arithmetic='Python standard-library Gaussian-rational matrices',
                scope='Finite full accepted-state and algebraic yield/visit guards. General passivity, renewal, source statistics, phase/reference access and physical timing proofs remain analytic; no measured Bell-rate certificate.')


def verify_raman_cavity_frontier():
    N = 4
    UNIT = (0,)*N


    def const(q):
        return {UNIT: F(q)} if q else {}


    def var(j):
        key = tuple(int(k == j) for k in range(N))
        return {key: F(1)}


    def add(*ps):
        ans = {}
        for p in ps:
            for key, value in p.items():
                ans[key] = ans.get(key, F(0))+value
        return {key: value for key, value in ans.items() if value}


    def scale(p, q):
        return {key: value*q for key, value in p.items() if value*q}


    def sub(a, b):
        return add(a, scale(b, -1))


    def mul(*ps):
        ans = const(1)
        for p in ps:
            out = {}
            for a, ca in ans.items():
                for b, cb in p.items():
                    key = tuple(i+j for i, j in zip(a, b))
                    out[key] = out.get(key, F(0))+ca*cb
            ans = {key: value for key, value in out.items() if value}
        return ans


    def square(p):
        return mul(p, p)


    def cadd(a, b):
        return add(a[0], b[0]), add(a[1], b[1])


    def csub(a, b):
        return sub(a[0], b[0]), sub(a[1], b[1])


    def cmul(a, b):
        return sub(mul(a[0], b[0]), mul(a[1], b[1])), add(mul(a[0], b[1]), mul(a[1], b[0]))


    def cnorm(a):
        return add(square(a[0]), square(a[1]))


    one = const(1)
    r, s, x, y = [var(j) for j in range(N)]
    D, H = sub(square(s), one), add(square(s), one)
    a, e = add(r, one), sub(r, s)
    z, w = (x, a), (y, one)
    zw = cmul(z, w)
    d = csub(zw, (D, {}))
    zd = cmul(z, d)
    # Numerator u=(c+h)/2 = [zd - i*r*(2zw-D)]/(zd).
    twozw_D = csub((scale(zw[0], 2), scale(zw[1], 2)), (D, {}))
    ir_times = cmul(({}, r), twozw_D)
    unum = csub(zd, ir_times)
    braces = sub(add(mul(H, add(square(e), square(x))),
                     scale(mul(add(square(a), square(x)), square(y)), 2)),
                 scale(mul(D, x, y), 2))
    f_over_m_num_squared = mul(square(r), square(square(add(s, one))))
    residual = sub(sub(cnorm(zd), cnorm(unum)), f_over_m_num_squared)
    assert residual == scale(mul(r, braces), 2)

    # Spectator passivity |z|^2-|z-2ir|^2=4r.
    assert sub(cnorm(z), cnorm((x, sub(one, r)))) == scale(r, 4)
    # The last AM--GM coefficient is nonnegative for s>=1.
    assert sub(scale(H, 2), square(sub(s, one))) == square(add(s, one))

    # Resonant transfer optimum and resonant ellipse are polynomial identities.
    den = mul(add(r, one), add(r, square(s)))
    Fnum = mul(r, square(add(s, one)))
    assert sub(den, Fnum) == square(sub(r, s))
    Unum = sub(square(r), square(s))
    assert sub(sub(square(den), square(Fnum)), square(Unum)) == scale(mul(r, square(sub(r, s)), H), 2)

    # AM--GM itself is checked in each pair by its squared difference.
    for p, q in ((mul(H, square(e)), scale(mul(square(x), square(y)), 2)),
                 (mul(H, square(x)), scale(mul(square(a), square(y)), 2))):
        assert sub(square(add(p, q)), scale(mul(p, q), 4)) == square(sub(p, q))

    # Source-nominal resonance arithmetic includes scalar spectator loss.
    kex, ki, g, gamma = map(F, (60, 6, 27, 3))
    kappa = kex+ki
    c = 1-2*kex/kappa
    h = 1-2*kex*gamma/(kappa*gamma+2*g*g)
    u, f = (c+h)/2, (c-h)/2
    assert (c, h, u, f, f/c) == (F(-9, 11), F(18, 23), F(-9, 506), F(-405, 506), F(45, 46))
    p1, ps = f*f, f*f*(c*c+u*u)
    assert p1 == F(164025, 256036) and ps == F(28126514925, 65554433296)
    assert p1 > ps
    return {"status": "passed", "formal_real_variables": 4,
            "complete_detuned_ellipse_identity": True,
            "spectator_passivity_identity": True,
            "AM_GM_polynomial_guards": 3,
            "resonant_transfer_maximum_identity": True,
            "nominal_one_node_Bell_yield": str(p1),
            "nominal_switch_Bell_yield": str(ps),
            "scope": "Exact polynomial transcription and nominal arithmetic; universal nonnegativity, continuum extension, accessible coupling range, calibrated phase references and clock costs remain analytic or physical assumptions."}



def verify_raman_passive_filter():
    """Exact ordered-word cancellation at p=1/2 in Q(sqrt(2))."""
    z, one = (F(0), F(0)), (F(1), F(0))


    def add(a, b):
        return a[0]+b[0], a[1]+b[1]


    def mul(a, b):
        return a[0]*b[0]+2*a[1]*b[1], a[0]*b[1]+a[1]*b[0]


    def scale(a, b):
        return a[0]*b, a[1]*b


    def dot(a, b):
        out = z
        for x, y in zip(a, b):
            out = add(out, mul(x, y))
        return out


    W = [[z]*4 for _ in range(4)]
    W[0][0], W[3][0] = (0, 1), (2, 0)
    W[1][1], W[2][1] = one, (0, 1)
    W[1][2], W[2][2] = (-1, 0), (0, -1)
    gram = [[scale(dot([W[k][i] for k in range(4)],
                      [W[k][j] for k in range(4)]), F(1, 6))
             for j in range(4)] for i in range(4)]
    for i, j in product(range(4), repeat=2):
        assert dot(gram[i], [gram[k][j] for k in range(4)]) == gram[i][j]
    assert all(gram[i][j] == gram[j][i] for i, j in product(range(4), repeat=2))
    # The complementary optical effect is an orthogonal projector as well.
    reject = [[add((one if i == j else z), scale(gram[i][j], -1))
               for j in range(4)] for i in range(4)]
    assert all(dot(reject[i], [reject[k][j] for k in range(4)]) == reject[i][j]
               for i, j in product(range(4), repeat=2))
    # diag(1,1/2) has a valid positive complementary local-filter effect.
    assert F(1, 4) + F(3, 4) == 1 and F(3, 4) > 0

    f, g = [(0, 1), z, z, (-1, 0)], [z, (0, 1), (-1, 0), z]
    assert dot(f, f) == dot(g, g) == (3, 0) and dot(f, g) == z


    def swap_pa(vector, site):
        out = [z]*16
        bit = 1 << (3-site)
        for i, a in enumerate(vector):
            j = i ^ (8 | bit) if bool(i & 8) != bool(i & bit) else i
            out[j] = add(out[j], a)
        return out


    def processor(vector):
        out = [z]*16
        for i, a in enumerate(vector):
            pq, ab = divmod(i, 4)
            for j in range(4):
                out[4*j+ab] = add(out[4*j+ab], mul(W[j][pq], a))
        return out


    def herald(vector, h):
        return [dot([vector[4*pq+ab] for pq in range(4)], h)
                for ab in range(4)]


    source = [z]*16
    source[4] = source[8] = one
    checked = 0
    for sa, sb in product(range(2), repeat=2):
        state = swap_pa(source, 2) if sa else source
        state = processor(state)
        state = swap_pa(state, 3) if sb else state
        of, og = herald(state, f), herald(state, g)
        og = [scale(a, F(1, 2) if i >= 2 else 1) for i, a in enumerate(og)]
        assert of == ([z, (2, 0), (2, 0), z] if sa and sb else [z]*4)
        assert og == ([(0, 1), z, z, (0, 1)] if sa and sb else [z]*4)
        checked += 8
        if sa and sb:
            pf, pg = scale(dot(of, of), F(1, 36)), scale(dot(og, og), F(1, 36))
            assert pf == (F(2, 9), 0) and pg == (F(1, 9), 0)
            assert add(pf, pg) == (F(1, 3), 0)

    return {"ordered_word_memory_coefficients": checked,
                      "processor_Gram": "exact projector",
                      "heralds": "orthogonal normalized after division by sqrt(3)",
                      "Bell_yield_coefficient": "1/3",
                      "scope": "Two accepted heralds; second includes the actual diag(1,1/2) spin-filter success. Rejected optical ports, other readouts, filter failure and photon loss are charged."}


def bare_swap_rank_guards():
    """Finite literal bare-SWAP rank ingredients; general bounds are analytic."""
    from fractions import Fraction as F
    from retained_photon_serial import G, add, adj, eye, kron, mm, require, scale, zeros

    def rank(a):
        a=[row[:] for row in a]
        row=0
        for col in range(len(a[0])):
            pivot=next((i for i in range(row,len(a)) if a[i][col] != 0),None)
            if pivot is None:
                continue
            a[row],a[pivot]=a[pivot],a[row]
            factor=a[row][col]
            a[row]=[x/factor for x in a[row]]
            for i in range(len(a)):
                if i != row and a[i][col] != 0:
                    factor=a[i][col]
                    a[i]=[x-factor*y for x,y in zip(a[i],a[row])]
            row+=1
            if row==len(a):
                break
        return row

    def tr(a):
        return sum((a[i][i] for i in range(len(a))),G())

    def norm2(z):
        return z.r*z.r+z.i*z.i

    def outer(v):
        return [[x*y.conj() for y in v] for x in v]

    def run_guards():
        source_cases=columns=flag_cases=rank_cases=score_cases=0
        max_rank=0
        for d in (2,3):
            D=d*d
            swap_a,swap_b=zeros(d**3),zeros(d**3)
            for s in range(d):
                for a in range(d):
                    for b in range(d):
                        j=(s*d+a)*d+b
                        swap_a[(a*d+s)*d+b][j]=G(1)
                        swap_b[(b*d+a)*d+s][j]=G(1)
            require(mm(swap_a,swap_a)==mm(swap_b,swap_b)==eye(d**3),
                    'literal full bus-memory SWAP matrices')
            e0=[G(int(i==0)) for i in range(d)]
            e1=[G(int(i==1)) for i in range(d)]
            u=([G(F(3,5)),G(0,F(4,5))] if d==2 else
               [G(F(1,3)),G(0,F(2,3)),G(F(2,3))])
            v=[x.conj() for x in u]
            f=eye(d)
            f[0][0]=f[1][1]=G(F(3,5))
            f[0][1]=f[1][0]=G(0,F(4,5))
            if d==3:
                f[2][2]=G(0,1)
            require(mm(adj(f),f)==eye(d),'literal complex terminal bus rotation')
            h=[[G(1),G(1)],[G(1),G(-1)]]
            measurement=kron(h,f) # normalized rows carry an external 1/2 effect weight
            ab_swap=zeros(D)
            for a in range(d):
                for b in range(d):
                    ab_swap[d*b+a][d*a+b]=G(1)
            for chi0,chi1 in ((u,u),(u,v),(e0,e1),(u,[G()]*d)):
                source_norm=sum((norm2(x) for x in chi0+chi1),F(0))
                require(source_norm in (F(1),F(2)),'source normalization ledger')
                # The source is |0>chi0+|1>chi1; raw W is not divided by sqrt(source_norm).
                w=zeros(2*d*D,D)
                for a in range(d):
                    for b in range(d):
                        for k in range(d):
                            w[((0*d+b)*d+k)*d+a][d*a+b]+=chi0[k] # B_S A_S product: A=chi0,B=a,S=b
                            w[((1*d+a)*d+b)*d+k][d*a+b]+=chi1[k] # reverse: A=b,B=chi1,S=a
                initial=[]
                for chi in (chi0,chi1):
                    entry=zeros(d**3,D)
                    for s in range(d):
                        for a in range(d):
                            for b in range(d):
                                entry[(s*d+a)*d+b][d*a+b]=chi[s]
                    initial.append(entry)
                literal=mm(swap_b,mm(swap_a,initial[0]))+mm(swap_a,mm(swap_b,initial[1]))
                require(w==literal,'independently multiplied two-SWAP word images')
                require(mm(adj(w),w)==scale(eye(D),source_norm),'literal controlled two-SWAP isometry')
                p0,p1=outer(chi0),outer(chi1)
                if all(x==0 for x in chi1):
                    p= kron(p0,eye(d))
                    expected_dimension=d
                else:
                    p=add(add(kron(p0,eye(d)),kron(eye(d),p1)),scale(kron(p0,p1),-1))
                    expected_dimension=2*d-1
                require(p==adj(p) and mm(p,p)==p and tr(p)==G(expected_dimension),'AB range projector dimension')
                require(mm(kron(eye(2*d),p),w)==w,'full column support after literal words')
                require(expected_dimension < D,'full-unknown-input rank deficit')
                columns+=D
                ks=[]
                for m in range(2*d):
                    k=zeros(D)
                    for a in range(D):
                        for b in range(D):
                            k[a][b]=sum((measurement[m][cs]*w[cs*D+a][b] for cs in range(2*d)),G())
                    require(mm(p,k)==k,'complex joint terminal CS row preserves low output support')
                    require(rank(k)<=expected_dimension,'fine terminal Kraus rank')
                    ks.append(k)
                    flag_cases+=1
                weight=F(1,2)/source_norm
                effect=zeros(D)
                for k in ks:
                    effect=add(effect,scale(mm(adj(k),k),weight))
                require(effect==eye(D),'all terminal flags complete with normalized source/readout')
                for decoder in (eye(D),ab_swap):
                    decoded=[mm(decoder,k) for k in ks]
                    for k in decoded:
                        actual_rank=rank(k)
                        max_rank=max(max_rank,actual_rank)
                        require(actual_rank<=expected_dimension,'conditional AB decoder cannot raise rank')
                        rank_cases+=1
                    for target in (eye(D),ab_swap):
                        score=F(0)
                        for k in decoded:
                            overlap=norm2(tr(mm(adj(target),k)))
                            require(overlap<=expected_dimension*tr(mm(adj(k),k)).r,'rank versus trace overlap ingredient')
                            score+=weight*overlap/F(D*D)
                        require(score<=F(2*d-1,D),'all-attempt unitary-target ceiling ingredient')
                        score_cases+=1
                source_cases+=1
        return {'status':'passed','dimensions':[2,3],'source_fixtures':source_cases,
                'literal_input_columns':columns,'terminal_joint_rows':flag_cases,
                'decoded_fine_operator_ranks':rank_cases,'unitary_target_scores':score_cases,
                'maximum_observed_operator_rank':max_rank,
                'scope':'Literal finite source/CS readout/AB-unitary support and normalization ingredients only. General rank, arbitrary decoder, exact herald and full-isometry perturbation bounds are analytic; no physical SWAP/process/dilation certificate or all-resource two-contact no-go.'}

    return run_guards()


def partial_swap_gate_instruments():
    """Opposite ideal partial contacts: native CZ flag and ordinary match."""
    from retained_photon_serial import G, add, adj, eye, mm, require, scale, zeros

    def matrix(rows):
        return [[G(x) for x in row] for row in rows]

    def gram(a):
        return mm(adj(a), a)

    def total(matrices):
        out = zeros(4)
        for entry in matrices:
            out = add(out, entry)
        return out

    swap = matrix([[1, 0, 0, 0], [0, 0, 1, 0],
                   [0, 1, 0, 0], [0, 0, 0, 1]])
    for sign in (1, -1):
        numerator = add(eye(4), scale(swap, G(0, 2*sign)))
        require(gram(numerator) == scale(eye(4), 5), 'partial-contact normalization')
        # Gamma=1, delta=sign/2: the known bus-Z conjugation gives tI-rF.
        r = -G(1)/G(1, -F(sign, 2))
        raw = add(scale(eye(4), 1+r), scale(swap, -r))
        require(raw == scale(numerator, G(1, -2*sign)/5), 'source detuning and phase frame')
        require(gram(raw) == eye(4), 'lossless source-derived contact unitarity')
    bell = matrix([[1, 0, 0, 1], [1, 0, 0, -1],
                   [0, 1, 1, 0], [0, 1, -1, 0]])
    source_norm = sum((x*x for x in bell[0]), G())
    require(source_norm == 2 and gram(bell) == scale(eye(4), 2), 'Bell source and complete readout normalization')
    terminal_denominator_squared = source_norm.r*5*5*2
    early_denominator_squared = source_norm.r*5*2
    phase_filter = matrix([[1, 0, 0, 0], [0, 0, 0, 0],
                           [0, 0, 0, 0], [0, 0, 0, -1]])
    odd = matrix([[0, 0, 0, 0], [0, 1, 0, 0],
                  [0, 0, 1, 0], [0, 0, 0, 0]])
    require(add(gram(phase_filter), gram(odd)) == eye(4), 'physical filter/reject completion')

    def accumulate(state, key, value):
        state[key] = state.get(key, G())+value

    def contact(state, station, sign, coefficients=None):
        # Raw numerator I+sign*2iF, qubit order C,S,A,B.
        alpha, beta = (G(1), G(0, 2*sign)) if coefficients is None else coefficients
        out = {}
        for (c, s, a, b), value in state.items():
            accumulate(out, (c, s, a, b), alpha*value)
            target = (c, a, s, b) if station == 'A' else (c, b, a, s)
            accumulate(out, target, beta*value)
        return out

    def states(a, b, mode, coefficients=None):
        ca = None if coefficients is None else coefficients[:2]
        cb = None if coefficients is None else coefficients[2:]
        source = {(0, 0, a, b): G(1), (1, 1, a, b): G(1)}
        if mode == 'native':
            out = {}
            for c in (0, 1):
                branch = {k: v for k, v in source.items() if k[0] == c}
                branch = (contact(contact(branch, 'A', 1, ca), 'B', -1, cb) if c == 0
                          else contact(contact(branch, 'B', -1, cb), 'A', 1, ca))
                for key, value in branch.items():
                    accumulate(out, key, value)
            return out
        first = contact(source, 'A', 1, ca)
        if mode == 'early':
            return {k: v for k, v in first.items() if k[0] != k[1]}
        accepted = {k: v*((-1)**k[0]) for k, v in first.items() if k[0] == k[1]}
        return contact(accepted, 'B', -1, cb)

    def flags(mode, coefficients=None):
        labels = ((1, 0), (1, 1)) if mode == 'early' else tuple(product(range(2), repeat=2))
        out = {f'{m}{n}': zeros(4) for m, n in labels}
        for a, b in product(range(2), repeat=2):
            for (c, s, aa, bb), value in states(a, b, mode, coefficients).items():
                for m, n in labels:
                    if s == (c ^ m):
                        out[f'{m}{n}'][2*aa+bb][2*a+b] += ((-1)**(n*c))*value
        return out

    native, ordinary, early = flags('native'), flags('ordinary'), flags('early')
    expected_native = {
        '00': matrix([[6, 0, 0, 0], [0, 2, 8, 0], [0, 0, 2, 0], [0, 0, 0, 6]]),
        '01': matrix([[4, 0, 0, 0], [0, G(0, 4), 0, 0],
                      [0, 0, G(0, -4), 0], [0, 0, 0, -4]]),
        '10': matrix([[0, G(4, -2), G(0, 2), 0], [G(4, -2), 0, 0, G(4, 2)],
                      [G(0, 2), 0, 0, G(0, -2)], [0, G(4, 2), G(0, -2), 0]]),
        '11': matrix([[0, G(4, -2), G(0, 2), 0], [G(-4, 2), 0, 0, G(4, 2)],
                      [G(0, -2), 0, 0, G(0, -2)], [0, G(-4, -2), G(0, 2), 0]]),
    }
    expected_ordinary = {
        '00': expected_native['01'],
        '01': matrix([[6, 0, 0, 0], [0, 2, 0, 0], [0, 0, 2, 0], [0, 0, 0, 6]]),
        '10': matrix([[0, G(4, -2), 0, 0], [G(0, 2), 0, 0, 0],
                      [0, 0, 0, G(0, -2)], [0, 0, G(-4, 2), 0]]),
        '11': matrix([[0, G(4, -2), 0, 0], [G(0, -2), 0, 0, 0],
                      [0, 0, 0, G(0, -2)], [0, 0, G(4, -2), 0]]),
    }
    expected_early = {}
    for n in (0, 1):
        entry = zeros(4)
        for a, b in product(range(2), repeat=2):
            entry[2*(a ^ 1)+b][2*a+b] = G(0, 2*((-1)**(n*(1-a))))
        expected_early[f'1{n}'] = entry
    branch_entries = 0
    for actual, expected in ((native, expected_native), (ordinary, expected_ordinary), (early, expected_early)):
        for label in expected:
            for i, j in product(range(4), repeat=2):
                require(actual[label][i][j] == expected[label][i][j], 'direct all-input branch entry')
                branch_entries += 1

    target = scale(expected_native['01'], F(1, 4))
    correction = matrix([[1, 0, 0, 0], [0, G(0, -1), 0, 0],
                         [0, 0, G(0, 1), 0], [0, 0, 0, 1]])
    cz = matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, -1]])
    require(gram(target) == eye(4) and mm(correction, target) == cz, 'known output-local CZ correction')
    probability = F(16, terminal_denominator_squared)
    require(probability == F(4, 25), 'normalized selected gate mass')
    coefficients = 0
    for a, b, i, j in product(range(4), repeat=4):
        expected = probability*target[i][a]*target[j][b].conj()
        for branch in (native['01'], ordinary['00']):
            require(branch[i][a]*branch[j][b].conj()/terminal_denominator_squared == expected,
                    'all input matrix units including reference coherences')
        coefficients += 1
    native_effects = {k: gram(v) for k, v in native.items()}
    ordinary_effects = {k: gram(v) for k, v in ordinary.items()}
    early_effects = {k: gram(v) for k, v in early.items()}
    require(total(native_effects.values()) == scale(eye(4), terminal_denominator_squared), 'native four-flag TP')
    ordinary_total = scale(total(ordinary_effects.values()), 1/terminal_denominator_squared)
    early_total = scale(total(early_effects.values()), 1/early_denominator_squared)
    require(ordinary_total == scale(eye(4), F(3, 5)) and early_total == scale(eye(4), F(2, 5)), 'ordinary pass and early mass')
    require(add(ordinary_total, early_total) == eye(4), 'ordinary complete six-flag TP')
    for effect in early_effects.values():
        require(scale(effect, 1/early_denominator_squared) == scale(eye(4), F(1, 5)), 'each corrected early identity normalization')
    for effects, labels in ((native_effects, ('00', '10', '11')), (ordinary_effects, ('01', '10', '11'))):
        for label in labels:
            require(effects[label] != scale(eye(4), effects[label][0][0]), 'other terminal flag is nonunitary')

    # Generic scalar contacts use their actual coefficients, not point numerators.
    za = matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]])
    zb = matrix([[1, 0, 0, 0], [0, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, -1]])
    fixtures = [
        (G(F(3, 10), F(1, 10)), G(F(1, 5), -F(1, 10)), G(F(2, 5), -F(1, 5)), G(F(1, 10), F(1, 10))),
        (G(0, F(1, 2)), G(F(1, 4), F(1, 4)), G(F(1, 3)), G(0, F(1, 5))),
        (G(), G(1), G(F(3, 5)), G(0, F(4, 5))),
    ]
    frequencies = (F(-1, 4), F(1, 4))
    for xi in frequencies:
        ra, rb = -G(1)/G(1, -(xi+F(1, 2))), -G(1)/G(1, -(xi-F(1, 2)))
        fixtures.append((1+ra, -ra, 1+rb, -rb))
    selected_entries = 0
    selected_native, selected_ordinary, frequency_formula = [], [], []
    for index, (a, b, c, d) in enumerate(fixtures):
        for alpha, beta in ((a, b), (c, d)):
            for eigenvalue in (alpha+beta, alpha-beta):
                norm = (eigenvalue*eigenvalue.conj()).r
                require(norm <= 1 and (index < 3 or norm == 1), 'scalar fixture contact contraction/unitarity')
        expected = add(scale(za, b*c/2+b*d/4), scale(zb, a*d/2+b*d/4))
        kn = scale(flags('native', (a, b, c, d))['01'], F(1, 2))
        ko = scale(flags('ordinary', (a, b, c, d))['00'], F(1, 2))
        for i, j in product(range(4), repeat=2):
            require(kn[i][j] == ko[i][j] == expected[i][j], 'generic direct-action selected-branch identity')
            selected_entries += 2
        if index >= 3:
            xi = frequencies[index-3]
            denominator = 4*(G(1, -xi)*G(1, -xi)+F(1, 4))
            source_expected = add(scale(za, G(1, 1-2*xi)/denominator),
                                  scale(zb, G(1, -1-2*xi)/denominator))
            require(kn == source_expected, 'noncentral Fourier-source selected map')
            even, odd = kn[0][0], kn[1][1]
            require(even*even.conj() == (1+4*xi*xi)*odd*odd.conj() and xi != 0,
                    'finite spectral bins need not give proportional CZ')
            selected_native.append(kn)
            selected_ordinary.append(ko)
            frequency_formula.append(source_expected)
    frequency_coefficients = offdiagonal_coefficients = 0
    # Equal coherent bin amplitudes: retain output frequency and its off-diagonals.
    for f, g, a, b, i, j in product(range(2), range(2), range(4), range(4), range(4), range(4)):
        lhs = selected_native[f][i][a]*selected_native[g][j][b].conj()/2
        rhs = selected_ordinary[f][i][a]*selected_ordinary[g][j][b].conj()/2
        expected = frequency_formula[f][i][a]*frequency_formula[g][j][b].conj()/2
        require(lhs == rhs == expected, 'coherent retained-frequency matrix-unit coefficient')
        frequency_coefficients += 1
        offdiagonal_coefficients += int(f != g)
    require(selected_native[0][0][0]*selected_native[1][0][0].conj()/2 != 0,
            'coherent frequency off-diagonal is retained, not spectrally averaged')
    return {'status': 'passed', 'branch_entries': branch_entries, 'gate_CP_coefficients': coefficients,
            'native_flags': 4, 'ordinary_terminal_flags': 4, 'ordinary_early_flags': 2,
            'terminal_denominator_squared': str(terminal_denominator_squared),
            'early_denominator_squared': str(early_denominator_squared),
            'corrected_CZ_probability': str(probability), 'corrected_early_identity_probability': '2/5',
            'native_TP': True, 'ordinary_six_flag_TP': True,
            'scalar_elastic_selected_map': {'complex_scalar_fixtures': 3,
                'source_frequency_bins': [str(x) for x in frequencies],
                'selected_branch_entries': selected_entries,
                'coherent_frequency_CP_coefficients': frequency_coefficients,
                'offdiagonal_frequency_coefficients': offdiagonal_coefficients,
                'scope': 'Same frequency-diagonal elastic multipliers, Bell source/readout, matched history phase and ordinary midpoint filter. Selected retained-frequency map only; no frequency-changing/noncommuting bath kernel or other/rejected instrument equality.'},
            'scope': 'Exact opposite ideal partial contacts, Bell source/readout and paid ordinary midpoint parity filter. All-input flags and source/contact normalizations; no POVM/filter optimum, noisy instrument, clock or hardware certificate.'}


def operator_partial_swap_frontier():
    from fractions import Fraction as F
    from itertools import product
    from retained_photon_serial import G, add, adj, eye, kron, mm, require, scale, zeros

    def matrix(rows):
        return [[G(x) for x in row] for row in rows]

    def total(items, size):
        out = zeros(size)
        for item in items:
            out = add(out, item)
        return out

    def trace(a):
        return sum((a[i][i] for i in range(len(a))), G())

    def real(z):
        require(z.i == 0, 'real exact probability or squared norm')
        return z.r

    def gram(a):
        return mm(adj(a), a)

    def outer(v):
        return [[x*y.conj() for y in v] for x in v]

    def comm(a, b):
        return add(mm(a,b), scale(mm(b,a), -1))

    def column(a, j):
        return [row[j] for row in a]

    def embed_vector(v):
        h = len(v)
        out = zeros(4*h,4)
        for j,a in product(range(h),range(4)):
            out[4*j+a][a] = v[j]
        return out

    def lift2(a, third):
        out = zeros(3)
        for i,j in product(range(2), repeat=2):
            out[i][j] = a[i][j]
        out[2][2] = G(third)
        return out

    def partial_target(a, h):
        return [[sum((target[k].conj()*a[4*i+k][4*j+k] for k in range(4)), G())
                 for j in range(h)] for i in range(h)]

    swap = matrix([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]])
    za = matrix([[1,0,0,0],[0,1,0,0],[0,0,-1,0],[0,0,0,-1]])
    zb = matrix([[1,0,0,0],[0,-1,0,0],[0,0,1,0],[0,0,0,-1]])
    p0a = matrix([[1,0,0,0],[0,1,0,0],[0,0,0,0],[0,0,0,0]])
    remainder = mm(p0a, swap)
    require(remainder == matrix([[1,0,0,0],[0,0,1,0],[0,0,0,0],[0,0,0,0]]),
            'directed data-dependent remainder and physical output ports')
    target = [G(1),G(0,1),G(0,-1),G(-1)]
    va2 = matrix([[F(3,5),G(0,F(4,5))],[G(0,F(4,5)),F(3,5)]])
    vb2 = matrix([[G(0,F(5,13)),F(12,13)],[G(0,-F(12,13)),F(5,13)]])
    v = [G(F(1,3)),G(0,F(2,3)),G(F(2,3))]
    w3 = add(eye(3), scale(outer(v), -2))
    require(gram(w3) == eye(3), 'dense exact complex field basis')
    fields = (
        (2,va2,vb2,eye(2)),
        (3,mm(w3,mm(lift2(va2,1),adj(w3))),
           mm(w3,mm(lift2(vb2,G(0,1)),adj(w3))),w3),
    )
    selected_entries = triangular_entries = source_filter_cases = 0
    contrast_cases = kernel_cases = dilation_gram_entries = coherence_coefficients = 0
    conditional_cases = 0
    for h,va,vb,basis in fields:
        require(gram(va) == gram(vb) == eye(h), 'unitary bright field sectors')
        require(all(x != 0 for row in va for x in row)
                and all(x != 0 for row in vb for x in row), 'dense complex field contacts')
        x,y = scale(add(eye(h),scale(va,-1)),F(1,2)), scale(add(eye(h),scale(vb,-1)),F(1,2))
        a0,b0 = add(eye(h),scale(x,-1)), add(eye(h),scale(y,-1))
        c,d = comm(y,x), scale(add(x,scale(y,-1)),F(1,2))
        require(c != zeros(h), 'genuinely noncommuting field coefficients')
        for alpha,beta in ((a0,x),(b0,y)):
            contact = add(kron(alpha,eye(4)),kron(beta,swap))
            require(gram(contact) == eye(4*h), 'literal one-bright contact unitary')

        def accumulate(state,key,value):
            state[key] = state.get(key,G())+value

        def apply_contact(state,station):
            alpha,beta = (a0,x) if station == 'A' else (b0,y)
            out = {}
            for (field,control,s,a,b),value in state.items():
                for output in range(h):
                    accumulate(out,(output,control,s,a,b),alpha[output][field]*value)
                    key = ((output,control,a,s,b) if station == 'A'
                           else (output,control,b,a,s))
                    accumulate(out,key,beta[output][field]*value)
            return out

        def literal_selected(mode):
            out = zeros(4*h)
            for field,a,b in product(range(h),range(2),range(2)):
                initial = {(field,0,0,a,b):G(1),(field,1,1,a,b):G(1)}
                state = {}
                if mode == 'native':
                    for control in (0,1):
                        branch = {k:v for k,v in initial.items() if k[1] == control}
                        first,second = ('A','B') if control == 0 else ('B','A')
                        branch = apply_contact(apply_contact(branch,first),second)
                        for key,value in branch.items():
                            accumulate(state,key,value)
                else:
                    first,second = ('A','B') if mode == 'forward' else ('B','A')
                    state = apply_contact(initial,first)
                    state = {k:v*((-1)**k[1]) for k,v in state.items() if k[1] == k[2]}
                    state = apply_contact(state,second)
                for (output,control,s,aa,bb),value in state.items():
                    if control == s:
                        sign = (-1)**control if mode == 'native' else 1
                        out[4*output+2*aa+bb][4*field+2*a+b] += sign*value/2
            return out

        native,forward,reverse = (literal_selected(mode) for mode in ('native','forward','reverse'))
        yx,xy = mm(y,x),mm(x,y)
        lf = add(kron(add(scale(x,F(1,2)),scale(yx,-F(1,4))),za),
                 kron(add(scale(y,F(1,2)),scale(yx,-F(1,4))),zb))
        lr = add(kron(add(scale(x,F(1,2)),scale(xy,-F(1,4))),za),
                 kron(add(scale(y,F(1,2)),scale(xy,-F(1,4))),zb))
        difference = kron(scale(c,F(1,2)),remainder)
        expected = (add(lf,difference),lf,lr)
        for actual,wanted in zip((native,forward,reverse),expected):
            for i,j in product(range(4*h),repeat=2):
                require(actual[i][j] == wanted[i][j], 'literal full retained selected operator')
                selected_entries += 1
        fixed_phase = scale(add(x,scale(y,-1)),G(0,-1))
        tf = add(add(add(x,y),scale(yx,-1)),fixed_phase)
        tr = add(add(add(x,y),scale(xy,-1)),fixed_phase)
        require(partial_target(forward,h) == tf and partial_target(reverse,h) == tr
                and partial_target(native,h) == scale(add(tf,tr),F(1,2)),
                'fixed target G adjoint and exact operator partial traces')
        for outbit,inbit,wanted in ((1,1,d),(1,2,scale(c,F(1,2))),(2,1,zeros(h)),(2,2,scale(d,-1))):
            for i,j in product(range(h),repeat=2):
                require(native[4*i+outbit][4*j+inbit] == wanted[i][j], 'native odd triangular field block')
                triangular_entries += 1
        filters = [('identity',eye(h)),('noncommuting',matrix([[F(i+1,h+1) if i==j else 0
                                                           for j in range(h)] for i in range(h)]))]
        require(mm(filters[1][1],va) != mm(va,filters[1][1])
                and mm(filters[1][1],vb) != mm(vb,filters[1][1]), 'common field filter is noncommuting')
        sources = [('active',[(F(1),column(basis,0))]),
                   ('second',[(F(1),column(basis,1))])]
        if h == 3:
            sources += [('kernel',[(F(1),column(basis,2))]),
                        ('mixed',[(F(1,2),column(basis,0)),(F(1,2),column(basis,2))])]
        for source_name,ensemble in sources:
            tau = total((scale(outer(vector),weight) for weight,vector in ensemble),h)
            require(all(weight >= 0 for weight,_ in ensemble) and sum(weight for weight,_ in ensemble) == 1
                    and trace(tau) == 1 and all(real(trace(outer(vector))) == 1 for _,vector in ensemble),
                    'normalized independent pure or mixed field source')
            for filter_name,m in filters:
                filter_effect = gram(m)
                require(all((0 <= real(filter_effect[i][i]) <= 1) if i == j else filter_effect[i][j] == 0
                            for i,j in product(range(h),repeat=2)), 'common field filter contraction')
                lift = kron(m,eye(4))
                kn,kf,kr = (mm(lift,k) for k in (native,forward,reverse))
                effects = [gram(k) for k in (kn,kf,kr)]
                density = kron(tau,eye(4))
                masses = [real(trace(mm(effect,density)))/4 for effect in effects]
                scores = [real(trace(mm(t,mm(tau,adj(t)))))/16
                          for t in (partial_target(k,h) for k in (kn,kf,kr))]
                pn,pf,pr = masses
                gn,gf,gr = scores
                po,go = (pf+pr)/2,(gf+gr)/2
                q = real(trace(mm(m,mm(c,mm(tau,mm(adj(c),adj(m)))))))
                basis_masses = []
                for bit in (1,2):
                    block = [[effects[0][4*i+bit][4*j+bit] for j in range(h)] for i in range(h)]
                    basis_masses.append(real(trace(mm(block,tau))))
                require(basis_masses[1]-basis_masses[0] == q/4 and q >= 0, 'positive all-input acceptance contrast')
                if source_name == 'kernel':
                    require(q == 0, 'nontrivial commutator has an exact source-input kernel')
                require(pn-po == q/16 and go-gn == q/64, 'direct Choi mass and target-weight coin ledger')
                require((pn-gn)-(po-go) == 5*q/64, 'bad-weight improvement ledger')
                require(all(0 <= g <= p <= 1 for p,g in zip(masses,scores)), 'physical selected Choi probabilities')
                require(pn-gn >= q/16 and po >= gn, 'offdiagonal error and high-fidelity yield bound')
                if pn > 0:
                    require(po > 0 and go*pn >= gn*po, 'conditional target fidelity improves under ordinary order coin')
                    fn,fo = gn/pn,go/po
                    require(0 <= fn <= fo <= 1 and po >= pn*fn, 'conditional fidelity and high-fidelity yield normalization')
                    conditional_cases += 1
                delta_gram = zeros(4)
                for weight,vector in ensemble:
                    embedding = embed_vector(vector)
                    dn = mm(add(kn,scale(kf,-1)),embedding)
                    delta_gram = add(delta_gram,scale(gram(dn),weight))
                wanted = scale(gram(remainder),q/4)
                for i,j in product(range(4),repeat=2):
                    require(delta_gram[i][j] == wanted[i][j], 'full retained dilation difference operator-norm ingredient')
                    dilation_gram_entries += 1
                require(real(trace(delta_gram)) == q/2, 'retained difference Hilbert-Schmidt norm')
                if q == 0:
                    require(delta_gram == zeros(4), 'flat-contrast full selected equality on source support')
                    kernel_cases += 1
                else:
                    contrast_cases += 1
                # A few complete retained-output matrix units check the CP
                # expansion including reference coherences; no exhaustive CP grid.
                if source_name == 'active' and filter_name == 'identity':
                    embedding = embed_vector(ensemble[0][1])
                    an,af = mm(kn,embedding),mm(kf,embedding)
                    delta = add(an,scale(af,-1))
                    for a,b in ((1,2),(0,3),(2,2)):
                        for i,j in product(range(4*h),repeat=2):
                            lhs = an[i][a]*an[j][b].conj()-af[i][a]*af[j][b].conj()
                            rhs = (af[i][a]*delta[j][b].conj()+delta[i][a]*af[j][b].conj()
                                   +delta[i][a]*delta[j][b].conj())
                            require(lhs == rhs, 'retained output CP difference and passive-reference coefficient')
                            coherence_coefficients += 1
                source_filter_cases += 1
    require(contrast_cases > 0 and kernel_cases > 0, 'both nonzero contrast and exact input-kernel fixtures')
    return {'status':'passed','field_dimensions':[2,3],
            'literal_selected_matrix_entries':selected_entries,'odd_block_entries':triangular_entries,
            'source_filter_cases':source_filter_cases,'positive_contrast_cases':contrast_cases,
            'zero_contrast_cases':kernel_cases,'dilation_difference_gram_entries':dilation_gram_entries,
            'chosen_retained_CP_coefficients':coherence_coefficients,'conditional_fidelity_cases':conditional_cases,
            'target':'G=diag(1,i,-i,-1), with fixed output-local CZ correction',
            'scope':'Finite physical one-bright-sector field unitaries, literal Bell-selected native and ordinary words, common field filters and exact mass/score/error ledgers. General diamond and flat-herald proofs, continuum extension and physical source/interface/cost assumptions are outside this finite replay; no optimum or full-instrument compiler.'}


def two_port_selected_map():
    """Finite local two-port selected-map and coherent-frequency guards.

    The all-coefficient theorem and callable contraction/dilation/port
    assumptions remain in communication.md; these are not device fits.
    Every new guard stays active in an optimized extracted-body replay.
    """
    from retained_photon_serial import G, require, zeros, eye, mm, adj, add, scale

    def diag(values):
        out = zeros(len(values))
        for k, value in enumerate(values):
            out[k][k] = G(value)
        return out

    def rotation(c, s):
        return [[G(c), G(-s)], [G(s), G(c)]]

    def abs2(z):
        return (z*z.conj()).r

    def six_vertex(s0, s3, active):
        out = zeros(4)
        out[0][0], out[3][3] = G(s0), G(s3)
        for r, c in product(range(2), repeat=2):
            out[1+r][1+c] = active[r][c]
        return out

    def contact_from_singular(s0, s3, left, values, right):
        require(mm(adj(left), left) == eye(2), "left bright basis")
        require(mm(adj(right), right) == eye(2), "right bright basis")
        require(all(abs2(G(z)) <= 1 for z in (s0, s3, *values)),
                "contact singular values are contractions")
        return six_vertex(s0, s3, mm(mm(left, diag(values)), adj(right)))

    def source_contact(w, node):
        # Positive widths and kappa_ex <= kappa give passive contractions.
        # The rational constants are illustrative and are not source fits.
        kappa, kex = F(1), F(3, 4)
        dc = G(kappa, w+F(node, 5))
        de = G(F(1, 4), w-F(node, 3))
        dep = G(F(1, 3), w+F(5, 3)+F(node, 7))
        gp, gm = F(2, 3), F(3, 5)
        s0 = G(1)-G(2*kex)/dc
        sp = G(1)-G(2*kex)/(dc+G(2*gp*gp)/de)
        sm = G(1)-G(2*kex)/(dc+G(2*gm*gm)/dep)
        require(all(abs2(z) <= 1 for z in (s0, sp, sm)),
                "passive two-bright responses")
        require(sp != sm and sp != s0 and sm != s0,
                "genuine three elastic responses")
        phase = G(F(3, 5), F(4, 5)) if node else G(1)
        active = [[(sp+sm)/2, phase*(sp-sm)/2],
                  [phase.conj()*(sp-sm)/2, (sp+sm)/2]]
        return six_vertex(s0, s0, active)

    def step(state, contact, site):
        # Literal C,S,A,B basis. The source helper is never overwritten.
        out = {}
        for (c, s, a, b), value in state.items():
            bit = a if site == 0 else b
            for so, bo in product(range(2), repeat=2):
                z = contact[2*so+bo][2*s+bit]
                key = (c, so, bo, b) if site == 0 else (c, so, a, bo)
                out[key] = out.get(key, G())+z*value
        return out

    def selected(contact_a, contact_b, native=True):
        out = zeros(4)
        for a, b in product(range(2), repeat=2):
            if native:
                state = {}
                for c in range(2):
                    branch = {(c, c, a, b): G(1)}
                    if c == 0:
                        branch = step(step(branch, contact_a, 0), contact_b, 1)
                    else:
                        branch = step(step(branch, contact_b, 1), contact_a, 0)
                    for key, z in branch.items():
                        state[key] = state.get(key, G())+z
            else:
                state = step({(0, 0, a, b): G(1), (1, 1, a, b): G(1)},
                             contact_a, 0)
                # V = |00><00| - |11><11| on the preserved C/S registers.
                state = {key: z*((-1)**key[0] if key[0] == key[1] else 0)
                         for key, z in state.items()}
                state = step(state, contact_b, 1)
            for (c, s, ao, bo), z in state.items():
                if c == s:
                    out[2*ao+bo][2*a+b] += z*((-1)**c if native else 1)/2
        return out

    def expected(a, b):
        return diag([(a[x][x]*b[y][y]-a[2+x][2+x]*b[2+y][2+y])/2
                     for x, y in product(range(2), repeat=2)])

    def householder(values):
        norm = sum(abs2(G(z)) for z in values)
        out = eye(len(values))
        for i, j in product(range(len(values)), repeat=2):
            out[i][j] -= G(values[i])*G(values[j]).conj()*2/norm
        require(mm(adj(out), out) == eye(len(values)), "exact dense local bright basis")
        return out

    def dense_contact(d, node):
        vectors = ([G(1+i, (i+node) % 3-1) for i in range(2*d)],
                   [G(2+(i+node) % 3, (-1)**i) for i in range(2*d)])
        left, right = (householder(v) for v in vectors)
        values = [G(F(1+(i % 3), 5), F((-1)**i, 7)) for i in range(2*d)]
        require(all(abs2(z) <= 1 for z in values), "dense contact contraction singular values")
        out = mm(mm(left, diag(values)), adj(right))
        require(out[0][1] != 0 and out[0][d] != 0,
                "dense contact does not preserve displayed excitation number")
        return out

    def general_step(state, contact, site, da, db):
        out = {}
        d = da if site == 0 else db
        for (c, s, a, b), value in state.items():
            bit = a if site == 0 else b
            for so, bo in product(range(2), range(d)):
                z = contact[d*so+bo][d*s+bit]
                key = (c, so, bo, b) if site == 0 else (c, so, a, bo)
                out[key] = out.get(key, G())+z*value
        return out

    def general_selected(ta, tb, da, db, native=True):
        out = zeros(da*db)
        for a, b in product(range(da), range(db)):
            if native:
                state = {}
                for c in range(2):
                    branch = {(c, c, a, b): G(1)}
                    if c == 0:
                        branch = general_step(general_step(branch, ta, 0, da, db), tb, 1, da, db)
                    else:
                        branch = general_step(general_step(branch, tb, 1, da, db), ta, 0, da, db)
                    for key, z in branch.items():
                        state[key] = state.get(key, G())+z
            else:
                state = general_step({(0, 0, a, b): G(1), (1, 1, a, b): G(1)}, ta, 0, da, db)
                state = {key: z*((-1)**key[0] if key[0] == key[1] else 0)
                         for key, z in state.items()}
                state = general_step(state, tb, 1, da, db)
            for (c, s, ao, bo), z in state.items():
                if c == s:
                    out[db*ao+bo][db*a+b] += z*((-1)**c if native else 1)/2
        return out

    def general_expected(ta, tb, da, db):
        out = zeros(da*db)
        for ao, bo, ai, bi in product(range(da), range(db), range(da), range(db)):
            out[db*ao+bo][db*ai+bi] = (tb[bo][bi]*ta[ao][ai]
                -tb[db+bo][db+bi]*ta[da+ao][da+ai])/2
        return out

    r = rotation(F(3, 5), F(4, 5))
    t = rotation(F(5, 13), F(12, 13))
    algebraic = (
        (contact_from_singular(G(F(2, 3), F(1, 5)), F(1, 3), r,
             (G(F(1, 2), F(1, 3)), G(F(-2, 5), F(1, 5))), t),
         contact_from_singular(F(4, 5), G(F(1, 4), F(-1, 3)), t,
             (G(F(3, 5), F(-2, 5)), F(-1, 2)), r)),
        (six_vertex(1, G(0, 1), [[G(), G(1)], [G(0, 1), G()]]),
         six_vertex(G(0, -1), 1, [[G(F(3, 5)), G(F(4, 5))],
                                 [G(F(-4, 5)), G(F(3, 5))]])),
    )
    point_entries = cp_coefficients = 0
    for a, b in algebraic:
        n, o, e = selected(a, b), selected(a, b, False), expected(a, b)
        require(n == e, "literal native six-vertex selected operator")
        require(o == e, "ordinary V selected operator")
        point_entries += 32
        for r0, c0, r1, c1 in product(range(4), repeat=4):
            require(n[r0][c0]*n[r1][c1].conj() ==
                    o[r0][c0]*o[r1][c1].conj(), "full AB/R CP coefficient")
            cp_coefficients += 1
    # Frequency is an actual retained coherent output register, not a
    # classical mixture. Test every pair of frequency/input/output indices.
    bins = (F(-2, 5), F(0), F(3, 7))
    ns, os = [], []
    for w in bins:
        a, b = source_contact(w, 0), source_contact(w, 1)
        n, o, e = selected(a, b), selected(a, b, False), expected(a, b)
        require(n == o == e, "two-bright elastic source reduction")
        ns.append(n)
        os.append(o)
        point_entries += 32
    frequency_coefficients = cross_frequency = 0
    for f, g, r0, c0, r1, c1 in product(range(3), range(3),
                                      range(4), range(4), range(4), range(4)):
        require(ns[f][r0][c0]*ns[g][r1][c1].conj() ==
                os[f][r0][c0]*os[g][r1][c1].conj(),
                "coherent retained-frequency full-reference CP coefficient")
        frequency_coefficients += 1
        cross_frequency += int(f != g)
    require(any(ns[0][r][r]*ns[1][c][c].conj() != 0
                for r, c in product(range(4), repeat=2)),
            "cross-frequency test is nonvacuous")
    dense_entries = dense_cp = local_qutrit_entries = 0
    dense_pairs = ((2, 2), (3, 3))
    for da, db in dense_pairs:
        ta, tb = dense_contact(da, 0), dense_contact(db, 1)
        n = general_selected(ta, tb, da, db)
        o = general_selected(ta, tb, da, db, False)
        e = general_expected(ta, tb, da, db)
        require(n == e, "dense local-block native source and terminal flag")
        require(o == e, "dense local-block ordinary midpoint source and flag")
        dense_entries += 2*(da*db)**2
        if da == 3:
            require(any(n[db*2+b][db*a+bi] != 0 for a, bi, b in
                        product(range(2), range(2), range(db))),
                    "local qutrit output includes populated code exits")
            local_qutrit_entries += 2*(da*db)**2
        for r0, c0, r1, c1 in product(range(da*db), repeat=4):
            require(n[r0][c0]*n[r1][c1].conj() ==
                    o[r0][c0]*o[r1][c1].conj(),
                    "dense local-block full input-reference CP coefficient")
            dense_cp += 1
    return {"dense_local_memory_pairs": [list(p) for p in dense_pairs],
            "dense_literal_selected_entries": dense_entries,
            "local_qutrit_selected_entries": local_qutrit_entries,
            "dense_full_reference_coefficients": dense_cp,
            "algebraic_contraction_pairs": len(algebraic),
            "two_bright_frequency_bins": len(bins),
            "literal_selected_entries": point_entries,
            "full_AB_reference_coefficients": cp_coefficients,
            "retained_frequency_coefficients": frequency_coefficients,
            "off_diagonal_frequency_coefficients": cross_frequency,
            "scope": "Finite selected-map identities only; arbitrary local two-port/commuting-multiplier proof and full physical loss/router instrument remain analytic or supplied."}




def inelastic_gate_remainder():
    """Exact stationary Raman shifts, flags and selected-gate ingredients.

    Fixtures use a nonperiodic frequency line and are not a converter fit.
    Universal TNI/decoder and physical port/dilation statements are analytic.
    Every new guard stays active in an optimized extracted-body replay.
    """
    from retained_photon_serial import G, require, eye, zeros, mm, adj, add, scale

    def norm(values):
        return sum((z*z.conj()).r for z in values)

    def response(energy, node, flat=False):
        if flat:
            return G(F(3, 5)), G(0, F(4, 5))
        delta = G(energy-F(node, 2))
        denominator = delta+G(0, 1)
        t, r = delta/denominator, G(0, -1)/denominator
        require((t*t.conj()+r*r.conj()) == 1 and
                t*r.conj()+r*t.conj() == 0, "energy-sector unitary contact")
        return t, r

    def step(state, node, gaps, flat=False):
        out = {}
        gap = gaps[node]
        for (c, s, a, b, w), z in state.items():
            bit = a if node == 0 else b
            key = (c, s, a, b, w)
            if s == bit:
                out[key] = out.get(key, G())+z
            else:
                t, r = response(w+gap*bit, node, flat)
                out[key] = out.get(key, G())+z*t
                # Physical energy conservation; there is no cyclic wrap.
                target = ((c, bit, s, b, w+gap*(bit-s)) if node == 0 else
                          (c, bit, a, s, w+gap*(bit-s)))
                out[target] = out.get(target, G())+z*r
        return {key: z for key, z in out.items() if z != 0}

    def frequency_range():
        return tuple(range(-4, 5))

    def index(w, a, b):
        return 4*(w+4)+2*a+b

    def circuit(packet, gaps, native, flat=False):
        flags = {(m, n): zeros(36, 4) for m, n in product(range(2), repeat=2)}
        reject = zeros(144, 4)
        for a, b in product(range(2), repeat=2):
            col = 2*a+b
            if native:
                state = {}
                for c in range(2):
                    branch = {(c, c, a, b, w): z for w, z in packet.items()}
                    first, second = (0, 1) if c == 0 else (1, 0)
                    branch = step(step(branch, first, gaps, flat), second, gaps, flat)
                    for key, z in branch.items():
                        state[key] = state.get(key, G())+z
            else:
                state = {(c, c, a, b, w): z for c in range(2) for w, z in packet.items()}
                state = step(state, 0, gaps, flat)
                kept = {}
                for (c, s, ao, bo, w), z in state.items():
                    if c == s:
                        kept[(c, s, ao, bo, w)] = z*((-1)**c)
                    else:
                        reject[36*(2*c+s)+index(w, ao, bo)][col] += z
                state = step(kept, 1, gaps, flat)
            for (c, s, ao, bo, w), z in state.items():
                require(w in frequency_range(), "all output frequency records retained")
                for m, n in product(range(2), repeat=2):
                    if s == (c ^ m):
                        flags[(m, n)][index(w, ao, bo)][col] += z*((-1)**(n*c))/2
        return flags, reject

    def diagonal(node, s, bit, w, gaps, flat):
        return G(1) if s == bit else response(w+gaps[node]*bit, node, flat)[0]

    def commutator_packet(packet, gaps, flat=False):
        out = {}
        ga, gb = gaps
        for w, value in packet.items():
            p_then_q = response(w+ga, 0, flat)[1]*response(w+ga, 1, flat)[1]
            q_then_p = response(w, 1, flat)[1]*response(w+ga-gb, 0, flat)[1]
            out[w+ga-gb] = (p_then_q-q_then_p)*value
        return out

    def expected(packet, gaps, flat=False):
        ordinary = zeros(36, 4)
        for a, b in product(range(2), repeat=2):
            for w, value in packet.items():
                coefficient = (diagonal(0, 0, a, w, gaps, flat)*diagonal(1, 0, b, w, gaps, flat)
                             -diagonal(0, 1, a, w, gaps, flat)*diagonal(1, 1, b, w, gaps, flat))/2
                ordinary[index(w, a, b)][2*a+b] += coefficient*value
        native = [list(row) for row in ordinary]
        for w, value in commutator_packet(packet, gaps, flat).items():
            native[index(w, 0, 1)][2] += value/2
        return native, ordinary

    def filtered(matrix, field_filter):
        out = zeros(36, 4)
        for wo, wi, a, b, col in product(range(9), range(9), range(2), range(2), range(4)):
            out[4*wo+2*a+b][col] += field_filter[wo][wi]*matrix[4*wi+2*a+b][col]
        return out

    def field_filters():
        # A complex noncommuting spectral processor is a PAID hypothetical port.
        vector = [G(1, (i % 3)-1) for i in range(9)]
        house = eye(9)
        weight = norm(vector)
        for i, j in product(range(9), repeat=2):
            house[i][j] -= vector[i]*vector[j].conj()*2/weight
        require(mm(adj(house), house) == eye(9), "spectral mixing is unitary")
        diagonal_filter = zeros(9)
        for i in range(9):
            diagonal_filter[i][i] = G(F(i % 4, 3))
        kill_shift = zeros(9)
        kill_shift[4][4] = G(1)
        filters = {"identity": [eye(9)],
                   "two_record_complex": [scale(mm(house, diagonal_filter), F(3, 5)),
                                          scale(eye(9), F(4, 5))],
                   "zero_frequency": [kill_shift]}
        for records in filters.values():
            effect = zeros(9)
            for m in records:
                effect = add(effect, mm(adj(m), m))
            defect = add(eye(9), scale(effect, -1))
            require(all(defect[i][j] == 0 for i, j in product(range(9), repeat=2) if i != j)
                    and all(defect[i][i].i == 0 and defect[i][i].r >= 0 for i in range(9)),
                    "common field filter has a positive diagonal CP/TNI defect")
        return filters

    def mass(matrix):
        return sum(norm(row) for row in matrix)/4

    def good(matrix, target):
        return sum(norm([sum(target[ab].conj()*matrix[4*w+ab][ab] for ab in range(4))])
                   for w in range(9))/16

    def unitary_targets():
        rotation = eye(4)
        rotation[1][1], rotation[2][2] = G(F(3, 5)), G(F(3, 5))
        rotation[1][2], rotation[2][1] = G(F(4, 5)), G(F(-4, 5))
        vector = [G(1), G(0, 1), G(2), G(-1)]
        house = eye(4)
        for i, j in product(range(4), repeat=2):
            house[i][j] -= vector[i]*vector[j].conj()*2/norm(vector)
        targets = (eye(4), rotation, house)
        for u in targets:
            require(mm(adj(u), u) == eye(4), "full unitary target")
            diagonal_weight = sum(norm([u[i][i]]) for i in range(4))/4
            jump_weight = norm([u[1][2]])/4
            require(diagonal_weight+2*jump_weight <= 1,
                    "unitary cut-flow and weighted support metric ingredient")
        return targets

    def arbitrary_unitary_good(matrix, target):
        return sum(norm([sum(target[i][j].conj()*matrix[4*w+i][j]
                             for i, j in product(range(4), repeat=2))])
                   for w in range(9))/16

    def cp_map(matrix, i, j):
        # Exact sparse full-output map of |i><j|, including all zero blocks.
        return {(r, s): matrix[r][i]*matrix[s][j].conj()
                for r, s in product(range(36), repeat=2)
                if matrix[r][i] != 0 and matrix[s][j] != 0}

    packets = {"coherent": {-1: G(F(1, 3)), 0: G(0, F(2, 3)), 1: G(F(2, 3))},
               "single": {0: G(1)}}
    require(all(norm(packet.values()) == 1 for packet in packets.values()), "normalized independent field sources")
    filters = field_filters()
    target = [G(1), G(0, 1), G(0, -1), G(-1)]
    counts = {"native_complete_instruments": 0, "ordinary_complete_instruments": 0,
              "selected_entries": 0, "full_reference_units": 0,
              "source_filter_ledgers": 0, "positive_error_cases": 0,
              "zero_error_cases": 0, "dilation_gram_entries": 0,
              "near_unitary_support_cases": 0}
    coherent_cross = False
    for flat, source in product((False, True), packets):
        packet, gaps = packets[source], (1, 2)
        nflags, _ = circuit(packet, gaps, True, flat)
        oflags, rejected = circuit(packet, gaps, False, flat)
        require(sum(mass(k) for k in nflags.values()) == 1, "all native flags have unit total Choi mass")
        ng = zeros(4)
        og = scale(mm(adj(rejected), rejected), F(1, 2))
        for key in nflags:
            ng = add(ng, mm(adj(nflags[key]), nflags[key]))
            og = add(og, mm(adj(oflags[key]), oflags[key]))
        require(ng == eye(4), "native four-flag full-input trace preservation")
        require(og == eye(4), "ordinary early reject and four late flags trace preservation")
        counts["native_complete_instruments"] += 1
        counts["ordinary_complete_instruments"] += 1
        n, o = nflags[(0, 1)], oflags[(0, 0)]
        en, eo = expected(packet, gaps, flat)
        require(n == en and o == eo, "literal weighted-translation source and selected map")
        counts["selected_entries"] += 288
        # Exact nonnormal weighted-translation witness, not a generic 2x2 unitary.
        if not flat:
            require(norm([response(1, 0)[1]]) != norm([response(0, 0)[1]]),
                    "Raman frequency shift has nonnormal weight")
        for name, record_filters in filters.items():
            if source != "single" and name == "zero_frequency":
                continue
            an = [filtered(n, m) for m in record_filters]
            ao = [filtered(o, m) for m in record_filters]
            dn = [add(x, scale(y, -1)) for x, y in zip(an, ao)]
            jvec = zeros(9, 1)
            for w, z in commutator_packet(packet, gaps, flat).items():
                jvec[w+4][0] += z
            q = sum(norm(row) for m in record_filters for row in mm(m, jvec))
            pn, po = sum(map(mass, an)), sum(map(mass, ao))
            gn, go = sum(good(k, target) for k in an), sum(good(k, target) for k in ao)
            require(pn-po == q/16 and gn == go, "same Bell-good mass and exact added accepted error")
            require((pn-gn)-(po-go) == q/16 and po >= gn, "accepted-error and high-fidelity yield ledger")
            if po:
                require(go*pn >= gn*po, "ordinary conditional Choi fidelity is no lower")
                require(po >= gn, "ordinary retains at least native good mass")
            else:
                require(gn == 0, "zero ordinary acceptance has no native target weight")
            gram = zeros(4)
            for delta in dn:
                gram = add(gram, mm(adj(delta), delta))
            wanted = zeros(4)
            wanted[2][2] = G(q/4)
            require(gram == wanted, "retained filtered dilation difference and half-diamond norm ingredient")
            counts["dilation_gram_entries"] += 16
            for u in unitary_targets():
                gu = sum(arbitrary_unitary_good(k, u) for k in an)
                require(gu <= pn-q/32, "arbitrary unitary target near-support bound ingredient")
                counts["near_unitary_support_cases"] += 1
            for actual, prediction in ((an, [filtered(en, m) for m in record_filters]),
                                       (ao, [filtered(eo, m) for m in record_filters])):
                for raw, predicted in zip(actual, prediction):
                    for i, j in product(range(4), repeat=2):
                        require(cp_map(raw, i, j) == cp_map(predicted, i, j),
                                "all AB/reference matrix units with retained frequency and filter record")
                        counts["full_reference_units"] += 1
            # Acceptance order is NOT pointwise on all coherent data inputs.
            cross = sum(mm(adj(x), d)[1][2] for x, d in zip(ao, dn))
            coherent_cross = coherent_cross or cross != 0
            counts["source_filter_ledgers"] += 1
            counts["positive_error_cases" if q else "zero_error_cases"] += 1
    require(coherent_cross, "coherent input acceptance cross term retained; no CP/order dominance")
    require(counts["positive_error_cases"] and counts["zero_error_cases"], "nonzero and erased/flat commutator cases")
    return {"status": "passed", **counts,
            "scope": "Declared stationary lossless Raman energy-sector fixtures and common paid field filters. General CPTNI bound, triangular-unitary argument, source/interface and converter costs remain analytic; no actual converter fit, full bath-loss instrument or all-readout optimum."}


def verify_raman_stronger_baselines():
    from verify_raman_bell_certificate import verify
    return {
        "status": "passed",
        "same_helper_passive_filter": verify_raman_passive_filter(),
        "local_ancilla_instruments": raman_local_ancilla_examples(),
        "unknown_coefficient_projections": raman_uniform_ancilla_examples(),
        "ordered_auxiliary_operator_projection": raman_operator_ancilla_examples(),
        "fixed_beta_ordinary_lower_bound": verify(Path(__file__).with_name("raman_bell_certificate.json")),
        "source_and_occupied_visit_frontier": verify_raman_source_clock_frontier(),
        "balanced_cavity_frontier": verify_raman_cavity_frontier(),
        "bare_swap_gate_rank": bare_swap_rank_guards(),
        "partial_swap_cz_instruments": partial_swap_gate_instruments(),
        "operator_partial_swap_frontier": operator_partial_swap_frontier(),
        "two_port_selected_map": two_port_selected_map(),
        "inelastic_gate_remainder": inelastic_gate_remainder(),
        "scope": "Exact achievable ordinary instruments and polynomial identities. No ordinary optimum, source/clock advantage, microscopic device fit or native architecture advantage is asserted."
    }

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
        "scope": "Exact achievable ordinary instruments and polynomial identities. No ordinary optimum, source/clock advantage, microscopic device fit or native architecture advantage is asserted."
    }

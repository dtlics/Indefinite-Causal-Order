"""Full matrix-unit coefficient kernels for the audited phase restrictions.

All entries are rational. No unitary-context sampling is used. The Gram
matrices sum every coefficient defect, and their exact rational kernels are
then made reducing for the actual normalized single-query representation.
"""
from pathlib import Path
from itertools import product
import json
import numpy as np
import sympy as s
from exact_fixtures import E, WORDS

ROOT = Path(__file__).parent
I16 = s.eye(16)
UNITS = list(product(range(2), repeat=2))
LABELS = list(product(range(4), repeat=4))


def row_tensor(which, sign):
    """Return integer coefficients 4F_new, normalized at all identities."""
    base = np.zeros((16, 16, 16), dtype=np.int64)
    masks = np.zeros((16, 16), dtype=np.int64)
    for o, ow in enumerate(WORDS):
        for a, aw in enumerate(WORDS):
            v = 4*s.eye(16)[a, :] - sum(
                (8*E[i][a, :] for i in range(4) if ow[i] != aw[i]),
                s.zeros(1, 16))
            assert all(x.is_Integer for x in v)
            base[o, a] = [int(x) for x in v]
            if which == 4:
                masks[o, a] = int(ow[1] == 0 and
                    ((aw[0] == 0 and aw[3] == 0) or
                     (aw[0] == 1 and aw[2] == 0)))
            elif which == 5:
                masks[o, a] = int(ow[3] == 0 and
                    (aw[2] == 0 or (aw[0] == 0 and aw[1] == 1 and aw[2] == 1)))
    origin = np.diag(masks.diagonal())
    assert np.array_equal(origin @ origin, origin)
    # K_z inverse is K_z for z in {+1,-1}; the origin projection is diagonal.
    norm = 1+(sign-1)*masks.diagonal()
    return base*(1+(sign-1)*masks[:, :, None])*norm[None, None, :]


def coefficient_table(T):
    coeff = {}
    for lab in LABELS:
        ow = [UNITS[k][0] for k in lab]
        aw = [UNITS[k][1] for k in lab]
        o = sum(x << (3-i) for i, x in enumerate(ow))
        a = sum(x << (3-i) for i, x in enumerate(aw))
        mat = np.zeros((16, 16), dtype=np.int64)
        mat[o] = T[o, a]
        coeff[lab] = mat
    return coeff


def specialize(coeff, selected):
    """Unselected variables are identities, i.e. sums of their diagonal units."""
    out = {}
    other = [i for i in range(4) if i not in selected]
    for active in product(range(4), repeat=len(selected)):
        mat = np.zeros((16, 16), dtype=np.int64)
        for diag in product([0, 3], repeat=len(other)):
            key = [0]*4
            for i, a in zip(selected, active): key[i] = a
            for i, a in zip(other, diag): key[i] = a
            mat += coeff[tuple(key)]
        out[active] = mat
    return out


def kernel_projector(gram):
    M = s.Matrix(gram.tolist()) if isinstance(gram, np.ndarray) else gram
    ns = M.nullspace()
    B = s.Matrix.hstack(*ns) if ns else s.zeros(16, 0)
    Q = B*(B.H*B).inv()*B.H if ns else s.zeros(16)
    assert Q.H == Q and Q*Q == Q and M*Q == s.zeros(16)
    return B, Q


def encode(M):
    return [[str(x) for x in row] for row in M.tolist()]


def run_one(which, sign):
    coeff = coefficient_table(row_tensor(which, sign))
    assert np.array_equal(specialize(coeff, [])[()], 4*np.eye(16, dtype=np.int64))
    answer = {'phase_projector_rank': which, 'phase': sign, 'ports': []}
    projectors = {'first': [], 'last': []}
    for i in range(4):
        singles = specialize(coeff, [i])
        assert all(np.max(np.abs(A)) <= 4 for A in singles.values())
        actual = [s.Matrix(singles[(k,)].tolist())/4 for k in range(4)]
        assert actual[0]+actual[3] == I16
        for a, (r, t) in enumerate(UNITS):
            assert actual[a].H == actual[UNITS.index((t, r))]
            for b, (u, v) in enumerate(UNITS):
                expect = actual[UNITS.index((r, v))] if t == u else s.zeros(16)
                assert actual[a]*actual[b] == expect
        others = [j for j in range(4) if j != i]
        bars = specialize(coeff, others)
        assert all(np.max(np.abs(B)) <= 4 for B in bars.values())
        grams = {'first': np.zeros((16,16), dtype=np.int64),
                 'last': np.zeros((16,16), dtype=np.int64)}
        defects = {'first': [], 'last': []}
        maxdef = 0
        for lab in LABELS:
            A = singles[(lab[i],)]
            B = bars[tuple(lab[j] for j in others)]
            for name, D in [('first', 4*coeff[lab]-B@A),
                            ('last', 4*coeff[lab]-A@B)]:
                maxdef = max(maxdef, int(np.max(np.abs(D))))
                defects[name].append(D)
                grams[name] += D.T@D if name == 'first' else D@D.T
        # Every entry in a Gram sum has magnitude at most this integer bound.
        integer_bound = 256*16*maxdef**2
        assert maxdef <= 4*4+16*4*4
        assert integer_bound < 2**63
        rec = {'query': i+1, 'integer_Gram_bound': integer_bound,
               'single_matrix_units': [encode(A) for A in actual]}
        for name in ['first', 'last']:
            Braw, Qraw = kernel_projector(grams[name])
            # Largest invariant (hence reducing) subspace in the raw kernel.
            G = s.Matrix(grams[name].tolist())
            reduced_gram = sum((A.H*G*A for A in actual), s.zeros(16))
            Bred, Qred = kernel_projector(reduced_gram)
            assert Qraw*Qred == Qred
            assert all(Qred*A == A*Qred for A in actual)
            # Independent final coefficientwise verification on the projector.
            for D in defects[name]:
                DD = s.Matrix(D.tolist())
                assert (DD*Qred if name == 'first' else Qred*DD) == s.zeros(16)
            projectors[name].append(Qred)
            rec[name] = {'raw_kernel_rank': Braw.cols,
                         'reducing_carrier_rank': Bred.cols,
                         'raw_kernel_already_reduces': Qraw == Qred,
                         'basis': encode(Bred), 'projector': encode(Qred),
                         'all_256_coefficient_defects_annihilated': True}
        answer['ports'].append(rec)
        print('phase', which, sign, 'query', i+1,
              'first', rec['first']['reducing_carrier_rank'],
              'last', rec['last']['reducing_carrier_rank'], flush=True)
    for name, Ps in projectors.items():
        answer[name+'_union_rank'] = s.Matrix.hstack(*Ps).rank()
        answer[name+'_pairwise_orthogonal'] = all(Ps[i]*Ps[j] == s.zeros(16)
                                                for i in range(4) for j in range(i))
        answer[name+'_sum_rank'] = sum(int(s.trace(P)) for P in Ps)
    return answer


if __name__ == '__main__':
    results = [run_one(4, 1), run_one(4, -1), run_one(5, -1)]
    def decode(M):
        return s.Matrix([[s.sympify(x) for x in row] for row in M])
    original = [decode(p['first']['projector']) for p in results[0]['ports']]
    for variant, inds in [(1, [0,2,8,9]), (2, [0,4,6,8,12])]:
        K = s.diag(*[-1 if n in inds else 1 for n in range(16)])
        target = original.copy()
        if variant == 1:
            target[0] = E[0]
        for i, p in enumerate(results[variant]['ports']):
            assert decode(p['first']['projector']) == K*target[i]*K
        results[variant]['carrier_formula_verified'] = (
            'K4 (E1,S2,S3,S4) K4' if variant == 1 else 'K5 (S1,S2,S3,S4) K5')
    report = {'status': 'PASS', 'coefficient_basis': 'all 4^4 tensor products of 2x2 matrix units',
              'meaning': 'Exact maximal fixed first/last serial-query carriers, reducing actual normalized singles',
              'results': results,
              'plus_phase': 'Both plus-phase restrictions equal the original normalized quartet.',
              'scope': 'Restrictions only; no routed realization of either complete phase family is inferred.'}
    (ROOT/'phase_endpoint_exact_checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: full coefficientwise endpoint kernels', flush=True)

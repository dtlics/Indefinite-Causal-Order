"""Exact finite field-pilot fixtures; no measured fiber or readout model."""
from fractions import Fraction as F
from itertools import product
import json

if not __debug__:
    raise RuntimeError('Run exact field-pilot fixtures without -O.')
from verify_fault_simulation import (ZERO, ONE, gaussian, add, times,
                                     multiply, conjugate, identity, matmul)


def inner(x, y):
    out = ZERO
    for a, b in zip(x, y):
        out = add(out, multiply(conjugate(a), b))
    return out


def vplus(x, y):
    return [add(a, b) for a, b in zip(x, y)]


def norm(x):
    out = inner(x, x)
    assert out[1] == 0
    return out[0]


def check():
    # Arbitrary rectangular measured/predicted fields, three input columns.
    t = [[gaussian(F(1, 2)), gaussian(0, F(2, 3)), gaussian(F(1, 5), F(1, 7))],
         [gaussian(F(1, 4), F(-1, 6)), ZERO, gaussian(F(-2, 5))]]
    m = [[gaussian(F(1, 3)), gaussian(0, F(1, 2)), gaussian(F(2, 7))],
         [gaussian(F(1, 5)), gaussian(F(1, 6)), gaussian(F(-1, 3))]]
    residuals = [[add(t[i][j], times(m[i][j], -1)) for i in range(2)]
                 for j in range(3)]
    column_mean = sum((norm(r) for r in residuals), F(0))/3
    frob = sum((norm([add(a, times(b, -1)) for a, b in zip(ta, ma)])
                for ta, ma in zip(t, m)), F(0))/3
    assert column_mean == frob
    r = [gaussian(F(3, 5), F(4, 5)), gaussian(F(1, 3), F(-2, 7))]
    noise_reports = []
    for scales in [(F(1, 2), F(1, 2)), (F(1, 2), F(3, 5))]:
        phases = [ONE, gaussian(-1), gaussian(0, 1), gaussian(0, -1)]
        errors = [[times(z, s) for z, s in zip(zs, scales)]
                  for zs in product(phases, repeat=2)]
        count = len(errors)**2
        values = [inner(vplus(r, e1), vplus(r, e2))[0]
                  for e1 in errors for e2 in errors]
        avg = sum(values, F(0))/count
        var = sum(((y-avg)**2 for y in values), F(0))/count
        nus = [s*s for s in scales]
        predicted_var = sum((nu*norm([x]) for nu, x in zip(nus, r)), F(0))
        predicted_var += sum((nu*nu for nu in nus), F(0))/2
        assert avg == norm(r)
        assert var == predicted_var
        # Independent repeats matter: shared noise retains squared-noise bias.
        shared_avg = sum((norm(vplus(r, e)) for e in errors), F(0))/len(errors)
        assert shared_avg == norm(r)+sum(nus)
        noise_reports.append({'noise_covariance_diagonal': [str(x) for x in nus],
                              'independent_pair_cases': count,
                              'unbiased_mean': str(avg), 'variance': str(var)})
    # Exact endpoint of T(delta)=diag(exp(iKdelta^2),exp(-iKdelta^2)).
    tdelta = [[gaussian(0, 1), ZERO], [ZERO, gaussian(0, -1)]]
    assert matmul(tdelta, identity(2)) == matmul(identity(2), tdelta)
    assert add(tdelta[0][0], tdelta[1][1]) == ZERO
    endpoint_residual = sum((norm([add(tdelta[i][j],
                                     times(identity(2)[i][j], -1))
                                  for i in range(2)]) for j in range(2)), F(0))/2
    assert endpoint_residual == 2
    assert norm([tdelta[0][0]]) == norm([tdelta[1][1]]) == 1
    return {'status': 'passed', 'rectangular_column_mean_residual': str(column_mean),
            'noise_cases': noise_reports, 'normal_unitary_endpoint_overlap': '0',
            'normal_unitary_endpoint_mean_residual': str(endpoint_residual),
            'scope': 'Finite exact declared field/noise identities only; no measured power/noise/phase bound, physical adjoint, native rate, or hardware advantage certificate.'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))

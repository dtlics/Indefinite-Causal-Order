"""Exact real-rational diagram sum-of-squares certificates.

This module never uses an eigensolver or an irreducible representation.  It
checks a sufficient condition for positivity of the actual tensor operator

    S = sum_j X_j^dagger X_j + R,
    R = r_0 I + sum_{i != 0} r_i B_i.

If S is coefficientwise Hermitian and

    margin = r_0 - sum_{i != 0} |r_i| D**cups(B_i) >= 0,

then S >= margin I >= 0.  All coefficient arithmetic uses fractions.Fraction.
Floating-point input is rejected rather than silently rationalized.  Factors
are real-rational algebra elements; they need not themselves be Hermitian.

Why the norm bound is exact: a pairing has c top cups, c bottom caps, and
n-2c through lines.  Independent unitary permutations of its output and input
tensor factors put its operator into cups tensor caps tensor identity form.
An unnormalized cup/cap has norm sqrt(D), so ||B_i|| = D**c.  Equivalently,
every nonzero singular value is D**c, of multiplicity D**(n-2c).

The replay multiplication table is recomputed from diagram composition in
memory.  It does not trust the on-disk numerical-search cache.  JSON reports
are descriptive only: replay recomputes the residual and the exact margin.
"""
from __future__ import annotations
if not __debug__:
    raise RuntimeError('Exact SOS replay requires Python without -O.')

from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
import argparse
import json
import math
from numbers import Integral
from pathlib import Path
from typing import Iterable, Sequence

from brauer_exact_replay import ExactBrauerAlgebra as BrauerAlgebra


_EXACT_TABLES = {}
_SCHEMA = 'brauer-real-rational-sos-v1'


def _fraction(value) -> Fraction:
    """Accept exact rationals only; a float must be rounded by the caller."""
    if isinstance(value, Fraction):
        return value
    if isinstance(value, Integral) and not isinstance(value, bool):
        return Fraction(int(value))
    if isinstance(value, str):
        return Fraction(value)
    raise TypeError(f'Expected Fraction, integer, or rational string; got {type(value).__name__}')


def exact_coefficients(algebra: BrauerAlgebra, coefficients: Sequence) -> tuple[Fraction, ...]:
    """Validate one dense coefficient array and convert it to Fractions."""
    if len(coefficients) != algebra.size:
        raise ValueError(f'Expected {algebra.size} coefficients, received {len(coefficients)}')
    return tuple(_fraction(value) for value in coefficients)


def _integer_vector(coefficients: Sequence[Fraction]):
    denominator = reduce(math.lcm, (c.denominator for c in coefficients), 1)
    return [c.numerator * (denominator // c.denominator) for c in coefficients], denominator


def _exact_table(algebra: BrauerAlgebra):
    key = algebra.signature
    if key not in _EXACT_TABLES:
        # A fresh object has no loaded table; its multiply() calls the direct
        # integer graph-composition implementation rather than reading cache.
        fresh = BrauerAlgebra(key)
        index, loops = fresh.multiplication_table()
        _EXACT_TABLES[key] = index, loops
    return _EXACT_TABLES[key]


def coefficient_product(algebra: BrauerAlgebra, D: int, left: Sequence, right: Sequence) -> tuple[Fraction, ...]:
    """Exact coefficients of left*right; all scalar diagram loops are included."""
    D = _positive_dimension(D)
    a, denominator_a = _integer_vector(exact_coefficients(algebra, left))
    b, denominator_b = _integer_vector(exact_coefficients(algebra, right))
    index, loops = _exact_table(algebra)
    powers = [D**k for k in range(algebra.n + 1)]
    output = [0] * algebra.size
    nonzero_b = [(j, value) for j, value in enumerate(b) if value]
    for i, value_a in enumerate(a):
        if not value_a:
            continue
        for j, value_b in nonzero_b:
            output[int(index[i][j])] += value_a * value_b * powers[int(loops[i][j])]
    denominator = denominator_a * denominator_b
    return tuple(Fraction(value, denominator) for value in output)


def star_coefficients(algebra: BrauerAlgebra, coefficients: Sequence) -> tuple[Fraction, ...]:
    """Exact adjoint coefficients for a real-rational algebra element."""
    coefficients = exact_coefficients(algebra, coefficients)
    return tuple(coefficients[int(algebra.star[i])] for i in range(algebra.size))


def coefficient_sum(algebra: BrauerAlgebra, *terms: Sequence) -> tuple[Fraction, ...]:
    """Exact sum, including a zero element when no terms are supplied."""
    output = [Fraction(0)] * algebra.size
    for term in terms:
        for i, value in enumerate(exact_coefficients(algebra, term)):
            output[i] += value
    return tuple(output)


def partial_trace_coefficients(algebra: BrauerAlgebra, D: int, coefficients: Sequence, remove_wire: int):
    """Return (target algebra, exact coefficient array) after a wire trace."""
    D = _positive_dimension(D)
    coefficients = exact_coefficients(algebra, coefficients)
    target, indices, loops = algebra.partial_trace_map(remove_wire)
    output = [Fraction(0)] * target.size
    for i, value in enumerate(coefficients):
        output[int(indices[i])] += value * D**int(loops[i])
    return target, tuple(output)


def insert_identity_coefficients(algebra: BrauerAlgebra, coefficients: Sequence, position: int, sign: int):
    """Return (target algebra, exact coefficients) after identity insertion."""
    coefficients = exact_coefficients(algebra, coefficients)
    target, indices = algebra.insert_identity_map(position, sign)
    output = [Fraction(0)] * target.size
    for i, value in enumerate(coefficients):
        output[int(indices[i])] += value
    return target, tuple(output)


def sos_residual(algebra: BrauerAlgebra, D: int, slack: Sequence, factors: Iterable[Sequence]) -> tuple[Fraction, ...]:
    """Exact coefficients of S - sum_j X_j^dagger X_j."""
    residual = list(exact_coefficients(algebra, slack))
    for factor in factors:
        factor = exact_coefficients(algebra, factor)
        square = coefficient_product(algebra, D, star_coefficients(algebra, factor), factor)
        residual = [a - b for a, b in zip(residual, square)]
    return tuple(residual)


@dataclass(frozen=True)
class PSDReport:
    hermitian: bool
    residual: tuple[Fraction, ...]
    identity_coefficient: Fraction
    nonidentity_radius: Fraction
    margin: Fraction
    verified: bool

    def to_dict(self, include_residual: bool = True):
        result = {
            'hermitian': self.hermitian,
            'identity_coefficient': str(self.identity_coefficient),
            'nonidentity_radius': str(self.nonidentity_radius),
            'margin': str(self.margin),
            'verified': self.verified,
        }
        if include_residual:
            result['residual'] = [str(value) for value in self.residual]
        return result


def _positive_dimension(D):
    if not isinstance(D, Integral) or isinstance(D, bool) or int(D) < 1:
        raise ValueError('D must be a positive integer')
    return int(D)


def certify_psd(algebra: BrauerAlgebra, D: int, slack: Sequence, factors: Iterable[Sequence] = ()) -> PSDReport:
    """Check the exact diagram SOS plus triangle-bound positivity criterion.

    A false result is inconclusive about the operator; a true result proves
    S >= margin*I.  Coefficientwise Hermiticity is a sufficient condition even
    when D<n makes the diagram family linearly dependent.
    """
    D = _positive_dimension(D)
    slack = exact_coefficients(algebra, slack)
    hermitian = slack == star_coefficients(algebra, slack)
    residual = sos_residual(algebra, D, slack, factors)
    identity = residual[algebra.identity]
    radius = sum((abs(value) * D**int(algebra.cups[i])
                  for i, value in enumerate(residual) if i != algebra.identity), Fraction(0))
    margin = identity - radius
    return PSDReport(hermitian, residual, identity, radius, margin, hermitian and margin >= 0)


def make_certificate(algebra: BrauerAlgebra, D: int, slack: Sequence, factors: Iterable[Sequence] = (), metadata=None):
    """Build a JSON-serializable certificate; metadata has no proof semantics."""
    D = _positive_dimension(D)
    slack = exact_coefficients(algebra, slack)
    factors = tuple(exact_coefficients(algebra, factor) for factor in factors)
    report = certify_psd(algebra, D, slack, factors)
    result = {
        'schema': _SCHEMA,
        'signature': list(algebra.signature),
        'D': D,
        'slack': [str(value) for value in slack],
        'factors': [[str(value) for value in factor] for factor in factors],
        'report': report.to_dict(),
    }
    if metadata is not None:
        result['metadata'] = metadata
    return result


def replay_certificate(certificate) -> PSDReport:
    """Recompute all proof arithmetic, ignoring every claimed report field."""
    if certificate.get('schema') != _SCHEMA:
        raise ValueError('Unsupported certificate schema')
    algebra = BrauerAlgebra(certificate['signature'])
    return certify_psd(algebra, certificate['D'], certificate['slack'], certificate['factors'])


def replay_certificate_file(path) -> PSDReport:
    return replay_certificate(json.loads(Path(path).read_text(encoding='utf-8')))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', help='JSON certificate to replay')
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError('Exact SOS replay requires Python without -O.')
    result = replay_certificate_file(args.certificate)
    print(json.dumps(result.to_dict(include_residual=False), indent=2))
    raise SystemExit(0 if result.verified else 1)

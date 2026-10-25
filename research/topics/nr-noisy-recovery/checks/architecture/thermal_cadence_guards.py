"""Exact finite identities for the declared code/vacuum reset model.

This does not evaluate exponentials, fit a source rate, optimize a cadence,
or simulate a device. The owner's analytic ODE proof carries continuous time.
"""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Run the exact thermal-cadence guard without -O/-OO.")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def zeros(rows, cols=None):
    if cols is None:
        cols = rows
    return [[F(0) for _ in range(cols)] for _ in range(rows)]


def unit(n, i, j):
    out = zeros(n)
    out[i][j] = F(1)
    return out


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def add(a, b):
    return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]


def scale(a, factor):
    return [[factor*x for x in row] for row in a]


def mm(a, b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def transpose(a):
    return [list(row) for row in zip(*a)]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), F(0))


def kron(a, b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def code_projector(d):
    return [[F(i == j and i < d) for j in range(d+1)]
            for i in range(d+1)]


def generator(rho, a, b, d):
    """Literal Lindblad generator with rate factors and matrix units; no sqrt."""
    n = d+1
    p = code_projector(d)
    pe = unit(n,d,d)
    out = zeros(n)
    for i in range(d):
        out = add(out, scale(mm(mm(unit(n,d,i),rho),unit(n,i,d)),a))
        out = add(out, scale(mm(mm(unit(n,i,d),rho),unit(n,d,i)),b/F(d)))
    out = add(out,scale(add(mm(p,rho),mm(rho,p)),-a/F(2)))
    return add(out,scale(add(mm(pe,rho),mm(rho,pe)),-b/F(2)))


def reset(rho):
    d = len(rho)
    return scale(eye(d),trace(rho)/F(d))


def accepted(rho, u, p):
    return add(scale(rho,u),scale(reset(rho),p-u))


# Sparse polynomials over Q[u,p,v,q]; exponent tuples are exact formal powers.
def poly_var(index):
    powers = [0,0,0,0]
    powers[index] = 1
    return {tuple(powers): F(1)}


def poly_add(*polys):
    out = {}
    for poly in polys:
        for powers,coefficient in poly.items():
            out[powers] = out.get(powers,F(0))+coefficient
    return {powers:value for powers,value in out.items() if value}


def poly_scale(poly, factor):
    return {powers:factor*value for powers,value in poly.items() if factor*value}


def poly_mul(a,b):
    out = {}
    for pa,ca in a.items():
        for pb,cb in b.items():
            powers = tuple(x+y for x,y in zip(pa,pb))
            out[powers] = out.get(powers,F(0))+ca*cb
    return {powers:value for powers,value in out.items() if value}


def verify():
    counts = {
        "generator_full_matrix_units":0,
        "traceless_code_basis":0,
        "population_basis":0,
        "reset_idempotence_matrix_units":0,
        "formal_composition_coefficients":0,
        "rational_composition_matrix_units":0,
        "deferred_marker_kraus_matrix_units":0,
        "marker_unitarity_and_isometry":0,
        "helper_parity_and_or_inner_products":0,
    }
    dims = (2,3,4)
    for d in dims:
        n = d+1
        p = code_projector(d)
        pe = unit(n,d,d)
        tau = scale(p,F(1,d))
        # G is linear in rates a,b. These two basis rates prove each listed
        # finite-dimension generator identity for every nonnegative a,b.
        for a,b in ((F(1),F(0)),(F(0),F(1))):
            for i in range(n):
                for j in range(n):
                    rho = unit(n,i,j)
                    if i < d and j < d:
                        expected = scale(rho,-a)
                        if i == j:
                            expected = add(expected,scale(pe,a))
                    elif i == d and j == d:
                        expected = add(scale(tau,b),scale(pe,-b))
                    else:
                        expected = scale(rho,-(a+b)/F(2))
                    require(generator(rho,a,b,d) == expected,
                            f"literal generator matrix unit failed: {d,a,b,i,j}")
                    counts["generator_full_matrix_units"] += 1
            traceless = [unit(n,i,j) for i in range(d)
                         for j in range(d) if i != j]
            traceless += [add(unit(n,i,i),scale(unit(n,d-1,d-1),F(-1)))
                          for i in range(d-1)]
            for rho in traceless:
                require(trace(rho) == 0 and generator(rho,a,b,d) == scale(rho,-a),
                        "traceless-code generator identity failed")
                counts["traceless_code_basis"] += 1
            require(generator(tau,a,b,d) == add(scale(tau,-a),scale(pe,a)),
                    "G(tau) identity failed")
            require(generator(pe,a,b,d) == add(scale(tau,b),scale(pe,-b)),
                    "G(Pe) identity failed")
            counts["population_basis"] += 2
        for i in range(d):
            for j in range(d):
                rho = unit(d,i,j)
                require(reset(reset(rho)) == reset(rho), "reset not idempotent")
                counts["reset_idempotence_matrix_units"] += 1
                for u,p0,v,q in (
                    (F(1,3),F(3,4),F(2,5),F(4,5)),
                    (F(0),F(1,2),F(1,7),F(4,7)),
                    (F(2,3),F(2,3),F(5,6),F(1)),
                ):
                    require(accepted(accepted(rho,v,q),u,p0)
                            == accepted(rho,u*v,p0*q),
                            "rational accepted-map composition failed")
                    counts["rational_composition_matrix_units"] += 1
        # Data-major ordering (data i, helper h). J embeds helper |0>.
        i2 = eye(2)
        x = [[F(0),F(1)],[F(1),F(0)]]
        marker = add(kron(p,i2),kron(pe,x))
        j0 = zeros(2*n,n)
        for i in range(n):
            j0[2*i][i] = F(1)
        require(mm(transpose(marker),marker) == eye(2*n), "marker not unitary")
        require(mm(mm(transpose(j0),mm(transpose(marker),marker)),j0) == eye(n),
                "ready-helper marker isometry failed")
        counts["marker_unitarity_and_isometry"] += 2
        # For every matrix-unit later data Kraus operator K, the exact accepted
        # amplitude is P K P. By complex linearity this holds for arbitrary K,
        # hence any data-only CP map and passive reference, with ideal helper.
        for i in range(n):
            for j in range(n):
                k = unit(n,i,j)
                actual = mm(mm(mm(mm(p,transpose(j0)),kron(k,i2)),marker),j0)
                require(actual == mm(mm(p,k),p), "deferred midpoint amplitude failed")
                counts["deferred_marker_kraus_matrix_units"] += 1
    # D^2=D above supplies the superoperator algebra. Verify its universal
    # composition coefficients formally, not by evaluating sampled variables.
    u,p,v,q = [poly_var(i) for i in range(4)]
    pmu = poly_add(p,poly_scale(u,F(-1)))
    qmv = poly_add(q,poly_scale(v,F(-1)))
    # Multiply in the two-superoperator basis (I,D). I is the unit and
    # D^2=D was checked above. Derive coefficients with this multiplication
    # table before comparing to the closed R(uv,pq) expression.
    left = (u,pmu)
    right = (v,qmv)
    composition = [{},{}]
    for i,ci in enumerate(left):
        for j,cj in enumerate(right):
            basis_index = int(bool(i or j))
            composition[basis_index] = poly_add(composition[basis_index],poly_mul(ci,cj))
    expected = (poly_mul(u,v),
                poly_add(poly_mul(p,q),poly_scale(poly_mul(u,v),F(-1))))
    for actual,wanted in zip(composition,expected):
        require(actual == wanted, "formal superoperator composition coefficient")
    counts["formal_composition_coefficients"] = 2
    x = [[F(0),F(1)],[F(1),F(0)]]
    z = [[F(1)],[F(0)]]
    one = [[F(0)],[F(1)]]
    require(mm(x,z) == one and mm(mm(x,x),z) == z, "repeated-X parity failed")
    counts["helper_parity_and_or_inner_products"] += 1
    # Preserving the same bad data while mapping both helper inputs to |1>
    # would change their inner product 0->1, so cannot be a unitary OR update.
    require(mm(transpose(z),one) == [[F(0)]]
            and mm(transpose(one),one) == [[F(1)]], "OR inner-product witness")
    counts["helper_parity_and_or_inner_products"] += 1
    return {
        "status":"passed",
        "arithmetic":"exact rational matrices and formal polynomial coefficients",
        "code_dimensions":list(dims),
        "rate_basis":[[1,0],[0,1]],
        "counts":counts,
        "continuous_time_result":"analytic ODE/exponential proof in owner; not numerically replayed",
        "scope":"Declared code/vacuum uniform-reset identities and ideal deferred helper only; no source rate fit, hardware instrument, full two-rail GAD model, finite-cost cadence optimum or native-order advantage.",
    }


if __name__ == "__main__":
    print(json.dumps(verify(),sort_keys=True))

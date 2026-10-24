"""Integer certificates for NR-R11's terminal separable CZ correction bound.

The four amplitude sectors prove an inequality for every complex product
vector. The owning analytic proof connects it to complete photon readout
followed by separable corrections, including all failed local filters.
No intermediate controller, finite pulse or hardware rate is certified.
All guards remain active under optimized Python; import is silent.
"""
import json
from pathlib import Path


def require(test, message):
    if not test:
        raise ValueError(message)


def determinant(matrix):
    if len(matrix) == 1:
        return matrix[0][0]
    return sum((-1)**j * matrix[0][j] * determinant(
        [row[:j] + row[j+1:] for row in matrix[1:]])
        for j in range(len(matrix)))


def integer_matrix(matrix, size):
    require(isinstance(matrix, list) and len(matrix) == size
            and all(isinstance(row, list) and len(row) == size for row in matrix),
            "matrix shape")
    require(all(type(value) is int for row in matrix for value in row),
            "integer matrix entries")
    require(matrix == [list(row) for row in zip(*matrix)], "matrix symmetry")


def verify(certificate=None):
    data = certificate if certificate is not None else json.loads(
        Path(__file__).with_name("projector_gate_gap.json").read_text(encoding="utf-8"))
    require(data["schema"] == "projector-cz-gate-gap-v1", "source schema")
    filtered = data["terminal_separable_filters"]
    require(filtered["schema"] == "projector-cz-terminal-local-filter-dual-v1",
            "filter certificate schema")
    denominator, source_denominator = filtered["denominator"], data["dual_denominator"]
    require(type(denominator) is int and type(source_denominator) is int,
            "integer denominators")
    require(source_denominator > 0 and denominator > 0
            and denominator % source_denominator == 0, "common denominator")
    z = data["dual_numerators"]["Z"]
    integer_matrix(z, 4)
    for size in range(1, 5):
        require(determinant([row[:size] for row in z[:size]]) > 0,
                "shared Z positive definiteness")
    signs = [1, 1, 1, -1]
    c = [[z[a][b] * (denominator // source_denominator) * signs[a] * signs[b]
          for b in range(4)] for a in range(4)]
    require(isinstance(filtered["sectors"], list) and len(filtered["sectors"]) == 4,
            "four sectors")
    seen, identities, minors = set(), 0, 0
    for sector in filtered["sectors"]:
        indices = sector["sector"]
        require(isinstance(indices, list) and len(indices) == 2
                and all(type(value) is int for value in indices), "integer sector indices")
        i, j = indices
        require((i, j) in {(0, 0), (0, 1), (1, 0), (1, 1)} and (i, j) not in seen,
                "sector coverage")
        seen.add((i, j))
        sa = [-1, 1] if i == 0 else [1, -1]
        sb = [-1, 1] if j == 0 else [1, -1]
        for name, size in (("A", 4), ("B", 4), ("MA", 2), ("MB", 2)):
            matrix = sector[name]
            integer_matrix(matrix, size)
            for leading in range(1, size+1):
                require(determinant([row[:leading] for row in matrix[:leading]]) > 0,
                        "sector positive definiteness")
                minors += 1
        a_matrix, b_matrix, ma, mb = (sector[name] for name in ("A", "B", "MA", "MB"))
        for a in range(4):
            aa, ab = divmod(a, 2)
            for b in range(4):
                ba, bb = divmod(b, 2)
                rhs = a_matrix[a][b] + b_matrix[2*aa+bb][2*ba+ab]
                if aa == ba:
                    rhs += sa[aa] * mb[ab][bb]
                if ab == bb:
                    rhs += ma[aa][ba] * sb[ab]
                lhs = c[a][b] - (denominator if a == b == 2*i+j else 0)
                require(lhs == rhs, "sector identity")
                identities += 1
    require(len(seen) == 4, "missing sector")
    return {"status": "passed", "exact_sector_identities": identities,
            "positive_sector_leading_minors": minors, "shared_Z_leading_minors": 4,
            "all_complex_product_inequality": "DZD expectation >= product of minimum local populations",
            "scope": "complete photon readout then terminal separable/LOCC correction; "
                     "no premeasurement/interleaved controller, finite pulse or hardware rate"}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))

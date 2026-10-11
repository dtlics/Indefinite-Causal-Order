#!/usr/bin/env python3
"""Exact algebraic calibrations for optional completion and split vertices.

These are finite identity checks, not a routed-host construction or a proof
of the general downset theorem. Only the Python standard library is used.
"""
import json
import random
from pathlib import Path


def identity(n):
    return tuple((i, 1) for i in range(n))


def multiply(a, b):
    """Signed permutations as column images; return a @ b."""
    return tuple((a[j][0], s * a[j][1]) for j, s in b)


def adjoint(a):
    out = [None] * len(a)
    for j, (i, s) in enumerate(a):
        out[i] = (j, s)
    return tuple(out)


def random_unitary(n, rng):
    p = list(range(n))
    rng.shuffle(p)
    return tuple((i, rng.choice((-1, 1))) for i in p)


def tensor_id_left(d, z):
    k = len(z)
    return tuple((q * k + z[e][0], z[e][1])
                 for q in range(d) for e in range(k))


def private_gate(z, vertex, D=16):
    """Act on E_vertex, with H=C^D and E_0=E_1=C^2."""
    out = []
    for h in range(D):
        for ev in range(2):
            for ew in range(2):
                es = [ev, ew]
                es[vertex], sign = z[es[vertex]]
                out.append((h * 4 + es[0] * 2 + es[1], sign))
    return tuple(out)


def optional_gate(branches, inputs, z, vertex, D=16):
    """One actual vertex, one shared private factor, one absent scalar."""
    assignment = {h: (b, q) for b, hs in enumerate(branches)
                  for q, h in enumerate(hs)}
    assert len(assignment) == sum(map(len, branches))
    out = []
    for h in range(D):
        for ev in range(2):
            for ew in range(2):
                es = [ev, ew]
                if h in assignment:
                    b, q = assignment[h]
                    local_out, sign = inputs[b][q * 2 + es[vertex]]
                    q_out, es[vertex] = divmod(local_out, 2)
                    h_out = branches[b][q_out]
                else:
                    h_out = h
                    es[vertex], sign = z[es[vertex]]
                out.append((h_out * 4 + es[0] * 2 + es[1], sign))
    return tuple(out)


def check_optional_completion():
    rng = random.Random(20260930)
    # Two active branches at the SAME vertex share E_0. The other vertex's
    # support overlaps an active and an absent sector of the first vertex.
    branches_v = [(0, 1), (2, 3)]
    branches_w = [(1, 4), (5, 6)]
    correct = 0
    wrong_left_substitution = 0
    wrong_final_left_multiplication = 0
    for _ in range(100):
        uv = [random_unitary(4, rng) for _ in branches_v]
        uw = [random_unitary(4, rng) for _ in branches_w]
        zv, zw = random_unitary(2, rng), random_unitary(2, rng)
        j = identity(2)
        completed = multiply(optional_gate(branches_w, uw, zw, 1),
                             optional_gate(branches_v, uv, zv, 0))
        uv_right = [multiply(u, tensor_id_left(2, adjoint(zv))) for u in uv]
        uw_right = [multiply(u, tensor_id_left(2, adjoint(zw))) for u in uw]
        baseline = multiply(optional_gate(branches_w, uw_right, j, 1),
                            optional_gate(branches_v, uv_right, j, 0))
        zs = multiply(private_gate(zv, 0), private_gate(zw, 1))
        assert completed == multiply(baseline, zs)
        assert multiply(adjoint(completed), completed) == identity(64)
        correct += 1
        uv_left = [multiply(tensor_id_left(2, adjoint(zv)), u) for u in uv]
        uw_left = [multiply(tensor_id_left(2, adjoint(zw)), u) for u in uw]
        bad_baseline = multiply(optional_gate(branches_w, uw_left, j, 1),
                                optional_gate(branches_v, uv_left, j, 0))
        wrong_left_substitution += completed != multiply(bad_baseline, zs)
        wrong_final_left_multiplication += completed != multiply(zs, baseline)
    assert wrong_left_substitution and wrong_final_left_multiplication
    return {
        "dimension_base_memory": 16,
        "private_dimensions_by_actual_vertex": [2, 2],
        "completed_unitary_identity_trials": correct,
        "wrong_left_substitution_rejected_trials": wrong_left_substitution,
        "wrong_final_left_multiplication_rejected_trials":
            wrong_final_left_multiplication,
    }


def check_shared_split_vertex():
    rng = random.Random(9302026)
    branches = [(2 * i, 2 * i + 1) for i in range(8)]
    ancestral, residual = branches[:3], branches[3:]
    j = identity(2)
    shared_parameter_trials = 0
    independent_branch_trials = 0
    for shared in (False, True):
        for _ in range(50):
            u = random_unitary(4, rng)
            inputs = [u if shared else random_unitary(4, rng)
                      for _ in branches]
            full = optional_gate(branches, inputs, j, 0)
            w = optional_gate(ancestral, inputs[:3], j, 0)
            v = optional_gate(residual, inputs[3:], j, 0)
            assert multiply(v, w) == full
            if shared:
                shared_parameter_trials += 1
            else:
                independent_branch_trials += 1
    # Every amplified matrix-unit coefficient of B followed by A is zero.
    # The blocks share one E_0, rather than receiving separate ancillas.
    zero_products = 0
    for ahs in ancestral:
        for bhs in residual:
            arows = [h * 2 + e for h in ahs for e in range(2)]
            brows = [h * 2 + e for h in bhs for e in range(2)]
            for ar in arows:
                for ac in arows:
                    for br in brows:
                        for bc in brows:
                            assert bc != ar  # E_(br,bc) E_(ar,ac) = 0.
                            zero_products += 1
    # Three distinct ancestral branches form ONE residual absent event.
    absent_rank = 16 - sum(map(len, residual))
    assert absent_rank == sum(map(len, ancestral)) == 6
    return {
        "same_vertex_A_branches": len(ancestral),
        "same_vertex_B_branches": len(residual),
        "private_dimension_at_shared_vertex": 2,
        "independent_branch_factorization_trials": independent_branch_trials,
        "shared_original_parameter_factorization_trials": shared_parameter_trials,
        "exact_incompatible_matrix_unit_products_zero": zero_products,
        "one_scalar_absent_event_represented_rank": absent_rank,
    }


if __name__ == "__main__":
    result = {
        "status": "PASS",
        "optional_completion": check_optional_completion(),
        "split_vertex": check_shared_split_vertex(),
        "scope": "Finite exact algebraic calibrations, not a routed-host construction",
    }
    path = Path(__file__).with_name("core_ancestral_controlled_factor_independent_checks.json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))

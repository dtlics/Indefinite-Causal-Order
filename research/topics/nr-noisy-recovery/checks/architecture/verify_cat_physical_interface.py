"""Exact retained-register route guards, not a fitted bosonic device model."""

if not __debug__:
    raise RuntimeError('Exact route checks require assertions; do not use -O.')


def verify_retained_cat_route():
    # Registers C,S,D,bufferA,bufferB,earlyField,lateField.
    # Monomial unitaries retain all phases (i**k) on all basis vectors;
    # complete operator equality therefore includes arbitrary references.
    width = 7
    masks = [1 << (width-1-j) for j in range(width)]

    def x_c(j):
        return j ^ masks[0], 0

    def swap(j):
        return (j ^ (masks[1] | masks[2]) if bool(j & masks[1]) != bool(j & masks[2]) else j), 0

    def q(j):
        return swap(j) if j & masks[0] else (j, 0)

    def qbar(j):
        return (j, 0) if j & masks[0] else swap(j)

    def controlled_flip(j, controls, target):
        return j ^ masks[target] if all(j & masks[c] for c in controls) else j

    def window1(dependent):
        def apply(j):
            j = controlled_flip(j, [1], 3)
            j = controlled_flip(j, [2, 3], 4)
            j = controlled_flip(j, [4], 5)
            phase = int(bool(j & masks[1]) and bool(j & masks[4]))
            if dependent:
                phase += int(bool(j & masks[0]) and bool(j & masks[2]))
            return j, phase % 4
        return apply

    def window2(dependent):
        def apply(j):
            j = controlled_flip(j, [3], 2)
            if bool(j & masks[3]) != bool(j & masks[4]):
                j ^= masks[3] | masks[4]
            j = controlled_flip(j, [1], 4)
            j = controlled_flip(j, [4], 6)
            phase = int(bool(j & masks[2]) and bool(j & masks[3]))
            if dependent:
                j = controlled_flip(j, [0], 3)
                phase += int(bool(j & masks[0]) and bool(j & masks[1]))
            return j, phase % 4
        return apply

    def run(j, operations):
        phase = 0
        for operation in operations:
            j, value = operation(j)
            phase = (phase + value) % 4
        return j, phase

    cases = literal = branches = independent_selector = mismatches = 0
    for dependent in (False, True):
        v1, v2 = window1(dependent), window2(dependent)
        program = [q, v1, swap, v2, qbar]
        expanded = [q, v1, q, x_c, q, x_c, v2, x_c, q, x_c]
        # Four Q gates and four X pulses; no commutation through V2.
        selector_program = [q, v1, q, x_c, q, v2, q, x_c]
        for j in range(1 << width):
            assert run(j, program) == run(j, expanded)
            literal += 1
            branch_program = ([swap, v1, swap, v2] if j & masks[0]
                              else [v1, swap, v2, swap])
            assert run(j, program) == run(j, branch_program)
            branches += 1
            if dependent:
                mismatches += run(j, program) != run(j, selector_program)
            else:
                assert run(j, program) == run(j, selector_program)
                independent_selector += 1
            cases += 1
    assert mismatches > 0

    # Direct guard: a vacuum-activating dummy processor leaves a retained
    # dummy tag. It is an abstract finite-register guard, not a cat fit.
    def active_dummy(j):
        j ^= masks[2]
        j = controlled_flip(j, [2], 5)
        return j, 0

    identity = lambda j: (j, 0)
    vacuum0, vacuum1 = 0, masks[0]
    out0 = run(vacuum0, [q, active_dummy, swap, identity, qbar])[0]
    out1 = run(vacuum1, [q, active_dummy, swap, identity, qbar])[0]
    assert bool(out0 & masks[2]) != bool(out1 & masks[2])
    return dict(status='passed', full_register_basis_phase_cases=cases,
                literal_four_cswap_four_flip_identities=literal,
                retained_full_branch_identities=branches,
                control_independent_native_selector_identities=independent_selector,
                control_dependent_false_selector_mismatches=mismatches,
                dummy_tag_not_deleted=1,
                scope='Finite full-register operator/permutation guards including persistent buffers, separate early/late field registers and helper-dependent windows. No oscillator cutoff approximation, physical gate noise, bath matching or memory frontier is certified.')


def verify_dummy_opportunities():
    from fractions import Fraction as F
    from math import comb
    moments = 0
    for number in range(17):
        for eta in [F(0), F(1, 9), F(9, 25), F(16, 25), F(1)]:
            probabilities = [F(comb(number, left))*eta**left*(1-eta)**(number-left)
                             for left in range(number+1)]
            assert sum(probabilities) == 1
            assert sum(left*prob for left, prob in enumerate(probabilities)) == eta*number
            moments += 1
    # A normalized even-photon output of a driven block: the exact
    # finite input example witnesses the photon-number difference.
    b_populations = [F(9, 25), F(0), F(16, 25)]
    nb = sum(number*prob for number, prob in enumerate(b_populations))
    assert nb == F(32, 25)
    witnesses = 0
    for eta in [F(0), F(1, 9), F(9, 25), F(16, 25)]:
        after = []
        for left in range(3):
            after.append(sum(b_populations[number]*F(comb(number, left))*eta**left*(1-eta)**(number-left)
                             for number in range(left, 3)))
        assert sum(after) == 1
        assert sum(left*prob for left, prob in enumerate(after)) == eta*nb
        assert eta*nb < nb
        assert after != b_populations
        witnesses += 1
    return dict(exact_loss_population_normalizations_and_moments=moments,
                finite_time_dummy_order_witnesses=witnesses,
                scope='Finite binomial moment guards for the analytic all-Fock pure-loss identity; no fitted cat state, warm-bath reduction, visibility or trace-distance constant.')


def verify_cat_physical_interface():
    return dict(status='passed', retained_route=verify_retained_cat_route(),
                dummy_opportunities=verify_dummy_opportunities())


if __name__ == '__main__':
    import json
    print(json.dumps(verify_cat_physical_interface(), indent=2))

"""Exact discrete-slot Raman routing checks; analytic scope is communication.md.

Import has no output or file effects. Physical mode matching, component loss,
stationarity and finite-pulse/bath tails remain explicit device hypotheses.
"""
from collections import defaultdict
from fractions import Fraction as F

if not __debug__:
    raise RuntimeError("Exact Raman port checks require assertions; do not use -O.")


def verify_raman_port_routes():
    """Replay the selected passive ring and its ordinary temporal codec."""
    def mm(a, b):
        return [[sum((x*y for x, y in zip(row, col)), F(0))
                 for col in zip(*b)] for row in a]

    # RT1 rational-amplitude coupler, including its rejected output port.
    alpha, beta = F(3, 5), F(4, 5)
    coupler = [[alpha, beta], [beta, -alpha]]
    assert mm(coupler, coupler) == [[1, 0], [0, 1]]
    k, tau = alpha*alpha, beta*beta
    assert k+tau == 1
    # Initial reflection, every finite exit, and the later circulating tail.
    tail_cases = 0
    for nmax in range(1, 15):
        exits = tau+sum((k*k*tau**(n-1) for n in range(1, nmax+1)), F(0))
        assert exits+k*tau**nmax == 1
        tail_cases += 1
    route_amplitude = -alpha*alpha*beta
    assert route_amplitude**2 == k*k*tau
    order_routes = []
    for initial in ('A', 'B'):
        station, visits = initial, []
        for _ in range(2):
            visits.append(station)
            station = 'B' if station == 'A' else 'A'
        assert visits == (['A', 'B'] if initial == 'A' else ['B', 'A'])
        assert station == initial  # extraction occurs before a third query
        order_routes.append(''.join(visits))

    # 4/27-k^2(1-k)=(k-2/3)^2(k+1/3), not a routing impossibility bound.
    lhs, rhs = [F(4, 27), F(0), F(-1), F(1)], [F(0)]*4
    for i, ci in enumerate([F(4, 9), F(-4, 3), F(1)]):
        for j, cj in enumerate([F(1, 3), F(1)]):
            rhs[i+j] += ci*cj
    assert lhs == rhs
    assert F(2, 3)**2*(1-F(2, 3)) == F(4, 27)
    # Static reconfiguration gives deterministic ordinary A-then-B routing.
    k_a, k_b = F(1), F(0)
    assert k_a*k_a*(1-k_b) == 1

    # Formal V entries, retaining all decoder leakage rather than deleting it.
    # Input Q times are 0,1; decoder delays are 1,0. Remux Q separation is4;
    # final decoder delays are4,0. Only the final central clock5 is accepted.
    selected, rejected_times = defaultdict(list), set()
    for qi in range(2):
        for pi in range(2):
            for decoder_q in range(2):
                central_time = qi+(1-decoder_q)
                for qo in range(2):
                    for po in range(2):
                        label = ((po, qo), (pi, decoder_q))
                        remux_time = central_time+4*qo
                        for final_q in range(2):
                            time = remux_time+4*(1-final_q)
                            if time == 5:
                                selected[((po, final_q), (pi, qi))].append(label)
                            else:
                                rejected_times.add(time)
    for qi in range(2):
        for pi in range(2):
            for qo in range(2):
                for po in range(2):
                    key = ((po, qo), (pi, qi))
                    assert selected[key] == [key]
    assert 5 not in rejected_times and len(selected) == 16
    # Three physical split/merge factors, each 1/sqrt2 in field amplitude.
    assert F(1, 2)**3 == F(1, 8)
    return {
        "ring_coupler_unitarity_cases": 1,
        "complete_exit_tail_identities": tail_cases,
        "selected_node_order_words": order_routes,
        "symmetric_ring_selected_probability_max": "4/27",
        "reconfigured_ordinary_route_probability": "1",
        "formal_temporal_processor_entries": len(selected),
        "temporal_codec_probability_factor": "1/8",
        "scope": "conditional discrete slots; component loss, bath/code stationarity and pulse tails remain physical hypotheses",
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify_raman_port_routes(), indent=2))

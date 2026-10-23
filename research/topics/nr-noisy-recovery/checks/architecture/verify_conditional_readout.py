"""Exact finite guards for conditional-noise readout and known S/D control.

The all-Fock Weyl relations and Gaussian radial integral are analytic.
These Fraction tests check their nontrivial phases and all-record laws,
not a truncated-Fock numerical approximation or measured device fit.
"""

if not __debug__:
    raise RuntimeError("Exact guards require Python assertions; do not use -O")

from fractions import Fraction as F


def z(x=0, y=0):
    return F(x), F(y)


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def neg(a):
    return -a[0], -a[1]


def scale(a, r):
    return a[0]*r, a[1]*r


def star(a):
    return a[0], -a[1]


def mul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def norm(a):
    return mul(a, star(a))[0]


def weyl(left, right):
    """D(left)D(right) = exp(i phase)D(total), phase in radians."""
    return mul(left, star(right))[1], add(left, right)


def verify_known_gaussian_control():
    hyperbolic = [(F(1), F(0)), (F(5, 3), F(4, 3)),
                  (F(13, 5), F(12, 5)), (F(17, 15), F(8, 15))]
    phases = [z(1), z(-1), z(0, 1), z(F(3, 5), F(4, 5))]
    amplitudes = [z(), z(1), z(0, 1), z(F(1, 3), F(2, 5)),
                  z(F(-2, 7), F(3, 4)), z(F(5, 3), F(-7, 11))]
    branches = cocycles = energy = 0
    for c, s in hyperbolic:
        assert c*c-s*s == 1
        for phase in phases:
            assert norm(phase) == 1

            def squeezed(alpha):
                # S a S^dagger = c a + exp(i phi)s a^dagger.
                return add(scale(alpha, c), neg(scale(mul(star(alpha), phase), s)))

            for alpha in amplitudes:
                beta = squeezed(alpha)
                mu = scale(add(alpha, beta), F(1, 2))
                d = scale(add(alpha, neg(beta)), F(1, 2))
                theta = mul(mu, star(d))[1]
                # The two known helper Z phases cancel opposite Weyl phases.
                for displacement, correction, target in [
                        (neg(d), theta, beta), (d, -theta, alpha)]:
                    phase_g, total = weyl(mu, displacement)
                    assert total == target
                    assert correction+phase_g == 0
                    branches += 1
                assert norm(mu)+norm(d) == (norm(alpha)+norm(beta))/2
                energy += 1
                # S conjugation is symplectic: the Weyl cocycle is preserved.
                # This checks products on arbitrary input, beyond vacuum means.
                for gamma in amplitudes:
                    original_phase, original_sum = weyl(alpha, gamma)
                    new_phase, new_sum = weyl(squeezed(alpha), squeezed(gamma))
                    assert new_phase == original_phase
                    assert new_sum == squeezed(original_sum)
                    cocycles += 1
    return {"controlled_branch_phase_identities": branches,
            "weyl_symplectic_product_identities": cocycles,
            "drive_amplitude_identities": energy,
            "scope": "Known squeeze/displacement preparation only; unknown sensed parameters cannot set helper controls."}


def verify_conditional_noise_readout():
    records = posterior = 0
    for ratio in range(2, 8):
        # Ne=ratio*Ng and R^2=ratio*Ng*ln(m): exactly integrable tails.
        for m in range(2, 31):
            tail_g, tail_e = F(1, m**ratio), F(1, m)
            # Joint law for equal priors and keep/reject records.
            law = [tail_g/2, (1-tail_g)/2, tail_e/2, (1-tail_e)/2]
            assert sum(law) == 1 and all(0 < p < 1 for p in law)
            pkeep = law[0]+law[2]
            prej = law[1]+law[3]
            assert pkeep+prej == 1
            pe_keep = law[2]/pkeep
            assert pe_keep == F(m**(ratio-1), 1+m**(ratio-1))
            # Bayesian averaging of the retained and rejected posteriors
            # recovers the original excited-state probability exactly.
            pe_reject = law[3]/prej
            assert pkeep*pe_keep+prej*pe_reject == F(1, 2)
            if ratio == 2:
                assert pkeep == (F(1, m)+F(1, m*m))/2
                assert pe_keep == F(m, m+1)
            records += 4
            posterior += 1
    # For Ne=2Ng the likelihood crossing is at R^2=2Ng ln2.
    # Error = P(g and keep) + P(e and reject); means coincide.
    assert (F(1, 4)+1-F(1, 2))/2 == F(3, 8)
    assert (F(1, 2)+F(1, 4))/2 == F(3, 8)
    variance_pairs = 0
    for va in [F(0), F(1, 8), F(1, 2), F(1), F(3)]:
        for vb in [F(0), F(1, 3), F(2), F(5)]:
            v = va+vb
            if v == 0:
                continue
            c = 1/(1+va*vb)
            narrower = c*v
            pplus, pminus = (1+c)/2, (1-c)/2
            # Unnormalized second moments include every flag; no input
            # quantum variance has been included in this added-noise law.
            qplus, qminus = (v+c*narrower)/2, (v-c*narrower)/2
            plus_ratio = qplus/(pplus*v)
            assert plus_ratio == (1+c*c)/(1+c)
            if pminus:
                assert qminus/pminus == v*(1+c)
            else:
                assert qminus == 0
            assert qplus+qminus == v
            # Equivalent exact rational form of plus_ratio >= 2sqrt(2)-2.
            # Both sides of plus_ratio+2 >= 2sqrt(2) are positive.
            assert ((plus_ratio+2)**2-8)*(1+c)**2 == (c*c+2*c-1)**2
            assert (plus_ratio+2)**2 >= 8
            variance_pairs += 1
    return {"normalized_joint_record_probabilities": records,
            "accepted_rejected_posterior_identities": posterior,
            "optimal_ratio_two_error": "3/8",
            "isotropic_all_flag_variance_laws": variance_pairs,
            "isotropic_lower_bound_factorizations": variance_pairs,
            "scope": "Ideal equal-prior circular Gaussian variance readout and isotropic added-noise flag moments, not a device fit, FI/error bound or native advantage."}


if __name__ == "__main__":
    import json
    print(json.dumps({"known_gaussian_control": verify_known_gaussian_control(),
                      "conditional_noise_readout": verify_conditional_noise_readout()}, indent=2))

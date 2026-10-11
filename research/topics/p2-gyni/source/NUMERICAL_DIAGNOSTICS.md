<a id="p2-r24"></a>

# Uncertified L10 diagnostic and its limits

The recorded 1 October 2026 run was one unconstrained universal coset-L10 positive-tester optimization, initialized from the certified six-angle physical tester. It imposed no angle-support or annihilator condition. The run terminated at its 300-second limit after 26,805 iterations. No new optimization is part of this package.

- Raw PSD tester score: 0.6221663049677824; this is not a physical lower certificate
- Raw NS completion scale: 0.6221746799392069; its minimum slack eigenvalue was about -9.13e-8, so it is not an upper certificate
- The floating repaired finite-relaxation gap was about 0.0001852041; this does not establish the relaxation optimum
- After mapping to ordinary word level 10, the tester affine residual was about 4.37e-9
- The smallest local aggregate eigenvalue was about 9.878e-4, and the current six-angle full-annihilator residual was about 0.02327. The iterate had left its initially flat support

No exact reconstruction was justified. These observations do not prove nonattainment, rule out other optimizers or supports, or establish infeasibility. The exact interval remains the one in CERTIFIED_BOUNDS.json. Compact values are preserved in L10_DIAGNOSTICS.json; bulky floating checkpoints and optimization logs are deliberately not included. Exact adjoint/overlap algebra is covered by the coset proofs and checks in support/.

# Application-by-application screen

This is a calculation map, not a list of proved advantages. **Full ordinary compilation** means identical control-target output under the stated channel-query interface. **Scalar baseline** means only the I/d visibility is estimated. **Restricted output gain** means a specified code/decoder/resource class improves; it is not an all-ordinary lower bound. Details and proofs are in [report.md](report.md).

| # | Practitioner target and AA/AB choice | Calculation / observation | Strong ordinary comparison and disposition |
|---|---|---|---|
| 1 | Coherent calibration error, AA of an unknown rotation | p-=0 identically although the gate can be very wrong | Self-statistic is blind; unitary full simulation is cheap. |
| 2 | Relative coherent-axis/crosstalk test, two unitary boxes AB | Measures the unitary order overlap/commutator | Repeated-unitary full simulator; no large query gap from this substitution. |
| 3 | Stabilizer-check compatibility, two unread projectors AB | Z/X qubit dephasers give p-=1/4 | Readable projective labels give ABA; even hidden qubit case has two-copy scalar baseline. |
| 4 | Noisy stabilizer readout strength, weak Luders AB | For axes n,m, p-=q_A q_B[1-(n dot m)^2], q=(1-sqrt(1-eta^2))/2 | Not the readable-projector identity, but exact qubit two-copy scalar test applies. |
| 5 | Measurement backaction versus classical readout probabilities | Z measurement followed by H has p-self=1/4, despite the same POVM effects as ordinary Z measurement whose p-self=0 | Useful instrument distinction, but qubit-scale ordinary process/Choi tests are cheap; no established advantage. |
| 6 | Biased Pauli memory noise, AA | p-=2(p_Xp_Y+p_Yp_Z+p_Zp_X) | Bell sampling gives unknown error probabilities; exact full-switch compiler applies. |
| 7 | Depolarizing strength, AA | p-=3 lambda^2/8 for qubit (1-lambda)id+lambda Omega | Exact ordinary full simulation with one query per slot; no need to know lambda. |
| 8 | Pauli-layer correlations, AB | ZZ and XX commute, hence p-=0; ZZ versus XI at error rates .1 has p-=.01 | Known-frame Pauli compiler and Bell sampling. Spatial correlation need not create a signal. |
| 9 | General correlated Pauli noise on many qubits | Flag is binary symplectic parity of sampled errors | Exact full compiler still works; locality of the Pauli distribution is unnecessary. |
| 10 | Small coherent superpositions of local fault operators | Known Kraus span {I,X_j,Y_j,Z_j} has commutator-test norm squared 2 | Ordinary coherent Choi test has constant overhead, even when the channel is not Pauli diagonal. |
| 11 | Unknown-axis rare faults | Conditional error Choi state is pure; isotropic error state is I_3/3 | Filter single faults before pairing copies; explicit 4,045-call 99% test at r=.01, versus a much worse primitive switch sampler. |
| 12 | T1 relaxation, AA | p-=gamma(1-sqrt(1-gamma))^2/4, of cubic order for weak damping | Small signal; qubit scalar baseline plus ordinary T1/Choi measurements. Minus is not useful identity recovery. |
| 13 | Heating versus cooling, AB/AA thermal channels | Noncommuting raising/lowering jumps yield a t^2 coefficient; one lowering jump has no t^2 term | Useful jump-algebra diagnostic, not a new all-ordinary advantage. |
| 14 | Collective versus independent relaxation | At the tested t=.1, collective/independent two-qubit self p values are about 2.99e-5 and 1.49e-5 | Distinguishable fingerprint; four-dimensional Choi baseline, ordinary Lindblad learning and support information must be counted. |
| 15 | Collective versus differential dephasing | Both diagonal jump algebras; switch signal vanishes | Does not certify absence of correlations or crosstalk. |
| 16 | Readable syndrome extraction plus arbitrary physical noise | One actual Luders-projective arm suffices for ABA at I/d | Direct scalar baseline from the supplied note. Input/code restrictions must not be ignored. |
| 17 | Ideal recovery R versus Pauli noise N on a code | p- = half the probability of a nonzero syndrome | Syndrome record already reports it; logical normalizer faults invisible. Pauli arm gives full compilation in the oracle model. |
| 18 | Compare two recovery policies R,S on the same code | p-=(1-Tr(P_code rho))/2, independent of which correction is used | Signal cannot rank these decoders; checked on distinct policies. |
| 19 | Subsystem/gauge-measurement disturbance | Gauge X/Z example has p-=1/4 but exact identity on the logical subsystem | A large NCOM need not imply logical failure. |
| 20 | Five-qubit QEC with two depolarizing layers | Flag gain is 80 p^4/27+O(p^5); leading 40p^2 logical error unchanged | Intermediate recovery halves leading coefficient; full Pauli simulation is stronger still. |
| 21 | Five-qubit biased X/Z layers | Flag changes leading error 35p^2 ->30p^2 | Intermediate syndrome makes it 20p^3. Extra flag helps a limited decoder but not the best admitted ordinary construction. |
| 22 | Steane CSS X/Z layers | At p=.01: .00400413 -> .00394935 with flag | Improvement over this final/intermediate-syndrome comparator is small; full Pauli compiler excludes unrestricted-query advantage. |
| 23 | Logical X-or-Y burst noise | On-code final error .5 ->0 with flagged correction | Known activation pattern; oracle Pauli compiler reproduces it, while mandatory-noise/no-bypass tasks need a different justified model. |
| 24 | Known Pauli/parity check with actual unknown channel | Corrected branch (E_i +/- P E_i P)/2 | Exactly ordinary Pauli check sandwiching with one actual E query. |
| 25 | Leakage followed by repumping, AB | Minus probability proportional to logical population rho_11; minus map is EB on the code | Not a nondestructive leakage syndrome or state-independent erasure flag. |
| 26 | Three-level leakage measurement / reset | Acceptance can depend strongly on input; full physical qutrit retained in simulation | Readable projector baseline where valid; qutrit scalar estimator penalty 9/2, not astronomical. |
| 27 | Bosonic photon loss AA | Finite-Fock tests give weak self-signals; no unmodeled excitation at truncation boundary | Known loss model, energy, error filtration and encoded recovery must be compared. No advantage established. |
| 28 | Loss with photon-number/parity operations AB | Nonzero interference possible; known parity arm is explicitly compilable | Standard bosonic syndrome extraction is the correct comparator. |
| 29 | Gaussian diffusion characterization | v=1/sqrt(1+sigma_q^2 sigma_p^2) for orthogonal kicks | Ordinary covariance estimation; repeatable programmed kicks remove the black-box difficulty. |
| 30 | Ideal GKP analog decoding with switch area flag | Conditional likelihood [1+c cos(xy)]/2; numerical flag benefit negligible at low noise and fragile at sigma=.5 | Compared with optimal analog-syndrome logical correction; no finite-energy or all-protocol advantage. |
| 31 | Reset purity or alignment, AA/AB replacers | v=Tr(tau sigma)/d at I/d | Ordinary output SWAP test measures Tr(tau sigma) directly, without the 1/d suppression. |
| 32 | Reset-to-magic source, two stabilizer resets AB | Ideal plus output Bloch (2/3,0,2/3), probability 3/4; noisy formula and distillation ledger derived | Strict resource-conversion gain over stabilizer operations plus the same resets. Native controller is a priced non-Clifford resource; no unrestricted-query claim. |
| 33 | Known Hamiltonian OTOC or known-probe noise comparison | Switch overlap is an OTOC-shaped expression | Known-arm compiler/ordinary echo; replacing the evolved block by noise does not remove a known probe's compiler. |
| 34 | Generic hidden multi-qubit non-Pauli backaction | Not settled by the small-dimensional / known-span constructions | Remaining natural-black-box candidate class. This sweep supplies no new large-call lower bound for a realistic family. |

Cases 1--32 have explicit finite models or direct derived formulas in the package. Case 33 is the sufficient-condition screen from the prior note, not a new expensive numerical experiment. Case 34 is explicitly an unresolved target, not a computed success.

## Resource labels that must survive into any paper

* Unknown probabilities are not the same as an unknown error operator basis.
* Classical device outcomes, an engineered Bell-probe outcome, and coherent environment access are different resources.
* A two-copy characterization test need not supply per-run fault information on a live payload.
* A full ordinary channel simulator reproduces the output law, not the physical environment's historical realization.
* A one-logical-qubit decoded interface is not the same as an arbitrary large physical recovery instrument.
* “No magic from stabilizer-only processing” is not a lower bound against arbitrary ordinary quantum gates.
* Extra syndrome extraction, Bell probes, memory and control gates are part of real resource accounting even when query complexity treats known processing as free.

import ICO.C4FullSwitchTheorem

/-! # Named statements of Section 4 (`sec:approximation`)

This module exposes standalone formal endpoints for the named statements and
displayed three-step tradeoff equations of Section 4 (`sec:approximation`) in
`paper/main.tex`:

- Lemma 11 (`lem:gram`, `eq:gram`): Near-orthonormality of `S_0`, `S_1`, and `S`.
- Claim 12 (`clm:switch-passes`, `eq:R1`): The quantum switch passes the Gram effect test.
- Lemma 13 (`lem:reverse`, `eq:bd`): Subcomb monotonicity (`0 ≤ C' ≤ C`) and the
  ordered-circuit reverse-product fidelity bound.
- Corollary 14 (`cor:coherence`, `eq:coherence`): Unified Haar-averaged order-coherence
  bound for any ordinary adaptive strategy calling each of `U` and `V` at most once.
- Claim 15 (`clm:fresh`, `eq:R2`): Pointwise trace-distance and channel-diamond bounds
  for fresh index sampling without replacement, together with `eq:R2`.
- Claim 16 (`clm:pair`) and `eq:R3`: Per-pair and summed fresh-process coherence bounds
  and the frame expectation bound `𝔼 Tr(S S† ρ_fresh) ≤ 1/2 + r^2/d + 7 r^2/(3d)`.
-/

namespace ICO.C4NamedClaims

open Matrix QIT MeasureTheory
open ICO.CausalReverse ICO.HaarFrame ICO.HaarLink ICO.ReverseFidelity ICO.ReverseIntegral
open ICO.CircuitOutput ICO.ClassicalDilation ICO.ControlOutcomeReverse ICO.ControlCoherence
open ICO.AverageCoherence ICO.TreeCoherence ICO.OptionalTreeCoherence
open ICO.HaarFamily ICO.CompositionGram ICO.ReverseCompositionGram ICO.CompositionGramAverage
open ICO.GramWitness ICO.ChoiWitnessState ICO.SwitchChoiWitness ICO.CoupledChoi
open ICO.FullSwitchChannel ICO.AtMostFamilyCoherence ICO.C4PhysicalEnsemble
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1200000

section WitnessGeometry

variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

/-- Normalized maximally entangled Choi vector `|W⟩ = d^{-1/2} ∑_k |k⟩ ⊗ W|k⟩`
on `Reference × Target = A × A` (`sec:witness`). -/
def unitaryKet (W : CMatrix A) : A × A → ℂ :=
  coefficient (A := A) • targetVector W

/-- Off-diagonal block `σ_{01}` of a bipartite-plus-control matrix `σ` between
control states `|0⟩` (`false`) and `|1⟩` (`true`). -/
def controlOffDiagBlock (σ : CMatrix ((A × A) × Bool)) : CMatrix (A × A) :=
  σ.submatrix (fun pf => (pf, false)) (fun qg => (qg, true))

/-- Cross-order coherence amplitude `⟨VU | σ_{01} | UV⟩` between the two ordered
unitary products on the control off-diagonal block `σ_{01}`. -/
def orderCoherenceAmplitude (σ : CMatrix ((A × A) × Bool))
    (U V : Unitary (A := A)) : ℂ :=
  star (unitaryKet ((V : CMatrix A) * (U : CMatrix A))) ⬝ᵥ
    (controlOffDiagBlock σ *ᵥ unitaryKet ((U : CMatrix A) * (V : CMatrix A)))

omit [DecidableEq A] [Nontrivial A] in
theorem controlOffDiagBlock_quadratic (σ : CMatrix ((A × A) × Bool))
    (v w : A × A → ℂ) :
    star v ⬝ᵥ (controlOffDiagBlock σ *ᵥ w) =
      star (controlVector v false) ⬝ᵥ (σ *ᵥ controlVector w true) := by
  simp [controlOffDiagBlock, controlVector, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.submatrix]

theorem orderCoherenceAmplitude_eq_mapCoherence (Φ : Channel A (A × Bool))
    (U V : Unitary (A := A)) :
    orderCoherenceAmplitude (normalizedChoiState Φ).matrix U V =
      mapCoherence Φ.map false true
        ((V : CMatrix A) * (U : CMatrix A))
        ((U : CMatrix A) * (V : CMatrix A)) := by
  unfold orderCoherenceAmplitude unitaryKet
  rw [controlOffDiagBlock_quadratic]
  exact normalized_quadratic_eq_coherence Φ false true _ _

omit [DecidableEq A] [Nontrivial A] in
theorem reverseFactor_eq_paper :
    reverseFactor (A := A) =
      1 / (Fintype.card A : ℝ) +
        (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1) := by
  simp [reverseFactor, one_div]

end WitnessGeometry

/-! ## Lemma 11 (`lem:gram`, `eq:gram`): Near-orthonormality -/

section LemmaGram

variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

/-- Product Haar ensemble of `r` independent unitaries for `A` and `r` independent
unitaries for `B`, parameterized directly by the ensemble size `r : ℕ`. -/
def haarBoxEnsemble (r : ℕ) :
    Measure ((Fin r → Unitary (A := A)) × (Fin r → Unitary (A := A))) :=
  (familyMeasure (A := A) r).prod (familyMeasure (A := A) r)

instance haarBoxEnsemble_probability (r : ℕ) :
    IsProbabilityMeasure (haarBoxEnsemble (A := A) r) :=
  inferInstanceAs (IsProbabilityMeasure
    ((familyMeasure (A := A) r).prod (familyMeasure (A := A) r)))

/-- `Sample A r` formulation of Lemma 11 (`lem:gram`), with `r + 1` unitaries per box. -/
theorem lem_gram_near_orthonormality_sample (r : ℕ) :
    ((∫ UV : Sample A r, ‖(columns UV.1 UV.2)ᴴ * columns UV.1 UV.2 - 1‖
        ∂ensembleMeasure (A := A) r r) ≤
      ((r + 1 : ℝ) ^ 2) / (Fintype.card A : ℝ)) ∧
    ((∫ UV : Sample A r, ‖(reverseColumns UV.1 UV.2)ᴴ * reverseColumns UV.1 UV.2 - 1‖
        ∂ensembleMeasure (A := A) r r) ≤
      ((r + 1 : ℝ) ^ 2) / (Fintype.card A : ℝ)) ∧
    ((∫ UV : Sample A r, ‖(switchSampleColumns UV)ᴴ * switchSampleColumns UV - 1‖
        ∂ensembleMeasure (A := A) r r) ≤
      ((r + 1 : ℝ) ^ 2) / (Fintype.card A : ℝ)) := by
  have hr2 : (((r + 1) * (r + 1) : ℕ) : ℝ) = (r + 1 : ℝ) ^ 2 := by
    push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · simpa only [gram, hr2] using defect_norm_average_le (A := A) r r
  · simpa only [gram, hr2] using reverse_defect_norm_average_le (A := A) r r
  · simpa only [gram, hr2] using gramZ_mean_bound (A := A) r

/-- **Lemma 11 (`lem:gram`, `eq:gram` — Near-orthonormality)**:
For `K = S_0` (`columns`), `S_1` (`reverseColumns`), and `S` (`switchColumns S_0 S_1`),
`𝔼 ‖K† K - I‖_∞ ≤ r^2 / d`. -/
theorem lem_gram_near_orthonormality (r : ℕ) :
    ((∫ UV, ‖(columns UV.1 UV.2)ᴴ * columns UV.1 UV.2 - 1‖
        ∂haarBoxEnsemble (A := A) r) ≤
      (r : ℝ) ^ 2 / (Fintype.card A : ℝ)) ∧
    ((∫ UV, ‖(reverseColumns UV.1 UV.2)ᴴ * reverseColumns UV.1 UV.2 - 1‖
        ∂haarBoxEnsemble (A := A) r) ≤
      (r : ℝ) ^ 2 / (Fintype.card A : ℝ)) ∧
    ((∫ UV,
        ‖(switchColumns (columns UV.1 UV.2) (reverseColumns UV.1 UV.2))ᴴ *
            switchColumns (columns UV.1 UV.2) (reverseColumns UV.1 UV.2) - 1‖
        ∂haarBoxEnsemble (A := A) r) ≤
      (r : ℝ) ^ 2 / (Fintype.card A : ℝ)) := by
  cases r with
  | zero =>
    have h1 (UV : (Fin 0 → Unitary (A := A)) × (Fin 0 → Unitary (A := A))) :
        (columns UV.1 UV.2)ᴴ * columns UV.1 UV.2 - 1 = 0 :=
      Subsingleton.elim _ 0
    have h2 (UV : (Fin 0 → Unitary (A := A)) × (Fin 0 → Unitary (A := A))) :
        (reverseColumns UV.1 UV.2)ᴴ * reverseColumns UV.1 UV.2 - 1 = 0 :=
      Subsingleton.elim _ 0
    have h3 (UV : (Fin 0 → Unitary (A := A)) × (Fin 0 → Unitary (A := A))) :
        (switchColumns (columns UV.1 UV.2) (reverseColumns UV.1 UV.2))ᴴ *
          switchColumns (columns UV.1 UV.2) (reverseColumns UV.1 UV.2) - 1 = 0 :=
      Subsingleton.elim _ 0
    simp [h1, h2, h3]
  | succ n =>
    simpa only [haarBoxEnsemble, ensembleMeasure, switchSampleColumns, Nat.cast_add,
      Nat.cast_one] using lem_gram_near_orthonormality_sample (A := A) n

end LemmaGram

/-! ## Claim 12 (`clm:switch-passes`, `eq:R1`): The switch passes -/

section ClaimSwitchPasses

variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

/-- `Sample A r` formulation of Claim 12 (`clm:switch-passes`, `eq:R1`) for the
physical switch probe output `switchTarget UV = normalizedChoiState ((fullSwitch UV).comp plusChannel)`. -/
theorem clm_switch_passes_sample (r : ℕ) :
    1 - ((r + 1 : ℝ) ^ 2) / (Fintype.card A : ℝ) ≤
      ∫ UV : Sample A r,
        ((effect (switchSampleColumns UV) * (switchTarget UV).matrix).trace).re
        ∂ensembleMeasure (A := A) r r := by
  have hZ : Continuous (switchSampleColumns (A := A) (r := r)) := switchSample_continuous
  have hIdealCont := witness_acceptance_continuous _ _ hZ
    (ideal_matrix_continuous _ hZ switchSample_diagonal)
  have hIdealInt := hIdealCont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := ensembleMeasure (A := A) r r)
  have hMean := mean_ideal_acceptance_ge_one_sub_defect
    (switchSampleColumns (A := A) (r := r)) switchSample_diagonal
    hIdealInt (gramZ_integrable (A := A) r)
  change 1 - (∫ UV : Sample A r, ‖gram (switchSampleColumns UV) - 1‖
      ∂ensembleMeasure (A := A) r r) ≤
    ∫ UV : Sample A r, ((witnessTest (switchSampleColumns UV)).acceptProb (ideal UV) : ℝ)
      ∂ensembleMeasure (A := A) r r at hMean
  have hG := gramZ_mean_bound (A := A) r
  have hr2 : (((r + 1) * (r + 1) : ℕ) : ℝ) = (r + 1 : ℝ) ^ 2 := by
    push_cast; ring
  rw [hr2] at hG
  have heq (UV : Sample A r) :
      ((witnessTest (switchSampleColumns UV)).acceptProb (ideal UV) : ℝ) =
        ((effect (switchSampleColumns UV) * (switchTarget UV).matrix).trace).re := by
    rw [← switchTarget_eq_ideal UV, BinaryHypothesisTest.acceptProb_eq_trace_re]
    change (((switchTarget UV).matrix * effect (switchSampleColumns UV)).trace).re = _
    rw [Matrix.trace_mul_comm]
  simp_rw [← heq]
  linarith

/-- **Claim 12 (`clm:switch-passes`, `eq:R1` — The switch passes)**:
For every integer `r ≥ 1`, let `ρ_sw` be the output of the full-control quantum switch
`fullChannel` on the probe (`|+⟩` on the control and half of a maximally entangled state on
the target) and `Θ = effect S`. Then `𝔼 Tr(Θ ρ_sw) ≥ 1 - r^2 / d`. -/
theorem clm_switch_passes {r : ℕ} (hr : 1 ≤ r) :
    1 - (r : ℝ) ^ 2 / (Fintype.card A : ℝ) ≤
      ∫ UV,
        ((effect (switchColumns (columns UV.1 UV.2) (reverseColumns UV.1 UV.2)) *
          (normalizedChoiState
            ((fullChannel (Nat.lt_of_lt_of_le Nat.zero_lt_one hr)
              (Nat.lt_of_lt_of_le Nat.zero_lt_one hr) UV.1 UV.2).comp plusChannel)).matrix).trace).re
        ∂haarBoxEnsemble (A := A) r := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have heq (UV : Sample A n) :
      normalizedChoiState
        ((fullChannel (Nat.zero_lt_succ n) (Nat.zero_lt_succ n) UV.1 UV.2).comp plusChannel) =
        switchTarget UV := by
    apply State.ext
    simp [switchTarget, full_plus_map, normalizedChoiState]
  simpa only [haarBoxEnsemble, ensembleMeasure, switchSampleColumns, heq,
    Nat.cast_add, Nat.cast_one] using clm_switch_passes_sample (A := A) n

end ClaimSwitchPasses

/-! ## Lemma 13 (`lem:reverse`, `eq:bd`): Subcomb monotonicity and ordered reverse bound -/

section LemmaReverse

variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

/-- Monotonicity of the averaged reverse-product test `Γ = reverseTest`:
if `0 ≤ C'` (`C'.PosSemidef`) and `C' ≤ C` (`(C - C').PosSemidef`), then
`0 ≤ Tr(C' Γ) ≤ Tr(C Γ)`. -/
theorem reverse_test_trace_mono
    (C' C : CMatrix (SixWires A))
    (hC' : C'.PosSemidef) (hle : (C - C').PosSemidef) :
    0 ≤ (C' * reverseTest (A := A)).trace.re ∧
      (C' * reverseTest (A := A)).trace.re ≤ (C * reverseTest (A := A)).trace.re := by
  have hle' : C' ≤ C := Matrix.le_iff.mpr hle
  have hnonneg : (0 : CMatrix (SixWires A)) ≤ reverseTest (A := A) :=
    Matrix.nonneg_iff_posSemidef.mpr (reverseTest_pos (A := A))
  constructor
  · have h0 := tracePair_mono_right hC' hnonneg
    simpa [tracePair] using h0
  · exact outcome_test_le_parent (reverseTest_pos (A := A)) hle'

/-- **Lemma 13 matrix form (`lem:reverse` — `0 ≤ C' ≤ C` subcomb clause)**:
If `0 ≤ C' ≤ C` where `C ≥ 0` satisfies the causal ordered-comb equation
`Tr_f C = C₂ ⊗ I_e` with `C₂ ≥ 0`, then
`Tr(C' Γ) ≤ Tr(C Γ) ≤ (Tr C / d^3) (1/d + d/(d^2 - 1))^2`. -/
theorem causal_reverse_test_subcomb_bound
    (C' C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hC' : C'.PosSemidef) (hle : (C - C').PosSemidef)
    (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    (C' * reverseTest (A := A)).trace.re ≤ (C * reverseTest (A := A)).trace.re ∧
      (C' * reverseTest (A := A)).trace.re ≤
        (C.trace.re / (Fintype.card A : ℝ) ^ 3) *
          (1 / (Fintype.card A : ℝ) +
            (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  have hmono := (reverse_test_trace_mono C' C hC' hle).2
  have hparent := causal_reverse_test_bound C C₂ hC hC₂ hcausal
  simp only [tracePair, one_div] at hparent ⊢
  exact ⟨hmono, hmono.trans hparent⟩

/-- Unnormalized output state `σ'(U, V) = d⁻¹ • outputChoi C' U V` of a subcomb `C'`
when the input wire `P` is half of a normalized maximally entangled state (`lem:reverse`). -/
def subcombBellOutput (C' : CMatrix (SixWires A)) (U V : CMatrix A) : CMatrix (A × A) :=
  (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) • outputChoi C' U V

theorem subcombBellOutput_overlap (C' : CMatrix (SixWires A)) (U V T : CMatrix A) :
    (star (unitaryKet T) ⬝ᵥ (subcombBellOutput C' U V *ᵥ unitaryKet T)).re =
      outputOverlap C' U V T := by
  unfold unitaryKet subcombBellOutput outputOverlap
  rw [tracePair_rankOne_eq_quadratic]
  simp only [star_smul, coefficient_star, Matrix.smul_mulVec, Matrix.mulVec_smul,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  have hc : (coefficient (A := A) * (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) *
      coefficient (A := A)) = ((((Fintype.card A : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    calc
      _ = (coefficient (A := A) * coefficient (A := A)) *
          (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) := by ring
      _ = _ := by
        rw [coefficient_square]
        simp only [Complex.ofReal_inv, Complex.ofReal_natCast,
          Complex.ofReal_mul, pow_two, mul_inv]
  have hmul :
      coefficient (A := A) *
          ((((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) *
            (coefficient (A := A) *
              (star (targetVector T) ⬝ᵥ (outputChoi C' U V *ᵥ targetVector T)))) =
        ((((Fintype.card A : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) *
          (star (targetVector T) ⬝ᵥ (outputChoi C' U V *ᵥ targetVector T)) := by
    rw [← hc]
    ring
  rw [hmul]
  exact Complex.re_ofReal_mul _ _

/-- **Lemma 13 operational form (`lem:reverse`, `eq:bd`)**:
Let `C ≥ 0` obey the homogeneous comb equation `d • Tr_f C = (Tr_{ef} C) ⊗ I_e` of a
circuit calling `U` before `V`, let `0 ≤ C' ≤ C`, and let `σ'(U, V)` (`subcombBellOutput C'`)
be the unnormalized output of `C'` when `P` is half of a maximally entangled state.
For independent Haar-random `U, V`,
`𝔼 ⟨UV | σ'(U, V) | UV⟩ ≤ (Tr C / d^3) (1/d + d/(d^2 - 1))^2`. -/
theorem lem_reverse_ordered_subcomb
    (C' C : CMatrix (SixWires A))
    (hC : C.PosSemidef) (hC' : C'.PosSemidef) (hle : (C - C').PosSemidef)
    (hcomb : (Fintype.card A : ℂ) • partialTraceB C =
      Matrix.kronecker (partialTraceB (partialTraceB C)) (1 : CMatrix A)) :
    (∫ U : Unitary (A := A), ∫ V : Unitary (A := A),
      (star (unitaryKet ((U : CMatrix A) * (V : CMatrix A))) ⬝ᵥ
        (subcombBellOutput C' (U : CMatrix A) (V : CMatrix A) *ᵥ
          unitaryKet ((U : CMatrix A) * (V : CMatrix A)))).re
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
      (C.trace.re / (Fintype.card A : ℝ) ^ 3) *
        (1 / (Fintype.card A : ℝ) +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  let _ := hC'
  let C₂ : CMatrix (FirstFourWires A) :=
    (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) • partialTraceB (partialTraceB C)
  have hC₂ : C₂.PosSemidef := by
    apply (partialTraceB_posSemidef (partialTraceB_posSemidef hC)).smul
    exact_mod_cast (by positivity : (0 : ℝ) ≤ (Fintype.card A : ℝ)⁻¹)
  have hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A) := by
    have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hs := congrArg ((Fintype.card A : ℂ)⁻¹ • ·) hcomb
    dsimp only at hs
    rw [smul_smul, inv_mul_cancel₀ hd, one_smul] at hs
    rw [hs]
    ext i j
    simp only [C₂, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    ring
  simp_rw [subcombBellOutput_overlap]
  simpa only [one_div] using
    outcome_outputOverlap_bound C' C C₂ (Matrix.le_iff.mpr hle) hC hC₂ hcausal

end LemmaReverse

/-! ## R3 — Corollary 14 (`cor:coherence`, `eq:coherence`): Coherence between the two orders -/

section CorollaryCoherence

variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

/-- Instrument preparing the control qubit in `|+⟩` while passing the target `A` through. -/
def plusPrepInstrument : ICO.InstrumentCompression.Instrument A (A × Bool) PUnit where
  op := fun _ => plusMatrix
  complete := by simpa using plus_isometry (A := A)

/-- Two-box unitary oracle assignment (`false ↦ U`, `true ↦ V`) with private memory `M`. -/
def twoUnitaryOracles (U V : Unitary (A := A)) : Bool → Channel (A × M) (A × M) :=
  fun b => cond b (oracleChannel V) (oracleChannel U)

/-- Output state `σ(U, V)` on the probe (`|+⟩` on control, maximally entangled state on
`Reference × Target`) of an ordinary strategy calling each of `U` and `V` at most once. -/
def atMostOnceProbeState {s : Finset Bool}
    (tree : ICO.AtMostLabelledQueryTree.Tree Bool (A × M) (A × Bool) s (A × Bool))
    (U V : Unitary (A := A)) : State ((A × A) × Bool) :=
  normalizedChoiState ((tree.channel (twoUnitaryOracles U V)).comp plusChannel)

/-- Output state `σ(U, V)` on the probe of an `OptionalTwoQuery.QueryTree` strategy. -/
def optionalTwoQueryProbeState
    (tree : ICO.OptionalTwoQuery.QueryTree A M (A × Bool) (A × Bool))
    (U V : Unitary (A := A)) : State ((A × A) × Bool) :=
  normalizedChoiState ((tree.channel (oracleChannel U) (oracleChannel V)).comp plusChannel)

/-- Output state `σ(U, V)` on the probe of a `TwoQueryTree.QueryTree` strategy. -/
def twoQueryProbeState
    (tree : ICO.TwoQueryTree.QueryTree (A × M) (A × Bool) (A × Bool))
    (U V : Unitary (A := A)) : State ((A × A) × Bool) :=
  normalizedChoiState ((tree.channel (oracleChannel U) (oracleChannel V)).comp plusChannel)

omit [Nonempty M] in
private theorem plusPrep_atMost_map {s : Finset Bool}
    (tree : ICO.AtMostLabelledQueryTree.Tree Bool (A × M) (A × Bool) s (A × Bool))
    (oracles : Bool → Channel (A × M) (A × M)) :
    ((ICO.AtMostLabelledQueryTree.Tree.node plusPrepInstrument (fun _ => tree)).channel
      oracles).map = ((tree.channel oracles).comp plusChannel).map := by
  ext X i j
  change ICO.InstrumentCompression.adaptiveMap plusPrepInstrument
    (fun _ => tree.channel oracles) X i j =
      (tree.channel oracles).map ((isometryChannel plusMatrix plus_isometry).map X) i j
  rw [ICO.InstrumentCompression.adaptiveMap_apply, isometryChannel_apply]
  simp [plusPrepInstrument]

omit [Nontrivial A] [Nonempty M] in
private theorem twoAssignment_bool (U V : Unitary (A := A)) :
    ICO.AtMostSelectedQueryTree.twoAssignment (twoUnitaryOracles (M := M) 1 1) false true
      (oracleChannel U).map (oracleChannel V).map =
        fun b => (twoUnitaryOracles (M := M) U V b).map := by
  funext b
  cases b <;> rfl

/-- Stronger expected-modulus form of Corollary 14 (`cor:coherence`):
for any ordinary adaptive strategy calling each of `U` and `V` at most once,
`𝔼 ‖⟨VU | σ_{01}(U, V) | UV⟩‖ ≤ 1/d + d/(d^2 - 1)`. -/
theorem cor_coherence_at_most_once_norm {s : Finset Bool}
    (tree : ICO.AtMostLabelledQueryTree.Tree Bool (A × M) (A × Bool) s (A × Bool)) :
    (∫ UV : Unitary (A := A) × Unitary (A := A),
      ‖orderCoherenceAmplitude (atMostOnceProbeState tree UV.1 UV.2).matrix UV.1 UV.2‖
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))) ≤
      1 / (Fintype.card A : ℝ) +
        (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1) := by
  let treePlus : ICO.AtMostLabelledQueryTree.Tree Bool (A × M) (A × Bool) s A :=
    .node plusPrepInstrument (fun _ => tree)
  have hbound := ICO.AtMostSelectedQueryTree.selected_mean_coherence_bound
    treePlus (twoUnitaryOracles (M := M) 1 1) false true (by decide) false true
  have heq (UV : Unitary (A := A) × Unitary (A := A)) :
      orderCoherenceAmplitude (atMostOnceProbeState tree UV.1 UV.2).matrix UV.1 UV.2 =
        mapCoherence
          (treePlus.map (ICO.AtMostSelectedQueryTree.twoAssignment
            (twoUnitaryOracles (M := M) 1 1) false true
            (oracleChannel UV.1).map (oracleChannel UV.2).map))
          false true ((UV.2 : CMatrix A) * (UV.1 : CMatrix A))
          ((UV.1 : CMatrix A) * (UV.2 : CMatrix A)) := by
    rw [atMostOnceProbeState, orderCoherenceAmplitude_eq_mapCoherence,
      ← plusPrep_atMost_map, ICO.AtMostLabelledQueryTree.Tree.channel_map,
      twoAssignment_bool]
  simp_rw [heq]
  rwa [reverseFactor_eq_paper] at hbound

/-- **Corollary 14 (`cor:coherence`, `eq:coherence` — Coherence between the two orders)**:
Let `σ(U, V)` be the output on the probe (`|+⟩` on control, maximally entangled state on
`Reference × Target`) of an ordinary adaptive strategy calling each of `U` and `V` at most
once, and `σ_{01}` its off-diagonal control block. For independent Haar-random `U, V`,
`|𝔼 ⟨VU | σ_{01}(U, V) | UV⟩| ≤ 1/d + d/(d^2 - 1)`. -/
theorem cor_coherence_at_most_once {s : Finset Bool}
    (tree : ICO.AtMostLabelledQueryTree.Tree Bool (A × M) (A × Bool) s (A × Bool)) :
    ‖∫ UV : Unitary (A := A) × Unitary (A := A),
      orderCoherenceAmplitude (atMostOnceProbeState tree UV.1 UV.2).matrix UV.1 UV.2
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))‖ ≤
      1 / (Fintype.card A : ℝ) +
        (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1) :=
  (norm_integral_le_integral_norm _).trans (cor_coherence_at_most_once_norm tree)

/-- Corollary 14 (`cor:coherence`) stated for `OptionalTwoQuery.QueryTree` strategies
calling each of `U` and `V` at most once on the probe. -/
theorem cor_coherence_optional_two_query
    (tree : ICO.OptionalTwoQuery.QueryTree A M (A × Bool) (A × Bool)) :
    ‖∫ UV : Unitary (A := A) × Unitary (A := A),
      orderCoherenceAmplitude (optionalTwoQueryProbeState tree UV.1 UV.2).matrix UV.1 UV.2
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))‖ ≤
      1 / (Fintype.card A : ℝ) +
        (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1) := by
  let treePlus : ICO.OptionalTwoQuery.QueryTree A M (A × Bool) A :=
    .node plusPrepInstrument (fun _ => tree)
  have hbound := ICO.OptionalTreeCoherence.queryTree_average_bound
    (Classical.arbitrary A) treePlus false true
  have heq (UV : Unitary (A := A) × Unitary (A := A)) :
      orderCoherenceAmplitude (optionalTwoQueryProbeState tree UV.1 UV.2).matrix UV.1 UV.2 =
        mapCoherence (treePlus.channel (oracleChannel UV.1) (oracleChannel UV.2)).map
          false true ((UV.2 : CMatrix A) * (UV.1 : CMatrix A))
          ((UV.1 : CMatrix A) * (UV.2 : CMatrix A)) := by
    rw [optionalTwoQueryProbeState, orderCoherenceAmplitude_eq_mapCoherence]
    suffices hmap :
        ((tree.channel (oracleChannel UV.1) (oracleChannel UV.2)).comp plusChannel).map =
          (treePlus.channel (oracleChannel UV.1) (oracleChannel UV.2)).map by
      rw [hmap]
    ext X i j
    change ((tree.channel (oracleChannel UV.1) (oracleChannel UV.2)).map
      ((isometryChannel plusMatrix plus_isometry).map X)) i j =
      ICO.InstrumentCompression.adaptiveMap plusPrepInstrument
        (fun _ => tree.channel (oracleChannel UV.1) (oracleChannel UV.2)) X i j
    rw [ICO.InstrumentCompression.adaptiveMap_apply, isometryChannel_apply]
    simp [plusPrepInstrument]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp_rw [heq]
  rwa [reverseFactor_eq_paper] at hbound

omit [Nonempty M] in
/-- Corollary 14 (`cor:coherence`) stated for `TwoQueryTree.QueryTree` strategies
calling each of `U` and `V` once on the probe. -/
theorem cor_coherence_two_query
    (tree : ICO.TwoQueryTree.QueryTree (A × M) (A × Bool) (A × Bool)) :
    ‖∫ UV : Unitary (A := A) × Unitary (A := A),
      orderCoherenceAmplitude (twoQueryProbeState tree UV.1 UV.2).matrix UV.1 UV.2
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))‖ ≤
      1 / (Fintype.card A : ℝ) +
        (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1) := by
  let treePlus : ICO.TwoQueryTree.QueryTree (A × M) (A × Bool) A :=
    .node plusPrepInstrument (fun _ => tree)
  have hbound := ICO.TreeCoherence.queryTree_average_bound treePlus false true
  have heq (UV : Unitary (A := A) × Unitary (A := A)) :
      orderCoherenceAmplitude (twoQueryProbeState tree UV.1 UV.2).matrix UV.1 UV.2 =
        mapCoherence (treePlus.channel (oracleChannel UV.1) (oracleChannel UV.2)).map
          false true ((UV.2 : CMatrix A) * (UV.1 : CMatrix A))
          ((UV.1 : CMatrix A) * (UV.2 : CMatrix A)) := by
    rw [twoQueryProbeState, orderCoherenceAmplitude_eq_mapCoherence]
    suffices hmap :
        ((tree.channel (oracleChannel UV.1) (oracleChannel UV.2)).comp plusChannel).map =
          (treePlus.channel (oracleChannel UV.1) (oracleChannel UV.2)).map by
      rw [hmap]
    ext X i j
    change ((tree.channel (oracleChannel UV.1) (oracleChannel UV.2)).map
      ((isometryChannel plusMatrix plus_isometry).map X)) i j =
      ICO.InstrumentCompression.adaptiveMap plusPrepInstrument
        (fun _ => tree.channel (oracleChannel UV.1) (oracleChannel UV.2)) X i j
    rw [ICO.InstrumentCompression.adaptiveMap_apply, isometryChannel_apply]
    simp [plusPrepInstrument]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp_rw [heq]
  rwa [reverseFactor_eq_paper] at hbound

end CorollaryCoherence

/-! ## Claim 15 (`clm:fresh`, `eq:R2`): Indices may be taken fresh -/

section ClaimFresh

variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

/-- Full-control fresh-index circuit channel on `(A × Bool)` without index replacement. -/
def freshFullCircuit {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q (A × Bool))
    (hq : q ≤ r + 1) (UV : Sample A r) : Channel (A × Bool) (A × Bool) :=
  (ICO.FreshBudgetCompile.fresh (r := r + 1) tree Finset.univ Finset.univ
    (by simpa using hq) (by simpa using hq)).channel
      (ICO.AtMostFamilyCoherence.familyChannels UV.1 UV.2)

/-- **Claim 15 (`clm:fresh` — Indices may be taken fresh, probe state distance)**:
For every choice of the unitaries `UV`, the normalized trace distance between the actual
and fresh probe output states is at most `q(q - 1) / (2(r + 1))`. -/
theorem clm_fresh_distance {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r + 1)
    (UV : Sample A r) :
    QIT.normalizedTraceDistance (ordinary tree UV).matrix (fresh tree hq UV).matrix ≤
      (q : ℝ) * (q - 1) / (2 * (r + 1)) :=
  ordinary_fresh_coupling tree hq UV

omit [Nonempty M] in
/-- Channel-level strengthening of Claim 15 (`clm:fresh`):
for every choice of the unitaries `UV`, the half-diamond distance between the actual
full-control circuit `fullCircuit tree UV` and the fresh-index circuit
`freshFullCircuit tree hq UV` is at most `q(q - 1) / (2(r + 1))`. -/
theorem clm_fresh_channel_diamond_distance {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q (A × Bool)) (hq : q ≤ r + 1)
    (UV : Sample A r) :
    (fullCircuit tree UV).diamondTraceDistance (freshFullCircuit tree hq UV) ≤
      (q : ℝ) * (q - 1) / (2 * (r + 1)) := by
  let oracles := ICO.AtMostFamilyCoherence.familyChannels (M := M) UV.1 UV.2
  let B := A × Bool
  let Cmap := ICO.FreshSamplingMaps.commonMap tree oracles Finset.univ Finset.univ
  apply Channel.diamondTraceDistance_le_of_inputReferenceBound
  intro ω
  let Cω : CMatrix (B × B) := MatrixMap.kron Cmap (Channel.idChannel B).map ω.matrix
  have hId : (Channel.idChannel B).map = LinearMap.id :=
    ICO.DiamondPreprocessing.identity_map
  have hOrd : (((fullCircuit tree UV).prod (Channel.idChannel B)).applyState ω).matrix - Cω
      |>.PosSemidef := by
    change (MatrixMap.kron (ICO.SamplingOrdinary.ordinaryChannel tree oracles).map
      (Channel.idChannel B).map ω.matrix -
        MatrixMap.kron Cmap (Channel.idChannel B).map ω.matrix).PosSemidef
    rw [← LinearMap.sub_apply, ← MatrixMap.kron_sub_left, hId]
    exact (ICO.SamplingOrdinary.ordinary_sub_common_cp tree oracles
      Finset.univ Finset.univ).mapsPositiveUnderAncilla B ω.matrix ω.pos
  have hFresh :
      (((freshFullCircuit tree hq UV).prod (Channel.idChannel B)).applyState ω).matrix - Cω
      |>.PosSemidef := by
    have hfmap : (freshFullCircuit tree hq UV).map =
        ICO.FreshSamplingMaps.freshMap tree oracles Finset.univ Finset.univ :=
      ICO.FreshSamplingMaps.fresh_compile_map _ _ _ _ _ _
    change (MatrixMap.kron (freshFullCircuit tree hq UV).map
      (Channel.idChannel B).map ω.matrix -
        MatrixMap.kron Cmap (Channel.idChannel B).map ω.matrix).PosSemidef
    rw [hfmap, ← LinearMap.sub_apply, ← MatrixMap.kron_sub_left, hId]
    exact (ICO.SamplingOrderCore.fresh_sub_common_cp tree oracles
      Finset.univ Finset.univ).mapsPositiveUnderAncilla B ω.matrix ω.pos
  apply (ICO.CommonPartDistance.distance_le_missing_trace _ _ Cω hOrd hFresh).trans
  have htrCω : Cω.trace = (Cmap ω.marginalA.matrix).trace := by
    rw [← partialTraceB_trace Cω]
    congr 1
    ext i i'
    simp only [Cω, partialTraceB, State.marginalA_matrix]
    let S : B → CMatrix B := fun j x x' => ω.matrix (x, j) (x', j)
    have hsum : (fun x x' => ∑ j : B, ω.matrix (x, j) (x', j)) = ∑ j : B, S j := by
      ext x x'
      simp [S, Matrix.sum_apply]
    change (∑ j : B, MatrixMap.kron Cmap (Channel.idChannel B).map ω.matrix (i, j) (i', j)) =
      Cmap (fun x x' => ∑ j : B, ω.matrix (x, j) (x', j)) i i'
    rw [hsum, map_sum]
    simp only [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simpa [S] using
      (MatrixMap.kron_idChannel_apply_slice (a := B) (b := B) (r := B)
        (Φ := Cmap) (X := ω.matrix) (br := (i, j)) (br' := (i', j)))
  have hLoss := ICO.SamplingTrace.initial_trace_loss tree oracles (Nat.zero_lt_succ r)
    ω.marginalA.pos
  rw [htrCω]
  have hm1 : ω.marginalA.matrix.trace.re = 1 := by
    rw [ω.marginalA.trace_eq_one]; simp
  rw [hm1, mul_one] at hLoss
  simpa using hLoss

/-- **Claim 15 consequence (`eq:R2`)**:
For every choice of the unitaries `UV`,
`Tr(Θ ρ_act) ≤ Tr(S S† ρ_fresh) + q(q - 1) / (2(r + 1))`. -/
theorem clm_fresh_trace_bound {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r + 1)
    (UV : Sample A r) :
    ((effect (switchSampleColumns UV) * (ordinary tree UV).matrix).trace).re ≤
      ((frame (switchSampleColumns UV) * (fresh tree hq UV).matrix).trace).re +
        (q : ℝ) * (q - 1) / (2 * (r + 1)) := by
  have hgap := ICO.QuantumDecision.accept_gap_le_traceDistance
    (witnessTest (switchSampleColumns UV)) (ordinary tree UV) (fresh tree hq UV)
  have hdist := ordinary_fresh_coupling tree hq UV
  have hframe := tracePair_mono_right (fresh tree hq UV).pos
    (effect_le_frame (switchSampleColumns UV))
  rw [BinaryHypothesisTest.acceptProb_eq_trace_re,
    BinaryHypothesisTest.acceptProb_eq_trace_re] at hgap
  change tracePair (ordinary tree UV).matrix (effect (switchSampleColumns UV)) -
    tracePair (fresh tree hq UV).matrix (effect (switchSampleColumns UV)) ≤ _ at hgap
  have hcomm1 : ((effect (switchSampleColumns UV) * (ordinary tree UV).matrix).trace).re =
      tracePair (ordinary tree UV).matrix (effect (switchSampleColumns UV)) := by
    unfold tracePair; rw [Matrix.trace_mul_comm]
  have hcomm2 : ((frame (switchSampleColumns UV) * (fresh tree hq UV).matrix).trace).re =
      tracePair (fresh tree hq UV).matrix (frame (switchSampleColumns UV)) := by
    unfold tracePair; rw [Matrix.trace_mul_comm]
  linarith

end ClaimFresh

/-! ## Claim 16 (`clm:pair`) and `eq:R3`: One pair at a time and fresh frame expectation -/

section ClaimPairAndR3

variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

omit [Nonempty M] in
theorem fresh_pair_coherence_eq {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r + 1)
    (i j : Fin (r + 1)) (UV : Sample A r) :
    orderCoherenceAmplitude (fresh tree hq UV).matrix (UV.1 i) (UV.2 j) =
      familyCoherence (sampledFreshTree tree hq) i j false true UV := by
  rw [fresh, orderCoherenceAmplitude_eq_mapCoherence]
  simp only [familyCoherence, ICO.AtMostLabelledQueryTree.Tree.channel_map]

/-- Stronger expected-modulus form of Claim 16 (`clm:pair`):
in the fresh process, for every pair `(i, j)`,
`𝔼 ‖⟨V_j U_i | (ρ_fresh)_{01} | U_i V_j⟩‖ ≤ 1/d + d/(d^2 - 1)`. -/
theorem clm_pair_fresh_coherence_norm {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r + 1)
    (i j : Fin (r + 1)) :
    (∫ UV : Sample A r,
      ‖orderCoherenceAmplitude (fresh tree hq UV).matrix (UV.1 i) (UV.2 j)‖
      ∂ensembleMeasure (A := A) r r) ≤
      1 / (Fintype.card A : ℝ) +
        (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1) := by
  simp_rw [fresh_pair_coherence_eq]
  simpa only [ensembleMeasure, reverseFactor_eq_paper] using
    familyCoherence_average_bound (sampledFreshTree tree hq) i j false true

/-- **Claim 16 (`clm:pair` — One pair at a time)**:
In the fresh process, for every pair `(i, j)`,
`|𝔼 ⟨V_j U_i | (ρ_fresh)_{01} | U_i V_j⟩| ≤ 1/d + d/(d^2 - 1)`. -/
theorem clm_pair_fresh_coherence {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r + 1)
    (i j : Fin (r + 1)) :
    ‖∫ UV : Sample A r,
      orderCoherenceAmplitude (fresh tree hq UV).matrix (UV.1 i) (UV.2 j)
      ∂ensembleMeasure (A := A) r r‖ ≤
      1 / (Fintype.card A : ℝ) +
        (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1) :=
  (norm_integral_le_integral_norm _).trans (clm_pair_fresh_coherence_norm tree hq i j)

/-- Summed fresh-process coherence bound across all `(r + 1)^2` pairs `(i, j)`:
`𝔼 ∑_{i, j} ‖⟨V_j U_i | (ρ_fresh)_{01} | U_i V_j⟩‖ ≤ (r + 1)^2 (1/d + d/(d^2 - 1))`. -/
theorem clm_pair_fresh_coherence_sum {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r + 1) :
    (∫ UV : Sample A r,
      ∑ ij : Fin (r + 1) × Fin (r + 1),
        ‖orderCoherenceAmplitude (fresh tree hq UV).matrix (UV.1 ij.1) (UV.2 ij.2)‖
      ∂ensembleMeasure (A := A) r r) ≤
      ((r + 1 : ℝ) ^ 2) *
        (1 / (Fintype.card A : ℝ) +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) := by
  simp_rw [fresh_pair_coherence_eq]
  have hr2 : (((r + 1) * (r + 1) : ℕ) : ℝ) = (r + 1 : ℝ) ^ 2 := by
    push_cast; ring
  simpa only [ensembleMeasure, hr2, reverseFactor_eq_paper] using
    total_coherence_average_bound (sampledFreshTree tree hq) false true

private theorem frame_score_le_defects_add_cross
    {H I : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (X Y : Matrix H I ℂ) (ρ : State (H × Bool)) :
    ((frame (switchColumns X Y) * ρ.matrix).trace).re ≤
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * ‖gram X - 1‖ +
        (1 / 2 : ℝ) * ‖gram Y - 1‖ + crossNormSum X Y ρ := by
  have hcomm : ((frame (switchColumns X Y) * ρ.matrix).trace).re =
      tracePair ρ.matrix (frame (switchColumns X Y)) := by
    unfold tracePair; rw [Matrix.trace_mul_comm]
  rw [hcomm, switch_frame_score X Y ρ.matrix ρ.pos.isHermitian]
  have hx := frame_pair_le_one_add_defect X (block ρ.matrix false)
    (block_pos ρ.matrix ρ.pos false)
  have hy := frame_pair_le_one_add_defect Y (block ρ.matrix true)
    (block_pos ρ.matrix ρ.pos true)
  have hp := block_mass_sum ρ.matrix
  rw [ρ.trace_eq_one] at hp
  simp only [Complex.one_re] at hp
  have hp0 := block_mass_nonneg ρ.matrix ρ.pos false
  have hp1 := block_mass_nonneg ρ.matrix ρ.pos true
  have hp0le : (block ρ.matrix false).trace.re ≤ 1 := by linarith
  have hp1le : (block ρ.matrix true).trace.re ≤ 1 := by linarith
  have hd0 := mul_le_mul_of_nonneg_left hp0le (norm_nonneg (gram X - 1))
  have hd1 := mul_le_mul_of_nonneg_left hp1le (norm_nonneg (gram Y - 1))
  have hc := crossScore_le_norms X Y ρ.matrix
  change crossScore X Y ρ.matrix ≤ crossNormSum X Y ρ at hc
  nlinarith

/-- **Equation (`eq:R3` — No coherence without a repeated unitary)**:
In the fresh process (`q ≤ r + 1`),
`𝔼 Tr(S S† ρ_fresh) ≤ 1/2 + (r + 1)^2 / d + 7 (r + 1)^2 / (3 d)`. -/
theorem eq_R3_fresh_frame_bound {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r + 1) :
    (∫ UV : Sample A r,
      ((frame (switchSampleColumns UV) * (fresh tree hq UV).matrix).trace).re
      ∂ensembleMeasure (A := A) r r) ≤
      1 / 2 + ((r + 1 : ℝ) ^ 2) / (Fintype.card A : ℝ) +
        7 * ((r + 1 : ℝ) ^ 2) / (3 * (Fintype.card A : ℝ)) := by
  have hFrameCont : Continuous (fun UV : Sample A r =>
      ((frame (switchSampleColumns UV) * (fresh tree hq UV).matrix).trace).re) :=
    Complex.continuous_re.comp
      (((frame_continuous _ switchSample_continuous).matrix_mul
        (fresh_matrix_continuous tree hq)).matrix_trace)
  have hFrameInt := hFrameCont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := ensembleMeasure (A := A) r r)
  have hx := gramX_integrable (A := A) r
  have hy := gramY_integrable (A := A) r
  have hc := cross_integrable tree hq
  have hb0 : Integrable (fun UV : Sample A r =>
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * ‖gram (columns UV.1 UV.2) - 1‖)
      (ensembleMeasure (A := A) r r) :=
    (integrable_const (1 / 2 : ℝ)).add (hx.const_mul (1 / 2))
  have hb : Integrable (fun UV : Sample A r =>
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * ‖gram (columns UV.1 UV.2) - 1‖ +
        (1 / 2 : ℝ) * ‖gram (reverseColumns UV.1 UV.2) - 1‖)
      (ensembleMeasure (A := A) r r) :=
    hb0.add (hy.const_mul (1 / 2))
  have hmono := integral_mono hFrameInt (hb.add hc)
    (fun UV => frame_score_le_defects_add_cross
      (columns UV.1 UV.2) (reverseColumns UV.1 UV.2) (fresh tree hq UV))
  simp only [Pi.add_apply] at hmono
  rw [integral_add hb hc, integral_add hb0 (hy.const_mul (1 / 2)),
    integral_add (integrable_const (1 / 2 : ℝ)) (hx.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hmono
  have hX := defect_norm_average_le (A := A) r r
  have hY := reverse_defect_norm_average_le (A := A) r r
  have hC := cross_mean_bound tree hq
  have hRF := mul_le_mul_of_nonneg_left (reverseFactor_le (A := A))
    (show (0 : ℝ) ≤ (((r + 1) * (r + 1) : ℕ) : ℝ) by positivity)
  have hr2 : (((r + 1) * (r + 1) : ℕ) : ℝ) = (r + 1 : ℝ) ^ 2 := by
    push_cast; ring
  rw [hr2] at hX hY hC hRF
  have h7 : ((r + 1 : ℝ) ^ 2) * (7 / (3 * (Fintype.card A : ℝ))) =
      7 * ((r + 1 : ℝ) ^ 2) / (3 * (Fintype.card A : ℝ)) := by ring
  linarith

end ClaimPairAndR3

end

end ICO.C4NamedClaims

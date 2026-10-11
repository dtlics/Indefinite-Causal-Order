import ICO.GramControl
import ICO.QuantumDecision
import Mathlib.MeasureTheory.Integral.Average

/-! From an actual Gram effect to a worst-case channel-state distance. The
probability-space estimates remain explicit so that the Haar and collision
modules, rather than axioms, must supply them. -/

namespace ICO.GramWitness
open Matrix QIT ICO.CausalReverse ICO.ControlCoherence MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 0
variable {H I Ω : Type} [Fintype H] [DecidableEq H] [Nonempty H]
  [Fintype I] [DecidableEq I] [Nonempty I] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def crossNormSum (X Y : Matrix H I ℂ) (ρ : State (H × Bool)) : ℝ :=
  ∑ i : I, ‖star (controlVector (fun h => X h i) false) ⬝ᵥ
    (ρ.matrix *ᵥ controlVector (fun h => Y h i) true)‖

theorem mean_switch_witness_acceptance_le
    (X Y : Ω → Matrix H I ℂ) (ρ : Ω → State (H × Bool))
    (hx : Integrable (fun ω => ‖gram (X ω) - 1‖) μ)
    (hy : Integrable (fun ω => ‖gram (Y ω) - 1‖) μ)
    (hc : Integrable (fun ω => crossNormSum (X ω) (Y ω) (ρ ω)) μ)
    (ha : Integrable (fun ω =>
      ((witnessTest (switchColumns (X ω) (Y ω))).acceptProb (ρ ω) : ℝ)) μ) :
    (∫ ω, ((witnessTest (switchColumns (X ω) (Y ω))).acceptProb (ρ ω) : ℝ) ∂μ) ≤
      1 / 2 + (1 / 2 : ℝ) * (∫ ω, ‖gram (X ω) - 1‖ ∂μ) +
        (1 / 2 : ℝ) * (∫ ω, ‖gram (Y ω) - 1‖ ∂μ) +
          ∫ ω, crossNormSum (X ω) (Y ω) (ρ ω) ∂μ := by
  have hb0 : Integrable (fun ω => (1 / 2 : ℝ) + (1 / 2 : ℝ) * ‖gram (X ω) - 1‖) μ :=
    (integrable_const (1 / 2 : ℝ)).add (hx.const_mul (1 / 2))
  have hb : Integrable (fun ω => (1 / 2 : ℝ) + (1 / 2 : ℝ) * ‖gram (X ω) - 1‖ +
      (1 / 2 : ℝ) * ‖gram (Y ω) - 1‖) μ := hb0.add (hy.const_mul (1 / 2))
  have hh := integral_mono ha (hb.add hc)
    (fun ω => switch_witness_acceptance_le (X ω) (Y ω) (ρ ω))
  simp only [Pi.add_apply] at hh
  rw [integral_add hb hc,
    integral_add hb0
      (hy.const_mul (1 / 2)),
    integral_add (integrable_const (1 / 2 : ℝ)) (hx.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul] at hh
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

/-- All tests in this theorem are the valid Born-rule tests constructed from
the sampled columns. Coupling changes the physical ordinary output state,
not the normalization of a selected transcript. -/
theorem exists_distance_from_gram_estimates
    (X Y : Ω → Matrix H I ℂ) (ordinary fresh : Ω → State (H × Bool))
    (hdiag : ∀ ω i, gram (switchColumns (X ω) (Y ω)) i i = 1)
    (hx : Integrable (fun ω => ‖gram (X ω) - 1‖) μ)
    (hy : Integrable (fun ω => ‖gram (Y ω) - 1‖) μ)
    (hz : Integrable (fun ω => ‖gram (switchColumns (X ω) (Y ω)) - 1‖) μ)
    (hc : Integrable (fun ω => crossNormSum (X ω) (Y ω) (fresh ω)) μ)
    (hordinary : Integrable (fun ω =>
      ((witnessTest (switchColumns (X ω) (Y ω))).acceptProb (ordinary ω) : ℝ)) μ)
    (hfresh : Integrable (fun ω =>
      ((witnessTest (switchColumns (X ω) (Y ω))).acceptProb (fresh ω) : ℝ)) μ)
    (hideal : Integrable (fun ω =>
      ((witnessTest (switchColumns (X ω) (Y ω))).acceptProb
        (idealState (switchColumns (X ω) (Y ω)) (hdiag ω)) : ℝ)) μ)
    (gX gY gZ c η : ℝ)
    (hX : (∫ ω, ‖gram (X ω) - 1‖ ∂μ) ≤ gX)
    (hY : (∫ ω, ‖gram (Y ω) - 1‖ ∂μ) ≤ gY)
    (hZ : (∫ ω, ‖gram (switchColumns (X ω) (Y ω)) - 1‖ ∂μ) ≤ gZ)
    (hC : (∫ ω, crossNormSum (X ω) (Y ω) (fresh ω) ∂μ) ≤ c)
    (hCoupling : ∀ ω, (ordinary ω).normalizedTraceDistance (fresh ω) ≤ η) :
    ∃ ω, 1 / 2 - gZ - (1 / 2 : ℝ) * gX - (1 / 2 : ℝ) * gY - c - η ≤
      (idealState (switchColumns (X ω) (Y ω)) (hdiag ω)).normalizedTraceDistance
        (ordinary ω) := by
  let T := fun ω => witnessTest (switchColumns (X ω) (Y ω))
  let S := fun ω => idealState (switchColumns (X ω) (Y ω)) (hdiag ω)
  have hMeanFresh := mean_switch_witness_acceptance_le X Y fresh hx hy hc hfresh
  have hMeanIdeal := mean_ideal_acceptance_ge_one_sub_defect
    (fun ω => switchColumns (X ω) (Y ω)) hdiag hideal hz
  have hPoint (ω : Ω) : (T ω |>.acceptProb (ordinary ω) : ℝ) ≤
      (T ω |>.acceptProb (fresh ω) : ℝ) + η := by
    have hh := ICO.QuantumDecision.accept_gap_le_traceDistance (T ω)
      (ordinary ω) (fresh ω)
    have hη := hCoupling ω
    linarith
  have hMeanOrdinary := integral_mono hordinary (hfresh.add (integrable_const η)) hPoint
  simp only [Pi.add_apply] at hMeanOrdinary
  rw [integral_add hfresh (integrable_const η)] at hMeanOrdinary
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hMeanOrdinary
  have hGap : 1 / 2 - gZ - (1 / 2 : ℝ) * gX - (1 / 2 : ℝ) * gY - c - η ≤
      ∫ ω, (T ω |>.acceptProb (S ω) : ℝ) -
        (T ω |>.acceptProb (ordinary ω) : ℝ) ∂μ := by
    rw [integral_sub hideal hordinary]
    linarith
  obtain ⟨ω, hω⟩ := exists_integral_le (hideal.sub hordinary)
  refine ⟨ω, (hGap.trans hω).trans ?_⟩
  exact ICO.QuantumDecision.accept_gap_le_traceDistance (T ω) (S ω) (ordinary ω)

#print axioms mean_switch_witness_acceptance_le
#print axioms exists_distance_from_gram_estimates
end
end ICO.GramWitness

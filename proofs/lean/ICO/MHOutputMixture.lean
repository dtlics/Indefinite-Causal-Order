import ICO.MHTraceIntegral

/-! Actual output mixtures obtained from close purified vectors. The output
map can be rectangular and can erase any private environment or history. -/
namespace ICO.MHOutputMixture
open Matrix QIT MeasureTheory ICO.PureHybrid ICO.RecordingDistance ICO.MHTraceIntegral
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1400000
variable {H O Ω : Type*} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
  [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

local instance cmContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

theorem outer_continuous (x : Ω → EuclideanSpace ℂ H) (hx : Continuous x) :
    Continuous (fun ω => outer (x ω) (x ω)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((PiLp.continuous_apply 2 (fun _ : H => ℂ) i).comp hx).mul
    (((PiLp.continuous_apply 2 (fun _ : H => ℂ) j).comp hx).star)

theorem pure_output_distance_le (Φ : MatrixMap H O) (hΦ : MatrixMap.TraceNonincreasingCP Φ)
    (x y : EuclideanSpace ℂ H) (hx : ‖x‖≤1) (hy : ‖y‖≤1) :
    normalizedTraceDistance (Φ (outer x x)) (Φ (outer y y)) ≤ ‖x-y‖ := by
  have px : (outer x x).PosSemidef := Matrix.posSemidef_vecMulVec_self_star (fun i => x i)
  have py : (outer y y).PosSemidef := Matrix.posSemidef_vecMulVec_self_star (fun i => y i)
  exact (distance_contract Φ hΦ _ _ px py).trans (subnormalized_pure_distance_le x y hx hy)

theorem mean_output_distance_le (Φ : MatrixMap H O) (hΦ : MatrixMap.TraceNonincreasingCP Φ)
    (x y : Ω → EuclideanSpace ℂ H) (hx : Continuous x) (hy : Continuous y)
    (hnx : ∀ ω, ‖x ω‖≤1) (hny : ∀ ω, ‖y ω‖≤1) :
    normalizedTraceDistance (∫ ω, Φ (outer (x ω) (x ω)) ∂μ)
      (∫ ω, Φ (outer (y ω) (y ω)) ∂μ) ≤ ∫ ω, ‖x ω-y ω‖ ∂μ := by
  have hM := Φ.continuous_of_finiteDimensional.comp (outer_continuous x hx)
  have hN := Φ.continuous_of_finiteDimensional.comp (outer_continuous y hy)
  have hMi := hM.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := μ)
  have hNi := hN.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := μ)
  have hTN := (traceNorm_continuous.comp (hM.sub hN)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := μ)
  apply (distance_integral_le _ _ hMi hNi hTN).trans
  have hdist : Integrable (fun ω => normalizedTraceDistance
      (Φ (outer (x ω) (x ω))) (Φ (outer (y ω) (y ω)))) μ := hTN.const_mul (1/2)
  exact integral_mono hdist ((hx.sub hy).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (fun ω => pure_output_distance_le Φ hΦ _ _ (hnx ω) (hny ω))

theorem output_distance_of_mean_error (Φ : MatrixMap H O) (hΦ : MatrixMap.TraceNonincreasingCP Φ)
    (x y : Ω → EuclideanSpace ℂ H) (hx : Continuous x) (hy : Continuous y)
    (hnx : ∀ ω, ‖x ω‖≤1) (hny : ∀ ω, ‖y ω‖≤1) (ε : ℝ)
    (hε : (∫ ω, ‖x ω-y ω‖ ∂μ)≤ε) :
    normalizedTraceDistance (∫ ω, Φ (outer (x ω) (x ω)) ∂μ)
      (∫ ω, Φ (outer (y ω) (y ω)) ∂μ) ≤ ε :=
  (mean_output_distance_le Φ hΦ x y hx hy hnx hny).trans hε

#print axioms mean_output_distance_le
#print axioms output_distance_of_mean_error
end
end ICO.MHOutputMixture


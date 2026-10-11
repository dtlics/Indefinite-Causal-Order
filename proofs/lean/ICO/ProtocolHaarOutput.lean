import ICO.ProtocolContinuity
import ICO.ProtocolRecordingBound
import ICO.MHHaarPurifiedMixture
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace ICO.ProtocolHaarOutput
open Matrix QIT MeasureTheory ICO.SequentialIsometry ICO.RecordingHistory
  ICO.RecordingPurifiedProtocol ICO.PureHybrid ICO.MHHaarPurifiedMixture
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
universe u
set_option maxHeartbeats 2400000
variable {A M O B I : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

local instance matrixNonUnitalCStar {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NonUnitalCStarAlgebra (CMatrix ι) := ⟨⟩

local instance cmContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

def response {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ)
    (t : ℕ) (U : Matrix.unitaryGroup A ℂ) :
    EuclideanSpace ℂ (A×(History A t×tail.tailMemory t)) :=
  WithLp.toLp 2 (ICO.ProtocolLudersTrajectory.run tail (U:CMatrix A) v t)

theorem response_continuous {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) (t : ℕ) :
    Continuous (response tail v t) :=
  (PiLp.continuous_toLp 2 _).comp
    ((ICO.ProtocolLudersTrajectory.run_continuous tail v t).comp continuous_subtype_val)

def visibleDensity {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ)
    (t : ℕ) (U : Matrix.unitaryGroup A ℂ) : CMatrix (A×tail.tailMemory t) :=
  eraseHistory.map (outer (response tail v t U) (response tail v t U))

theorem visibleDensity_evolution {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M → ℂ) (t : ℕ) (U : Matrix.unitaryGroup A ℂ) :
    visibleDensity tail v t U =
      tail.tailEvolution (ICO.SwitchObservable.basisProjection (U:CMatrix A)) (rankOneMatrix v) t :=
  ICO.ProtocolLudersTrajectory.run_erasure tail (U:CMatrix A) v t

theorem visibleDensity_continuous {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) (t : ℕ) :
    Continuous (visibleDensity tail v t) :=
  eraseHistory.map.continuous_of_finiteDimensional.comp
    (ICO.MHOutputMixture.outer_continuous _ (response_continuous tail v t))

def haarDensity {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) (t : ℕ) :
    CMatrix (A×tail.tailMemory t) :=
  ∫ U,visibleDensity tail v t U ∂unitaryHaarMeasure (a:=A)

theorem haarDensity_pos {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) (t : ℕ) :
    (haarDensity tail v t).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply integral_nonneg
  intro U
  exact (eraseHistory.mapsPositive _
    (Matrix.posSemidef_vecMulVec_self_star (fun i => response tail v t U i))).nonneg

theorem tailEvolution_trace {q : ℕ} (tail : Protocol A (A×M) O q)
    (U : I → CMatrix A) (hU : ∑ i,(U i).conjTranspose*U i=1)
    (X : CMatrix (A×M)) (t : ℕ) : (tail.tailEvolution U X t).trace=X.trace := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hk := (ICO.ClassicalDilation.isometryChannel (tail.tailKnown t)
      (tail.tailKnown_isometry t)).tracePreserving
        (ICO.AllChannelDilation.oracleMap U (tail.tailEvolution U X t))
    simp only [ICO.ClassicalDilation.isometryChannel_apply] at hk
    have hu := (ICO.AllChannelDilation.oracleChannel (M:=tail.tailMemory t) U hU).tracePreserving
      (tail.tailEvolution U X t)
    exact hk.trans (hu.trans ih)

theorem haarDensity_trace {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) (t : ℕ) :
    (haarDensity tail v t).trace=(rankOneMatrix v).trace := by
  have hi := (visibleDensity_continuous tail v t).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ:=unitaryHaarMeasure (a:=A))
  have ht := (ICO.MHTraceIntegral.traceMulCLM (1 : CMatrix (A×tail.tailMemory t))).integral_comp_comm hi
  change (∫ U,(visibleDensity tail v t U * 1).trace ∂unitaryHaarMeasure (a:=A)) =
    ((∫ U,visibleDensity tail v t U ∂unitaryHaarMeasure (a:=A))*1).trace at ht
  simp only [Matrix.mul_one] at ht
  rw [haarDensity,←ht]
  have hconst (U : Matrix.unitaryGroup A ℂ) :
      (visibleDensity tail v t U).trace=(rankOneMatrix v).trace := by
    rw [visibleDensity_evolution]
    exact tailEvolution_trace tail _
      (ICO.SwitchObservable.hidden_basis_kraus_complete _ U.property.1 U.property.2) _ t
  simp_rw [hconst]
  simp

/-- The actual public output averaged over one Haar hidden basis equals the
uniform phase-permutation purification averaged over its two Haar rotations. -/
theorem purified_haar_output {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) :
    (∫ D, ∫ C, tail.terminalChannel.map
      (eraseHistory.map (partialTraceB
        (outer (purifiedResponse (response tail v (q+1)) C D)
          (purifiedResponse (response tail v (q+1)) C D))))
      ∂unitaryHaarMeasure (a:=A) ∂unitaryHaarMeasure (a:=A)) =
    ∫ U, tail.map (ICO.SwitchObservable.basisProjection (U:CMatrix A))
      (ICO.AllChannelDilation.oracleMap (ICO.SwitchObservable.basisProjection (U:CMatrix A))
        (rankOneMatrix v)) ∂unitaryHaarMeasure (a:=A) := by
  change (∫ D, ∫ C, (tail.terminalChannel.map.comp eraseHistory.map)
    (partialTraceB (outer (purifiedResponse (response tail v (q+1)) C D)
      (purifiedResponse (response tail v (q+1)) C D)))
      ∂unitaryHaarMeasure (a:=A) ∂unitaryHaarMeasure (a:=A)) = _
  rw [erased_haar_two _ _ (response_continuous tail v (q+1))]
  apply integral_congr_ae
  filter_upwards [] with U
  change tail.terminalChannel.map (visibleDensity tail v (q+1) U)=_
  rw [visibleDensity_evolution]
  exact tail.tailEvolution_output _ _

theorem purified_haar_visible {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) (t : ℕ) :
    (∫ D, ∫ C, eraseHistory.map (partialTraceB
      (outer (purifiedResponse (response tail v t) C D)
        (purifiedResponse (response tail v t) C D)))
      ∂unitaryHaarMeasure (a:=A) ∂unitaryHaarMeasure (a:=A)) = haarDensity tail v t :=
  erased_haar_two eraseHistory.map _ (response_continuous tail v t)

theorem haarDensity_output {q : ℕ} (tail : Protocol A (A×M) O q) (v : A×M → ℂ) :
    tail.terminalChannel.map (haarDensity tail v (q+1)) =
      ∫ U, tail.map (ICO.SwitchObservable.basisProjection (U:CMatrix A))
        (ICO.AllChannelDilation.oracleMap (ICO.SwitchObservable.basisProjection (U:CMatrix A))
          (rankOneMatrix v)) ∂unitaryHaarMeasure (a:=A) := by
  have hi := (visibleDensity_continuous tail v (q+1)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ:=unitaryHaarMeasure (a:=A))
  have ht := tail.terminalChannel.map.toContinuousLinearMap.integral_comp_comm hi
  change (∫ U,tail.terminalChannel.map (visibleDensity tail v (q+1) U)
    ∂unitaryHaarMeasure (a:=A))=tail.terminalChannel.map (haarDensity tail v (q+1)) at ht
  rw [←ht]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [visibleDensity_evolution]
  exact tail.tailEvolution_output _ _

/-- Every physical and initialization premise of the ordinary-circuit endpoint
is discharged here. The only remaining premise is the quantitative comparison
of its Haar-averaged marginal with its concrete recording trajectory. -/
theorem haar_output_bound {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M → ℂ) (hv : ‖WithLp.toLp 2 v‖≤1) (hmass : (rankOneMatrix v).trace.re=1)
    (hqd : 2*(q+1)<Fintype.card A) (ε : ℝ)
    (hHaar : normalizedTraceDistance (haarDensity tail v (q+1))
      (visible (q+1) (ICO.ProtocolRecordingTrajectory.run tail
        ICO.RecordingOracleAlgebra.forwardRecording v (q+1))) ≤ ε) :
    normalizedTraceDistance
      (∫ U, tail.map (ICO.SwitchObservable.basisProjection (U:CMatrix A))
        (ICO.AllChannelDilation.oracleMap (ICO.SwitchObservable.basisProjection (U:CMatrix A))
          (rankOneMatrix v)) ∂unitaryHaarMeasure (a:=A))
      (tail.map depolarizingKraus (ICO.AllChannelDilation.oracleMap depolarizingKraus (rankOneMatrix v))) ≤
      2*ε + 4*(q+1 : ℕ)*Real.sqrt (1/((Fintype.card A : ℝ)-(2*(q+1) : ℕ))) +
        (q+1 : ℕ)^2/(Fintype.card A : ℝ) := by
  rw [←haarDensity_output]
  exact ICO.ProtocolRecordingBound.output_bound tail v hv hmass hqd
    (haarDensity tail v (q+1)) ((congrArg Complex.re (haarDensity_trace tail v (q+1))).trans hmass)
    (haarDensity_pos tail v (q+1)) ε hHaar

#print axioms haar_output_bound
#print axioms haarDensity_pos
#print axioms haarDensity_trace
#print axioms purified_haar_output
end
end ICO.ProtocolHaarOutput

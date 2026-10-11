import ICO.RecordingOracleAlgebra
import ICO.RecordingDistance

/-!
# Completely positive contractions for the recording oracle

The maps here are constructed from the actual finite recording matrices.
Their contraction and lost-memory statements have no physical bridge
hypothesis: they follow from the checked initial projection identities.
-/

namespace ICO.RecordingOracleChannel

open QIT ICO.RecordingOperatorSupport ICO.RecordingOracleAlgebra
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {a : Type*} [Fintype a] [DecidableEq a]

def singleOperatorMap (A : CMatrix a) : MatrixMap a a :=
  MatrixMap.ofKraus (fun _ : Unit => A)

theorem singleOperatorMap_apply (A X : CMatrix a) :
    singleOperatorMap A X = A * X * A.conjTranspose := by
  simp [singleOperatorMap, MatrixMap.ofKraus]

theorem singleOperatorMap_trace_duality (A X : CMatrix a) :
    (singleOperatorMap A X).trace = (X * (A.conjTranspose * A)).trace := by
  have h := MatrixMap.ofKraus_trace_duality (fun _ : Unit => A) X (1 : CMatrix a)
  simpa [singleOperatorMap, MatrixMap.krausAdjoint] using h

theorem singleOperatorMap_TNI_of_projection (A : CMatrix a)
    (hA : IsStarProjection (A.conjTranspose * A)) :
    MatrixMap.TraceNonincreasingCP (singleOperatorMap A) := by
  refine ⟨MatrixMap.ofKraus_completelyPositive _, ?_⟩
  intro X hX
  have hLoss : (1 - A.conjTranspose * A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hA.one_sub.nonneg
  have h := QIT.cMatrix_trace_mul_posSemidef_re_nonneg hX hLoss
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub,
    ← singleOperatorMap_trace_duality] at h
  simpa only [Complex.sub_re, sub_nonneg] using h

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem forwardRecording_TNI :
    MatrixMap.TraceNonincreasingCP (singleOperatorMap (forwardRecording (α := α))) :=
  singleOperatorMap_TNI_of_projection _ forward_initial_projection

theorem inverseRecording_TNI :
    MatrixMap.TraceNonincreasingCP (singleOperatorMap (inverseRecording (α := α))) :=
  singleOperatorMap_TNI_of_projection _ inverse_initial_projection

/-- The visible memory lost during the actual inverse recording operation
    is positive, even for entangled query, record, and memory inputs. -/
theorem inverseRecording_lost_memory {μ : Type*} [Fintype μ] [DecidableEq μ]
    (ρ : CMatrix (Basis α × μ)) (hρ : ρ.PosSemidef) :
    (QIT.partialTraceA ρ - QIT.partialTraceA
      (MatrixMap.kron (singleOperatorMap inverseRecording)
        (Channel.idChannel μ).map ρ)).PosSemidef :=
  ICO.RecordingDistance.local_contraction_loses_positive_memory _ inverseRecording_TNI ρ hρ

theorem inverseRecording_distance_contract (ρ σ : CMatrix (Basis α))
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    normalizedTraceDistance (singleOperatorMap inverseRecording ρ)
      (singleOperatorMap inverseRecording σ) ≤ normalizedTraceDistance ρ σ :=
  ICO.RecordingDistance.distance_contract _ inverseRecording_TNI ρ σ hρ hσ

end
end ICO.RecordingOracleChannel

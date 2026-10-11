import ICO.RecordingProcess
import ICO.RecordingWrapperDistance

/-!
# The actual active-basis inverse and visible growing wrapper

The inverse operation is followed by the explicit supported-basis compression.
On the reachable invariant sector this compression is exact, as proved in
`RecordingSupportCompression`. It is a CP contraction on every input, so its
lost-memory estimate needs no extra positivity premise.
-/

namespace ICO.RecordingActiveWrapper

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingOracleChannel ICO.RecordingFreshOutput ICO.RecordingCopyIdentity
  ICO.RecordingSupportCompression ICO.RecordingWrapperDistance
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {a b c : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

def rectSingleOperatorMap (A : Matrix b a ℂ) : MatrixMap a b :=
  MatrixMap.ofKraus (fun _ : Unit => A)

theorem rectSingleOperatorMap_TNI (A : Matrix b a ℂ)
    (hA : IsStarProjection (A.conjTranspose * A)) :
    MatrixMap.TraceNonincreasingCP (rectSingleOperatorMap A) := by
  refine ⟨MatrixMap.ofKraus_completelyPositive _, ?_⟩
  intro X hX
  have hLoss : (1 - A.conjTranspose * A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hA.one_sub.nonneg
  have h := QIT.cMatrix_trace_mul_posSemidef_re_nonneg hX hLoss
  have hdual := MatrixMap.ofKraus_trace_duality (fun _ : Unit => A) X (1 : CMatrix b)
  have hdual' : (rectSingleOperatorMap A X).trace = (X * (A.conjTranspose * A)).trace := by
    simpa only [rectSingleOperatorMap, Matrix.mul_one, MatrixMap.krausAdjoint,
      Finset.univ_unique, Finset.sum_singleton] using hdual
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, ← hdual'] at h
  simpa only [Complex.sub_re, sub_nonneg] using h

theorem rectangular_image_projection (J : Matrix b a ℂ)
    (hJ : J.conjTranspose * J = 1) : IsStarProjection (J * J.conjTranspose) := by
  refine ⟨?_, ?_⟩
  · change (J * J.conjTranspose) * (J * J.conjTranspose) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J.conjTranspose, hJ,
      Matrix.one_mul]
  · change (J * J.conjTranspose).conjTranspose = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem basisCompression_TNI (f : a → b) (hf : Function.Injective f) :
    MatrixMap.TraceNonincreasingCP (rectSingleOperatorMap (basisEmbedding f).conjTranspose) := by
  apply rectSingleOperatorMap_TNI
  rw [Matrix.conjTranspose_conjTranspose]
  exact rectangular_image_projection _ (basisEmbedding_gram f hf)

theorem TNI_comp (Φ : MatrixMap a b) (Ψ : MatrixMap b c)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ) (hΨ : MatrixMap.TraceNonincreasingCP Ψ) :
    MatrixMap.TraceNonincreasingCP (Ψ.comp Φ) := by
  refine ⟨MatrixMap.isCompletelyPositive_comp _ _ hΨ.completelyPositive hΦ.completelyPositive, ?_⟩
  intro X hX
  exact (hΨ.traceNonincreasing (Φ X) (hΦ.mapsPositive X hX)).trans (hΦ.traceNonincreasing X hX)

variable {α μ : Type*} [Fintype α] [DecidableEq α] [Fintype μ] [DecidableEq μ]

def activeSourceEmbed (m : ℕ) (s : ActiveSource α m) : Basis α := s.val.val

theorem activeSourceEmbed_injective (m : ℕ) :
    Function.Injective (activeSourceEmbed (α := α) m) := by
  intro s t h
  exact Subtype.ext (Subtype.ext h)

def activeInverse (m : ℕ) : MatrixMap (Basis α) (ActiveSource α m) :=
  (rectSingleOperatorMap (basisEmbedding (activeSourceEmbed m)).conjTranspose).comp
    (singleOperatorMap inverseRecording)

theorem activeInverse_TNI (m : ℕ) :
    MatrixMap.TraceNonincreasingCP (activeInverse (α := α) m) :=
  TNI_comp _ _ inverseRecording_TNI
    (basisCompression_TNI _ (activeSourceEmbed_injective m))

def activeInverseWithMemory (m : ℕ) :
    MatrixMap (Basis α × μ) (ActiveSource α m × μ) :=
  MatrixMap.kron (activeInverse m) (Channel.idChannel μ).map

theorem activeInverseWithMemory_TNI (m : ℕ) :
    MatrixMap.TraceNonincreasingCP (activeInverseWithMemory (α := α) (μ := μ) m) :=
  MatrixMap.traceNonincreasingCP_kron_id (activeInverse_TNI m)

def visibleGrowingWrapper (m : ℕ) (ρ : CMatrix (Basis α × μ)) : CMatrix (α × μ) :=
  MatrixMap.kron (MatrixMap.ofKraus (copiedLeftKraus m)) (Channel.idChannel μ).map
    (activeInverseWithMemory m ρ)

/-- The concrete CP inverse/compression/copy/A map satisfies the local bound
    with its actual lost trace. There is no assumed memory-order premise. -/
theorem visibleGrowingWrapper_distance (m : ℕ) (hm : m < Fintype.card α)
    (ρ : CMatrix (Basis α × μ)) (hρ : ρ.PosSemidef) (hmass : ρ.trace.re ≤ 1) :
    normalizedTraceDistance (visibleGrowingWrapper m ρ)
      (uniformOutput (QIT.partialTraceA ρ)) ≤
      (m : ℝ) / (Fintype.card α : ℝ) +
        (ρ.trace.re - (activeInverseWithMemory m ρ).trace.re) / 2 := by
  have hInv := activeInverseWithMemory_TNI (α := α) (μ := μ) m
  have hτ := hInv.mapsPositive ρ hρ
  have hmassτ := (hInv.traceNonincreasing ρ hρ).trans hmass
  have hLoss := ICO.RecordingDistance.local_contraction_loses_positive_memory
    (activeInverse m) (activeInverse_TNI m) ρ hρ
  have h := copiedLeft_with_lost_memory m hm (activeInverseWithMemory m ρ)
    hτ hmassτ (QIT.partialTraceA ρ) hLoss
  rwa [QIT.partialTraceA_trace] at h

theorem copiedLeft_tracePreserving (m : ℕ) (hm : m < Fintype.card α) :
    MatrixMap.IsTracePreserving (MatrixMap.ofKraus (copiedLeftKraus (α := α) m)) := by
  rw [copiedLeftKraus_eq_recordingKraus m hm]
  exact (freshRecordingChannel (activeEnvironment m) (activeEnvironment_eq_iff m)
    (outputForbidden m) (fun s => lt_of_le_of_lt (outputForbidden_card_le m s) hm)).tracePreserving

theorem visibleGrowingWrapper_trace (m : ℕ) (hm : m < Fintype.card α)
    (ρ : CMatrix (Basis α × μ)) :
    (visibleGrowingWrapper m ρ).trace = (activeInverseWithMemory m ρ).trace :=
  MatrixMap.isTracePreserving_kron _ _ (copiedLeft_tracePreserving m hm)
    (Channel.idChannel μ).tracePreserving _

theorem visibleGrowingWrapper_distance_by_output_mass (m : ℕ) (hm : m < Fintype.card α)
    (ρ : CMatrix (Basis α × μ)) (hρ : ρ.PosSemidef) (hmass : ρ.trace.re ≤ 1) :
    normalizedTraceDistance (visibleGrowingWrapper m ρ)
      (uniformOutput (QIT.partialTraceA ρ)) ≤
      (m : ℝ) / (Fintype.card α : ℝ) +
        (ρ.trace.re - (visibleGrowingWrapper m ρ).trace.re) / 2 := by
  rw [visibleGrowingWrapper_trace m hm]
  exact visibleGrowingWrapper_distance m hm ρ hρ hmass

end
end ICO.RecordingActiveWrapper

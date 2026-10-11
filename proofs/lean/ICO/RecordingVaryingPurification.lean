import ICO.RecordingPurifiedProtocol
import ICO.RecordingVaryingDistance

namespace ICO.RecordingVaryingPurification
open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingPublicHistory ICO.RecordingPublicStep ICO.RecordingProcess
  ICO.RecordingHistory ICO.RecordingRetainedProcess ICO.RecordingKnownChannel
  ICO.RecordingActiveWrapper ICO.RecordingDistance ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1600000
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
variable {μ : ℕ → Type*} [∀ t,Fintype (μ t)] [∀ t,DecidableEq (μ t)]

def rectPublicChannel {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (K : Matrix (α × b) (α × a) ℂ) (hK : K.conjTranspose*K=1) : Channel (α×a) (α×b) :=
  Channel.ofReferenceIsometry ⟨K,hK⟩

theorem rectPublicChannel_map {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (K : Matrix (α × b) (α × a) ℂ) (hK : K.conjTranspose*K=1) :
    (rectPublicChannel K hK).map=rectSingleOperatorMap K := rfl

theorem modified_support
    (ψ : (t : ℕ) → Basis α × (History α t × μ t) → ℂ)
    (K : (t : ℕ) → Matrix (α × μ (t+1)) (α × μ t) ℂ)
    (hempty : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hstep : ∀ t, ψ (t + 1) =
      stepMatrix leftInsertion (publicStep (h := History α t) (K t)) *ᵥ ψ t) :
    ∀ t i, ψ t i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ 2 * t := by
  apply iterated_modified_wrapper_support (fun t => History α t × μ t) ψ
    (fun t => publicStep (h := History α t) (K t)) hempty
  intro t
  rw [hstep t, stepMatrix, ← Matrix.mulVec_mulVec, wrapperMatrix_A_mulVec]
  rfl

theorem modified_reduced_recurrence
    (ψ : (t : ℕ) → Basis α × (History α t × μ t) → ℂ)
    (K : (t : ℕ) → Matrix (α × μ (t+1)) (α × μ t) ℂ) (hK : ∀ t, (K t).conjTranspose * K t = 1)
    (hempty : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hstep : ∀ t, ψ (t + 1) =
      stepMatrix leftInsertion (publicStep (h := History α t) (K t)) *ᵥ ψ t)
    (t : ℕ) :
    reduced (t + 1) (ψ (t + 1)) =
      liftKnown (rectPublicChannel (K t) (hK t)).map
        (retainedGrowingWrapper (2 * t + 1) (reduced t (ψ t))) := by
  rw [reduced, hstep t, stepMatrix, ← Matrix.mulVec_mulVec,
    wrapperMatrix_A_mulVec, publicStep_mulVec, rectPublicChannel_map]
  exact purified_modified_step_reduction (2 * t) (K t) (ψ t)
    (modified_support ψ K hempty hstep t)

theorem purified_modified_depolarizing_distance
    (ψ : (t : ℕ) → Basis α × (History α t × μ t) → ℂ)
    (K : (t : ℕ) → Matrix (α × μ (t+1)) (α × μ t) ℂ) (hK : ∀ t, (K t).conjTranspose * K t = 1)
    (hempty : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hmass : (rankOneMatrix (ψ 0)).trace.re = 1)
    (hstep : ∀ t, ψ (t + 1) =
      stepMatrix leftInsertion (publicStep (h := History α t) (K t)) *ᵥ ψ t)
    (σ : (t : ℕ) → CMatrix (α × μ t))
    (hinit : visible 0 (ψ 0) = σ 0)
    (hideal : ∀ t, σ (t + 1) =
      (ICO.RecordingVaryingDistance.followedBy (rectPublicChannel (K t) (hK t))).map (σ t))
    (q : ℕ) (hqd : 2 * q < Fintype.card α) :
    normalizedTraceDistance (visible q (ψ q)) (σ q) ≤
      (q : ℝ) ^ 2 / (Fintype.card α : ℝ) +
        (1 - (visible q (ψ q)).trace.re) / 2 := by
  have h := ICO.RecordingVaryingDistance.modified_depolarizing_distance (fun t => reduced t (ψ t)) σ
    (fun t => rectPublicChannel (K t) (hK t)) q hqd
    (eraseHistory.mapsPositive _ (rankOneMatrix_pos _))
    (by
      exact (congrArg Complex.re ((eraseHistory (a := Basis α)
        (h := History α 0) (μ := μ 0)).tracePreserving (rankOneMatrix (ψ 0)))).trans hmass)
    hinit (fun t _ => modified_reduced_recurrence ψ K hK hempty hstep t)
    (fun t _ => hideal t)
  simpa only [visible, visibleMap_trace] using h

#print axioms purified_modified_depolarizing_distance
end
end ICO.RecordingVaryingPurification


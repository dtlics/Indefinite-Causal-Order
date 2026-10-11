import ICO.RecordingPublicStep
import ICO.RecordingAdaptiveDistance
import ICO.RecordingCombination

/-! Fully specified public-isometry protocols with inaccessible copied
query histories. The only remaining external comparison in the final
assembly is the analytic Haar-to-recording theorem. -/

namespace ICO.RecordingPurifiedProtocol

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingPublicHistory ICO.RecordingPublicStep ICO.RecordingProcess
  ICO.RecordingHistory ICO.RecordingRetainedProcess ICO.RecordingKnownChannel
  ICO.RecordingActiveWrapper ICO.RecordingAdaptiveDistance
  ICO.RecordingDepolarizing ICO.RecordingOracleAlgebra ICO.RecordingPartialIsometry
  ICO.RecordingDistance ICO.RecordingCombination
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section
set_option maxHeartbeats 2000000

universe u
def History (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | t + 1 => α × History α t

instance historyFintype (α : Type u) [Fintype α] (t : ℕ) : Fintype (History α t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ t ih =>
      letI : Fintype (History α t) := ih
      exact inferInstanceAs (Fintype (α × History α t))

instance historyDecidableEq (α : Type u) [DecidableEq α] (t : ℕ) : DecidableEq (History α t) := by
  induction t with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ t ih =>
      letI : DecidableEq (History α t) := ih
      exact inferInstanceAs (DecidableEq (α × History α t))

variable {α : Type u} {μ : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype μ] [DecidableEq μ]

def publicChannel (K : CMatrix (α × μ)) (hK : K.conjTranspose * K = 1) :
    Channel (α × μ) (α × μ) := Channel.ofReferenceIsometry ⟨K, hK⟩

theorem publicChannel_map (K : CMatrix (α × μ)) (hK : K.conjTranspose * K = 1) :
    (publicChannel K hK).map = rectSingleOperatorMap K := rfl

def reduced (t : ℕ) (v : Basis α × (History α t × μ) → ℂ) : CMatrix (Basis α × μ) :=
  eraseHistory.map (rankOneMatrix v)

def visible (t : ℕ) (v : Basis α × (History α t × μ) → ℂ) : CMatrix (α × μ) :=
  visibleMap (reduced t v)

theorem modified_support
    (ψ : (t : ℕ) → Basis α × (History α t × μ) → ℂ)
    (K : ℕ → CMatrix (α × μ))
    (hempty : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hstep : ∀ t, ψ (t + 1) =
      stepMatrix leftInsertion (publicStep (h := History α t) (K t)) *ᵥ ψ t) :
    ∀ t i, ψ t i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ 2 * t := by
  apply iterated_modified_wrapper_support (fun t => History α t × μ) ψ
    (fun t => publicStep (h := History α t) (K t)) hempty
  intro t
  rw [hstep t, stepMatrix, ← Matrix.mulVec_mulVec, wrapperMatrix_A_mulVec]
  rfl

theorem modified_reduced_recurrence
    (ψ : (t : ℕ) → Basis α × (History α t × μ) → ℂ)
    (K : ℕ → CMatrix (α × μ)) (hK : ∀ t, (K t).conjTranspose * K t = 1)
    (hempty : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hstep : ∀ t, ψ (t + 1) =
      stepMatrix leftInsertion (publicStep (h := History α t) (K t)) *ᵥ ψ t)
    (t : ℕ) :
    reduced (t + 1) (ψ (t + 1)) =
      liftKnown (publicChannel (K t) (hK t)).map
        (retainedGrowingWrapper (2 * t + 1) (reduced t (ψ t))) := by
  rw [reduced, hstep t, stepMatrix, ← Matrix.mulVec_mulVec,
    wrapperMatrix_A_mulVec, publicStep_mulVec, publicChannel_map]
  exact purified_modified_step_reduction (2 * t) (K t) (ψ t)
    (modified_support ψ K hempty hstep t)

theorem purified_modified_depolarizing_distance
    (ψ : (t : ℕ) → Basis α × (History α t × μ) → ℂ)
    (K : ℕ → CMatrix (α × μ)) (hK : ∀ t, (K t).conjTranspose * K t = 1)
    (hempty : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hmass : (rankOneMatrix (ψ 0)).trace.re = 1)
    (hstep : ∀ t, ψ (t + 1) =
      stepMatrix leftInsertion (publicStep (h := History α t) (K t)) *ᵥ ψ t)
    (σ : ℕ → CMatrix (α × μ))
    (hinit : visible 0 (ψ 0) = σ 0)
    (hideal : ∀ t, σ (t + 1) =
      (followedBy (publicChannel (K t) (hK t))).map (σ t))
    (q : ℕ) (hqd : 2 * q < Fintype.card α) :
    normalizedTraceDistance (visible q (ψ q)) (σ q) ≤
      (q : ℝ) ^ 2 / (Fintype.card α : ℝ) +
        (1 - (visible q (ψ q)).trace.re) / 2 := by
  have h := modified_depolarizing_distance (fun t => reduced t (ψ t)) σ
    (fun t => publicChannel (K t) (hK t)) q hqd
    (eraseHistory.mapsPositive _ (rankOneMatrix_pos _))
    (by
      exact (congrArg Complex.re ((eraseHistory (a := Basis α)
        (h := History α 0) (μ := μ)).tracePreserving (rankOneMatrix (ψ 0)))).trans hmass)
    hinit (fun t _ => modified_reduced_recurrence ψ K hK hempty hstep t)
    (fun t _ => hideal t)
  simpa only [visible, visibleMap_trace] using h

end
end ICO.RecordingPurifiedProtocol

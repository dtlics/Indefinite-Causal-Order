import ICO.RecordingKnownChannel
import ICO.RecordingDepolarizing

/-!
# Adaptive retained-record versus depolarizing processes

The local fresh-output premise is discharged by concrete CP maps.  The two
recurrences below describe the actual modified private-record process and
an ordinary adaptive computation with completely depolarizing oracle calls.
-/

namespace ICO.RecordingVaryingDistance

open QIT ICO.RecordingRetainedProcess ICO.RecordingKnownChannel
  ICO.RecordingDepolarizing ICO.RecordingDistance
  ICO.PathRecordingSupport ICO.RecordingOperatorSupport
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {μ : ℕ → Type*} [∀ t, Fintype (μ t)] [∀ t, DecidableEq (μ t)]

def followedBy {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (K : Channel (α × a) (α × b)) : Channel (α × a) (α × b) := K.comp withMemory

theorem followedBy_apply {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (K : Channel (α × a) (α × b)) (ρ : CMatrix (α × a)) :
    (followedBy K).map ρ=K.map (ICO.RecordingWrapperDistance.uniformOutput (partialTraceA ρ)) := by
  change K.map (withMemory.map ρ)=_
  rw [withMemory_apply]


theorem modified_depolarizing_distance
    (ρ : (t : ℕ) → CMatrix (Basis α × μ t)) (σ : (t : ℕ) → CMatrix (α × μ t))
    (K : (t : ℕ) → Channel (α × μ t) (α × μ (t+1)))
    (q : ℕ) (hqd : 2 * q < Fintype.card α)
    (hρ0 : (ρ 0).PosSemidef) (hmass0 : (ρ 0).trace.re = 1)
    (hinit : visibleMap (ρ 0) = σ 0)
    (hactual : ∀ t < q, ρ (t + 1) =
      liftKnown (K t).map (retainedGrowingWrapper (2 * t + 1) (ρ t)))
    (hideal : ∀ t < q, σ (t + 1) = (followedBy (K t)).map (σ t)) :
    normalizedTraceDistance (visibleMap (ρ q)) (σ q) ≤
      (q : ℝ) ^ 2 / (Fintype.card α : ℝ) + (1 - (ρ q).trace.re) / 2 := by
  have hStates : ∀ t ≤ q, (ρ t).PosSemidef ∧ (ρ t).trace.re ≤ 1 ∧ (σ t).PosSemidef := by
    intro t
    induction t with
    | zero =>
        intro _
        refine ⟨hρ0, le_of_eq hmass0, ?_⟩
        rw [← hinit]
        exact visibleMap_TNI.mapsPositive _ hρ0
    | succ t ih =>
        intro ht
        have htq : t < q := by omega
        obtain ⟨hρ, hm, hσ⟩ := ih (by omega)
        have hdim : 2 * t + 1 < Fintype.card α := by omega
        refine ⟨?_, ?_, ?_⟩
        · rw [hactual t htq]
          exact liftKnown_posSemidef _ (K t).completelyPositive _
            (retainedGrowingWrapper_posSemidef _ _ hρ)
        · rw [hactual t htq, liftKnown_trace _ (K t).tracePreserving]
          exact (retainedGrowingWrapper_trace_le _ hdim _ hρ).trans hm
        · rw [hideal t htq]
          exact (followedBy (K t)).mapsPositive _ hσ
  have hBound : ∀ t ≤ q, normalizedTraceDistance (visibleMap (ρ t)) (σ t) ≤
      (t : ℝ) ^ 2 / (Fintype.card α : ℝ) + (1 - (ρ t).trace.re) / 2 := by
    intro t
    induction t with
    | zero =>
        intro _
        simp [hinit, hmass0]
    | succ t ih =>
        intro ht
        have htq : t < q := by omega
        obtain ⟨hρ, hm, hσ⟩ := hStates t (by omega)
        have hdim : 2 * t + 1 < Fintype.card α := by omega
        have hlocal := liftKnown_local_distance (K t) (2 * t + 1) hdim (ρ t) hρ hm
        rw [← hactual t htq, ← followedBy_apply] at hlocal
        have hContract := distance_contract (followedBy (K t)).map
          (MatrixMap.traceNonincreasingCP_of_tracePreserving
            (followedBy (K t)).completelyPositive (followedBy (K t)).tracePreserving)
          (visibleMap (ρ t)) (σ t) (visibleMap_TNI.mapsPositive _ hρ) hσ
        have hTriangle := normalizedTraceDistance_triangle
          (visibleMap (ρ (t + 1))) ((followedBy (K t)).map (visibleMap (ρ t)))
          ((followedBy (K t)).map (σ t))
        rw [← hideal t htq] at hTriangle hContract
        have hprev := ih (by omega)
        have hcast : ((2 * t + 1 : ℕ) : ℝ) = 2 * (t : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hlocal
        push_cast
        have halgebra : (t : ℝ) ^ 2 / (Fintype.card α : ℝ) +
            (1 - (ρ t).trace.re) / 2 +
            ((2 * (t : ℝ) + 1) / (Fintype.card α : ℝ) +
              ((ρ t).trace.re - (ρ (t + 1)).trace.re) / 2) =
            ((t : ℝ) + 1) ^ 2 / (Fintype.card α : ℝ) +
              (1 - (ρ (t + 1)).trace.re) / 2 := by ring
        linarith
  exact hBound q le_rfl

#print axioms modified_depolarizing_distance
end
end ICO.RecordingVaryingDistance


import ICO.C6FlaggedHybrid
import ICO.C6HistoryVisible
import ICO.MHOutputMixture

/-! Orthogonally retained flags can be erased before the final visible
comparison. The statement preserves arbitrary quantum correlations. -/
namespace ICO.C6FlagVisible
open QIT Matrix ICO.C6FlaggedHybrid ICO.MHOutputMixture ICO.PureHybrid
  ICO.C6HistoryVisible ICO.MHFockRotationErasure ICO.MHFockVisibleDistance
  ICO.MHBoundedRecording ICO.C6RetainedHistory ICO.C6PairedTrajectory
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 2048
set_option Elab.async false
variable {H O J : Type*} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
  [Fintype J] [DecidableEq J]

theorem traced_pack (v : J→EuclideanSpace ℂ H) :
    partialTraceA (outer (pack v) (pack v))=∑j,outer (v j) (v j) := by
  ext a b
  simp [partialTraceA,outer,pack,Matrix.vecMulVec_apply,Matrix.sum_apply]

theorem mixture_distance (Φ : MatrixMap H O) (hΦ : MatrixMap.TraceNonincreasingCP Φ)
    (v w : J→EuclideanSpace ℂ H) (hv : ‖pack v‖≤1) (hw : ‖pack w‖≤1) :
    normalizedTraceDistance (∑j,Φ (outer (v j) (v j)))
      (∑j,Φ (outer (w j) (w j)))≤‖pack v-pack w‖ := by
  let Ψ:=Φ.comp (Channel.traceOutLeft J H).map
  have hΨ : MatrixMap.TraceNonincreasingCP Ψ := by
    refine ⟨MatrixMap.isCompletelyPositive_comp _ _ hΦ.completelyPositive
      (Channel.traceOutLeft J H).completelyPositive, ?_⟩
    intro X hX
    have hh := hΦ.traceNonincreasing ((Channel.traceOutLeft J H).map X)
      ((Channel.traceOutLeft J H).mapsPositive X hX)
    have ht := congrArg Complex.re ((Channel.traceOutLeft J H).tracePreserving X)
    exact hh.trans_eq ht
  have hh:=pure_output_distance_le Ψ hΨ (pack v) (pack w) hv hw
  simpa only [Ψ,LinearMap.comp_apply,Channel.traceOutLeft_map,traced_pack,map_sum] using hh

variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ : ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def output (T n : ℕ) : MatrixMap
    (InputCutoff (α := A) T×Public (A := A) μ n) ((A×Bool)×μ n) := by
  classical
  exact (erasePrivate n).map.comp (visibleChannel T).map

theorem output_TNI (T n : ℕ) : MatrixMap.TraceNonincreasingCP
    (output (A:=A) (μ:=μ) T n) := by
  classical
  apply MatrixMap.traceNonincreasingCP_of_tracePreserving
  · exact MatrixMap.isCompletelyPositive_comp _ _ (erasePrivate n).completelyPositive
      (visibleChannel T).completelyPositive
  · exact MatrixMap.isTracePreserving_comp _ _ (erasePrivate n).tracePreserving
      (visibleChannel T).tracePreserving

theorem output_outer (T n : ℕ)
    (v : EuclideanSpace ℂ (InputCutoff (α := A) T×Public (A := A) μ n)) :
    output T n (outer v v)=ICO.C6HistoryVisible.visible (WithLp.ofLp v) := by
  classical
  simp only [output,Channel.comp,LinearMap.comp_apply,visible_outer,
    ICO.C6HistoryVisible.visible]

theorem visible_mixture_distance (T n : ℕ)
    (v w : J→EuclideanSpace ℂ (InputCutoff (α := A) T×Public (A := A) μ n))
    (hv : ‖pack v‖≤1) (hw : ‖pack w‖≤1) :
    normalizedTraceDistance
      (∑j,ICO.C6HistoryVisible.visible (WithLp.ofLp (v j)))
      (∑j,ICO.C6HistoryVisible.visible (WithLp.ofLp (w j)))≤‖pack v-pack w‖ := by
  classical
  have hh:=mixture_distance (output (A:=A) (μ:=μ) T n) (output_TNI T n) v w hv hw
  simpa only [output_outer] using hh

#print axioms mixture_distance
#print axioms visible_mixture_distance
end
end ICO.C6FlagVisible

import ICO.C6ActualFlagErasure
import ICO.C6ReindexChannel

/-! Actual erasure of both occupation records and the copied outcome history. -/
namespace ICO.C6HistoryVisible
open Matrix QIT ICO.C6ActualFlagErasure ICO.C6FlagSlices ICO.C6BirthFlags
  ICO.C6RetainedHistory ICO.C6NativeFresh ICO.C6PairedTrajectory
  ICO.MHBoundedRecording ICO.MHFockKnownOperation ICO.MHDecompressionErasure
  ICO.RecordingPurifiedProtocol ICO.RecordingHistory ICO.RecordingProcess
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def erasePrivate (n:ℕ) : Channel (A×Public (A:=A) μ n) ((A×Bool)×μ n) :=
  eraseHistory.comp (ICO.C6ReindexChannel.channel (Equiv.prodAssoc A Bool (History (A×Bool) n×μ n)))

def visible {T n:ℕ} (v:InputCutoff (α:=A) T×Public (A:=A) μ n→ℂ) :
    CMatrix ((A×Bool)×μ n) := (erasePrivate n).map (fockVisible T v)

theorem visible_slices {T n:ℕ}
    (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ n)) :
    visible (WithLp.ofLp v)=∑η:History (A×Bool) n,
      (fockVisible T (WithLp.ofLp (slice η v))).submatrix
        (Equiv.prodAssoc A Bool (μ n)) (Equiv.prodAssoc A Bool (μ n)) := by
  ext ⟨⟨a,b⟩,m⟩ ⟨⟨c,e⟩,u⟩
  simp only [visible,erasePrivate,Channel.comp,LinearMap.comp_apply,
    ICO.C6ReindexChannel.apply,eraseHistory_apply,Matrix.sum_apply,
    Matrix.submatrix_apply,fockVisible,partialTraceB,rankOneMatrix,slice,
    Matrix.vecMulVec_apply,WithLp.ofLp_toLp,Function.comp_apply]
  rfl

theorem visible_fresh_flags {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) :
    visible (WithLp.ofLp (freshVector h H K z q))=
      ∑κ:History Bool q,visible (WithLp.ofLp (flagRun h H K
        (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) q κ)) := by
  rw [visible_slices]
  simp only [visible_slices]
  ext o i
  simp only [Matrix.sum_apply,Matrix.submatrix_apply]
  simp_rw [outcome_flag_erasure h ht H K z]
  simp only [Matrix.sum_apply]
  exact Finset.sum_comm

#print axioms visible_fresh_flags
end
end ICO.C6HistoryVisible

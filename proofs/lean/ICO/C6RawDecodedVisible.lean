import ICO.C6RawDecoded
import ICO.C6DecodedValid
import ICO.C6HistoryVisible

namespace ICO.C6RawDecodedVisible
open Matrix QIT ICO.C6RawDecoded ICO.C6ModeFockEncoding ICO.C6DecodedHistory
  ICO.C6DecodedValid ICO.C6RawFlagSlices ICO.C6RawFlags ICO.C6FlagCount
  ICO.C6AcceptedModes ICO.C6ActualAcceptedModes ICO.C6CacheVisible
  ICO.C6PairedTrajectory ICO.MHFockTrajectory ICO.MHDecompressionErasure
  ICO.RecordingPurifiedProtocol
open scoped Matrix BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem raw_branch_visible {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (n:ℕ) (hn:2*n≤t)
    (η:History (A×Bool) n) (κ:History Bool n) :
    fockVisible T (WithLp.ofLp (slice η
      (rawFlagRun h H K (WithLp.toLp 2 (initial T z)) n κ)))=
      (sectorVisible (flagCount n κ)).map (partialTraceB (rankOneMatrix
        (C6DecodedHistory.run H K (decodedInitial z) n η κ))) := by
  rw [raw_decoded h ht H K z n hn η κ]
  by_cases hv:C6DecodedHistory.run H K (decodedInitial z) n η κ=0
  · rw [hv,Matrix.mulVec_zero]
    have hz {I:Type} [Fintype I] : rankOneMatrix (0:I→ℂ)=0 := by
      ext i j; simp [rankOneMatrix]
    have hp {I J:Type} [Fintype I] [Fintype J] : partialTraceB (0:CMatrix (I×J))=0 := by
      ext i j; simp [partialTraceB]
    simp [fockVisible,hz,hp]
  · exact encoding_visible T _ _ _ _
      (actual_modes_orthonormal H K (decodedInitial z) n η κ hv) _

theorem raw_visible_sum {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (n:ℕ) (hn:2*n≤t) :
    (∑κ:History Bool n,ICO.C6HistoryVisible.visible (WithLp.ofLp
      (rawFlagRun h H K (WithLp.toLp 2 (initial T z)) n κ)))=
      ∑η:History (A×Bool) n,∑κ:History Bool n,
        ((sectorVisible (flagCount n κ)).map (partialTraceB (rankOneMatrix
          (C6DecodedHistory.run H K (decodedInitial z) n η κ)))).submatrix
          (Equiv.prodAssoc A Bool (μ n)) (Equiv.prodAssoc A Bool (μ n)) := by
  simp only [ICO.C6HistoryVisible.visible_slices]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro κ _
  exact congrArg (fun X:CMatrix (A×(Bool×μ n))=>X.submatrix
    (Equiv.prodAssoc A Bool (μ n)) (Equiv.prodAssoc A Bool (μ n)))
      (raw_branch_visible h ht H K z n hn η κ)

#print axioms raw_branch_visible
#print axioms raw_visible_sum
end
end ICO.C6RawDecodedVisible

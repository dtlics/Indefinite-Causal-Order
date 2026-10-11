import ICO.C6ActualFlagErasure
import ICO.C6RightHistorySupport

namespace ICO.C6ActualRightSupport
open Matrix QIT ICO.C6ActualFlagErasure ICO.C6RightHistorySupport ICO.C6PermanentFlags
  ICO.C6FixedHistoryBasis ICO.C6FlagPrefixRun ICO.C6FlagSlices ICO.C6BirthFlags
  ICO.C6RetainedHistory ICO.C6ResidualModes ICO.C6ResidualSpan ICO.C6CacheSpanProjection
  ICO.C6HistoryCoordinates ICO.C6NumberRotationAlgebra ICO.MHBoundedRecording
  ICO.MHRectangularAction ICO.RecordingPurifiedProtocol ICO.C6PairedTrajectory
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem actual_right_support {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (η:History (A×Bool) q) (κ:History Bool q) :
    rectAct (Matrix.kronecker (rightFockSupport (historyProjection (vectors H q η)) T)
      (1:CMatrix (Bool×μ q)))
      (slice η (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) q κ))=
        slice η (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) q κ) := by
  obtain ⟨U,labels,hinj,hcol,hP⟩:=actual_history_basis H q η
  have hc:∀i,ICO.C6CacheHistorySpan.column U (labels i)=mode (vectors H q η) i := by
    intro i; ext a; exact hcol i a
  let B:=activeIndices (vectors H q η) labels q
  have hp:historyProjection (vectors H q η)=spanProjection U B := by
    simpa only [prefixHistory_self] using hP q le_rfl
  have hh:=prefixRun_unoccupied h ht H K
    (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) η U labels hc hP Bᶜ
    (vacuum_slice U Bᶜ T z _) q le_rfl κ (by
      intro a ha
      simp only [Finset.mem_compl,not_not]
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,rfl⟩)
  rw [zero_number_geometric,←hp] at hh
  simpa only [prefixRun,prefixHistory_self] using hh

theorem canonical_right_zero {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (η:History (A×Bool) q) (κ:History Bool q) :
    rectAct (Matrix.kronecker
      (rotatedNumber (historyUnitary (vectors H q η)) (historyIndices (vectors H q η))ᶜ 0 T)
      (1:CMatrix (Bool×μ q)))
      (slice η (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) q κ))=
        slice η (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) q κ) := by
  rw [zero_number_geometric]
  exact actual_right_support h ht H K z η κ

#print axioms canonical_right_zero
end
end ICO.C6ActualRightSupport

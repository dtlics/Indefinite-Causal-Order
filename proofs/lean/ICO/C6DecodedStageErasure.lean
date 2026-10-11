import ICO.C6DecodedChoiceErasure
import ICO.C6WeightedHistorySupport

namespace ICO.C6DecodedStageErasure
open Matrix QIT ICO.C6DecodedHistory ICO.C6DecodedChoiceErasure
  ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache ICO.C6GradedCacheReference
  ICO.C6GradedTransport ICO.C6RetainedGradeSupport ICO.C6RetainedSectorOperations
  ICO.C6WeightedHistory ICO.C6WeightedHistorySupport ICO.C6AcceptedBirthFactor
  ICO.C6ActualResidualWeight ICO.C6RawFlagSlices ICO.C6FlagCount
  ICO.RecordingPurifiedProtocol
open scoped Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem stage_erasure (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (i:ℕ) (hi:i<Q) (η:History (A×Bool) i) (κ:History Bool i)
    (j:A) (b f:Bool)
    (X:CMatrix (ImageCache (A:=A) (flagCount i κ) (Bool×μ i))) :
    conjugate (embed Q (historyGrade Q (i+1) (by omega) (f,κ)))
      (partialTraceB (conjugate (stage H K i η κ j b f) X))=
      branches Q hpos hQ H (fun i=>smallKnown (K i)) (weight H) i η κ (j,b) f
        (conjugate (embed Q (historyGrade Q i (by omega) κ)) (partialTraceB X)) := by
  have hr:(historyGrade Q i (by omega) κ).val<Q:=flagCount_lt hi κ
  have he:=selected_core_erasure (M:=μ i) Q hpos hQ (outcomeBasis H) (weight H i η)
    (historyGrade Q i (by omega) κ) hr j b f (birthAmplitude H i η b j)
    (birthAmplitude_square H i η b j) X
  have hp:=partialTraceB_known
    (ICO.C6CacheKnownOperation.externalLift (flagCount (i+1) (f,κ)) (smallKnown (K i)))
    (conjugate (core (outcomeBasis H b) j (birthAmplitude H i η b j) (flagCount i κ) f*
      choiceImages (flagCount i κ) b) X)
  have hs:stage H K i η κ j b f=
      knownImages (flagCount (i+1) (f,κ)) (smallKnown (K i)) *
      (core (outcomeBasis H b) j (birthAmplitude H i η b j) (flagCount i κ) f*
        choiceImages (flagCount i κ) b) := by
    exact Matrix.mul_assoc _ _ _
  rw [hs,←conjugate_comp_apply]
  have hp':=congrArg (conjugate (embed (A:=A) (M:=Bool×μ (i+1)) Q
    (historyGrade Q (i+1) (by omega) (f,κ)))) hp
  refine hp'.trans ?_
  have hk:=known_included Q (historyGrade Q (i+1) (by omega) (f,κ)) (smallKnown (K i))
    (partialTraceB (conjugate (core (outcomeBasis H b) j (birthAmplitude H i η b j)
      (flagCount i κ) f*choiceImages (flagCount i κ) b) X))
  have ha:=congrArg (conjugate (known Q (smallKnown (K i)))) he
  have hf:=hk.symm.trans ha
  exact hf

#print axioms stage_erasure
end
end ICO.C6DecodedStageErasure

import ICO.C6MeasuredFlagTransport
import ICO.C6FlagZero
import ICO.C6FixedHistoryBasis
import ICO.C6HistoryPrefixSteps
import ICO.C6BirthFlags

namespace ICO.C6FlagCore
open Matrix QIT ICO.C6MeasuredFlagTransport ICO.C6SelectedBirthFlag ICO.C6FlagZero
  ICO.C6BirthFlags ICO.C6RetainedHistory ICO.C6ResidualModes ICO.C6ResidualCoordinates
  ICO.C6CacheHistorySpan ICO.C6CacheSpanProjection ICO.C6BosonicHistorySupport
  ICO.C6BosonicReencoding ICO.C6FockQueryMatrix ICO.C6BosonicFockRotated
  ICO.C6NumberRotationAlgebra ICO.C6PolarFock ICO.MHBoundedRecording
  ICO.C6FixedHistoryBasis ICO.C6HistoryCoordinates ICO.RecordingPurifiedProtocol
noncomputable section
set_option maxHeartbeats 900000
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def measuredCore {q t T:ℕ} (h:t+1≤T) (v:Fin q→EuclideanSpace ℂ A)
    (i:Fin q) (U:Matrix.unitaryGroup A ℂ) (B:Finset A) (f:Bool) :
    CMatrix (InputCutoff (α:=A) T) :=
  polarLeftOnFock h*queryMatrix (rankOne (v i)) T*
    (if f then rotatedFresh U B T*polarRightOnFock h*
      (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ) else (polarLeftOnFock h)ᴴ)*
        historySupport (prior v i) T

theorem core_retrieval {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (v:Fin q→EuclideanSpace ℂ A) (i:Fin q) (U:Matrix.unitaryGroup A ℂ)
    (B S:Finset A) (hB:historyProjection (prior v i)=spanProjection U B) (k:ℕ) :
    rotatedNumber U S k T*measuredCore h v i U B false=
      measuredCore h v i U B false*rotatedNumber U S k T := by
  simpa only [measuredCore,Bool.false_eq_true,if_false] using
    measured_retrieval_preserves (prior v i) (v i) U B S hB k h ht

theorem core_birth_other {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (v:Fin q→EuclideanSpace ℂ A) (i:Active v) (U:Matrix.unitaryGroup A ℂ)
    (a:A) (ha:column U a=mode v i) (B S:Finset A)
    (hB:historyProjection (prior v i)=spanProjection U B) (haS:a∉S) (k:ℕ) :
    rotatedNumber U S k T*measuredCore h v i U B true=
      measuredCore h v i U B true*rotatedNumber U S k T := by
  simpa only [measuredCore,if_true,Matrix.mul_assoc] using
    measured_birth_preserves_other v i U a ha B S hB haS k h ht

theorem core_birth_new {q t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (v:Fin q→EuclideanSpace ℂ A) (i:Active v) (U:Matrix.unitaryGroup A ℂ)
    (a:A) (ha:column U a=mode v i) (B:Finset A)
    (hB:historyProjection (prior v i)=spanProjection U B) :
    rotatedNumber U {a} 1 T*measuredCore h v i U B true*rotatedNumber U {a} 0 T=
      measuredCore h v i U B true*rotatedNumber U {a} 0 T := by
  simpa only [measuredCore,if_true,Matrix.mul_assoc] using
    measured_birth_flag v i U a ha B hB h ht

theorem core_birth_zero {q t T:ℕ} (h:t+1≤T)
    (v:Fin q→EuclideanSpace ℂ A) (i:Fin q) (hi:residual v i=0)
    (U:Matrix.unitaryGroup A ℂ) (B:Finset A)
    (hB:historyProjection (prior v i)=spanProjection U B) :
    measuredCore h v i U B true=0 := by
  simpa only [measuredCore,if_true,Matrix.mul_assoc] using inactive_birth v i hi U B hB h

theorem actual_core {q t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (η:History (A×Bool) q) (i:Fin q) (U:Matrix.unitaryGroup A ℂ) (B:Finset A)
    (hB:historyProjection (prior (vectors H q η) i)=spanProjection U B) (f:Bool) :
    polarLeftOnFock h*queryMatrix (rankOne (vectors H q η i)) T*
      flagInverse h H i (prefixHistory η i i.isLt.le) f=
        measuredCore h (vectors H q η) i U B f := by
  have hQ:rotatedFresh (historyUnitary (vectors H i (prefixHistory η i i.isLt.le)))
      (historyIndices (vectors H i (prefixHistory η i i.isLt.le))) T=rotatedFresh U B T := by
    rw [ICO.C6BosonicQueryAlgebra.rotatedFresh_complement,
      ICO.C6BosonicQueryAlgebra.rotatedFresh_complement]
    change 1-queryMatrix (historyProjection (vectors H i (prefixHistory η i i.isLt.le))) T=_
    rw [prior_actual,hB]
  unfold flagInverse measuredCore
  rw [hQ,prior_actual]
  simp only [Matrix.mul_assoc]

#print axioms actual_core
#print axioms core_birth_new
end
end ICO.C6FlagCore

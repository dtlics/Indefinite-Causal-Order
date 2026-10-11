import ICO.MHRecordingChoiceOperators
import ICO.MHRotatedTrajectory
import ICO.MHWRestricted

/-! The literal reachable-domain mean for either direction of an actual
recording query, including arbitrary spectator memory. -/
namespace ICO.MHRecordingChoiceTwirl
open Matrix QIT MeasureTheory ICO.MHRecordingChoiceOperators ICO.MHRotatedTrajectory
  ICO.MHFockRotation ICO.MHFockSpace ICO.MHFockAlgebra ICO.MHWRestricted
  ICO.RecordingCopyIdentity ICO.MHBoundedRecording ICO.MHMemoryMeanDomain
  ICO.MHDomainMeanProduct ICO.MHProfileTurnFock ICO.MHInverseDomainTwirl
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 512
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem compressed_drop_cutoff {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (J : Matrix K H ℂ) (T B G S : CMatrix K)
    (hcomm : Commute S T) (hSJ : S*J=J) :
    J.conjTranspose*T.conjTranspose*(B-G*S)*T*J=
      J.conjTranspose*T.conjTranspose*(B-G)*T*J := by
  have hSTJ : S*(T*J)=T*J := by
    rw [←Matrix.mul_assoc,hcomm.eq,Matrix.mul_assoc,hSJ]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
  rw [hSTJ]

theorem source_embedding {q T : ℕ} (hq : q≤T) :
    sourceProjection (α:=A) hq*basisEmbedding (inputEmbed hq)=basisEmbedding (inputEmbed hq) := by
  rw [sourceProjection,Matrix.mul_assoc,inputEmbed_gram,Matrix.mul_one]

def choiceTurn (T : ℕ) (inv : Bool)
    (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) : CMatrix (InputCutoff (α:=A) T) :=
  (fockQuery (before p.1 p.2 inv) T : CMatrix (InputCutoff (α:=A) T))*
    (fockQ p.1 p.2 T : CMatrix (InputCutoff (α:=A) T))

def choiceIntegrand {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (hq : q≤T) (inv : Bool)
    (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) : CMatrix (InputCutoff (α:=A) q) :=
  (basisEmbedding (inputEmbed (α:=A) hq)).conjTranspose*(choiceTurn T inv p).conjTranspose*
    (ICO.MHWDomainProjection.bijProjection (α:=A) T-choiceDomain hT hq inv)*
      choiceTurn T inv p*basisEmbedding (inputEmbed hq)

theorem choiceIntegrand_eq {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (hq : q≤T)
    (inv : Bool) (p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) :
    choiceIntegrand hT hq inv p=
      if inv then inverseIntegrand hT hq p else forwardIntegrand hT hq p := by
  unfold choiceIntegrand choiceDomain choiceTurn
  rw [compressed_drop_cutoff _ _ _ _ _
    ((source_commute_query (before p.1 p.2 inv) hq).mul_right
      (source_commute_rotation p.1 p.2 hq)) (source_embedding hq)]
  cases inv <;> simp only [choiceTurn,before,choiceGram,ICO.MHFockTrajectory.Wchoice,
    if_false,if_true,Bool.false_eq_true,Matrix.conjTranspose_conjTranspose,
    inverseIntegrand,forwardIntegrand,inverseTurn,actualTurn,inverseMissing,missingMatrix,
    Matrix.mul_assoc]

theorem choiceIntegrand_integrable {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q≤T) (inv : Bool) : Integrable (choiceIntegrand hT hq inv) (rotationMeasure A) := by
  have he : choiceIntegrand hT hq inv=(fun p => if inv then inverseIntegrand hT hq p else forwardIntegrand hT hq p) :=
    funext (choiceIntegrand_eq hT hq inv)
  rw [he]
  cases inv
  · simpa only [if_false,Bool.false_eq_true] using forwardIntegrand_integrable hT hq
  · simpa only [if_true] using inverseIntegrand_integrable hT hq

theorem choice_mean_norm {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q≤T) (hsize : q<Fintype.card A) (hsmall : 2*q≤Fintype.card A) (inv : Bool) :
    ‖∫ p, choiceIntegrand hT hq inv p ∂rotationMeasure A‖≤
      6*(q:ℝ)*Real.sqrt ((q:ℝ)/Fintype.card A) := by
  simp only [choiceIntegrand_eq]
  cases inv
  · simpa only [if_false,Bool.false_eq_true] using actual_forward_mean_norm hT hq hsize hsmall
  · simpa only [if_true] using actual_inverse_mean_norm hT hq hsize hsmall

variable {M : Type} [Fintype M] [DecidableEq M]

theorem choice_memory_mean_norm {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q≤T) (hsize : q<Fintype.card A) (hsmall : 2*q≤Fintype.card A) (inv : Bool) :
    ‖∫ p, Matrix.kronecker (choiceIntegrand hT hq inv p) (1:CMatrix M)
      ∂rotationMeasure A‖≤6*(q:ℝ)*Real.sqrt ((q:ℝ)/Fintype.card A) :=
  mean_tensor_norm _ (choiceIntegrand_integrable hT hq inv) _
    (choice_mean_norm hT hq hsize hsmall inv)

#print axioms choiceIntegrand_eq
#print axioms choice_memory_mean_norm
end
end ICO.MHRecordingChoiceTwirl

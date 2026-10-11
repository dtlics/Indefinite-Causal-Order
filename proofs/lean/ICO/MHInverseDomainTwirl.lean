import ICO.MHCoherentDomainTwirl
import ICO.MHHaarInverseTransport
import ICO.MHWRecordSwap
import ICO.MHFockRotationSwap

/-! The inverse query has the same actual Haar mean domain loss, by
record transposition and normalized Haar inversion invariance. -/
namespace ICO.MHInverseDomainTwirl
open Matrix QIT MeasureTheory ICO.MHCoherentDomainTwirl ICO.MHHaarInverseTransport
  ICO.MHProfileTurnFock ICO.MHFockSpace ICO.MHFockProjection ICO.MHFockSwap
  ICO.MHFockOracle ICO.MHWRecordSwap ICO.MHFockRotationSwap ICO.MHFockRotation
  ICO.MHWEmbedding ICO.MHWDomainProjection ICO.RecordingCopyIdentity ICO.MHBoundedRecording
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
local instance cmContinuousENorm {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

def inverseTurn (C D : Matrix.unitaryGroup A ℂ) (T : ℕ) : CMatrix (InputCutoff (α := A) T) :=
  (fockQuery D⁻¹ T : CMatrix (InputCutoff (α := A) T))*(fockQ C D T : CMatrix (InputCutoff (α := A) T))

theorem inverse_turn_swap (C D : Matrix.unitaryGroup A ℂ) (T : ℕ) :
    inverseTurn C D T=swapMatrix T*actualTurn D⁻¹ C⁻¹ T*swapMatrix T := by
  rw [actualTurn,involution_sandwich_mul _ _ _ (swapMatrix_sq T),swap_fockQuery,swap_fockQ]
  simp only [inv_inv,inverseTurn]

def inverseMissing {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) : CMatrix (InputCutoff (α := A) T) :=
  bijProjection T-recordW hT*(recordW hT).conjTranspose

theorem inverse_missing_swap {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    inverseMissing hT=swapMatrix T*missingMatrix hT*swapMatrix T := (missingInverse_swap hT).symm

theorem inverse_conjugation_swap (C D : Matrix.unitaryGroup A ℂ) {T : ℕ}
    (hT : 2*Fintype.card (A×A)≤T) :
    (inverseTurn C D T).conjTranspose*inverseMissing hT*inverseTurn C D T=
      swapMatrix T*((actualTurn D⁻¹ C⁻¹ T).conjTranspose*missingMatrix hT*actualTurn D⁻¹ C⁻¹ T)*swapMatrix T := by
  rw [inverse_turn_swap,inverse_missing_swap]
  simp only [Matrix.conjTranspose_mul,swapMatrix_selfAdjoint]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc (swapMatrix (α := A) T) (swapMatrix (α := A) T),swapMatrix_sq,Matrix.one_mul]

theorem swap_compression {t T : ℕ} (ht : t≤T) (X : CMatrix (InputCutoff (α := A) T)) :
    (basisEmbedding (inputEmbed ht)).conjTranspose*(swapMatrix T*X*swapMatrix T)*basisEmbedding (inputEmbed ht)=
      swapMatrix t*((basisEmbedding (inputEmbed ht)).conjTranspose*X*basisEmbedding (inputEmbed ht))*swapMatrix t := by
  rw [basisEmbedding_compression]
  nth_rw 1 [← swapMatrix_selfAdjoint T]
  change ((basisEmbedding (recordSwapEquiv T)).conjTranspose*X*basisEmbedding (recordSwapEquiv T)).submatrix
      (inputEmbed ht) (inputEmbed ht)=_
  rw [basisEmbedding_compression,basisEmbedding_compression]
  nth_rw 1 [← swapMatrix_selfAdjoint t]
  change _=(basisEmbedding (recordSwapEquiv t)).conjTranspose*(X.submatrix (inputEmbed ht) (inputEmbed ht))*basisEmbedding (recordSwapEquiv t)
  rw [basisEmbedding_compression]
  ext o i
  exact congrArg₂ (fun o i => X o i) (recordSwap_inputEmbed ht o) (recordSwap_inputEmbed ht i)

def forwardIntegrand {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ) : CMatrix (InputCutoff (α := A) t) :=
  (basisEmbedding (inputEmbed ht)).conjTranspose*
    ((actualTurn p.1 p.2 T).conjTranspose*missingMatrix hT*actualTurn p.1 p.2 T)*basisEmbedding (inputEmbed ht)

theorem forwardIntegrand_continuous {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T) :
    Continuous (forwardIntegrand hT ht) := by
  have he : forwardIntegrand hT ht=fun p => profileBlocks t (sectorConjugation hT ht p) := by
    funext p
    exact compressed_missing_conjugation p.1 p.2 hT ht
  rw [he]
  exact (blocksCLM (A := A) t).continuous.comp (sectorConjugation_continuous hT ht)

theorem inverse_mean_eq_swap {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T) :
    (∫ D, ∫ C, (basisEmbedding (inputEmbed (α := A) ht)).conjTranspose*
      ((inverseTurn C D T).conjTranspose*inverseMissing hT*inverseTurn C D T)*basisEmbedding (inputEmbed ht)
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) =
    swapMatrix t*(∫ D, ∫ C, forwardIntegrand hT ht (C,D)
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A))*swapMatrix t := by
  simp_rw [inverse_conjugation_swap,swap_compression]
  have hh := inverse_swap_compression (swapMatrix (α := A) t) (forwardIntegrand hT ht)
    (forwardIntegrand_continuous hT ht)
  simpa only [swapMatrix_selfAdjoint,forwardIntegrand] using hh

theorem actual_inverse_mean_domain_norm_le {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (hsize : t<Fintype.card A) (hsmall : 2*t≤Fintype.card A) :
    ‖∫ D, ∫ C, (basisEmbedding (inputEmbed (α := A) ht)).conjTranspose*
      ((inverseTurn C D T).conjTranspose*inverseMissing hT*inverseTurn C D T)*basisEmbedding (inputEmbed ht)
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)‖ ≤
        6*(t : ℝ)*Real.sqrt ((t : ℝ)/Fintype.card A) := by
  rw [inverse_mean_eq_swap]
  have hS := swapMatrix_norm_le (α := A) t
  have hM := actual_mean_domain_norm_le hT ht hsize hsmall
  change ‖∫ D, ∫ C, forwardIntegrand hT ht (C,D)
    ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)‖≤_ at hM
  calc
    _ ≤ (‖swapMatrix (α := A) t‖*‖∫ D, ∫ C, forwardIntegrand hT ht (C,D)
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)‖)*‖swapMatrix (α := A) t‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*(6*(t : ℝ)*Real.sqrt ((t : ℝ)/Fintype.card A)))*1 :=
      mul_le_mul (mul_le_mul hS hM (norm_nonneg _) (by norm_num)) hS (norm_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms actual_inverse_mean_domain_norm_le
end
end ICO.MHInverseDomainTwirl
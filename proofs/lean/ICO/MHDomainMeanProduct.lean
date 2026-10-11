import ICO.MHInverseDomainTwirl

/-! Product-Haar forms of the actual forward and inverse compressed domain means. -/
namespace ICO.MHDomainMeanProduct
open Matrix QIT MeasureTheory ICO.MHInverseDomainTwirl ICO.MHCoherentDomainTwirl
  ICO.MHProfileTurnFock ICO.MHFockSpace ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHBoundedRecording ICO.RecordingCopyIdentity
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
local instance cmContinuousENorm {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

def rotationMeasure (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] :
    Measure (Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ) :=
  (unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))

instance rotationMeasure_probability : IsProbabilityMeasure (rotationMeasure A) := by
  dsimp [rotationMeasure]
  infer_instance

def inverseIntegrand {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ) : CMatrix (InputCutoff (α := A) t) :=
  (basisEmbedding (inputEmbed ht)).conjTranspose*
    ((inverseTurn p.1 p.2 T).conjTranspose*inverseMissing hT*inverseTurn p.1 p.2 T)*basisEmbedding (inputEmbed ht)

theorem inverseIntegrand_eq_swap {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ) :
    inverseIntegrand hT ht p=swapMatrix t*forwardIntegrand hT ht (p.2⁻¹,p.1⁻¹)*swapMatrix t := by
  simp only [inverseIntegrand,inverse_conjugation_swap,swap_compression,forwardIntegrand]

theorem inverseIntegrand_continuous {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T) :
    Continuous (inverseIntegrand hT ht) := by
  simp_rw [show inverseIntegrand hT ht=fun p => swapMatrix t*forwardIntegrand hT ht (p.2⁻¹,p.1⁻¹)*swapMatrix t from funext (inverseIntegrand_eq_swap hT ht)]
  exact (continuous_const.matrix_mul ((forwardIntegrand_continuous hT ht).comp
    (continuous_snd.inv.prodMk continuous_fst.inv))).matrix_mul continuous_const

theorem forwardIntegrand_integrable {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T) :
    Integrable (forwardIntegrand hT ht) (rotationMeasure A) :=
  (forwardIntegrand_continuous hT ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem inverseIntegrand_integrable {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T) :
    Integrable (inverseIntegrand hT ht) (rotationMeasure A) :=
  (inverseIntegrand_continuous hT ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem actual_forward_mean_norm {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (hsize : t<Fintype.card A) (hsmall : 2*t≤Fintype.card A) :
    ‖∫ p, forwardIntegrand hT ht p ∂rotationMeasure A‖ ≤
      6*(t : ℝ)*Real.sqrt ((t : ℝ)/Fintype.card A) := by
  rw [rotationMeasure,integral_prod_symm _ (forwardIntegrand_integrable hT ht)]
  exact actual_mean_domain_norm_le hT ht hsize hsmall

theorem actual_inverse_mean_norm {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (hsize : t<Fintype.card A) (hsmall : 2*t≤Fintype.card A) :
    ‖∫ p, inverseIntegrand hT ht p ∂rotationMeasure A‖ ≤
      6*(t : ℝ)*Real.sqrt ((t : ℝ)/Fintype.card A) := by
  rw [rotationMeasure,integral_prod_symm _ (inverseIntegrand_integrable hT ht)]
  exact actual_inverse_mean_domain_norm_le hT ht hsize hsmall

#print axioms actual_forward_mean_norm
#print axioms actual_inverse_mean_norm
end
end ICO.MHDomainMeanProduct
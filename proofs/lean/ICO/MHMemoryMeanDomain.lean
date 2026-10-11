import ICO.MHDomainMeanProduct
import ICO.MHFockKnownOperation

/-! The actual compressed mean-domain estimates remain valid with arbitrary
entangled spectator memory. Tensoring and integrating commute literally. -/
namespace ICO.MHMemoryMeanDomain
open Matrix QIT MeasureTheory ICO.MHDomainMeanProduct ICO.MHCoherentDomainTwirl
  ICO.MHInverseDomainTwirl ICO.MHFockKnownOperation ICO.MHFockSpace
  ICO.RecordingCopyIdentity ICO.MHBoundedRecording
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 512
variable {H K M Ω : Type*} [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype M] [DecidableEq M]
  [MeasurableSpace Ω] {μ : Measure Ω}

local instance matrixContinuousENorm {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] : ContinuousENorm (Matrix b a ℂ) :=
  SeminormedAddGroup.toContinuousENorm

def tensorIdentityCLM : Matrix K H ℂ→L[ℝ]Matrix (K×M) (H×M) ℂ :=
  ({ toFun := fun X => Matrix.kronecker X (1 : CMatrix M)
     map_add' := by intros; exact Matrix.add_kronecker _ _ _
     map_smul' := by intros; exact Matrix.smul_kronecker _ _ _ } :
    Matrix K H ℂ→ₗ[ℝ]Matrix (K×M) (H×M) ℂ).toContinuousLinearMap

theorem tensor_integrable (F : Ω→Matrix K H ℂ) (hF : Integrable F μ) :
    Integrable (fun ω => Matrix.kronecker (F ω) (1 : CMatrix M)) μ :=
  (tensorIdentityCLM (M:=M)).integrable_comp hF

theorem integral_tensor (F : Ω→Matrix K H ℂ) (hF : Integrable F μ) :
    (∫ ω, Matrix.kronecker (F ω) (1 : CMatrix M) ∂μ)=
      Matrix.kronecker (∫ ω, F ω ∂μ) (1 : CMatrix M) :=
  (tensorIdentityCLM (M:=M)).integral_comp_comm hF

theorem mean_tensor_norm (F : Ω→CMatrix H) (hF : Integrable F μ) (α : ℝ)
    (hα : ‖∫ ω, F ω ∂μ‖≤α) :
    ‖∫ ω, Matrix.kronecker (F ω) (1 : CMatrix M) ∂μ‖≤α := by
  rw [integral_tensor (M:=M) F hF]
  exact (tensor_identity_norm_le _).trans hα

theorem tensor_compressed_conjugation (J : Matrix K H ℂ) (T P : CMatrix K) :
    (Matrix.kronecker J (1 : CMatrix M)).conjTranspose*
      (Matrix.kronecker T (1 : CMatrix M)).conjTranspose*
      Matrix.kronecker P (1 : CMatrix M)*Matrix.kronecker T (1 : CMatrix M)*
      Matrix.kronecker J (1 : CMatrix M)=
    Matrix.kronecker (J.conjTranspose*T.conjTranspose*P*T*J) (1 : CMatrix M) := by
  simp only [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
    ←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one]

variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem actual_forward_memory_mean_norm {t T : ℕ}
    (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (hsize : t<Fintype.card A) (hsmall : 2*t≤Fintype.card A) :
    ‖∫ p, Matrix.kronecker (forwardIntegrand hT ht p) (1 : CMatrix M)
      ∂rotationMeasure A‖≤6*(t:ℝ)*Real.sqrt ((t:ℝ)/Fintype.card A) :=
  mean_tensor_norm _ (forwardIntegrand_integrable hT ht) _
    (actual_forward_mean_norm hT ht hsize hsmall)

theorem actual_inverse_memory_mean_norm {t T : ℕ}
    (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (hsize : t<Fintype.card A) (hsmall : 2*t≤Fintype.card A) :
    ‖∫ p, Matrix.kronecker (inverseIntegrand hT ht p) (1 : CMatrix M)
      ∂rotationMeasure A‖≤6*(t:ℝ)*Real.sqrt ((t:ℝ)/Fintype.card A) :=
  mean_tensor_norm _ (inverseIntegrand_integrable hT ht) _
    (actual_inverse_mean_norm hT ht hsize hsmall)

#print axioms actual_forward_memory_mean_norm
#print axioms actual_inverse_memory_mean_norm
end
end ICO.MHMemoryMeanDomain

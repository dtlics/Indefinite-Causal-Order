import ICO.MHRecordingChoiceTwirl
import ICO.MHChoiceMemoryCovariance
import ICO.MHFockRunContinuity
import ICO.MHCompressedQueryStep

namespace ICO.MHActualQueryLoss
open Matrix QIT MeasureTheory ICO.MHRecordingChoiceOperators ICO.MHRecordingChoiceTwirl
  ICO.MHChoiceMemoryCovariance ICO.MHFockRunContinuity ICO.MHRotatedTrajectory
  ICO.MHFockTrajectory ICO.MHFockRotation ICO.MHFockSpace ICO.MHFockAlgebra
  ICO.MHFockSupportProjection ICO.MHFockKnownOperation ICO.MHBijectionProfiles
  ICO.MHFockLabels ICO.MHBoundedRecording ICO.MHMemoryMeanDomain ICO.MHDomainMeanProduct
  ICO.MHProtocolOverlap ICO.MHRectangularAction ICO.RecordingCopyIdentity
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 512
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]
abbrev Rotations (A : Type) [Fintype A] [DecidableEq A] :=
  Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ

def memoryUnitary {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix.unitaryGroup H ℂ) : Matrix.unitaryGroup (H×M) ℂ :=
  ICO.MHSectorCovariance.tensorUnitary U (1:Matrix.unitaryGroup M ℂ)

theorem memoryUnitary_val {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix.unitaryGroup H ℂ) :
    (memoryUnitary (M:=M) U : CMatrix (H×M))=Matrix.kronecker (U:CMatrix H) (1:CMatrix M) := rfl

theorem memory_embedding_gram {q T : ℕ} (hq : q≤T) :
    (Matrix.kronecker (basisEmbedding (inputEmbed (α:=A) hq)) (1:CMatrix M)).conjTranspose*
      Matrix.kronecker (basisEmbedding (inputEmbed (α:=A) hq)) (1:CMatrix M)=1 := by
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [←Matrix.mul_kronecker_mul,inputEmbed_gram,Matrix.mul_one,Matrix.one_kronecker_one]

theorem memory_embedding_image {q T : ℕ} (hq : q≤T) :
    Matrix.kronecker (basisEmbedding (inputEmbed (α:=A) hq)) (1:CMatrix M)*
      (Matrix.kronecker (basisEmbedding (inputEmbed hq)) (1:CMatrix M)).conjTranspose=
        Matrix.kronecker (sourceProjection hq) (1:CMatrix M) := by
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [←Matrix.mul_kronecker_mul,Matrix.mul_one]
  rfl

theorem compressed_memory_eq {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q≤T) (inv : Bool) (p : Rotations A) :
    (Matrix.kronecker (basisEmbedding (inputEmbed (α:=A) hq)) (1:CMatrix M)).conjTranspose*
      ((memoryUnitary (M:=M) (fockQuery (before p.1 p.2 inv) T) : CMatrix (InputCutoff (α:=A) T×M))*
        (memoryUnitary (M:=M) (fockQ p.1 p.2 T) : CMatrix (InputCutoff (α:=A) T×M))).conjTranspose*
      Matrix.kronecker (ICO.MHWDomainProjection.bijProjection T-choiceDomain hT hq inv) (1:CMatrix M)*
      ((memoryUnitary (M:=M) (fockQuery (before p.1 p.2 inv) T) : CMatrix (InputCutoff (α:=A) T×M))*
        (memoryUnitary (M:=M) (fockQ p.1 p.2 T) : CMatrix (InputCutoff (α:=A) T×M)))*
      Matrix.kronecker (basisEmbedding (inputEmbed hq)) (1:CMatrix M)=
        Matrix.kronecker (choiceIntegrand hT hq inv p) (1:CMatrix M) := by
  simp only [memoryUnitary_val,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,Matrix.mul_one]
  have hh := tensor_compressed_conjugation (M:=M) (basisEmbedding (inputEmbed (α:=A) hq))
    (choiceTurn T inv p) (ICO.MHWDomainProjection.bijProjection T-choiceDomain hT hq inv)
  simpa only [Matrix.kronecker,choiceIntegrand,choiceTurn,Matrix.mul_assoc] using hh

theorem query_bij_supported (C : Matrix.unitaryGroup A ℂ) (T : ℕ)
    (x : InputCutoff (α:=A) T×M→ℂ)
    (hx : Supported (fun i => BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2) x) :
    Matrix.kronecker (ICO.MHWDomainProjection.bijProjection T) (1:CMatrix M)*ᵥ
      (Matrix.kronecker (fockQuery C T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)*ᵥx)=
        Matrix.kronecker (fockQuery C T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)*ᵥx := by
  apply bij_fixed
  refine mulVec_support _ x _ _ hx ?_
  intro o i hi hb
  exact (query_bij C T o.1 i.1 (oracle_memory_support _ o i hi)).mpr hb

theorem query_mean_step {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q+1≤T) (hsize : q<Fintype.card A) (hsmall : 2*q≤Fintype.card A)
    (inv : Bool) (x : Rotations A→EuclideanSpace ℂ (InputCutoff (α:=A) T×M))
    (y : EuclideanSpace ℂ (InputCutoff (α:=A) T×M)) (hx : Continuous x)
    (hxn : ∀p,‖x p‖≤1) (hyn : ‖y‖≤1)
    (hxb : ∀p,Supported (fun i => BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2)
      (WithLp.ofLp (x p)))
    (hys : Matrix.kronecker (sourceProjection (Nat.le_trans (Nat.le_succ q) hq))
      (1:CMatrix M)*ᵥWithLp.ofLp y=WithLp.ofLp y) :
    (∫ p, (⟪x p,act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
      (1:CMatrix M)) y⟫_ℂ).re ∂rotationMeasure A)-
      Real.sqrt (6*(q:ℝ)*Real.sqrt ((q:ℝ)/Fintype.card A))-
        16*Real.sqrt (2*(q:ℝ)*(q+1)/Fintype.card A) ≤
    ∫ p, (⟪act (Matrix.kronecker (rotatedW hT p.1 p.2 inv) (1:CMatrix M)) (x p),
      act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M))
        (act (Matrix.kronecker (choiceRestrictedV hq inv) (1:CMatrix M)) y)⟫_ℂ).re ∂rotationMeasure A := by
  let ht := Nat.le_trans (Nat.le_succ q) hq
  let W := Matrix.kronecker (Wchoice (α:=A) hT inv) (1:CMatrix M)
  let V := Matrix.kronecker (choiceRestrictedV (A:=A) hq inv) (1:CMatrix M)
  let P := Matrix.kronecker (choiceDomain (A:=A) hT ht inv) (1:CMatrix M)
  let B := Matrix.kronecker (ICO.MHWDomainProjection.bijProjection (α:=A) T) (1:CMatrix M)
  let C := fun p : Rotations A => memoryUnitary (M:=M) (fockQuery (before p.1 p.2 inv) T)
  let D := fun p : Rotations A => memoryUnitary (M:=M) (fockQuery (after p.1 p.2 inv) T)
  let Q := fun p : Rotations A => memoryUnitary (M:=M) (fockQ p.1 p.2 T)
  let J := Matrix.kronecker (basisEmbedding (inputEmbed (α:=A) ht)) (1:CMatrix M)
  have hrot (p : Rotations A) : (D p:CMatrix _)*W*(C p:CMatrix _)=
      Matrix.kronecker (rotatedW hT p.1 p.2 inv) (1:CMatrix M) := by
    simp only [D,C,W,memoryUnitary_val,Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
    rfl
  have hdiff : B-P=Matrix.kronecker
      (ICO.MHWDomainProjection.bijProjection T-choiceDomain hT ht inv) (1:CMatrix M) := by
    ext o i
    simp only [B,P,Matrix.sub_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,sub_mul]
  have hc : Continuous (fun p => act (C p:CMatrix (InputCutoff (α:=A) T×M))) := by
    change Continuous (fun p : Rotations A => act (Matrix.kronecker
      (fockQuery (before p.1 p.2 inv) T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)))
    exact act_continuous _ (tensor_identity_continuous (μ:=M) _
      ((query_continuous T).comp (before_continuous inv)))
  have hqc : Continuous (fun p => act (Q p:CMatrix (InputCutoff (α:=A) T×M))) := recordAction_continuous T M
  have hpre := hqc.clm_apply (continuous_const (y:=y))
  have hpostx := (rotatedAction_continuous hT inv M).clm_apply hx
  have hposty := hqc.clm_apply (continuous_const (y:=act V y))
  have hloss := (act (B-P)).continuous.comp (hc.clm_apply hpre)
  have hcomp (p : Rotations A) : J.conjTranspose*
      ((C p:CMatrix (InputCutoff (α:=A) T×M))*(Q p:CMatrix (InputCutoff (α:=A) T×M))).conjTranspose*
        (B-P)*((C p:CMatrix (InputCutoff (α:=A) T×M))*(Q p:CMatrix (InputCutoff (α:=A) T×M)))*J=
      Matrix.kronecker (choiceIntegrand hT ht inv p) (1:CMatrix M) := by
    rw [hdiff]
    exact compressed_memory_eq hT ht inv p
  have hh := ICO.MHCompressedQueryStep.mean_query_step_compressed x y W V P B C D Q J
    (memory_embedding_gram ht)
    (by rw [←rectAct_mul,memory_embedding_image]; exact congrArg (WithLp.toLp 2) hys)
    (16*Real.sqrt (2*(q:ℝ)*(q+1)/Fintype.card A))
    (6*(q:ℝ)*Real.sqrt ((q:ℝ)/Fintype.card A)) hxn hyn
    ((tensor_identity_norm_le _).trans (ICO.MHRecordingChoiceOperators.Wchoice_norm_le hT inv))
    (memory_low_overlap hT hq hsize inv)
    ((tensor_projection _ (ICO.MHWDomainProjection.bij_projection T)).isSelfAdjoint.star_eq)
    (by
      intro p
      exact congrArg (WithLp.toLp 2) (query_bij_supported (before p.1 p.2 inv) T
        (WithLp.ofLp (x p)) (hxb p)))
    (fun p => choice_memory_covariance p.1 p.2 hq hsize inv M)
    (by rw [hdiff]; exact tensor_projection _ (choiceMissing_projection hT ht inv))
    (by
      simpa only [hcomp] using tensor_integrable (M:=M) (choiceIntegrand hT ht inv)
        (choiceIntegrand_integrable hT ht inv))
    (by
      simpa only [hcomp] using choice_memory_mean_norm (M:=M) hT ht hsize hsmall inv)
    ((Complex.continuous_re.comp (hx.inner hpre)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (by
      simp only [hrot]
      exact (Complex.continuous_re.comp (hpostx.inner hposty)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    (hloss.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hloss.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  simpa only [hrot,Q,memoryUnitary_val] using hh

#print axioms query_mean_step
#print axioms compressed_memory_eq
#print axioms query_bij_supported
end
end ICO.MHActualQueryLoss

import ICO.MHWRecordEntries
import ICO.MHBellProjectors

/-! The actual partial recording oracle has a projection domain supported on
bijective records, also after the unrestricted Fock embedding. -/
namespace ICO.MHWDomainProjection
open QIT ICO.MHFockNodup ICO.MHFockLabels ICO.MHFockSpace ICO.MHWEmbedding
  ICO.MHWRecordEntries ICO.MHWPartial ICO.MHFiniteWCanonical ICO.MHBijectionProfiles
  ICO.RecordingCopyIdentity ICO.RecordingOperatorSupport ICO.RecordingMultisetBridge
  ICO.MHBoundedRecording ICO.RecordingProcess
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem isometry_projection {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (K : Matrix b a ℂ) (P : CMatrix a)
    (hK : K.conjTranspose*K=1) (hP : IsStarProjection P) :
    IsStarProjection (K*P*K.conjTranspose) := by
  constructor
  · show K*P*K.conjTranspose*(K*P*K.conjTranspose)=_
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc K.conjTranspose K,hK,Matrix.one_mul,
      ← Matrix.mul_assoc P P,hP.isIdempotentElem.eq]
  · change (K*P*K.conjTranspose).conjTranspose=_
    have hp : P.conjTranspose=P := hP.isSelfAdjoint.star_eq
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hp,Matrix.mul_assoc]

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem recordW_initial_projection {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    IsStarProjection ((recordW hT).conjTranspose*recordW hT) := by
  rw [recordW_gram]
  exact isometry_projection _ _ (basisEmbedding_gram _ (setEmbedding_injective hT))
    oracle_initial_projection

theorem recordW_norm_le {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) : ‖recordW hT‖≤1 := by
  have hp := (recordW_initial_projection hT).norm_le
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hp
  nlinarith [norm_nonneg (recordW hT)]

def oldBijProjection : CMatrix (Basis α) := predicateProjection (fun i => BijRecord i.2.1 i.2.2)

theorem oldBij_mul_left : oldBijProjection*leftProjection=(leftProjection (A := α)) := by
  simp only [oldBijProjection,leftProjection,predicateProjection,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : leftPredicate i
  · simp [h,h.1]
  · simp [h]

theorem oldBij_mul_rightW : oldBijProjection*rightW=(rightW (A := α)) := by
  ext o i
  simp only [oldBijProjection,predicateProjection,Matrix.diagonal_mul]
  by_cases hb : BijRecord o.2.1 o.2.2
  · simp [hb]
  · have hz : rightW o i=0 := by rw [rightW_coefficient]; simp [hb]
    simp [hb,hz]

theorem oldBij_mul_gram : oldBijProjection*((oracleW (A := α)).conjTranspose*oracleW)=
    oracleW.conjTranspose*oracleW := by
  rw [oracle_gram,Matrix.mul_add,oldBij_mul_left,← Matrix.mul_assoc,oldBij_mul_rightW]

def bijProjection (T : ℕ) : CMatrix (InputCutoff (α := α) T) :=
  Matrix.diagonal (fun i => if BijMultiset (fockLabel i).2.1 (fockLabel i).2.2 then 1 else 0)

theorem bij_projection (T : ℕ) : IsStarProjection (bijProjection (α := α) T) := by
  constructor
  · show bijProjection T*bijProjection T=bijProjection (α := α) T
    simp only [bijProjection,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  · change (bijProjection (α := α) T).conjTranspose=_
    ext i j
    by_cases h : i=j
    · subst j; simp [bijProjection]
    · simp [bijProjection,Matrix.conjTranspose_apply,h,Ne.symm h]

theorem bij_embedding {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    bijProjection T*basisEmbedding (setEmbedding hT)=basisEmbedding (setEmbedding hT)*oldBijProjection := by
  ext o i
  simp only [bijProjection,oldBijProjection,predicateProjection,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases h : o=setEmbedding hT i
  · subst o
    rw [setEmbedding_label]
    simp only [embed,bijMultiset_sets]
    exact mul_comm _ _
  · simp [basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,h]

theorem bij_mul_recordGram {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    bijProjection T*((recordW hT).conjTranspose*recordW hT)=
      (recordW hT).conjTranspose*recordW hT := by
  rw [recordW_gram]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,bij_embedding]
  simp only [Matrix.mul_assoc]
  have hh := congrArg (fun M => basisEmbedding (setEmbedding hT)*M*
    (basisEmbedding (setEmbedding hT)).conjTranspose) (oldBij_mul_gram (α := α))
  simpa only [Matrix.mul_assoc] using hh

theorem recordGram_le_bij {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    (recordW hT).conjTranspose*recordW hT≤bijProjection T := by
  have hp := ICO.MHBellProjectors.projection_difference _ _ (bij_projection T)
    (recordW_initial_projection hT) (bij_mul_recordGram hT)
  exact sub_nonneg.mp hp.nonneg

end
end ICO.MHWDomainProjection

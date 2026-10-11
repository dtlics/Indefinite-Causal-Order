import ICO.MHFockPublicRotation
import ICO.MHFockRunIsometry

/-! The genuine record rotation fixes the empty-record initial state. -/
namespace ICO.MHFockEmptyRotation
open QIT ICO.MHFockTrajectory ICO.MHFockKnownOperation ICO.MHFockPublicRotation
  ICO.MHFockRotation ICO.MHFockLabels ICO.MHBoundedRecording ICO.MHSymmetric
  ICO.MHSectorCovariance ICO.MHCreationCovariance ICO.MHRightCovariance
  ICO.RecordingCopyIdentity ICO.MHProtocolOverlap ICO.MHRectangularAction
  ICO.MHFockRunIsometry
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 512

theorem occupationRotation_zero {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) : occupationRotation U 0=1 := by
  rw [occupationRotation,unitaryTensorPowerMatrix_zero]
  change (occupationEmbedding (a := a) 0).conjTranspose*1*occupationEmbedding (a := a) 0=1
  rw [Matrix.mul_one,occupationEmbedding_gram]

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem empty_rotation_entry (C D : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (o : InputCutoff (α := α) T) (x : α) :
    (fockQ C D T : CMatrix (InputCutoff (α := α) T)) o (emptyFock T x)=
      if o=emptyFock T x then 1 else 0 := by
  rcases o with ⟨⟨s,q⟩,y,p⟩
  by_cases hs : s=(emptyFock T x).1.1
  · subst s
    simp only [emptyFock,labelFock,Multiset.card_zero,fockQ,reindexUnitary,blockUnitary,
      sectorEquiv,Matrix.submatrix_apply,outputTurn,tensorUnitary,symmetricRotation,
      occupationRotation_zero,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.one_apply,Matrix.blockDiagonal'_apply_eq]
    split_ifs <;> simp_all [occupationRotation_zero,Matrix.one_apply]
  · have hz := fockQ_entry_other C D T ⟨⟨s,q⟩,(y,p)⟩ (emptyFock T x) hs
    have hn : (⟨⟨s,q⟩,(y,p)⟩ : InputCutoff (α := α) T)≠emptyFock T x := by
      intro he
      exact hs (congrArg (fun i : InputCutoff (α := α) T => i.1.1) he)
    rw [hz,if_neg hn]

theorem empty_rotation_embedding (C D : Matrix.unitaryGroup α ℂ) (T : ℕ)
    {μ : Type*} [Fintype μ] [DecidableEq μ] :
    Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)*
      basisEmbedding (initialEmbed (α := α) (μ := μ) T)=basisEmbedding (initialEmbed T) := by
  unfold basisEmbedding
  change _*(1 : CMatrix (InputCutoff (α := α) T×μ)).submatrix (Equiv.refl _) _=_
  rw [Matrix.mul_submatrix_one]
  ext o i
  simp only [Matrix.submatrix_apply,Equiv.refl_apply,initialEmbed,Matrix.kronecker,
    Matrix.kroneckerMap_apply,empty_rotation_entry,Matrix.one_apply,Prod.mk.injEq]
  by_cases ho : o.1=emptyFock T i.1 <;> by_cases hm : o.2=i.2 <;>
    simp [initialEmbed,empty_rotation_entry,ho,hm,Prod.ext_iff]

theorem empty_rotation_fixed (C D : Matrix.unitaryGroup α ℂ) (T : ℕ)
    {μ : Type*} [Fintype μ] [DecidableEq μ] (z : α×μ→ℂ) :
    Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)*ᵥ
      initial T z=initial T z := by
  unfold initial
  rw [Matrix.mulVec_mulVec,empty_rotation_embedding]

theorem public_rotation_intertwining (C D : Matrix.unitaryGroup α ℂ) (T : ℕ)
    {μ ν : Type*} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (K : Matrix (α×ν) (α×μ) ℂ) (hK : K.conjTranspose*K=1)
    (z : EuclideanSpace ℂ (InputCutoff (α := α) T×μ)) :
    act (Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix ν))
      (matrixIsometry (known T K) (known_isometry T K hK) z)=
    matrixIsometry (known T K) (known_isometry T K hK)
      (act (Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)) z) := by
  change rectAct _ (rectAct _ z)=rectAct _ (rectAct _ z)
  rw [←rectAct_mul,←rectAct_mul,rotation_known]

#print axioms empty_rotation_fixed
#print axioms public_rotation_intertwining
end
end ICO.MHFockEmptyRotation

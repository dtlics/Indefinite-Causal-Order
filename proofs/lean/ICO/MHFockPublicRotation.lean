import ICO.MHFockKnownOperation
import ICO.MHFockRotation

/-! Literal record rotations commute with every accessible rectangular
operation, including a change of public memory dimension. -/
namespace ICO.MHFockPublicRotation
open QIT ICO.MHFockKnownOperation ICO.MHFockRotation ICO.MHBoundedRecording
  ICO.MHSymmetric ICO.MHCreationCovariance ICO.MHRightCovariance ICO.MHSectorCovariance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 512
variable {α : Type*} [Fintype α] [DecidableEq α]

def recordRotation (C D : Matrix.unitaryGroup α ℂ) (T : ℕ) : CMatrix (Records (α := α) T) :=
  Matrix.blockDiagonal' (fun s : Lengths T => Matrix.kronecker
    (occupationRotation (leftEdgeUnitary C D) s.val.1.val)
    (occupationRotation (rightEdgeUnitary D⁻¹ C⁻¹) s.val.2.val))

variable {μ ν : Type*} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]

theorem rotation_tensor (C D : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)=
      (Matrix.kronecker (1 : CMatrix (α×μ)) (recordRotation C D T)).submatrix
        (queryMemoryFirst T μ) (queryMemoryFirst T μ) := by
  ext o i
  rcases o with ⟨⟨⟨s,q⟩,x,p⟩,m⟩
  rcases i with ⟨⟨⟨s',q'⟩,y,p'⟩,n⟩
  by_cases hs : s=s'
  · subst s'
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
      fockQ,reindexUnitary,blockUnitary,sectorEquiv,outputTurn,tensorUnitary,symmetricRotation,
      Matrix.submatrix_apply,queryMemoryFirst,records,recordRotation,
      Matrix.blockDiagonal'_apply_eq,Prod.mk.injEq]
    by_cases hx : x=y <;> by_cases hm : m=n <;> simp [hx,hm]
  · have hz := fockQ_entry_other C D T ⟨⟨s,q⟩,(x,p)⟩ ⟨⟨s',q'⟩,(y,p')⟩ hs
    simp [Matrix.kronecker,Matrix.kroneckerMap_apply,hz,Matrix.submatrix_apply,
      queryMemoryFirst,records,recordRotation,Matrix.blockDiagonal'_apply,hs]

theorem rotation_known (C D : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (K : Matrix (α×ν) (α×μ) ℂ) :
    Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix ν)*known T K=
      known T K*Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ) := by
  rw [rotation_tensor,rotation_tensor]
  simp only [known,Matrix.submatrix_mul_equiv]
  congr 1
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]

theorem query_tensor_known (C : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    Matrix.kronecker (fockQuery C T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)=
      known T (Matrix.kronecker (C : CMatrix α) (1 : CMatrix μ)) := by
  ext o i
  rcases o with ⟨⟨⟨s,q⟩,x,p⟩,m⟩
  rcases i with ⟨⟨⟨s',q'⟩,y,p'⟩,n⟩
  by_cases hs : s=s'
  · subst s'
    simp only [fockQuery,reindexUnitary,blockUnitary,sectorEquiv,Matrix.submatrix_apply,
      Matrix.blockDiagonal'_apply_eq,queryTurn,tensorUnitary,Matrix.kronecker,
      Matrix.kroneckerMap_apply,Matrix.one_apply,known_coefficient,records]
    simp only [Sigma.mk.inj_iff,heq_eq_eq,Prod.mk.injEq,true_and]
    by_cases hp : p=p' <;> by_cases hq : q=q' <;> by_cases hm : m=n <;> simp [hp,hq,hm]
  · simp [fockQuery,reindexUnitary,blockUnitary,sectorEquiv,Matrix.submatrix_apply,
      Matrix.blockDiagonal'_apply,hs,Matrix.kronecker,Matrix.kroneckerMap_apply,
      known_coefficient,records,Sigma.mk.inj_iff,hs]

#print axioms rotation_known
end
end ICO.MHFockPublicRotation

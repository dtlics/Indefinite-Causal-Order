import ICO.C6RetainedCacheLocal
import ICO.C6CacheKnownOperation
import ICO.C6CacheVisible
import ICO.C6GradedCacheReference

/-! Exact local recording/cache formulas. The incoming query becomes a
private image in a birth; this is valid for every mixed input and arbitrary
entangled memory. Retrieval retains the measured outcome. -/
namespace ICO.C6RetainedSectorOperations
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6CacheKnownOperation
  ICO.C6RetainedCacheLocal ICO.C6CacheQueryBound ICO.C6CacheReference
  ICO.C6MemoryDecode ICO.SwitchObservable ICO.C6CachePreparation
  ICO.C6GradedCacheReference
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2400000
set_option Elab.async false
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def projection (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A) :
    CMatrix (Cache (A := A) (M := M) n) :=
  externalLift n (Matrix.kronecker (basisProjection (U : CMatrix A) j)
    (1 : CMatrix M))

theorem projection_head (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A) :
    projection (M := M) U n j =
      (Matrix.kronecker (basisProjection (U : CMatrix A) j)
        (1 : CMatrix (SideMemory (A := A) (M := M) n))).submatrix
          (headEquiv n).symm (headEquiv n).symm := by
  ext ⟨⟨a,L⟩,m⟩ ⟨⟨b,P⟩,z⟩
  simp [projection,externalLift,externalEquiv,headEquiv,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,ite_and,mul_comm]
  split_ifs <;> simp_all

theorem basisBranch_projection (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A)
    (X : CMatrix (Cache (A := A) (M := M) n)) :
    basisBranch U n j X=conjugate (projection (M := M) U n j) X := by
  simp only [basisBranch,LinearMap.comp_apply,ICO.C6ReindexChannel.apply,
    conjugate_apply]
  rw [projection_head,Matrix.conjTranspose_submatrix,
    ←Matrix.submatrix_mul_equiv _ _ _ (headEquiv n).symm,
    ←Matrix.submatrix_mul_equiv _ _ _ (headEquiv n).symm]
  simp only [Matrix.submatrix_submatrix,Equiv.symm_comp_self,Matrix.submatrix_id_id]
  rfl

theorem retrieve_projection (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A)
    (X : CMatrix (Cache (A := A) (M := M) (n+1))) :
    retrieve U n j X=conjugate
      (memoryPolar n*projection (M := M) U n j*(memoryPolar n).conjTranspose) X := by
  simp only [retrieve,LinearMap.comp_apply,basisBranch_projection,conjugate_apply,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]

/-- The old query is retained as the private image; the new query is ψ_j. -/
def imagePreparation (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A) :
    Matrix (Cache (A := A) (M := M) n×A) (Cache (A := A) (M := M) n) ℂ :=
  fun o i => (U : CMatrix A) o.1.1.1 j *
    (if o.1.1.2=i.1.2 then 1 else 0) *
    (if o.1.2=i.2 then 1 else 0) * (if o.2=i.1.1 then 1 else 0)

theorem preparation_erasure (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A)
    (X : CMatrix (Cache (A := A) (M := M) n)) :
    partialTraceB (conjugate (imagePreparation (M := M) U n j) X)=
      (preparation U n j).map X := by
  rw [preparation_apply]
  ext ⟨⟨a,L⟩,m⟩ ⟨⟨b,P⟩,z⟩
  simp [partialTraceB,conjugate_apply,imagePreparation,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum,
    apply_ite,Finset.sum_ite_irrel,unhead,cacheHead,headEquiv,
    Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    basisState,basisProjection,Matrix.single,partialTraceA,mul_assoc,
    mul_left_comm,mul_comm]
  simp [ite_and,Finset.sum_ite_irrel,eq_comm]

theorem partialTraceB_known {H K R : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
    (F : Matrix K H ℂ) (X : CMatrix (H×R)) :
    partialTraceB (conjugate (Matrix.kronecker F (1:CMatrix R)) X)=
      conjugate F (partialTraceB X) := by
  ext a b
  simp [partialTraceB,conjugate_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum,mul_assoc,apply_ite,Finset.sum_ite_irrel]
  rw [Finset.sum_comm]
  congr 1
  ext i
  rw [Finset.sum_comm]

theorem birth_erasure (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A)
    (X : CMatrix (Cache (A := A) (M := M) (n+1))) :
    ((1/(Fintype.card A:ℝ):ℝ):ℂ) •
      partialTraceB (conjugate
        (Matrix.kronecker (memoryPolar (n+1)) (1:CMatrix A)*
          imagePreparation U (n+1) j*(1-image (memoryPolar n))) X)=
      ICO.C6RetainedCacheLocal.birth (M := M) U n j X := by
  simp only [ICO.C6RetainedCacheLocal.birth,LinearMap.smul_apply,LinearMap.comp_apply]
  rw [←conjugate_comp_apply,←conjugate_comp_apply,
    partialTraceB_known,preparation_erasure]

#print axioms retrieve_projection
#print axioms preparation_erasure
#print axioms birth_erasure
end
end ICO.C6RetainedSectorOperations

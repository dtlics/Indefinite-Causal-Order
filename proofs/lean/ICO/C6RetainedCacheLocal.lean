import ICO.C6CacheReference
import ICO.C6CacheExtension

/-! Literal outcome-resolved cache maps. A retrieved measurement outcome is
retained just like a birth outcome; only summing outcomes yields cacheStep. -/
namespace ICO.C6RetainedCacheLocal
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheReference ICO.C6CacheMap
  ICO.C6CachePreparation ICO.C6CacheWeighted ICO.C6MatrixCovariance
  ICO.C6MemoryDecode ICO.SwitchObservable ICO.C6CacheQueryBound
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def basisBranch (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A) :
    MatrixMap (Cache (A:=A) (M:=M) n) (Cache (A:=A) (M:=M) n) :=
  (ICO.C6ReindexChannel.channel (headEquiv n).symm).map.comp
    ((conjugate (Matrix.kronecker (basisProjection (U:CMatrix A) j)
      (1:CMatrix (SideMemory (A:=A) (M:=M) n)))).comp
      (ICO.C6ReindexChannel.channel (headEquiv n)).map)

theorem basisBranch_cp (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A) :
    MatrixMap.IsCompletelyPositive (basisBranch (M:=M) U n j) :=
  MatrixMap.isCompletelyPositive_comp _ _ (ICO.C6ReindexChannel.channel _).completelyPositive
    (MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
      (ICO.C6ReindexChannel.channel _).completelyPositive)

theorem basisBranch_sum (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (∑j,basisBranch (M:=M) U n j)=(basisChannel (M:=M) U n).map := by
  ext X a b
  simp only [LinearMap.sum_apply, Matrix.sum_apply]
  rw [basis_apply]
  simp only [basisBranch,LinearMap.comp_apply,ICO.C6ReindexChannel.apply,
    conjugate_apply,ICO.C6BasisDephase.basisMap,ICO.AllChannelDilation.oracleMap,
    MatrixMap.ofKraus,unhead,cacheHead,headEquiv,Matrix.submatrix_apply,Matrix.sum_apply]
  change _ = (∑j:A,Matrix.kronecker (basisProjection (U:CMatrix A) j)
    (1:CMatrix (SideMemory (A:=A) (M:=M) n)) *
    cacheHead n X * (Matrix.kronecker (basisProjection (U:CMatrix A) j)
      (1:CMatrix (SideMemory (A:=A) (M:=M) n))).conjTranspose :
        CMatrix (A×SideMemory (A:=A) (M:=M) n))
      ((headEquiv n).symm a) ((headEquiv n).symm b)
  rw [Matrix.sum_apply]
  rfl

def preparation (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A) :
    Channel (Cache (A:=A) (M:=M) n) (Cache (A:=A) (M:=M) n) :=
  (ICO.C6ReindexChannel.channel (headEquiv n).symm).comp
    ((ICO.C6CachePreparation.withMemory (M:=SideMemory (A:=A) (M:=M) n) U j).comp
      (ICO.C6ReindexChannel.channel (headEquiv n)))

theorem preparation_apply (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A)
    (X : CMatrix (Cache (A:=A) (M:=M) n)) :
    (preparation U n j).map X=unhead n
      (Matrix.kronecker (ICO.C6CachePreparation.basisState U j).matrix
        (partialTraceA (cacheHead n X))) := by
  change (ICO.C6ReindexChannel.channel (headEquiv n).symm).map
    ((ICO.C6CachePreparation.withMemory U j).map
      ((ICO.C6ReindexChannel.channel (headEquiv n)).map X))=_
  rw [ICO.C6ReindexChannel.apply,ICO.C6ReindexChannel.apply,
    ICO.C6CachePreparation.withMemory_apply]
  rfl

theorem memory_preparation_average (U : Matrix.unitaryGroup A ℂ)
    {N : Type u} [Fintype N] [DecidableEq N] (X : CMatrix (A×N)) :
    (∑j:A,((1/(Fintype.card A:ℝ):ℝ):ℂ) •
      (ICO.C6CachePreparation.withMemory U j).map X)=
        (ICO.RecordingDepolarizing.withMemory (α:=A) (μ:=N)).map X := by
  have hs : (∑j:A,(ICO.C6CachePreparation.basisState U j).matrix)=(1:CMatrix A) :=
    basisProjection_complete _ U.property.2
  rw [ICO.RecordingDepolarizing.withMemory_apply]
  ext ⟨a,m⟩ ⟨b,n⟩
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    ICO.C6CachePreparation.withMemory_apply,Matrix.kronecker,Matrix.kroneckerMap_apply]
  rw [←Finset.mul_sum,←Finset.sum_mul,←Matrix.sum_apply,hs]
  by_cases hab:a=b
  · subst b
    change _=QIT.Classical.block (QIT.Classical.blockDiagonal _) a a m n
    rw [QIT.Classical.blockDiagonal_block_self]
    simp [Matrix.one_apply,Matrix.smul_apply,smul_eq_mul]
  · change _=QIT.Classical.block (QIT.Classical.blockDiagonal _) a b m n
    rw [QIT.Classical.blockDiagonal_block_ne _ hab]
    simp [Matrix.one_apply,hab]

theorem preparation_average (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (∑j:A,((1/(Fintype.card A:ℝ):ℝ):ℂ) • (preparation (M:=M) U n j).map)=
      (uniformChannel (M:=M) n).map := by
  ext X a b
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul]
  rw [uniform_apply]
  have h:=congrArg (fun Y=>unhead n Y a b)
    (memory_preparation_average U (cacheHead n X))
  simpa only [preparation_apply,ICO.C6CachePreparation.withMemory_apply,unhead,Matrix.submatrix_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using h

def retrieve (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A) :
    MatrixMap (Cache (A:=A) (M:=M) (n+1)) (Cache (A:=A) (M:=M) (n+1)) :=
  (conjugate (memoryPolar n)).comp
    ((basisBranch U n j).comp (conjugate (memoryPolar (A:=A) (M:=M) n).conjTranspose))

def birth (U : Matrix.unitaryGroup A ℂ) (n : ℕ) (j : A) :
    MatrixMap (Cache (A:=A) (M:=M) (n+1)) (Cache (A:=A) (M:=M) (n+2)) :=
  ((1/(Fintype.card A:ℝ):ℝ):ℂ) •
    (conjugate (memoryPolar (n+1))).comp
      ((preparation U (n+1) j).map.comp (conjugate (1-image (memoryPolar n))))

theorem retrieve_sum (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (∑j,retrieve (M:=M) U n j)=retrieval (memoryPolar n) (basisChannel U n) := by
  ext X a b
  have h:=congrArg (fun Φ : MatrixMap (Cache (A:=A) (M:=M) n) (Cache (A:=A) (M:=M) n) =>
    conjugate (memoryPolar n) (Φ (conjugate (memoryPolar (A:=A) (M:=M) n).conjTranspose X)) a b)
    (basisBranch_sum (M:=M) U n)
  simpa only [retrieve,retrieval,LinearMap.sum_apply,LinearMap.comp_apply,
    map_sum,Matrix.sum_apply] using h

theorem birth_sum (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (∑j,birth (M:=M) U n j)=ICO.C6CacheMap.birth (memoryPolar n) (memoryPolar (n+1))
      (uniformChannel (M:=M) (n+1)) := by
  ext X a b
  have h:=congrArg (fun Φ : MatrixMap (Cache (A:=A) (M:=M) (n+1))
      (Cache (A:=A) (M:=M) (n+1)) =>
    conjugate (memoryPolar (n+1)) (Φ (conjugate (1-image (memoryPolar n)) X)) a b)
    (preparation_average (M:=M) U (n+1))
  simpa only [birth,ICO.C6CacheMap.birth,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply] using h

#print axioms basisBranch_sum
#print axioms preparation_average
#print axioms retrieve_sum
#print axioms birth_sum
end
end ICO.C6RetainedCacheLocal

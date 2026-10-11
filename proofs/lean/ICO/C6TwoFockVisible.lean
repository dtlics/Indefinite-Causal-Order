import ICO.C6TwoFockSector
import ICO.C6CacheVisible

/-! Fixed-sector insertion is a private isometry and preserves the actual
visible reduced matrix, even with arbitrary entanglement with learner memory. -/
namespace ICO.C6TwoFockVisible
open QIT Matrix ICO.C6TwoFockSector ICO.C6CacheDecode ICO.C6CacheKnownOperation
  ICO.C6CacheVisible ICO.C6PrivateIsometry ICO.MHBoundedRecording
  ICO.MHFockKnownOperation ICO.MHDecompressionErasure ICO.RecordingCopyIdentity
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
universe u
variable {A M N : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

abbrev PairRecords (l r : ℕ) :=
  TensorPowerProfile (A×A) l × TensorPowerProfile (A×A) r

def recordEmbed (T l r : ℕ) (h : l+r≤T) (p : PairRecords (A := A) l r) :
    Records (α := A) T := ⟨lengths T l r h,p⟩

def recordJ (T l r : ℕ) (h : l+r≤T) :
    Matrix (Records (α := A) T) (PairRecords (A := A) l r) ℂ :=
  basisEmbedding (recordEmbed T l r h)

theorem recordJ_gram (T l r : ℕ) (h : l+r≤T) :
    (recordJ (A := A) T l r h).conjTranspose*recordJ (A := A) T l r h=1 := by
  apply basisEmbedding_gram
  intro p q he
  exact eq_of_heq (Sigma.mk.inj he).2

def cacheFirst (l r : ℕ) (M : Type u) :
    (Cache (A := A) (M := M) l × TensorPowerProfile (A×A) r) ≃
      (A×M)×PairRecords (A := A) l r where
  toFun x := ((x.1.1.1,x.1.2),(x.1.1.2,x.2))
  invFun x := (((x.1.1,x.2.1),x.1.2),x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def memoryEmbed (T l r : ℕ) (h : l+r≤T)
    (x : Cache (A := A) (M := M) l × TensorPowerProfile (A×A) r) :
    InputCutoff (α := A) T×M := (sectorEmbed T l r h (x.1.1,x.2),x.1.2)

def memoryJ (T l r : ℕ) (h : l+r≤T) :
    Matrix (InputCutoff (α := A) T×M)
      (Cache (A := A) (M := M) l × TensorPowerProfile (A×A) r) ℂ :=
  basisEmbedding (memoryEmbed T l r h)

theorem memoryJ_tensor (T l r : ℕ) (h : l+r≤T) :
    memoryJ (A := A) (M := M) T l r h =
      (Matrix.kronecker (1 : CMatrix (A×M)) (recordJ T l r h)).submatrix
        (queryMemoryFirst T M) (cacheFirst l r M) := by
  ext o i
  have he : o=memoryEmbed T l r h i ↔
      (queryMemoryFirst (α := A) T M o).1=(cacheFirst l r M i).1 ∧
        (queryMemoryFirst T M o).2=recordEmbed T l r h (cacheFirst l r M i).2 := by
    rw [← (queryMemoryFirst (α := A) T M).injective.eq_iff]
    exact Prod.ext_iff
  simp only [memoryJ,basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,
    recordJ,Matrix.kronecker,Matrix.kroneckerMap_apply,id_eq]
  simp only [he]
  split_ifs <;> simp_all

theorem cache_trace (l r : ℕ)
    (X : CMatrix (Cache (A := A) (M := M) l × TensorPowerProfile (A×A) r)) :
    partialTraceB (X.submatrix (cacheFirst l r M).symm (cacheFirst l r M).symm) =
      (sectorVisible l).map (partialTraceB X) := by
  rw [sectorVisible_apply]
  ext ⟨a,m⟩ ⟨b,n⟩
  simp only [partialTraceB,partialTraceA,Fintype.sum_prod_type,
    Matrix.submatrix_apply,cacheFirst,externalEquiv,Equiv.coe_fn_mk,Equiv.symm_mk]

theorem visible_memoryJ (T l r : ℕ) (h : l+r≤T)
    (v : Cache (A := A) (M := M) l × TensorPowerProfile (A×A) r → ℂ) :
    fockVisible T (memoryJ T l r h*ᵥv) =
      (sectorVisible l).map (partialTraceB (rankOneMatrix v)) := by
  rw [fockVisible,memoryJ_tensor,Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id]
  rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
    private_erasure_matrix (recordJ T l r h) (recordJ_gram T l r h)]
  have he : rankOneMatrix (v ∘ (cacheFirst l r M).symm) =
      (rankOneMatrix v).submatrix (cacheFirst l r M).symm (cacheFirst l r M).symm := by
    ext i j
    rfl
  rw [he,cache_trace]

def cacheKnown (l r : ℕ) (K : Matrix (A×N) (A×M) ℂ) :
    Matrix (Cache (A := A) (M := N) l × TensorPowerProfile (A×A) r)
      (Cache (A := A) (M := M) l × TensorPowerProfile (A×A) r) ℂ :=
  (Matrix.kronecker K (1 : CMatrix (PairRecords (A := A) l r))).submatrix
    (cacheFirst l r N) (cacheFirst l r M)

theorem cacheKnown_eq (l r : ℕ) (K : Matrix (A×N) (A×M) ℂ) :
    cacheKnown l r K = Matrix.kronecker (externalLift l K)
      (1 : CMatrix (TensorPowerProfile (A×A) r)) := by
  ext ⟨⟨⟨a,L⟩,n⟩,R⟩ ⟨⟨⟨b,P⟩,m⟩,S⟩
  simp [cacheKnown,cacheFirst,externalLift,externalEquiv,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,mul_comm,ite_and]
  split_ifs <;> simp_all

theorem memoryJ_known (T l r : ℕ) (h : l+r≤T) (K : Matrix (A×N) (A×M) ℂ) :
    ICO.MHFockKnownOperation.known T K*memoryJ T l r h =
      memoryJ T l r h*cacheKnown l r K := by
  rw [memoryJ_tensor,memoryJ_tensor,ICO.MHFockKnownOperation.known,cacheKnown]
  rw [Matrix.submatrix_mul_equiv _ _ _ (queryMemoryFirst T M),
    Matrix.submatrix_mul_equiv _ _ _ (cacheFirst l r N)]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul]

#print axioms visible_memoryJ
#print axioms memoryJ_known
end
end ICO.C6TwoFockVisible

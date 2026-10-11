import ICO.C6TwoFockVisible
import ICO.C6TwoFockAdjoint
import ICO.C6RetainedSectorOperations

/-! Fixed-sector polar identities with arbitrary visible quantum memory. -/
namespace ICO.C6TwoFockMemory
open QIT Matrix ICO.C6TwoFockSector ICO.C6TwoFockAdjoint ICO.C6TwoFockVisible
  ICO.C6CacheDecode ICO.C6CacheQueryBound ICO.C6PolarFock ICO.C6BosonicPolar
  ICO.RecordingCopyIdentity ICO.MHBoundedRecording
  ICO.C6RetainedSectorOperations ICO.MHFockKnownOperation
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2400000
set_option Elab.async false
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def sectorMemoryFirst (l r : ℕ) :
    (Cache (A := A) (M := M) l×TensorPowerProfile (A×A) r) ≃
      TwoSector (A := A) l r×M where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem memoryJ_factor (T l r : ℕ) (h : l+r≤T) :
    memoryJ (A := A) (M := M) T l r h=
      (Matrix.kronecker (J T l r h) (1:CMatrix M)).submatrix
        id (sectorMemoryFirst l r) := by
  ext o i
  have he : o=memoryEmbed T l r h i ↔
      o.1=sectorEmbed T l r h (sectorMemoryFirst (M := M) l r i).1 ∧
        o.2=(sectorMemoryFirst (M := M) l r i).2 := Prod.ext_iff
  simp only [memoryJ,J,basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,id_eq,he]
  split_ifs <;> simp_all

theorem left_memory_factor (l k r : ℕ)
    (D : Matrix (Sector (A := A) k) (Sector (A := A) l) ℂ) :
    Matrix.kronecker (Matrix.kronecker D (1:CMatrix M))
        (1:CMatrix (TensorPowerProfile (A×A) r))=
      (Matrix.kronecker (Matrix.kronecker D
        (1:CMatrix (TensorPowerProfile (A×A) r))) (1:CMatrix M)).submatrix
          (sectorMemoryFirst (M := M) k r) (sectorMemoryFirst (M := M) l r) := by
  ext ⟨⟨s,m⟩,R⟩ ⟨⟨v,n⟩,S⟩
  simp [sectorMemoryFirst,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,mul_assoc,mul_comm,mul_left_comm]

theorem mul_submatrix_id {a b c p : Type*} [Fintype a]
    (F : Matrix p a ℂ) (G : Matrix a b ℂ) (f : c→b) :
    F*G.submatrix id f=(F*G).submatrix id f := by
  ext i j
  rfl

theorem memoryJ_left {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    Matrix.kronecker (polarLeftOnFock (α := A) h) (1:CMatrix M)*
      memoryJ T l r (by omega)=
      memoryJ T (l+1) r (by omega)*
        Matrix.kronecker (memoryPolar (A := A) (M := M) l)
          (1:CMatrix (TensorPowerProfile (A×A) r)) := by
  rw [memoryJ_factor,memoryJ_factor,memoryPolar,left_memory_factor]
  rw [mul_submatrix_id,Matrix.submatrix_mul_equiv _ _ _
    (sectorMemoryFirst (A := A) (M := M) (l+1) r)]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
  rw [polarLeft_sector h hs]
  rfl

theorem memoryJ_left_adjoint {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    (Matrix.kronecker (polarLeftOnFock (α := A) h) (1:CMatrix M)).conjTranspose*
      memoryJ T (l+1) r (by omega)=
      memoryJ T l r (by omega)*
        Matrix.kronecker (memoryPolar (A := A) (M := M) l).conjTranspose
          (1:CMatrix (TensorPowerProfile (A×A) r)) := by
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    memoryPolar]
  change Matrix.kronecker (polarLeftOnFock (α := A) h).conjTranspose (1:CMatrix M)*
      memoryJ T (l+1) r (by omega)=
    memoryJ T l r (by omega)*Matrix.kronecker
      (Matrix.kronecker (leftPolar (A := A) l).conjTranspose (1:CMatrix M))
        (1:CMatrix (TensorPowerProfile (A×A) r))
  rw [memoryJ_factor,memoryJ_factor,left_memory_factor]
  rw [mul_submatrix_id,Matrix.submatrix_mul_equiv _ _ _
    (sectorMemoryFirst (A := A) (M := M) l r)]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
  rw [polarLeft_adjoint_sector h hs]
  rfl

theorem kronecker_sub_left {a b c e : Type*}
    (D E : Matrix a b ℂ) (R : Matrix c e ℂ) :
    Matrix.kronecker (D-E) R=Matrix.kronecker D R-Matrix.kronecker E R := by
  ext i j
  simp [Matrix.kronecker,Matrix.kroneckerMap_apply,sub_mul]

theorem memoryJ_left_complement {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t) :
    (1-Matrix.kronecker (polarLeftOnFock (α := A) h) (1:CMatrix M)*
      (Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M)).conjTranspose)*
      memoryJ T (l+1) r (by omega)=
      memoryJ T (l+1) r (by omega)*
        Matrix.kronecker (1-memoryPolar (A := A) (M := M) l*(memoryPolar l).conjTranspose)
          (1:CMatrix (TensorPowerProfile (A×A) r)) := by
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,memoryJ_left_adjoint h hs,
    ←Matrix.mul_assoc,memoryJ_left h hs,Matrix.mul_assoc]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
  have hk : Matrix.kronecker
      (1-memoryPolar (A := A) (M := M) l*(memoryPolar l).conjTranspose)
        (1:CMatrix (TensorPowerProfile (A×A) r))=
      1-Matrix.kronecker (memoryPolar l*(memoryPolar l).conjTranspose)
        (1:CMatrix (TensorPowerProfile (A×A) r)) := by
    rw [kronecker_sub_left]
    simp only [Matrix.kronecker,Matrix.one_kronecker_one]
  simp only [Matrix.kronecker] at hk
  rw [hk,Matrix.mul_sub,Matrix.mul_one]

theorem memoryJ_retrieval {t T l r : ℕ} (h : t+1≤T) (hs : l+r≤t)
    (U : Matrix.unitaryGroup A ℂ) (j : A) :
    (Matrix.kronecker (polarLeftOnFock (α := A) h) (1:CMatrix M)*
      ICO.MHFockKnownOperation.known T
        (Matrix.kronecker (ICO.SwitchObservable.basisProjection (U:CMatrix A) j)
          (1:CMatrix M))*
      (Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M)).conjTranspose)*
      memoryJ T (l+1) r (by omega)=
      memoryJ T (l+1) r (by omega)*
        Matrix.kronecker
          (memoryPolar l*projection (M := M) U l j*(memoryPolar l).conjTranspose)
          (1:CMatrix (TensorPowerProfile (A×A) r)) := by
  rw [Matrix.mul_assoc,Matrix.mul_assoc,memoryJ_left_adjoint h hs,
    ←Matrix.mul_assoc (ICO.MHFockKnownOperation.known T _),memoryJ_known,
    ←Matrix.mul_assoc,←Matrix.mul_assoc,memoryJ_left h hs]
  rw [cacheKnown_eq]
  simp only [projection,Matrix.mul_assoc,Matrix.kronecker,
    ←Matrix.mul_kronecker_mul,Matrix.mul_one]

#print axioms memoryJ_left
#print axioms memoryJ_left_adjoint
#print axioms memoryJ_left_complement
#print axioms memoryJ_retrieval
end
end ICO.C6TwoFockMemory

import ICO.C6RetainedSectorOperations
import ICO.C6ChoiceCache
import ICO.C6RawFlagSlices

/-! Literal Bool pinching, with the tag kept in accessible memory.
Every local cache operator transports the tag as an untouched spectator. -/
namespace ICO.C6CacheMemoryTags
open Matrix QIT ICO.C6RetainedSectorOperations ICO.C6CacheDecode
  ICO.C6CacheQueryBound ICO.C6CacheKnownOperation ICO.C6ChoiceCache
  ICO.C6RawFlagSlices ICO.RecordingCopyIdentity ICO.RecordingPureCorrespondence
  ICO.C6BosonicPolar
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1900000
set_option Elab.async false
variable {A M:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def cacheTag (r:ℕ) (b:Bool) (i:Cache (A:=A) (M:=M) r) :
    Cache (A:=A) (M:=Bool×M) r := (i.1,(b,i.2))

def tag (r:ℕ) (b:Bool) : Matrix (Cache (A:=A) (M:=Bool×M) r)
    (Cache (A:=A) (M:=M) r) ℂ := basisEmbedding (cacheTag r b)

theorem tag_external (r:ℕ) (b:Bool) : tag (A:=A) (M:=M) r b=
    externalLift r (basisEmbedding (tagInjection (A:=A) (M:=M) b)) := by
  ext ⟨⟨a,L⟩,c,m⟩ ⟨⟨x,P⟩,z⟩
  simp [tag,cacheTag,basisEmbedding,tagInjection,externalLift,externalEquiv,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,ite_and]
  split_ifs <;> simp_all

theorem operator_tag (k r:ℕ) (D:Matrix (Sector (A:=A) k) (Sector (A:=A) r) ℂ) (b:Bool) :
    Matrix.kronecker D (1:CMatrix (Bool×M))*tag r b=
      tag k b*Matrix.kronecker D (1:CMatrix M) := by
  rw [tag,mul_basisEmbedding]
  ext ⟨o,c,m⟩ ⟨i,z⟩
  simp [tag,cacheTag,basisEmbedding,Matrix.mul_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Fintype.sum_prod_type,
    ite_and,Finset.sum_ite_irrel,eq_comm]

theorem memoryPolar_tag (r:ℕ) (b:Bool) :
    memoryPolar (A:=A) (M:=Bool×M) r*tag r b=
      tag (r+1) b*memoryPolar (A:=A) (M:=M) r := operator_tag _ _ _ b

theorem memoryPolar_adjoint_tag (r:ℕ) (b:Bool) :
    (memoryPolar (A:=A) (M:=Bool×M) r)ᴴ*tag (r+1) b=
      tag r b*(memoryPolar (A:=A) (M:=M) r)ᴴ := by
  simp only [memoryPolar,Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  exact operator_tag _ _ _ b

theorem projection_tag (U:Matrix.unitaryGroup A ℂ) (r:ℕ) (j:A) (b:Bool) :
    projection (M:=Bool×M) U r j*tag r b=tag r b*projection (M:=M) U r j := by
  have he (N:Type) [Fintype N] [DecidableEq N] : projection (M:=N) U r j=
      Matrix.kronecker (Matrix.kronecker (ICO.SwitchObservable.basisProjection (U:CMatrix A) j)
        (1:CMatrix (TensorPowerProfile (A×A) r))) (1:CMatrix N) := by
    ext ⟨⟨a,L⟩,m⟩ ⟨⟨x,P⟩,z⟩
    simp [projection,externalLift,externalEquiv,Matrix.kronecker,
      Matrix.kroneckerMap_apply,Matrix.one_apply,mul_assoc,mul_comm,mul_left_comm]
    split_ifs <;> simp_all
  rw [he,he]
  exact operator_tag _ _ _ b

theorem preparation_tag (U:Matrix.unitaryGroup A ℂ) (r:ℕ) (j:A) (b:Bool) :
    imagePreparation (M:=Bool×M) U r j*tag r b=
      Matrix.kronecker (tag (A:=A) (M:=M) r b) (1:CMatrix A)*imagePreparation (M:=M) U r j := by
  rw [tag,mul_basisEmbedding]
  ext ⟨⟨⟨a,L⟩,c,m⟩,y⟩ ⟨⟨x,P⟩,z⟩
  simp [tag,cacheTag,basisEmbedding,imagePreparation,Matrix.mul_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
    Fintype.sum_prod_type,ite_and,Finset.sum_ite_irrel,mul_assoc,eq_comm]
  split_ifs <;> simp_all

theorem choice_eq (r:ℕ) (b:Bool) :
    externalLift r (Matrix.kronecker (1:CMatrix A) (choiceProject b M))=
      tag (A:=A) (M:=M) r b*(tag r b)ᴴ := by
  ext ⟨⟨a,L⟩,c,m⟩ ⟨⟨x,P⟩,e,z⟩
  simp [tag,cacheTag,basisEmbedding,choiceProject,externalLift,externalEquiv,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Fintype.sum_prod_type,
    ite_and,Finset.sum_ite_irrel,eq_comm]
  split_ifs <;> simp_all

#print axioms preparation_tag
#print axioms choice_eq
end
end ICO.C6CacheMemoryTags

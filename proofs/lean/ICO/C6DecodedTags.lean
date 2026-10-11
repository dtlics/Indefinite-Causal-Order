import ICO.C6DecodedHistory
import ICO.C6CacheMemoryTags

namespace ICO.C6DecodedTags
open Matrix QIT ICO.C6DecodedHistory ICO.C6CacheMemoryTags ICO.C6CacheDecode
  ICO.C6CacheQueryBound ICO.C6ModeFockRetrieval ICO.C6PrivateImageAppend
  ICO.C6RetainedSectorOperations ICO.RecordingCopyIdentity ICO.RecordingPureCorrespondence
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem missing_tag (r:ℕ) (b:Bool) :
    missing (A:=A) (M:=Bool×M) r*tag r b=tag r b*missing (A:=A) (M:=M) r := by
  cases r with
  | zero=>simp only [missing,Matrix.one_mul,Matrix.mul_one]
  | succ r=>
    simp only [missing,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_sub,Matrix.mul_one]
    rw [Matrix.mul_assoc,memoryPolar_adjoint_tag,←Matrix.mul_assoc,memoryPolar_tag,Matrix.mul_assoc]

theorem retrieved_tag (U:Matrix.unitaryGroup A ℂ) (j:A) (r:ℕ) (b:Bool) :
    retrieved (M:=Bool×M) U j r*tag r b=tag r b*retrieved (M:=M) U j r := by
  cases r with
  | zero=>simp only [retrieved,Matrix.zero_mul,Matrix.mul_zero]
  | succ r=>
    simp only [retrieved,cacheRetrieval]
    rw [Matrix.mul_assoc,Matrix.mul_assoc,memoryPolar_adjoint_tag,
      ←Matrix.mul_assoc (projection _ _ _),projection_tag,
      ←Matrix.mul_assoc,←Matrix.mul_assoc,memoryPolar_tag]
    simp only [Matrix.mul_assoc]

theorem birthMatrix_tag (U:Matrix.unitaryGroup A ℂ) (j:A) (r:ℕ) (b:Bool) :
    birthMatrix (M:=Bool×M) U r j*tag r b=
      Matrix.kronecker (tag (A:=A) (M:=M) (r+1) b) (1:CMatrix A)*birthMatrix (M:=M) U r j := by
  rw [birthMatrix,birthMatrix,Matrix.mul_assoc,Matrix.mul_assoc,missing_tag,
    ←Matrix.mul_assoc (imagePreparation _ _ _),preparation_tag,
    ←Matrix.mul_assoc,←Matrix.mul_assoc]
  have hk:Matrix.kronecker (memoryPolar (A:=A) (M:=Bool×M) r) (1:CMatrix A)*
      Matrix.kronecker (tag r b) (1:CMatrix A)=
    Matrix.kronecker (tag (A:=A) (M:=M) (r+1) b) (1:CMatrix A)*
      Matrix.kronecker (memoryPolar (A:=A) (M:=M) r) (1:CMatrix A) := by
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one,memoryPolar_tag]
  rw [hk]
  simp only [Matrix.mul_assoc]

def imageTag (r:ℕ) (b:Bool) : Matrix (ImageCache (A:=A) r (Bool×M)) (ImageCache (A:=A) r M) ℂ :=
  Matrix.kronecker (tag r b) (1:CMatrix (Fin r→A))

theorem imageTag_embedding (r:ℕ) (b:Bool) : imageTag (A:=A) (M:=M) r b=
    basisEmbedding (fun x:ImageCache (A:=A) r M=>(cacheTag r b x.1,x.2)) := by
  ext o i
  simp only [imageTag,tag,basisEmbedding,Matrix.submatrix_apply,id_eq,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Prod.ext_iff]
  split_ifs <;> simp_all

theorem append_tag {r:ℕ} (F:Matrix (Cache (A:=A) (M:=Bool×M) (r+1)×A)
      (Cache (A:=A) (M:=Bool×M) r) ℂ)
    (G:Matrix (Cache (A:=A) (M:=M) (r+1)×A) (Cache (A:=A) (M:=M) r) ℂ)
    (b:Bool) (hF:F*tag r b=Matrix.kronecker (tag (r+1) b) (1:CMatrix A)*G) :
    appendPrivate r F*imageTag r b=imageTag (r+1) b*appendPrivate r G := by
  rw [imageTag_embedding,mul_basisEmbedding]
  ext ⟨o,v⟩ ⟨i,w⟩
  have he:=congrFun (congrFun hF (o,v 0)) i
  rw [tag,mul_basisEmbedding] at he
  simp only [Matrix.submatrix_apply,id_eq] at he
  simp only [appendPrivate,appendEquiv,Matrix.submatrix_apply,id_eq,
    Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,
    Equiv.prodAssoc_symm_apply,Fin.consEquiv_symm_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply]
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,imageTag,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  simp only [mul_ite,ite_mul,mul_one,one_mul,mul_zero,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply] at he
  simpa [Finset.sum_mul,Finset.mul_sum,mul_assoc,Matrix.one_apply,Finset.sum_ite_irrel] using
    congrArg (fun x:ℂ=>x*(if Fin.tail v=w then 1 else 0)) he

theorem core_tag (U:Matrix.unitaryGroup A ℂ) (j:A) (c:ℂ) (r:ℕ) (f b:Bool) :
    core (M:=Bool×M) U j c r f*imageTag r b=
      imageTag (r+if f then 1 else 0) b*core (M:=M) U j c r f := by
  cases f with
  | false=>
    change Matrix.kronecker (retrieved (M:=Bool×M) U j r) (1:CMatrix (Fin r→A))*imageTag r b=
      imageTag r b*Matrix.kronecker (retrieved (M:=M) U j r) (1:CMatrix (Fin r→A))
    have he:=congrArg (fun D=>Matrix.kronecker D ((1:CMatrix (Fin r→A))*1))
      (retrieved_tag (M:=M) U j r b)
    have hl:=Matrix.mul_kronecker_mul (retrieved (M:=Bool×M) U j r)
      (tag (A:=A) (M:=M) r b) (1:CMatrix (Fin r→A)) (1:CMatrix (Fin r→A))
    have hr:=Matrix.mul_kronecker_mul (tag (A:=A) (M:=M) r b)
      (retrieved (M:=M) U j r) (1:CMatrix (Fin r→A)) (1:CMatrix (Fin r→A))
    exact hl.symm.trans (he.trans hr)
  | true=>
    change (c • appendPrivate r (birthMatrix (M:=Bool×M) U r j))*imageTag r b=
      imageTag (r+1) b*(c •appendPrivate r (birthMatrix (M:=M) U r j))
    have hh:=congrArg (fun D:Matrix (ImageCache (A:=A) (r+1) (Bool×M))
        (ImageCache (A:=A) r M) ℂ=>c •D)
      (append_tag (M:=M) (birthMatrix (M:=Bool×M) U r j)
        (birthMatrix (M:=M) U r j) b (birthMatrix_tag (M:=M) U j r b))
    have hl:=Matrix.smul_mul c (appendPrivate r (birthMatrix (M:=Bool×M) U r j))
      (imageTag (A:=A) (M:=M) r b)
    have hr:=Matrix.mul_smul (imageTag (A:=A) (M:=M) (r+1) b) c
      (appendPrivate r (birthMatrix (M:=M) U r j))
    exact hl.trans (hh.trans hr.symm)

theorem choiceImages_eq (r:ℕ) (b:Bool) : choiceImages (A:=A) (M:=M) r b=
    imageTag r b*(imageTag r b)ᴴ := by
  rw [choiceImages,knownImages,choice_eq]
  simp only [imageTag,Matrix.kronecker,
    Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,←Matrix.mul_kronecker_mul,Matrix.mul_one]

#print axioms core_tag
end
end ICO.C6DecodedTags

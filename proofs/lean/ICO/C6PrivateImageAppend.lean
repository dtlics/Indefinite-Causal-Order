import ICO.C6RetainedSectorOperations
import ICO.C6AcceptedBirthFactor

/-! A new inaccessible image is prepended to the literal image word. Its
erasure commutes with arbitrary mixed input, older images, and side memory. -/
namespace ICO.C6PrivateImageAppend
open Matrix QIT ICO.C6RetainedSectorOperations ICO.C6CacheDecode
  ICO.C6CacheQueryBound ICO.C6CacheMap ICO.C6RetainedCacheLocal
  ICO.C6GradedCacheReference ICO.RecordingPureCorrespondence
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A H K:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

def appendEquiv (K:Type) (r:ℕ) :
    (K×(Fin (r+1)→A))≃((K×A)×(Fin r→A)) :=
  (Equiv.prodCongr (Equiv.refl K) (Fin.consEquiv (fun _:Fin (r+1)=>A)).symm).trans
    (Equiv.prodAssoc K A (Fin r→A)).symm

def appendPrivate (r:ℕ) (F:Matrix (K×A) H ℂ) :
    Matrix (K×(Fin (r+1)→A)) (H×(Fin r→A)) ℂ :=
  (Matrix.kronecker F (1:CMatrix (Fin r→A))).submatrix (appendEquiv K r) id

theorem erase_append (r:ℕ) (X:CMatrix ((K×A)×(Fin r→A))) :
    partialTraceB (X.submatrix (appendEquiv K r) (appendEquiv K r))=
      partialTraceB (partialTraceB X) := by
  ext a b
  change (∑v:Fin (r+1)→A,X ((a,v 0),Fin.tail v) ((b,v 0),Fin.tail v))=
    ∑x:A,∑v:Fin r→A,X ((a,x),v) ((b,x),v)
  have he:=Fintype.sum_equiv (Fin.consEquiv (fun _:Fin (r+1)=>A))
    (fun p:A×(Fin r→A)=>X ((a,p.1),p.2) ((b,p.1),p.2))
    (fun v:Fin (r+1)→A=>X ((a,v 0),Fin.tail v) ((b,v 0),Fin.tail v))
    (by intro p; simp [Fin.consEquiv])
  simpa only [Fintype.sum_prod_type] using he.symm

theorem append_erasure (r:ℕ) (F:Matrix (K×A) H ℂ)
    (X:CMatrix (H×(Fin r→A))) :
    partialTraceB (conjugate (appendPrivate r F) X)=
      partialTraceB (conjugate F (partialTraceB X)) := by
  have he:conjugate (appendPrivate r F) X=
      (conjugate (Matrix.kronecker F (1:CMatrix (Fin r→A))) X).submatrix
        (appendEquiv K r) (appendEquiv K r) := by
    ext a b
    rfl
  rw [he,erase_append,partialTraceB_known]

theorem appended_preparation {M:Type} [Fintype M] [DecidableEq M]
    (U:Matrix.unitaryGroup A ℂ) (l r:ℕ) (j:A)
    (X:CMatrix (Cache (A:=A) (M:=M) l×(Fin r→A))) :
    partialTraceB (conjugate (appendPrivate r (imagePreparation (M:=M) U l j)) X)=
      (ICO.C6RetainedCacheLocal.preparation U l j).map (partialTraceB X) := by
  rw [append_erasure,preparation_erasure]

theorem appended_birth {M:Type} [Fintype M] [DecidableEq M]
    (U:Matrix.unitaryGroup A ℂ) (l r:ℕ) (j:A)
    (X:CMatrix (Cache (A:=A) (M:=M) (l+1)×(Fin r→A))) :
    ((1/(Fintype.card A:ℝ):ℝ):ℂ) •
      partialTraceB (conjugate (appendPrivate r
        (Matrix.kronecker (memoryPolar (l+1)) (1:CMatrix A)*
          imagePreparation U (l+1) j*(1-image (memoryPolar l)))) X)=
        ICO.C6RetainedCacheLocal.birth U l j (partialTraceB X) := by
  rw [append_erasure,birth_erasure]

#print axioms append_erasure
#print axioms appended_birth
end
end ICO.C6PrivateImageAppend

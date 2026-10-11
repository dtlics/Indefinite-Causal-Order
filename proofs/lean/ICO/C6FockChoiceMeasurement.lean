import ICO.C6ChoiceMeasurement
import ICO.C6LocalDeletion

/-! The actual known middle measurement on Fock records is a private family
of normalized query-vector preparations, with arbitrary spectator memory. -/
namespace ICO.C6FockChoiceMeasurement
open Matrix QIT ICO.C6ChoiceMeasurement ICO.C6SharedStages
  ICO.MHFockKnownOperation ICO.MHBoundedRecording ICO.C6FockCompression
  ICO.C6QueryPreparation ICO.MHFockSpace
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A M N : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

def withQuery {T:ℕ} (R:Records (α:=A) T) (a:A) : InputCutoff (α:=A) T :=
  (queryRecordEquiv T).symm (a,R)

theorem withQuery_records {T:ℕ} (R:Records (α:=A) T) (a:A) : records (withQuery R a)=R := rfl

theorem withQuery_self {T:ℕ} (i:InputCutoff (α:=A) T) : withQuery (records i) i.2.1=i := rfl

theorem known_apply (T:ℕ) (K:Matrix (A×N) (A×M) ℂ)
    (v:InputCutoff (α:=A) T×M→ℂ) (o:InputCutoff (α:=A) T) (m:N) :
    (ICO.MHFockKnownOperation.known T K*ᵥv) (o,m)=
      ∑a:A,∑n:M,K (o.2.1,m) (a,n)*v (withQuery (records o) a,n) := by
  rw [ICO.MHFockKnownOperation.known,Matrix.submatrix_mulVec_equiv]
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,queryMemoryFirst,withQuery,
    queryRecordEquiv,records]

def middleQuery (H:Matrix.unitaryGroup A ℂ) :
    Matrix (A×(Bool×((A×Bool)×M))) (A×(Bool×M)) ℂ :=
  (middle (M:=M) H).submatrix (regroup ((A×Bool)×M)).symm (regroup M).symm

theorem middleQuery_isometry (H:Matrix.unitaryGroup A ℂ) :
    (middleQuery (M:=M) H)ᴴ*middleQuery (M:=M) H=1 := by
  simp only [middleQuery,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
    middle_isometry,Matrix.submatrix_one_equiv]

def coefficient {T:ℕ} (H:Matrix.unitaryGroup A ℂ)
    (v:InputCutoff (α:=A) T×(Bool×M)→ℂ) (p:Bool×A) : Records (α:=A) T×(Bool×M)→ℂ :=
  fun i=>if i.2.1=p.1 then ∑x,star (queryVector H p x)*v (withQuery i.1 x,i.2) else 0

def branchEquiv (T:ℕ) :
    (InputCutoff (α:=A) T×(Bool×((A×Bool)×M))) ≃
      ((Bool×A)×(InputCutoff (α:=A) T×(Bool×M))) where
  toFun i := ((i.2.2.1.2,i.2.2.1.1),(i.1,(i.2.1,i.2.2.2)))
  invFun i := (i.2.1,(i.2.2.1,((i.1.2,i.1.1),i.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem preparation_apply (T:ℕ) (ψ:A→ℂ) (v:Records (α:=A) T×M→ℂ)
    (o:InputCutoff (α:=A) T) (m:M) :
    (Matrix.kronecker (fockQuery T ψ) (1:CMatrix M)*ᵥv) (o,m)=
      ψ o.2.1*v (records o,m) := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,fockQuery]

theorem actual_middle_branches (T:ℕ) (H:Matrix.unitaryGroup A ℂ)
    (v:InputCutoff (α:=A) T×(Bool×M)→ℂ) :
    (ICO.MHFockKnownOperation.known T (middleQuery H)*ᵥv)=
      (fun z:(Bool×A)×(InputCutoff (α:=A) T×(Bool×M)) =>
        (Matrix.kronecker (fockQuery T (queryVector H z.1)) (1:CMatrix (Bool×M))*ᵥ
          coefficient H v z.1) z.2) ∘ branchEquiv T := by
  funext o
  rcases o with ⟨i,b,⟨j,c⟩,m⟩
  rw [known_apply]
  simp only [Function.comp_apply,branchEquiv,Equiv.coe_fn_mk,preparation_apply,
    middleQuery,Matrix.submatrix_apply,regroup,Equiv.symm_mk,Equiv.coe_fn_mk]
  simp only [Fintype.sum_prod_type,coefficient]
  change (∑x:A,∑e:Bool,∑n:M,
    middle H ((i.2.1,b),((j,c),m)) ((x,e),n)*v (withQuery (records i) x,(e,n)))=
    queryVector H (c,j) i.2.1*(if b=c then
      ∑x,star (queryVector H (c,j) x)*v (withQuery (records i) x,(b,m)) else 0)
  simp_rw [ICO.C6ChoiceMeasurement.middle_entry]
  by_cases h:b=c
  · subst b
    simp [ite_and,Finset.mul_sum,mul_assoc]
  · simp [h]

#print axioms actual_middle_branches
end
end ICO.C6FockChoiceMeasurement

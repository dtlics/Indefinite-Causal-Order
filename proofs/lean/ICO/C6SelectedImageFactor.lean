import ICO.C6PrivateImageAppend
import ICO.C6ModeFockEncoding

/-! The actual selected raw creator factors through the next explicit
private-image word. This identity precedes any trace or norm estimate. -/
namespace ICO.C6SelectedImageFactor
open Matrix QIT ICO.C6PrivateImageAppend ICO.C6RetainedSectorOperations
  ICO.C6CacheDecode ICO.C6RightImageErasure ICO.C6OrthogonalModeBirth
  ICO.C6AcceptedBirthFactor ICO.C6ActualAcceptedModes ICO.C6AcceptedModes
  ICO.C6FlagCount ICO.RecordingPurifiedProtocol ICO.RecordingCopyIdentity
  ICO.RecordingPureCorrespondence ICO.C6ActualResidualWeight
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M R S E:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]
  [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]

def selectedMemory (l:ℕ) (ψ:A→ℂ) (B:Matrix S (A×R) ℂ) :
    Matrix (Cache (A:=A) (M:=M) l×S) (Cache (A:=A) (M:=M) l×R) ℂ :=
  fun o i=>ψ o.1.1.1*B o.2 (i.1.1.1,i.2)*
    (if o.1.1.2=i.1.1.2 then 1 else 0)*(if o.1.2=i.1.2 then 1 else 0)

theorem selectedMemory_smul (l:ℕ) (ψ:A→ℂ) (c:ℂ) (B:Matrix S (A×R) ℂ) :
    selectedMemory (M:=M) l ψ (c • B)=c • selectedMemory (M:=M) l ψ B := by
  ext o i
  simp only [selectedMemory,Matrix.smul_apply,smul_eq_mul]
  ring

theorem selectedMemory_private (l:ℕ) (ψ:A→ℂ) (B:Matrix S (A×R) ℂ)
    (J:Matrix R E ℂ) :
    selectedMemory (M:=M) l ψ B*Matrix.kronecker
      (1:CMatrix (Cache (A:=A) (M:=M) l)) J=
      selectedMemory (M:=M) l ψ (B*Matrix.kronecker (1:CMatrix A) J) := by
  ext ⟨⟨⟨a,L⟩,m⟩,s⟩ ⟨⟨⟨b,P⟩,u⟩,e⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,selectedMemory,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Prod.mk.injEq]
  simp [ite_and,Finset.sum_ite_irrel,Finset.sum_mul,Finset.mul_sum,
    mul_assoc,mul_left_comm,mul_comm]

theorem selectedMemory_preparation (U:Matrix.unitaryGroup A ℂ) (l r:ℕ) (j:A)
    (J:Matrix S (Fin (r+1)→A) ℂ) :
    selectedMemory (M:=M) l (fun a=>(U:CMatrix A) a j)
      (J*basisEmbedding (imageCons (A:=A) (n:=r)))=
    Matrix.kronecker (1:CMatrix (Cache (A:=A) (M:=M) l)) J*
      appendPrivate r (imagePreparation (M:=M) U l j) := by
  ext ⟨⟨⟨a,L⟩,m⟩,s⟩ ⟨⟨⟨b,P⟩,u⟩,e⟩
  rw [selectedMemory,mul_basisEmbedding]
  simp only [Matrix.submatrix_apply,id_eq]
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Prod.mk.injEq,
    appendPrivate,appendEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.refl_apply,Equiv.prodAssoc_symm_apply,Fin.consEquiv_symm_apply,
    imagePreparation,Matrix.submatrix_apply,id_eq]
  simp only [ite_and,Finset.sum_ite_irrel]
  have hi (v:Fin (r+1)→A) : v 0=b ∧ Fin.tail v=e ↔ v=imageCons (b,e) := by
    constructor
    · rintro ⟨h0,ht⟩
      simpa only [imageCons,h0,ht] using (Fin.cons_self_tail v).symm
    · rintro rfl
      simp [imageCons]
  simp only [mul_ite,ite_mul,mul_one,one_mul,mul_zero,zero_mul]
  simp [←ite_and,hi,Finset.sum_ite_irrel,eq_comm,mul_comm,mul_left_comm,mul_assoc]
  have hc (x:A) (R:TensorPowerProfile (A×A) l) (z:M) (v:Fin (r+1)→A) :
      (e=Fin.tail v ∧ b=v 0 ∧ u=z ∧ P=R ∧ a=x ∧ L=R ∧ m=z) ↔
        (x=a ∧ R=L ∧ z=m ∧ v=imageCons (b,e) ∧ m=u ∧ L=P) := by
    rw [←hi]
    constructor
    · rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩
      subst_vars
      simp_all
    · rintro ⟨h1,h2,h3,⟨h4,h5⟩,h6,h7⟩
      subst_vars
      simp_all
  simp only [hc]
  simp [ite_and,mul_comm]

theorem actual_factorization_memory (H:Matrix.unitaryGroup A ℂ) (n l:ℕ)
    (η:History (A×Bool) n) (κ:History Bool n) (b:Bool) (j:A) :
    selectedMemory (M:=M) l (fun a=>(outcomeBasis H b:CMatrix A) a j)
      (selectedRaw (flagCount n κ) (fun x=>nextResidual H n η b j x))*
        Matrix.kronecker (1:CMatrix (Cache (A:=A) (M:=M) l))
          (directEncoding (modes (rightVectors H n η) κ))=
      birthAmplitude H n η b j •
        (Matrix.kronecker (1:CMatrix (Cache (A:=A) (M:=M) l))
          (directEncoding (fun k:Fin (flagCount n κ+1)=>
            modes (rightVectors H (n+1) ((j,b),η)) (n:=n+1) (true,κ)
              (Fin.cast (flagCount_true n κ).symm k)))*
          appendPrivate (flagCount n κ) (imagePreparation (M:=M) (outcomeBasis H b) l j)) := by
  rw [selectedMemory_private,actual_factorization,selectedMemory_smul,
    selectedMemory_preparation]

#print axioms actual_factorization_memory
end
end ICO.C6SelectedImageFactor

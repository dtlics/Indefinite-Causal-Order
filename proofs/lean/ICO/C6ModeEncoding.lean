import ICO.C6BosonicCCR
import ICO.C6BosonicBounds
import ICO.RecordingCopyIdentity
import ICO.RecordingProcess

/-! Distinct label modes encode a literal tensor product of image registers
inside the actual symmetric occupation space. -/
namespace ICO.C6ModeEncoding
open QIT ICO.C6BosonicCCR ICO.MHCreationCovariance ICO.MHCreationCoefficients
  ICO.MHOccupationCounts ICO.RecordingCopyIdentity ICO.RecordingProcess
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

def profile {n:ℕ} (labels images:Fin n→A) : TensorPowerProfile (A×A) n :=
  ⟨tensorPowerTypeProfile n ((tensorPowerEquiv n).symm (fun i=>(labels i,images i))),
    tensorPowerTypeProfile_mem_profiles _ _⟩

theorem profile_count {n:ℕ} (labels images:Fin n→A) (hl:Function.Injective labels)
    (i:Fin n) (y:A) : (profile labels images).val (labels i,y)=if images i=y then 1 else 0 := by
  change Fintype.card {j:Fin n // tensorPowerEquiv n
    ((tensorPowerEquiv n).symm (fun i=>(labels i,images i))) j=(labels i,y)}=_
  simp only [Equiv.apply_symm_apply,Prod.mk.injEq,hl.eq_iff]
  by_cases hy:images i=y
  · have he : (fun j:Fin n => j=i ∧ images j=y)=(fun j=>j=i) := by
      funext j
      apply propext
      constructor
      · exact And.left
      · intro hj; subst j; exact ⟨rfl,hy⟩
    simp only [he, if_pos hy]
    simp
  · have he : IsEmpty {j:Fin n // j=i ∧ images j=y} := ⟨fun j=>hy (j.property.1 ▸ j.property.2)⟩
    simp only [Fintype.card_eq_zero,if_neg hy]

theorem profile_injective {n:ℕ} (labels:Fin n→A) (hl:Function.Injective labels) :
    Function.Injective (profile labels) := by
  intro x y he
  funext i
  have hc := congrArg (fun p:TensorPowerProfile (A×A) n=>p.val (labels i,x i)) he
  dsimp only at hc
  rw [profile_count labels x hl,profile_count labels y hl,if_pos rfl] at hc
  by_contra hn
  rw [if_neg (Ne.symm hn)] at hc
  norm_num at hc

def encode {n:ℕ} (labels:Fin n→A) : Matrix (TensorPowerProfile (A×A) n) (Fin n→A) ℂ :=
  basisEmbedding (profile labels)

theorem encode_gram {n:ℕ} (labels:Fin n→A) (hl:Function.Injective labels) :
    (encode labels).conjTranspose*encode labels=1 :=
  basisEmbedding_gram _ (profile_injective labels hl)

theorem profile_fresh {n:ℕ} (labels images:Fin n→A) (a y:A)
    (ha:∀i,labels i≠a) : (profile labels images).val (a,y)=0 := by
  change Fintype.card {j:Fin n // tensorPowerEquiv n
    ((tensorPowerEquiv n).symm (fun i=>(labels i,images i))) j=(a,y)}=0
  simp only [Equiv.apply_symm_apply,Prod.mk.injEq]
  have he : IsEmpty {j:Fin n // labels j=a ∧ images j=y} :=
    ⟨fun j=>ha j.val j.property.1⟩
  simp

theorem profile_cons {n:ℕ} (labels images:Fin n→A) (a y:A) :
    profile (Fin.cons a labels) (Fin.cons y images)=incrementProfile (a,y) (profile labels images) := by
  have he : (tensorPowerEquiv (n+1)).symm (fun i=>(Fin.cons a labels i,Fin.cons y images i)) =
      ((a,y),(tensorPowerEquiv n).symm (fun i=>(labels i,images i))) := by
    apply (tensorPowerEquiv (n+1)).injective
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp [tensorPowerEquiv_succ_zero]
    · simp [tensorPowerEquiv_succ_succ]
  apply Subtype.ext
  funext z
  simp only [profile, he, tensorPowerTypeProfile_succ, incrementProfile_apply]

theorem creator_encoded_entry {n:ℕ} (labels images:Fin n→A) (a y:A)
    (ha:∀i,labels i≠a) (p:TensorPowerProfile (A×A) (n+1)) :
    creator n (a,y) p (profile labels images) =
      if p=profile (Fin.cons a labels) (Fin.cons y images) then 1 else 0 := by
  rw [creator,creationOccupation_basis_entry,profile_fresh labels images a y ha,
    profile_cons]
  norm_num

#print axioms encode_gram
end
end ICO.C6ModeEncoding

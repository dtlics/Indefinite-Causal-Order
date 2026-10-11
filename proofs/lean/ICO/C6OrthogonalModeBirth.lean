import ICO.C6ModeEncoding
import ICO.C6BosonicRight
import ICO.MHDecompressionErasure

/-! Successive raw inverse births in distinct orthogonal modes are an actual
tensor-product encoding of their image registers.  No product-state assumption
is imposed on the images or on the arbitrary visible reference. -/
namespace ICO.C6OrthogonalModeBirth
open QIT ICO.C6ModeEncoding ICO.C6BosonicCCR ICO.MHSymmetric
  ICO.MHCreationCovariance ICO.MHOccupationCovariance ICO.RecordingCopyIdentity
  ICO.RecordingPureCorrespondence ICO.C6BosonicRight ICO.MHDecompressionErasure
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

def rotatedEncode (U:Matrix.unitaryGroup A ℂ) {n:ℕ} (labels:Fin n→A) :
    Matrix (TensorPowerProfile (A×A) n) (Fin n→A) ℂ :=
  occupationRotation (leftEdgeUnitary U 1) n * encode labels

theorem rotatedEncode_gram (U:Matrix.unitaryGroup A ℂ) {n:ℕ}
    (labels:Fin n→A) (hl:Function.Injective labels) :
    (rotatedEncode U labels).conjTranspose*rotatedEncode U labels=1 := by
  rw [rotatedEncode,Matrix.conjTranspose_mul,Matrix.mul_assoc,
    ←Matrix.mul_assoc (occupationRotation (leftEdgeUnitary U 1) n).conjTranspose,
    occupationRotation_gram,Matrix.one_mul,encode_gram labels hl]

def appendImage {n:ℕ} (y:A) : Matrix (Fin (n+1)→A) (Fin n→A) ℂ :=
  basisEmbedding (fun images:Fin n→A=>Fin.cons y images)

theorem creator_encode {n:ℕ} (labels:Fin n→A) (a y:A) (ha:∀i,labels i≠a) :
    creator n (a,y)*encode labels=encode (Fin.cons a labels)*appendImage y := by
  rw [encode,mul_basisEmbedding,appendImage,mul_basisEmbedding]
  ext p images
  exact creator_encoded_entry labels images a y ha p

def modeVector (U:Matrix.unitaryGroup A ℂ) (a y:A) : A×A→ℂ :=
  fun z=>(U:CMatrix A) z.1 a * if z.2=y then 1 else 0

theorem modeVector_eq (U:Matrix.unitaryGroup A ℂ) (a y:A) :
    modeVector U a y=(leftEdgeUnitary U 1:CMatrix (A×A))*ᵥbasisVector (a,y) := by
  rw [mulVec_basisVector]
  funext z
  rcases z with ⟨x,z⟩
  simp [modeVector,leftEdgeUnitary_apply,Matrix.one_apply,eq_comm]

theorem creator_rotatedEncode (U:Matrix.unitaryGroup A ℂ) {n:ℕ}
    (labels:Fin n→A) (a y:A) (ha:∀i,labels i≠a) :
    creationOccupation n (modeVector U a y)*rotatedEncode U labels=
      rotatedEncode U (Fin.cons a labels)*appendImage y := by
  rw [modeVector_eq,rotatedEncode,←Matrix.mul_assoc,←creationOccupation_covariance,
    Matrix.mul_assoc,←creator,creator_encode labels a y ha]
  simp only [rotatedEncode,Matrix.mul_assoc]

def imageCons {n:ℕ} : A×(Fin n→A)→(Fin (n+1)→A) := fun i=>Fin.cons i.1 i.2

theorem imageCons_injective {n:ℕ} : Function.Injective (imageCons (A:=A) (n:=n)) := by
  intro i j h
  apply Prod.ext
  · exact congrFun h 0
  · funext k; exact congrFun h k.succ

def encodedBirth (U:Matrix.unitaryGroup A ℂ) {n:ℕ} (labels:Fin n→A) (a:A) :
    Matrix (TensorPowerProfile (A×A) (n+1)) (A×(Fin n→A)) ℂ :=
  rotatedEncode U (Fin.cons a labels)*basisEmbedding imageCons

theorem encodedBirth_gram (U:Matrix.unitaryGroup A ℂ) {n:ℕ}
    (labels:Fin n→A) (a:A) (hl:Function.Injective labels) (ha:∀i,labels i≠a) :
    (encodedBirth U labels a).conjTranspose*encodedBirth U labels a=1 := by
  have hc : Function.Injective (Fin.cons a labels) := by
    intro i j h
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ l => exact False.elim (ha l h.symm)
    | succ k =>
      cases j using Fin.cases with
      | zero => exact False.elim (ha k h)
      | succ l => exact congrArg Fin.succ (hl h)
  rw [encodedBirth,Matrix.conjTranspose_mul,Matrix.mul_assoc,
    ←Matrix.mul_assoc (rotatedEncode U (Fin.cons a labels)).conjTranspose,
    rotatedEncode_gram U _ hc,Matrix.one_mul,basisEmbedding_gram _ imageCons_injective]

variable [Nonempty A]

/-- Contract the output query of the literal normalized raw right creator
with the conjugate of the selected mode. The incoming query is the new image. -/
def selectedRaw (n:ℕ) (v:A→ℂ) :
    Matrix (TensorPowerProfile (A×A) (n+1)) (A×TensorPowerProfile (A×A) n) ℂ :=
  fun o i=>∑a,v a*rightInsertion (A:=A) n (a,o) i

theorem creationOccupation_expansion (n:ℕ) (v:A×A→ℂ) :
    creationOccupation n v=∑z,v z • creator n z := by
  rw [creationOccupation,creationWord_expansion,Matrix.mul_sum,Matrix.sum_mul]
  simp only [Matrix.mul_smul,Matrix.smul_mul,creator,creationOccupation]

theorem selectedRaw_entry (U:Matrix.unitaryGroup A ℂ) (a:A) (n:ℕ)
    (o:TensorPowerProfile (A×A) (n+1)) (i:A×TensorPowerProfile (A×A) n) :
    selectedRaw n (fun x=>(U:CMatrix A) x a) o i=
      (Real.sqrt (Fintype.card A):ℂ)⁻¹ * creationOccupation n (modeVector U a i.1) o i.2 := by
  rw [creationOccupation_expansion]
  simp only [selectedRaw,rightInsertion,Matrix.smul_apply,smul_eq_mul,occupationRightCreator,
    Matrix.sum_apply,Fintype.sum_prod_type,modeVector,creator]
  simp only [ite_mul,mul_ite,one_mul,zero_mul,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,
    if_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem raw_birth_factorization (U:Matrix.unitaryGroup A ℂ) {n:ℕ}
    (labels:Fin n→A) (a:A) (ha:∀i,labels i≠a) :
    selectedRaw n (fun x=>(U:CMatrix A) x a)*
      Matrix.kronecker (1:CMatrix A) (rotatedEncode U labels)=
      (Real.sqrt (Fintype.card A):ℂ)⁻¹ • encodedBirth U labels a := by
  ext o i
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_prod_type,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  simp only [ite_mul,one_mul,zero_mul,mul_ite,mul_zero,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp_rw [selectedRaw_entry,mul_assoc]
  rw [←Finset.mul_sum]
  change _* (creationOccupation n (modeVector U a i.1)*rotatedEncode U labels) o i.2=_
  rw [creator_rotatedEncode U labels a i.1 ha,appendImage,mul_basisEmbedding]
  simp only [encodedBirth,mul_basisEmbedding,Matrix.smul_apply,smul_eq_mul,
    Matrix.submatrix_apply,id_eq,imageCons]

variable {H:Type*} [Fintype H] [DecidableEq H]

/-- Erasure remains exact for arbitrary entanglement between the new image,
all earlier images, and any visible reference H. -/
theorem encodedBirth_erasure (U:Matrix.unitaryGroup A ℂ) {n:ℕ}
    (labels:Fin n→A) (a:A) (hl:Function.Injective labels) (ha:∀i,labels i≠a)
    (v:H×(A×(Fin n→A))→ℂ) :
    partialTraceB (rankOneMatrix (Matrix.kronecker (1:CMatrix H) (encodedBirth U labels a)*ᵥv))=
      partialTraceB (rankOneMatrix v) := by
  apply private_erasure
  rw [encodedBirth_gram U labels a hl ha]
  simp [Matrix.kronecker]

#print axioms raw_birth_factorization
#print axioms encodedBirth_erasure
end
end ICO.C6OrthogonalModeBirth

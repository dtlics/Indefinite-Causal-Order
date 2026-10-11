import ICO.C6OrthogonalModeBirth
import ICO.C6OrthogonalFrame

/-! Literal repeated bosonic births from vacuum equal the image-register
isometry. This proves the full product-of-creators assertion, not only a
one-step norm statement. -/
namespace ICO.C6ModeBirthProduct
open QIT ICO.C6ModeEncoding ICO.C6OrthogonalModeBirth ICO.C6OrthogonalFrame
  ICO.MHSymmetric ICO.MHCreationCovariance ICO.RecordingCopyIdentity
  ICO.RecordingPureCorrespondence
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

def birthProduct (U:Matrix.unitaryGroup A ℂ) :
    (n:ℕ)→(Fin n→A)→(Fin n→A)→TensorPowerProfile (A×A) n→ℂ
  | 0, labels, images => fun p=>encode labels p images
  | n+1, labels, images => creationOccupation n (modeVector U (labels 0) (images 0))*ᵥ
      birthProduct U n (Fin.tail labels) (Fin.tail images)

theorem birthProduct_eq (U:Matrix.unitaryGroup A ℂ) (n:ℕ)
    (labels images:Fin n→A) (hl:Function.Injective labels) :
    birthProduct U n labels images=fun p=>rotatedEncode U labels p images := by
  induction n with
  | zero =>
    have hr : occupationRotation (leftEdgeUnitary U 1) 0=1 := by
      rw [occupationRotation,unitaryTensorPowerMatrix_zero]
      simp only [OneMemClass.coe_one,Matrix.mul_one,occupationEmbedding_gram]
    simp only [birthProduct,rotatedEncode,hr,Matrix.one_mul]
  | succ n ih =>
    have ht : Function.Injective (Fin.tail labels) := fun i j h=>Fin.succ_injective n (hl h)
    have ha : ∀i,Fin.tail labels i≠labels 0 := by
      intro i h
      have hi := hl h
      exact Fin.succ_ne_zero i hi
    rw [birthProduct,ih _ _ ht]
    funext p
    change (creationOccupation n (modeVector U (labels 0) (images 0))*
      rotatedEncode U (Fin.tail labels)) p (Fin.tail images)=_
    rw [creator_rotatedEncode U (Fin.tail labels) (labels 0) (images 0) ha,
      appendImage,mul_basisEmbedding]
    simp only [Matrix.submatrix_apply,id_eq,Fin.cons_self_tail]

def productEncoding (U:Matrix.unitaryGroup A ℂ) (n:ℕ) (labels:Fin n→A) :
    Matrix (TensorPowerProfile (A×A) n) (Fin n→A) ℂ := fun p images=>birthProduct U n labels images p

theorem productEncoding_eq (U:Matrix.unitaryGroup A ℂ) (n:ℕ)
    (labels:Fin n→A) (hl:Function.Injective labels) :
    productEncoding U n labels=rotatedEncode U labels := by
  ext p images
  exact congrFun (birthProduct_eq U n labels images hl) p

theorem productEncoding_gram (U:Matrix.unitaryGroup A ℂ) (n:ℕ)
    (labels:Fin n→A) (hl:Function.Injective labels) :
    (productEncoding U n labels).conjTranspose*productEncoding U n labels=1 := by
  rw [productEncoding_eq U n labels hl,rotatedEncode_gram U labels hl]

/-- Every arbitrary orthonormal family, including the normalized fresh modes
of a fixed accepted history, has this literal product-of-creators realization. -/
theorem orthonormal_realization {n:ℕ} (v:Fin n→EuclideanSpace ℂ A)
    (hv:Orthonormal ℂ v) :
    ∃ (U:Matrix.unitaryGroup A ℂ) (labels:Fin n→A),
      (∀i x,(U:CMatrix A) x (labels i)=v i x) ∧
      (productEncoding U n labels).conjTranspose*productEncoding U n labels=1 := by
  obtain ⟨U,labels,hl,he⟩ := unitary_extension v hv
  exact ⟨U,labels,he,productEncoding_gram U n labels hl⟩

#print axioms productEncoding_gram
#print axioms orthonormal_realization
end
end ICO.C6ModeBirthProduct

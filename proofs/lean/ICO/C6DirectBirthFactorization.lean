import ICO.C6WeightedModeErasure

/-! Literal raw birth factors through the recursively defined image encoding,
including zero residuals; orthogonality is required only for later erasure. -/
namespace ICO.C6DirectBirthFactorization
open Matrix QIT ICO.C6WeightedModeErasure ICO.C6RightImageErasure
  ICO.C6OrthogonalModeBirth ICO.C6BosonicRight ICO.C6BosonicCCR
  ICO.MHCreationCovariance ICO.MHOccupationCovariance ICO.RecordingCopyIdentity
  ICO.RecordingPureCorrespondence
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem selectedRaw_general_entry (v:EuclideanSpace ℂ A) (n:ℕ)
    (o:TensorPowerProfile (A×A) (n+1)) (i:A×TensorPowerProfile (A×A) n) :
    selectedRaw n (fun x=>v x) o i=(Real.sqrt (Fintype.card A):ℂ)⁻¹*
      creationOccupation n (C6RightImageErasure.mode v i.1) o i.2 := by
  rw [ICO.C6OrthogonalModeBirth.creationOccupation_expansion]
  simp only [selectedRaw,rightInsertion,Matrix.smul_apply,smul_eq_mul,occupationRightCreator,
    Matrix.sum_apply,Fintype.sum_prod_type,C6RightImageErasure.mode,creator]
  simp only [ite_mul,mul_ite,one_mul,zero_mul,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,
    if_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem direct_factorization {n:ℕ} (v:EuclideanSpace ℂ A)
    (w:Fin n→EuclideanSpace ℂ A) :
    selectedRaw n (fun x=>v x)*Matrix.kronecker (1:CMatrix A) (directEncoding w)=
      (Real.sqrt (Fintype.card A):ℂ)⁻¹ •
        (directEncoding (Fin.cons v w)*basisEmbedding imageCons) := by
  ext o i
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_prod_type,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  simp only [ite_mul,one_mul,zero_mul,mul_ite,mul_zero,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp_rw [selectedRaw_general_entry,mul_assoc]
  rw [←Finset.mul_sum]
  rw [mul_basisEmbedding]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.submatrix_apply,id_eq,imageCons,
    directEncoding,directProduct,Fin.cons_zero,Fin.tail_cons]
  rfl

theorem normalized_decomposition_all (r:EuclideanSpace ℂ A) :
    (fun x=>r x)=(‖r‖:ℂ) • (fun x=>normalized r x) := by
  by_cases hr:r=0
  · subst r; simp only [norm_zero,Complex.ofReal_zero,zero_smul,WithLp.ofLp_zero]
  · exact residual_decomposition r hr

theorem normalized_factorization {n:ℕ} (r:EuclideanSpace ℂ A)
    (w:Fin n→EuclideanSpace ℂ A) :
    selectedRaw n (fun x=>r x)*Matrix.kronecker (1:CMatrix A) (directEncoding w)=
      ((‖r‖:ℂ)/(Real.sqrt (Fintype.card A):ℂ)) •
        (directEncoding (Fin.cons (normalized r) w)*basisEmbedding imageCons) := by
  rw [normalized_decomposition_all r,selectedRaw_smul,Matrix.smul_mul,direct_factorization,
    smul_smul,div_eq_mul_inv]

#print axioms normalized_factorization
end
end ICO.C6DirectBirthFactorization


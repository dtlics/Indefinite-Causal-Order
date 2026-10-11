import ICO.C6BosonicHistorySupport
import ICO.C6NumberRotationAlgebra
import ICO.MHWordRotation

/-! Zero occupation outside the conjugate history span depends only on that
span, not on the unitary chosen to coordinatize it. -/
namespace ICO.C6RightHistorySupport
open QIT ICO.C6BosonicGeometricSupport ICO.C6BosonicWordSupport
  ICO.C6BosonicHistorySupport ICO.C6BosonicLabelSupport ICO.C6BosonicSupport
  ICO.C6BosonicFreshRotated ICO.C6CacheSpanProjection ICO.C6FockNumber
  ICO.C6BosonicCacheSupport ICO.C6NumberRotationAlgebra ICO.MHWordRotation
  ICO.MHFockRotation ICO.MHFockTransport ICO.MHFockCovariance ICO.MHFockBothCovariance
  ICO.MHBoundedRecording ICO.MHSectorCovariance ICO.MHSymmetric
  ICO.MHCreationCovariance ICO.MHRightCovariance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem conjugate_span (U:Matrix.unitaryGroup A ℂ) (S:Finset A) :
    spanProjection (conjugateUnitary U) S=(spanProjection U S).map star := by
  ext i j
  simp only [spanProjection,conjugateUnitary_value,coordinateProjection]
  simp only [Matrix.map_apply,Matrix.mul_apply,Matrix.diagonal_apply,Finset.sum_ite_eq
    ,mul_ite,mul_zero,mul_one,Matrix.conjTranspose_apply,star_sum,star_mul,star_star]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h:k∈S <;> simp [apply_ite,star_zero,mul_comm,h]

theorem right_edge_conjugate (U:Matrix.unitaryGroup A ℂ) :
    rightEdgeUnitary (1:Matrix.unitaryGroup A ℂ) U⁻¹=leftEdgeUnitary (conjugateUnitary U) 1 := by
  apply Subtype.ext
  rw [edge_rotation,conjugateUnitary_value]
  have hh:=inverse_rightEdgeUnitary U (1:Matrix.unitaryGroup A ℂ)
  rw [inv_one] at hh
  change (rightEdgeUnitary 1 U⁻¹:CMatrix (A×A))=Matrix.kronecker ((U:CMatrix A).map star) (1:CMatrix A).conjTranspose at hh
  simpa only [Matrix.conjTranspose_one] using hh

def rightSupportSector (P:CMatrix A) (n r:ℕ) : CMatrix (Sector (α:=A) n r) :=
  Matrix.kronecker (1:CMatrix (A×TensorPowerProfile (A×A) n)) (occupationSupport (P.map star) r)

def rightFockSupport (P:CMatrix A) (T:ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  inputFamily (rightSupportSector P) T

def rightCoordinateSector (S:Finset A) (n r:ℕ) : CMatrix (Sector (α:=A) n r) :=
  Matrix.kronecker (1:CMatrix (A×TensorPowerProfile (A×A) n)) (profileSupport S r)

theorem zero_number_family (S:Finset A) (T:ℕ) :
    rightNumber Sᶜ 0 T=inputFamily (rightCoordinateSector S) T := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  by_cases hs:s=s'
  · subst s'
    rw [inputFamily_same]
    simp only [rightNumber,rightDiagonal,Matrix.diagonal_apply,rightCoordinateSector,profileSupport,
      Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,labelsIn_iff]
    by_cases hx:x=y <;> by_cases hp:p=p' <;> by_cases hq:q=q' <;>
      simp_all [Sigma.mk.inj_iff,Prod.mk.injEq]
    all_goals split_ifs <;> simp_all
  · rw [inputFamily_other _ _ _ _ hs]
    have hn:(⟨⟨s,q⟩,(x,p)⟩:InputCutoff (α:=A) T)≠⟨⟨s',q'⟩,(y,p')⟩ := by
      intro he
      exact hs (congrArg (fun i:InputCutoff (α:=A) T=>i.1.1) he)
    simp [rightNumber,rightDiagonal,Matrix.diagonal_apply,hn]

theorem right_sector_conjugate (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (n r:ℕ) :
    (outputTurn U 1 n r:CMatrix (Sector (α:=A) n r))*rightCoordinateSector S n r*
      (outputTurn U 1 n r:CMatrix (Sector (α:=A) n r)).conjTranspose=
      rightSupportSector (spanProjection U S) n r := by
  have hl:occupationRotation (leftEdgeUnitary U 1) n*
      (occupationRotation (leftEdgeUnitary U 1) n).conjTranspose=1 :=
    (symmetricRotation _ n).property.2
  simp only [outputTurn,ICO.MHSectorCovariance.tensorUnitary,symmetricRotation,rightCoordinateSector,rightSupportSector,
    Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,inv_one,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul,Matrix.mul_one]
  rw [←Matrix.mul_kronecker_mul,hl]
  have h1:((1:Matrix.unitaryGroup A ℂ):CMatrix A)*
      (((1:Matrix.unitaryGroup A ℂ):CMatrix A)).conjTranspose=1:=
    (1:Matrix.unitaryGroup A ℂ).property.2
  rw [h1,Matrix.one_kronecker_one,←conjugate_span U S,occupationSupport_rotated,right_edge_conjugate]

theorem zero_number_geometric (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (T:ℕ) :
    rotatedNumber U Sᶜ 0 T=rightFockSupport (spanProjection U S) T := by
  unfold rotatedNumber
  rw [zero_number_family]
  change inputFamily (fun n r=>(outputTurn U 1 n r:CMatrix (Sector (α:=A) n r))) T*
      inputFamily (rightCoordinateSector S) T*
      (inputFamily (fun n r=>(outputTurn U 1 n r:CMatrix (Sector (α:=A) n r))) T).conjTranspose=_
  rw [inputFamily_adjoint,inputFamily_mul,inputFamily_mul]
  simp only [right_sector_conjugate]
  rfl

theorem zero_number_basis_independent (U V:Matrix.unitaryGroup A ℂ) (S B:Finset A)
    (h:spanProjection U S=spanProjection V B) (T:ℕ) :
    rotatedNumber U Sᶜ 0 T=rotatedNumber V Bᶜ 0 T := by
  rw [zero_number_geometric,zero_number_geometric,h]

#print axioms zero_number_basis_independent
end
end ICO.C6RightHistorySupport




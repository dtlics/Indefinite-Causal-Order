import ICO.C6BosonicFresh
import ICO.C6BosonicRightCovariance

/-! The fresh-birth overlap bound for an arbitrary rotated query subspace. -/
namespace ICO.C6BosonicFreshRotated
open QIT ICO.C6BosonicRight ICO.C6BosonicPolar ICO.C6BosonicCompression
  ICO.C6BosonicFresh ICO.C6BosonicRightCovariance ICO.MHSectorCovariance
  ICO.MHSymmetric ICO.MHRightCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def coordinateProjection (S : Finset A) : CMatrix A :=
  Matrix.diagonal (fun x => if x∈S then 1 else 0)

theorem queryProjection_tensor (S : Finset A) (n : ℕ) :
    queryProjection S n=Matrix.kronecker (coordinateProjection S)
      (1 : CMatrix (TensorPowerProfile (A×A) n)) := by
  ext i j
  simp only [queryProjection,coordinateProjection,Matrix.diagonal_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Prod.ext_iff]
  by_cases h : i.1=j.1 <;> by_cases hp : i.2=j.2 <;> simp [h,hp]

def rotatedQueryProjection (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (n : ℕ) :
    CMatrix (Sector (A:=A) n) :=
  Matrix.kronecker ((U : CMatrix A)*coordinateProjection S*(U : CMatrix A).conjTranspose)
    (1 : CMatrix (TensorPowerProfile (A×A) n))

theorem rotatedQueryProjection_intertwine (U : Matrix.unitaryGroup A ℂ)
    (S : Finset A) (n : ℕ) :
    rotatedQueryProjection U S n *
        (rightOutputRotation 1 U⁻¹ n : CMatrix (Sector (A:=A) n)) =
      (rightOutputRotation 1 U⁻¹ n : CMatrix (Sector (A:=A) n))*queryProjection S n := by
  rw [queryProjection_tensor]
  simp only [rotatedQueryProjection,rightOutputRotation,inv_inv,tensorUnitary,
    symmetricRotation,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
    Matrix.one_mul,Matrix.mul_one]
  congr 1
  have hU : (U : CMatrix A).conjTranspose*(U : CMatrix A)=1 := U.property.1
  rw [Matrix.mul_assoc,Matrix.mul_assoc,hU,Matrix.mul_one]

section General
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem compression_covariant_norm (E : Matrix b a ℂ)
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ)
    (P Q : CMatrix b) (hE : (V : CMatrix b)*E=E*(U : CMatrix a))
    (hP : Q*(V : CMatrix b)=(V : CMatrix b)*P) : ‖Q*E‖≤‖P*E‖ := by
  have hu : (U : CMatrix a)*(U : CMatrix a).conjTranspose=1 := U.property.2
  have he : Q*E=((V : CMatrix b)*(P*E))*(U : CMatrix a).conjTranspose := by
    calc
      _ = (Q*(E*(U : CMatrix a)))*(U : CMatrix a).conjTranspose := by
        rw [Matrix.mul_assoc,Matrix.mul_assoc,hu,Matrix.mul_one]
      _ = (Q*((V : CMatrix b)*E))*(U : CMatrix a).conjTranspose := by rw [hE]
      _ = _ := by rw [←Matrix.mul_assoc Q,hP]; simp only [Matrix.mul_assoc]
  have hnU : ‖(U : CMatrix a).conjTranspose‖≤1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact unitary_norm_le U
  rw [he]
  calc
    _ ≤ (‖(V : CMatrix b)‖*‖P*E‖)*‖(U : CMatrix a).conjTranspose‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖P*E‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (unitary_norm_le V) (norm_nonneg _)) hnU
      (norm_nonneg _) (by positivity)
    _ = ‖P*E‖ := by ring

end General

theorem rotated_rightPolar_square (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {n : ℕ} (hn : n<Fintype.card A) :
    ‖rotatedQueryProjection U S (n+1)*rightPolar (A:=A) n‖^2 ≤
      ((S.card:ℝ)+n)/((Fintype.card A:ℝ)-n) := by
  have h := compression_covariant_norm (rightPolar (A:=A) n)
    (rightInputRotation 1 U⁻¹ n) (rightOutputRotation 1 U⁻¹ (n+1))
    (queryProjection S (n+1)) (rotatedQueryProjection U S (n+1))
    (rightPolar_covariance 1 U⁻¹ hn) (rotatedQueryProjection_intertwine U S (n+1))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (query_compressed_rightPolar_square S hn)

#print axioms rotated_rightPolar_square
end
end ICO.C6BosonicFreshRotated

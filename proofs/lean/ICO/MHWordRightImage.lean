import ICO.MHRightCovariance
import ICO.MHWordSymmetry
import ICO.MHWordDistinct

/-! The right bosonic creator has the actual Bell image in ordered words. -/
namespace ICO.MHWordRightImage
open Matrix QIT ICO.MHSymmetric ICO.MHRightCovariance ICO.MHWordSymmetry ICO.MHCreationCovariance
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev Out (n : ℕ) := A × TensorPower (A × A) (n+1)
abbrev In (n : ℕ) := A × TensorPower (A × A) n

def rawPrepend (n : ℕ) : Matrix (Out (A := A) n) (In (A := A) n) ℂ :=
  fun o i => (if o.1 = o.2.1.1 then 1 else 0) *
    (if o.2.1.2 = i.1 then 1 else 0) * (if o.2.2 = i.2 then 1 else 0)

def querySymmetry (n : ℕ) : CMatrix (A × TensorPower (A × A) n) :=
  Matrix.kronecker 1 (symmetricProjectionMatrix n)

def queryTail (n : ℕ) : CMatrix (Out (A := A) n) :=
  Matrix.kronecker 1 (tailMatrix n)

theorem rawPrepend_old_symmetry (n : ℕ) :
    rawPrepend (A := A) n * querySymmetry n = queryTail n * rawPrepend n := by
  ext o i
  change (∑ v : A × TensorPower (A × A) n,
    rawPrepend n o v * querySymmetry n v i) =
    ∑ v : A × ((A × A) × TensorPower (A × A) n),
      queryTail n o v * rawPrepend n v i
  simp only [rawPrepend, querySymmetry, queryTail, tailMatrix, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [Prod.ext_iff,ite_and]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  by_cases hq : o.1=o.2.1.1 <;> by_cases hx : o.2.1.2=i.1 <;> simp [hq,hx]

theorem query_symmetry_tail (n : ℕ) :
    querySymmetry (A := A) (n+1) * queryTail n = querySymmetry (A := A) (n+1) := by
  simp only [querySymmetry,queryTail,Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul,
    Matrix.one_mul,symmetric_tail_absorption]

theorem rightCreator_factor (n : ℕ) :
    rightCreator (α := A) n = (Real.sqrt (n+1) : ℂ) •
      (querySymmetry (n+1)*rawPrepend (A := A) n*querySymmetry n) := by
  ext o i
  simp only [rightCreator, creationWord, Matrix.smul_apply]
  congr 1
  change (∑ x : TensorPower (A × A) n, (∑ y : (A × A) × TensorPower (A × A) n,
    symmetricProjectionMatrix (n+1) o.2 y * prepend n (basisVector (o.1,i.1)) y x) *
      symmetricProjectionMatrix n x i.2) =
    ∑ x : A × TensorPower (A × A) n,
      (∑ y : A × ((A × A) × TensorPower (A × A) n),
        querySymmetry (n+1) o y * rawPrepend n y x) * querySymmetry n x i
  simp only [querySymmetry,rawPrepend,prepend,basisVector,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Fintype.sum_prod_type,
    ite_mul,mul_ite,one_mul,mul_one,zero_mul,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [Finset.sum_mul,Prod.mk.injEq,ite_and,ite_mul]
  simp only [zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem rightCreator_factor_absorbed (n : ℕ) :
    rightCreator (α := A) n = (Real.sqrt (n+1) : ℂ) •
      (querySymmetry (n+1)*rawPrepend (A := A) n) := by
  rw [rightCreator_factor,Matrix.mul_assoc,rawPrepend_old_symmetry,
    ← Matrix.mul_assoc,query_symmetry_tail]

def firstBell (n : ℕ) : CMatrix (Out (A := A) n) :=
  fun o i => if o.1=o.2.1.1 ∧ i.1=i.2.1.1 ∧ o.2.1.2=i.2.1.2 ∧ o.2.2=i.2.2
    then (Fintype.card A : ℂ)⁻¹ else 0

theorem rawPrepend_image (n : ℕ) :
    rawPrepend (A := A) n*(rawPrepend n).conjTranspose =
      (Fintype.card A : ℂ) • firstBell (A := A) n := by
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext o i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    rawPrepend,firstBell,Matrix.smul_apply,smul_eq_mul]
  by_cases ho : o.1=o.2.1.1
  · by_cases hi : i.1=i.2.1.1
    · by_cases hy : o.2.1.2=i.2.1.2
      · by_cases hw : o.2.2=i.2.2
        · simp [ho,hi,hy,hw,hd]
        · simp [ho,hi,hy,hw,Ne.symm hw]
      · simp [ho,hi,hy,Ne.symm hy]
    · simp [ho,hi]
  · simp [ho]

theorem querySymmetry_adjoint (n : ℕ) :
    (querySymmetry (A := A) n).conjTranspose=querySymmetry (A := A) n := by
  simp [querySymmetry,Matrix.conjTranspose_kronecker,symmetricProjectionMatrix_conjTranspose]

theorem rightCreator_image (n : ℕ) :
    rightCreator (α := A) n*(rightCreator n).conjTranspose =
      (((n+1 : ℕ) : ℂ)*(Fintype.card A : ℂ)) •
        (querySymmetry (n+1)*firstBell (A := A) n*querySymmetry (n+1)) := by
  rw [rightCreator_factor_absorbed]
  simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,querySymmetry_adjoint,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hs : star (Real.sqrt (n+1) : ℂ)*(Real.sqrt (n+1) : ℂ) = ((n+1 : ℕ) : ℂ) := by
    have hstar : star (Real.sqrt (n+1) : ℂ)=(Real.sqrt (n+1) : ℂ) := by simp
    rw [hstar]
    rw [← Complex.ofReal_mul]
    congr 1
    simpa only [pow_two,Nat.cast_add,Nat.cast_one] using Real.sq_sqrt (by positivity : (0:ℝ)≤n+1)
  rw [hs]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (rawPrepend (A := A) n),rawPrepend_image]
  simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul]

#print axioms rightCreator_image
end
end ICO.MHWordRightImage

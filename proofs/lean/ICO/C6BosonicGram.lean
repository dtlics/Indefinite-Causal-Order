import ICO.C6BosonicCCR
import ICO.C6BosonicDecode
import ICO.MHOccupationCovariance
import ICO.MHCreationCovariance
import ICO.MHERecordingApprox
import ICO.RecordingCopyIdentity
import ICO.RecordingProcess
import QIT.Symmetry.SymmetricSubspace

/-! The actual query-coupled bosonic Gram. Its deviation from the scalar
identity is a one-particle query/label exchange compression. -/
namespace ICO.C6BosonicGram
open QIT ICO.C6BosonicCCR ICO.C6BosonicDecode ICO.MHOccupationCovariance
  ICO.MHCreationCovariance ICO.MHERecordingApprox ICO.RecordingCopyIdentity
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
variable {A : Type*} [Fintype A] [DecidableEq A]

def normalGram (n : ℕ) : CMatrix (A × TensorPowerProfile (A×A) (n+1)) :=
  fun i j => ∑ y : A,
    (creator n (j.1,y) * (creator n (i.1,y)).conjTranspose) i.2 j.2

theorem occupationLeftCreator_gram (n : ℕ) :
    (occupationLeftCreator (α := A) (n+1)).conjTranspose * occupationLeftCreator (α := A) (n+1) =
      (Fintype.card A : ℂ) • (1 : CMatrix (A × TensorPowerProfile (A×A) (n+1))) +
        normalGram n := by
  ext i j
  have he : ((occupationLeftCreator (α := A) (n+1)).conjTranspose *
      occupationLeftCreator (α := A) (n+1)) i j =
      ∑ y : A, ((creator (n+1) (i.1,y)).conjTranspose * creator (n+1) (j.1,y)) i.2 j.2 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, occupationLeftCreator,
      creator, Fintype.sum_prod_type]
  rw [he]
  simp only [canonical_commutator, Matrix.add_apply, Finset.sum_add_distrib, normalGram]
  congr 1
  by_cases h : i.1=j.1
  · simp [h, Matrix.smul_apply, Matrix.one_apply, Prod.ext_iff]
  · simp [h, Matrix.smul_apply, Matrix.one_apply, Prod.ext_iff]

abbrev Decoded (n : ℕ) := A × ((A×A) × TensorPowerProfile (A×A) n)

def queryStack (n : ℕ) :
    Matrix (Decoded (A := A) n) (A × TensorPowerProfile (A×A) (n+1)) ℂ :=
  Matrix.kronecker 1 (annihilationStack n)

def swapLabel (n : ℕ) (x : Decoded (A := A) n) : Decoded (A := A) n :=
  (x.2.1.1, ((x.1,x.2.1.2),x.2.2))

theorem swapLabel_involutive (n : ℕ) : Function.Involutive (swapLabel (A := A) n) := by
  intro x
  rcases x with ⟨x,⟨⟨y,z⟩,p⟩⟩
  rfl

def swapLabelMatrix (n : ℕ) : CMatrix (Decoded (A := A) n) :=
  basisEmbedding (swapLabel n)

theorem swapLabelMatrix_gram (n : ℕ) :
    (swapLabelMatrix (A := A) n).conjTranspose * swapLabelMatrix n = 1 :=
  basisEmbedding_gram _ (swapLabel_involutive n).injective

theorem queryStack_gram (n : ℕ) :
    (queryStack (A := A) n).conjTranspose * queryStack n =
      ((n+1 : ℕ) : ℂ) • (1 : CMatrix (A × TensorPowerProfile (A×A) (n+1))) := by
  simp only [queryStack, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, annihilationStack_gram]
  ext i j
  simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Prod.ext_iff]
  by_cases h : i.1=j.1 <;> by_cases h' : i.2=j.2 <;> simp [h,h']

theorem swapLabel_queryStack_entry (n : ℕ) (o : Decoded (A := A) n)
    (i : A × TensorPowerProfile (A×A) (n+1)) :
    (swapLabelMatrix (A := A) n * queryStack (A := A) n) o i =
      if o.2.1.1 = i.1 then star (creator n (o.1,o.2.1.2) i.2 o.2.2) else 0 := by
  rw [Matrix.mul_apply]
  have he (z : Decoded (A := A) n) :
      swapLabelMatrix n o z = if z = swapLabel n o then 1 else 0 := by
    change (if o = swapLabel n z then 1 else 0) = _
    congr 1
    apply propext
    constructor
    · intro h
      rw [h,swapLabel_involutive n]
    · intro h
      rw [h,swapLabel_involutive n]
  simp only [he, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, queryStack, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, swapLabel, annihilationStack]

theorem normalGram_compression (n : ℕ) :
    normalGram (A := A) n =
      (queryStack n).conjTranspose * swapLabelMatrix n * queryStack n := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, swapLabel_queryStack_entry]
  simp only [queryStack, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, annihilationStack,
    Fintype.sum_prod_type]
  simp only [star_mul, apply_ite star, star_one, star_zero, star_star,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [normalGram, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem normalGram_norm_le (n : ℕ) : ‖normalGram (A := A) n‖ ≤ n+1 := by
  have hswap : ‖swapLabelMatrix (A := A) n‖ ≤ 1 :=
    ICO.RecordingProcess.isometry_matrix_norm_le _ (swapLabelMatrix_gram n)
  have hstack : ‖queryStack (A := A) n‖ * ‖queryStack (A := A) n‖ ≤ n+1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, queryStack_gram, norm_smul]
    have hI := IsStarProjection.norm_le
      (1 : CMatrix (A × TensorPowerProfile (A×A) (n+1))) (IsStarProjection.one _)
    have hc : ‖((n+1 : ℕ) : ℂ)‖ = (n+1 : ℝ) := by
      exact (Complex.norm_natCast (n+1)).trans (by norm_num)
    rw [hc]
    exact (mul_le_mul_of_nonneg_left hI (by positivity)).trans_eq (mul_one _)
  rw [normalGram_compression]
  calc
    _ ≤ (‖(queryStack (A := A) n).conjTranspose‖ * ‖swapLabelMatrix (A := A) n‖) *
          ‖queryStack (A := A) n‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖queryStack (A := A) n‖ * ‖queryStack (A := A) n‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hswap (norm_nonneg _)) (norm_nonneg _)).trans_eq
          (by ring)
    _ ≤ n+1 := hstack

#print axioms occupationLeftCreator_gram
#print axioms normalGram_compression
end
end ICO.C6BosonicGram

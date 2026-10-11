import ICO.C6BosonicPolar
import ICO.MHFockOracle

/-! Actual polar creators on one common finite multiset Fock space. -/
namespace ICO.C6PolarFock
open QIT ICO.C6BosonicPolar ICO.MHBoundedRecording ICO.MHFockSpace
  ICO.MHFockAlgebra ICO.MHFockProjection ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHERecordingApprox ICO.MHBlockNorm ICO.RecordingCopyIdentity
  ICO.RecordingOracleAlgebra
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def boundedPolar (t : ℕ) : Matrix (OutputCutoff (α:=α) t) (InputCutoff (α:=α) t) ℂ :=
  Matrix.blockDiagonal' (fun k : Block (α:=α) t => leftPolar (A:=α) k.1.val.1.val)

def polarLeftOnFock {t T : ℕ} (h : t+1≤T) : CMatrix (InputCutoff (α:=α) T) :=
  basisEmbedding (outputEmbed h)*boundedPolar t*
    (basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))).conjTranspose

def polarRightOnFock {t T : ℕ} (h : t+1≤T) : CMatrix (InputCutoff (α:=α) T) :=
  swapMatrix T*polarLeftOnFock h*(swapMatrix T).conjTranspose

theorem boundedPolar_gram (t : ℕ) (ht : t<Fintype.card α) :
    (boundedPolar (α:=α) t).conjTranspose*boundedPolar (α:=α) t=1 := by
  unfold boundedPolar
  rw [Matrix.blockDiagonal'_conjTranspose, ←Matrix.blockDiagonal'_mul]
  have hb (k:Block (α:=α) t) :
      (leftPolar (A:=α) k.1.val.1.val).conjTranspose*leftPolar (A:=α) k.1.val.1.val=1 :=
    leftPolar_isometry (A:=α) (n:=k.1.val.1.val) (by have hh:=k.1.property; omega)
  simp only [hb]
  exact Matrix.blockDiagonal'_one
theorem polarLeftOnFock_gram {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    (polarLeftOnFock (α := α) h).conjTranspose * polarLeftOnFock h =
      sourceProjection (Nat.le_trans (Nat.le_succ t) h) := by
  unfold polarLeftOnFock sourceProjection
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (basisEmbedding (outputEmbed (α := α) h)).conjTranspose
      (basisEmbedding (outputEmbed (α := α) h)), outputEmbed_gram, Matrix.one_mul,
    ← Matrix.mul_assoc (boundedPolar (α := α) t).conjTranspose (boundedPolar (α := α) t),
    boundedPolar_gram t ht, Matrix.one_mul]

theorem polarLeftOnFock_domain {t T : ℕ} (h : t + 1 ≤ T) :
    polarLeftOnFock (α := α) h * sourceProjection (Nat.le_trans (Nat.le_succ t) h) = polarLeftOnFock h := by
  unfold polarLeftOnFock sourceProjection
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
      (basisEmbedding (inputEmbed (α := α) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose
      (basisEmbedding (inputEmbed (α := α) (Nat.le_trans (Nat.le_succ t) h))),
    inputEmbed_gram, Matrix.one_mul]

theorem polarLeftOnFock_norm_le {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    ‖polarLeftOnFock (α := α) h‖ ≤ 1 := by
  have hn := IsStarProjection.norm_le _
    (sourceProjection_projection (α := α) (Nat.le_trans (Nat.le_succ t) h))
  rw [← polarLeftOnFock_gram h ht, Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg (polarLeftOnFock (α := α) h)]
theorem polarLeftOnFock_grade {t T : ℕ} (h : t + 1 ≤ T)
    (o i : InputCutoff (α := α) T) (hA : polarLeftOnFock h o i ≠ 0) : grade o = grade i + 1 := by
  obtain ⟨j, hj, hji⟩ := mul_entry_nonzero _ _ o i hA
  obtain ⟨k, hok, hkj⟩ := mul_entry_nonzero _ _ o j hj
  have ho := basisEmbedding_support (outputEmbed h) o k hok
  have hi : i = inputEmbed (Nat.le_trans (Nat.le_succ t) h) j := by
    apply basisEmbedding_support
    intro hz
    apply hji
    simp only [Matrix.conjTranspose_apply, hz, star_zero]
  have hblock : k.1 = j.1 := by
    by_contra hn
    exact hkj (by simp [boundedPolar, Matrix.blockDiagonal'_apply, hn])
  have hg := congrArg (fun b : Block (α := α) t => b.1.val.1.val + b.1.val.2.val) hblock
  dsimp only at hg
  rw [ho, hi]
  change k.1.1.val.1.val + 1 + k.1.1.val.2.val = j.1.1.val.1.val + j.1.1.val.2.val + 1
  omega
theorem source_commute_polarLeft_image {t T : ℕ} (h : t + 1 ≤ T) :
    Commute (sourceProjection (α := α) (Nat.le_trans (Nat.le_succ t) h))
      (polarLeftOnFock h * (polarLeftOnFock h).conjTranspose) := by
  rw [sourceProjection_diagonal]
  apply cutoff_commute_of_grade
  exact grade_image_preserved grade (polarLeftOnFock h) (polarLeftOnFock_grade h)
theorem polarRightOnFock_gram {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    (polarRightOnFock (α := α) h).conjTranspose * polarRightOnFock h =
      sourceProjection (Nat.le_trans (Nat.le_succ t) h) := by
  unfold polarRightOnFock
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    swapMatrix_selfAdjoint, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (swapMatrix (α := α) T) (swapMatrix (α := α) T), swapMatrix_sq,
    Matrix.one_mul, ← Matrix.mul_assoc (polarLeftOnFock (α := α) h).conjTranspose (polarLeftOnFock (α := α) h),
    polarLeftOnFock_gram h ht, ← Matrix.mul_assoc,
    ← (source_commute_swap (α := α) (Nat.le_trans (Nat.le_succ t) h)).eq,
    Matrix.mul_assoc, swapMatrix_sq, Matrix.mul_one]

theorem polarRightOnFock_domain {t T : ℕ} (h : t + 1 ≤ T) :
    polarRightOnFock (α := α) h * sourceProjection (Nat.le_trans (Nat.le_succ t) h) = polarRightOnFock h := by
  unfold polarRightOnFock
  rw [swapMatrix_selfAdjoint]
  simp only [Matrix.mul_assoc]
  rw [← (source_commute_swap (α := α) (Nat.le_trans (Nat.le_succ t) h)).eq,
    ← Matrix.mul_assoc (polarLeftOnFock (α := α) h), polarLeftOnFock_domain]

theorem polarRightOnFock_grade {t T : ℕ} (h : t + 1 ≤ T)
    (o i : InputCutoff (α := α) T) (hA : polarRightOnFock h o i ≠ 0) : grade o = grade i + 1 := by
  obtain ⟨j, hj, hji⟩ := mul_entry_nonzero _ _ o i hA
  obtain ⟨k, hok, hkj⟩ := mul_entry_nonzero _ _ o j hj
  have ho := swapMatrix_grade T o k hok
  have hi := swapMatrix_grade T j i (by simpa only [swapMatrix_selfAdjoint] using hji)
  have ha := polarLeftOnFock_grade h k j hkj
  omega

theorem source_commute_polarRight_image {t T : ℕ} (h : t + 1 ≤ T) :
    Commute (sourceProjection (α := α) (Nat.le_trans (Nat.le_succ t) h))
      (polarRightOnFock h * (polarRightOnFock h).conjTranspose) := by
  rw [sourceProjection_diagonal]
  apply cutoff_commute_of_grade
  exact grade_image_preserved grade (polarRightOnFock h) (polarRightOnFock_grade h)

theorem polarRightOnFock_norm_le {t T : ℕ} (h:t+1≤T) (ht:t<Fintype.card α) :
    ‖polarRightOnFock (α:=α) h‖≤1 := by
  have hn := IsStarProjection.norm_le _
    (sourceProjection_projection (α:=α) (Nat.le_trans (Nat.le_succ t) h))
  rw [←polarRightOnFock_gram h ht,Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg (polarRightOnFock (α:=α) h)]

def polarOracle {t T : ℕ} (h:t+1≤T) : CMatrix (InputCutoff (α:=α) T) :=
  polarLeftOnFock h*(1-polarRightOnFock h*(polarRightOnFock h).conjTranspose)+
    (1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)*(polarRightOnFock h).conjTranspose

theorem polarOracle_initial_projection {t T : ℕ} (h:t+1≤T) (ht:t<Fintype.card α) :
    IsStarProjection ((polarOracle (α:=α) h).conjTranspose*polarOracle h) :=
  oracle_initial_projection (polarLeftOnFock h) (polarRightOnFock h)
    (sourceProjection (Nat.le_trans (Nat.le_succ t) h))
    (sourceProjection_projection _) (polarLeftOnFock_gram h ht) (polarRightOnFock_gram h ht)
    (polarLeftOnFock_domain h) (polarRightOnFock_domain h)
    (source_commute_polarLeft_image h) (source_commute_polarRight_image h)

theorem polarOracle_norm_le {t T : ℕ} (h:t+1≤T) (ht:t<Fintype.card α) :
    ‖polarOracle (α:=α) h‖≤1 := by
  have hn := IsStarProjection.norm_le _ (polarOracle_initial_projection (α:=α) h ht)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg (polarOracle (α:=α) h)]

#print axioms polarLeftOnFock_gram
#print axioms polarRightOnFock_gram
#print axioms polarOracle_initial_projection
#print axioms polarOracle_norm_le
end
end ICO.C6PolarFock

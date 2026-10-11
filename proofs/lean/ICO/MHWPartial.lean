import ICO.RecordingOracleAlgebra
import QIT.Core.State

/-! The concrete partial recording oracle W on finite bijective records.
The full multiset recording oracle is related to these coordinates separately. -/
namespace ICO.MHWPartial
open Matrix QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
open ICO.RecordingPartialIsometry ICO.RecordingOracleAlgebra
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A]

def BijRecord (L R : Relation A A) : Prop :=
  Disjoint L R ∧ LeftUnique (L ∪ R) ∧ RightUnique (L ∪ R)

def leftPredicate (i : Basis A) : Prop :=
  BijRecord i.2.1 i.2.2 ∧ FreshLeft i.1 (i.2.1 ∪ i.2.2) ∧
    i.2.1.card + i.2.2.card < Fintype.card A

def rightPredicate (i : Basis A) : Prop :=
  BijRecord i.2.1 i.2.2 ∧ FreshRight i.1 (i.2.1 ∪ i.2.2) ∧
    i.2.1.card + i.2.2.card < Fintype.card A

def predicateProjection (p : Basis A → Prop) : CMatrix (Basis A) := by
  classical
  exact Matrix.diagonal (fun i => if p i then 1 else 0)

abbrev leftProjection : CMatrix (Basis A) := predicateProjection leftPredicate
abbrev rightProjection : CMatrix (Basis A) := predicateProjection rightPredicate

theorem predicate_projection (p : Basis A → Prop) : IsStarProjection (predicateProjection p) := by
  classical
  constructor
  · show predicateProjection p * predicateProjection p = _
    simp only [predicateProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  · change (predicateProjection p).conjTranspose = _
    ext i j
    by_cases h : i = j
    · subst j; simp [predicateProjection]
    · simp [predicateProjection, Matrix.conjTranspose_apply, h, Ne.symm h]

theorem cutoff_mul_left : domainProjection * leftProjection = (leftProjection (A := A)) := by
  classical
  simp only [domainProjection, leftProjection, predicateProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : leftPredicate i
  · simp [h, h.2.2]
  · simp [h]

theorem cutoff_mul_right : domainProjection * rightProjection = (rightProjection (A := A)) := by
  classical
  simp only [domainProjection, rightProjection, predicateProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : rightPredicate i
  · simp [h, h.2.2]
  · simp [h]

def leftW : CMatrix (Basis A) := leftInsertion * leftProjection
def rightW : CMatrix (Basis A) := rightInsertion * rightProjection
def oracleW : CMatrix (Basis A) := leftW + rightW.conjTranspose

theorem left_gram : (leftW (A := A)).conjTranspose * leftW = leftProjection := by
  have hP : leftProjection.conjTranspose = (leftProjection (A := A)) :=
    (predicate_projection leftPredicate).isSelfAdjoint.star_eq
  simp only [leftW, Matrix.conjTranspose_mul, hP]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc leftInsertion.conjTranspose,
    left_gram_eq_projection, cutoff_mul_left,
    (predicate_projection leftPredicate).isIdempotentElem.eq]

theorem right_gram : (rightW (A := A)).conjTranspose * rightW = rightProjection := by
  have hP : rightProjection.conjTranspose = (rightProjection (A := A)) :=
    (predicate_projection rightPredicate).isSelfAdjoint.star_eq
  simp only [rightW, Matrix.conjTranspose_mul, hP]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc rightInsertion.conjTranspose,
    right_gram_eq_projection, cutoff_mul_right,
    (predicate_projection rightPredicate).isIdempotentElem.eq]

theorem left_domain : leftW * leftProjection = (leftW (A := A)) := by
  rw [leftW, Matrix.mul_assoc, (predicate_projection leftPredicate).isIdempotentElem.eq]

theorem right_domain : rightW * rightProjection = (rightW (A := A)) := by
  rw [rightW, Matrix.mul_assoc, (predicate_projection rightPredicate).isIdempotentElem.eq]

theorem leftW_support {o i : Basis A} (h : leftW o i ≠ 0) :
    leftPredicate i ∧ LeftStep i o := by
  classical
  have he : leftW o i = leftInsertion o i * (if leftPredicate i then 1 else 0) := by
    simp [leftW, leftProjection, predicateProjection, Matrix.mul_diagonal]
  rw [he] at h
  have hp : leftPredicate i := by by_contra hp; simp [hp] at h
  have hi : leftInsertion o i ≠ 0 := by intro hi; simp [hi] at h
  exact ⟨hp, leftInsertion_support hi⟩

theorem rightW_support {o i : Basis A} (h : rightW o i ≠ 0) :
    rightPredicate i ∧ RightStep i o := by
  classical
  have he : rightW o i = rightInsertion o i * (if rightPredicate i then 1 else 0) := by
    simp [rightW, rightProjection, predicateProjection, Matrix.mul_diagonal]
  rw [he] at h
  have hp : rightPredicate i := by by_contra hp; simp [hp] at h
  have hi : rightInsertion o i ≠ 0 := by intro hi; simp [hi] at h
  exact ⟨hp, rightInsertion_support hi⟩

theorem leftProjection_mul_rightW : leftProjection * rightW = (0 : CMatrix (Basis A)) := by
  classical
  ext o i
  simp only [leftProjection, predicateProjection, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hp : leftPredicate o
  · rw [if_pos hp, one_mul]
    by_contra h
    have hs := (rightW_support h).2
    have he : (o.1,i.1) ∈ o.2.1 ∪ o.2.2 := by
      rw [hs.2.2]
      exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    exact hp.2.1 i.1 he
  · simp [hp]

theorem rightProjection_mul_leftW : rightProjection * leftW = (0 : CMatrix (Basis A)) := by
  classical
  ext o i
  simp only [rightProjection, predicateProjection, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hp : rightPredicate o
  · rw [if_pos hp, one_mul]
    by_contra h
    have hs := (leftW_support h).2
    have he : (i.1,o.1) ∈ o.2.1 ∪ o.2.2 := by
      rw [hs.2.2]
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    exact hp.2.1 i.1 he
  · simp [hp]

theorem rightW_mul_leftW : rightW * leftW = (0 : CMatrix (Basis A)) := by
  rw [← right_domain, Matrix.mul_assoc, rightProjection_mul_leftW]
  simp

theorem leftW_mul_rightW : leftW * rightW = (0 : CMatrix (Basis A)) := by
  rw [← left_domain, Matrix.mul_assoc, leftProjection_mul_rightW]
  simp

theorem oracle_gram : (oracleW (A := A)).conjTranspose * oracleW =
    leftProjection + rightW * rightW.conjTranspose := by
  have hz := congrArg Matrix.conjTranspose (rightW_mul_leftW (A := A))
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero] at hz
  simp only [oracleW, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
    Matrix.add_mul, Matrix.mul_add, left_gram, rightW_mul_leftW, hz, add_zero, zero_add]

theorem oracle_initial_projection :
    IsStarProjection ((oracleW (A := A)).conjTranspose * oracleW) := by
  rw [oracle_gram]
  have hi : IsStarProjection (rightW (A := A) * rightW.conjTranspose) :=
    image_projection rightW rightProjection right_gram right_domain
  apply (predicate_projection leftPredicate).add hi
  rw [← Matrix.mul_assoc, leftProjection_mul_rightW]
  simp

theorem oracle_norm_le : ‖oracleW (A := A)‖ ≤ 1 := by
  have h := (oracle_initial_projection (A := A)).norm_le
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg (oracleW (A := A))]

#print axioms oracle_initial_projection
#print axioms oracle_norm_le
end
end ICO.MHWPartial

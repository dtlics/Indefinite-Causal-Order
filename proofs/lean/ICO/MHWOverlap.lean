import ICO.MHWPartial

/-! Exact W†V overlap on the physical partial-recording domain. -/
namespace ICO.MHWOverlap
open Matrix QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
open ICO.RecordingPartialIsometry ICO.RecordingOracleAlgebra ICO.MHWPartial
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000

section Algebra
variable {S : Type*} [Ring S] [StarRing S]
theorem restricted_overlap (A B P L R : S)
    (hP : IsSelfAdjoint P) (hL : IsSelfAdjoint L) (hR : IsStarProjection R)
    (hA : star A*A=P) (hAP : A*P=A) (hLP : L*P=L)
    (hLB : L*B=0) (hRA : R*A=0) :
    star (A*L+star (B*R)) *
      (A*(1-B*star B)+(1-A*star A)*star B) = L+B*R*star B := by
  have hPAd : P*star A=star A := by
    simpa only [star_mul, hP.star_eq, star_star] using congrArg star hAP
  have hAd : star A*(1-A*star A)=0 := by
    rw [mul_sub, mul_one, ← mul_assoc, hA, hPAd, sub_self]
  have hBRA : B*R*A=0 := by rw [mul_assoc, hRA, mul_zero]
  calc
    _ = L*(star A*A)*(1-B*star B)+
        L*(star A*(1-A*star A))*star B+
        B*(R*A)*(1-B*star B)+B*R*(1-A*star A)*star B := by
      simp only [star_add, star_mul, star_star, hL.star_eq, hR.isSelfAdjoint.star_eq]
      noncomm_ring
    _ = L*(1-B*star B)+B*R*(1-A*star A)*star B := by
      rw [hA, hLP, hAd, hRA]
      simp
    _ = _ := by
      simp only [mul_sub, mul_one, sub_mul, ← mul_assoc, hLB, hBRA,
        zero_mul, sub_zero]
end Algebra

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem leftProjection_mul_insertion : leftProjection * rightInsertion = (0 : CMatrix (Basis A)) := by
  classical
  ext o i
  simp only [leftProjection, predicateProjection, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hp : leftPredicate o
  · rw [if_pos hp, one_mul]
    by_contra h
    have hs := rightInsertion_support h
    have he : (o.1,i.1) ∈ o.2.1 ∪ o.2.2 := by
      rw [hs.2.2]
      exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    exact hp.2.1 i.1 he
  · simp [hp]

theorem rightProjection_mul_insertion : rightProjection * leftInsertion = (0 : CMatrix (Basis A)) := by
  classical
  ext o i
  simp only [rightProjection, predicateProjection, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hp : rightPredicate o
  · rw [if_pos hp, one_mul]
    by_contra h
    have hs := leftInsertion_support h
    have he : (i.1,o.1) ∈ o.2.1 ∪ o.2.2 := by
      rw [hs.2.2]
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    exact hp.2.1 i.1 he
  · simp [hp]

theorem left_mul_cutoff : leftProjection * domainProjection = (leftProjection (A := A)) := by
  have hh := congrArg Matrix.conjTranspose (cutoff_mul_left (A := A))
  have hL : leftProjection.conjTranspose = (leftProjection (A := A)) :=
    (predicate_projection leftPredicate).isSelfAdjoint.star_eq
  have hP : domainProjection.conjTranspose = (domainProjection (α := A)) :=
    domainProjection_isStarProjection.isSelfAdjoint.star_eq
  simpa only [Matrix.conjTranspose_mul, hL, hP] using hh

theorem oracle_overlap : (oracleW (A := A)).conjTranspose * forwardRecording =
    leftProjection + rightW*rightW.conjTranspose := by
  have hh := restricted_overlap (S := CMatrix (Basis A))
    (leftInsertion (α := A)) rightInsertion domainProjection leftProjection rightProjection
    domainProjection_isStarProjection.isSelfAdjoint (predicate_projection leftPredicate).isSelfAdjoint
    (predicate_projection rightPredicate) left_gram_eq_projection left_domain_identity
    left_mul_cutoff leftProjection_mul_insertion rightProjection_mul_insertion
  have hR : rightProjection.conjTranspose = (rightProjection (A := A)) :=
    (predicate_projection rightPredicate).isSelfAdjoint.star_eq
  have he : rightW (A := A)*rightW.conjTranspose =
      rightInsertion (α := A)*rightProjection*rightInsertion.conjTranspose := by
    simp only [rightW, Matrix.conjTranspose_mul, hR]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc rightProjection,
      (predicate_projection rightPredicate).isIdempotentElem.eq]
    rw [Matrix.mul_assoc]
  rw [he]
  exact hh

theorem oracle_overlap_eq_gram :
    (oracleW (A := A)).conjTranspose * forwardRecording = oracleW.conjTranspose*oracleW := by
  rw [oracle_overlap, oracle_gram]

#print axioms oracle_overlap_eq_gram
end
end ICO.MHWOverlap

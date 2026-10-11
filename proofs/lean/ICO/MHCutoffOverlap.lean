import ICO.MHOverlapStep

/-! Exact restriction of overlap and covariance to reachable recording
grades. No uncut finite-set/multiset equality is used. -/
namespace ICO.MHCutoffOverlap
open Matrix QIT ICO.MHFockFullCovariance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {H : Type*} [Fintype H] [DecidableEq H]

theorem restricted_overlap (W V S : CMatrix H)
    (hWV : W.conjTranspose*V*S=W.conjTranspose*W*S) :
    (W*S).conjTranspose*(V*S)=(W*S).conjTranspose*(W*S) := by
  have hh := congrArg (fun M => S.conjTranspose*M) hWV
  simpa only [Matrix.conjTranspose_mul,Matrix.mul_assoc] using hh

theorem restricted_gram (W S : CMatrix H) (hS : IsStarProjection S)
    (hcomm : Commute S (W.conjTranspose*W)) :
    (W*S).conjTranspose*(W*S)=(W.conjTranspose*W)*S := by
  have hs : S.conjTranspose=S := hS.isSelfAdjoint.star_eq
  simp only [Matrix.conjTranspose_mul,hs,← Matrix.mul_assoc]
  rw [Matrix.mul_assoc S W.conjTranspose W,hcomm.eq,Matrix.mul_assoc,
    hS.isIdempotentElem.eq]

theorem restricted_domain_projection (W S : CMatrix H)
    (hW : IsStarProjection (W.conjTranspose*W)) (hS : IsStarProjection S)
    (hcomm : Commute S (W.conjTranspose*W)) :
    IsStarProjection ((W*S).conjTranspose*(W*S)) := by
  rw [restricted_gram W S hS hcomm]
  exact hW.mul hS hcomm.symm

theorem cutoff_covariance (V S : CMatrix H) (C D Q : Matrix.unitaryGroup H ℂ)
    (hS : IsStarProjection S) (hC : Commute S (C : CMatrix H))
    (hQ : Commute S (Q : CMatrix H)) (ε : ℝ)
    (hcov : ‖(Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H)‖≤ε) :
    ‖(Q : CMatrix H)*(V*S)-(D : CMatrix H)*(V*S)*(C : CMatrix H)*(Q : CMatrix H)‖≤ε := by
  have he : (Q : CMatrix H)*(V*S)-(D : CMatrix H)*(V*S)*(C : CMatrix H)*(Q : CMatrix H)=
      ((Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H))*S := by
    simp only [Matrix.sub_mul,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S (C : CMatrix H),hC.eq,Matrix.mul_assoc,
      hQ.eq]
  rw [he]
  have hh := norm_mul_le ((Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H)) S
  have hm := mul_le_mul_of_nonneg_left hS.norm_le
    (norm_nonneg ((Q : CMatrix H)*V-(D : CMatrix H)*V*(C : CMatrix H)*(Q : CMatrix H)))
  nlinarith

#print axioms restricted_domain_projection
#print axioms cutoff_covariance
end
end ICO.MHCutoffOverlap

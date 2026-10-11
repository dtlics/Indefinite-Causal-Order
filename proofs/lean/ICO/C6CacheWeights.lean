import ICO.C6CacheWeighted
import ICO.C6BosonicFreshRotated

/-! The actual overlap weights of a dephasing basis with a fresh subspace. -/
namespace ICO.C6CacheWeights
open QIT ICO.C6CacheWeighted ICO.C6BosonicFreshRotated
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1800000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def overlapWeight (U : Matrix.unitaryGroup A ℂ) (P : CMatrix A) (j : A) : ℝ :=
  ((U : CMatrix A).conjTranspose * (1-P) * (U : CMatrix A)) j j |>.re

theorem diagonal_nonnegative (X : CMatrix A) (hX : X.PosSemidef) (j : A) :
    0 ≤ (X j j).re := by
  have h : 0 ≤ X j j := by simpa using hX.2 (Finsupp.single j 1)
  exact (Complex.nonneg_iff.mp h).1

theorem overlapWeight_nonnegative (U : Matrix.unitaryGroup A ℂ) (P : CMatrix A)
    (hP : IsStarProjection P) (j : A) : 0 ≤ overlapWeight U P j := by
  exact diagonal_nonnegative _
    ((Matrix.nonneg_iff_posSemidef.mp hP.one_sub.nonneg).conjTranspose_mul_mul_same _) j

theorem overlapWeight_le_one (U : Matrix.unitaryGroup A ℂ) (P : CMatrix A)
    (hP : IsStarProjection P) (j : A) : overlapWeight U P j ≤ 1 := by
  have h := diagonal_nonnegative _
    ((Matrix.nonneg_iff_posSemidef.mp hP.nonneg).conjTranspose_mul_mul_same (U : CMatrix A)) j
  have hu : (U : CMatrix A).conjTranspose*(U : CMatrix A)=1 := U.property.1
  unfold overlapWeight
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hu]
  simp only [Matrix.sub_apply,Complex.sub_re,Matrix.one_apply_eq,Complex.one_re]
  linarith

theorem overlapWeight_deficit (U : Matrix.unitaryGroup A ℂ) (P : CMatrix A) :
    (∑ j : A, (1-overlapWeight U P j))=P.trace.re := by
  have hu : (U : CMatrix A)*(U : CMatrix A).conjTranspose=1 := U.property.2
  have ht : ((U : CMatrix A).conjTranspose*(1-P)*(U : CMatrix A)).trace=(1-P).trace := by
    rw [Matrix.trace_mul_comm,←Matrix.mul_assoc,hu,Matrix.one_mul]
  have hs : (∑ j : A, overlapWeight U P j)=((1-P).trace).re := by
    rw [←ht]
    simp [overlapWeight,Matrix.trace,Matrix.diag_apply,Complex.re_sum]
  rw [Finset.sum_sub_distrib,hs,Matrix.trace_sub,Complex.sub_re]
  simp [Matrix.trace_one,Complex.ofReal_natCast]

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- With the actual overlap weights, the uniform retained-outcome extension
has exact trace-norm deficit (rank P)/d times the input mass. -/
theorem actual_weighted_deficit (Φ : A → Channel a b)
    (U : Matrix.unitaryGroup A ℂ) (P : CMatrix A) (hP : IsStarProjection P)
    (X : CMatrix a) (hX : X.PosSemidef) :
    traceNorm (weighted Φ (fun _ => 1) X - weighted Φ (overlapWeight U P) X)=
      (P.trace.re/(Fintype.card A:ℝ))*X.trace.re := by
  rw [deficit_traceNorm Φ _ (overlapWeight_le_one U P hP) X hX,
    overlapWeight_deficit]

#print axioms actual_weighted_deficit
end
end ICO.C6CacheWeights

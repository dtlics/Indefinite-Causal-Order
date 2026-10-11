import ICO.C6OTOC

/-! The literal finite-clock OTOC is the normalized averaged squared
Hilbert--Schmidt commutator. This is an algebraic identity, with no time
evolution, unitary-design, or dynamical-scrambling assumption. -/
namespace ICO.C6OTOCCommutator
open Matrix QIT ICO.C6OTOC ICO.C6OTOCClock
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
set_option Elab.async false

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem unitary_commutator (P Q : CMatrix A)
    (hP : P.conjTranspose*P=1) (hQ : Q.conjTranspose*Q=1) :
    hilbertSchmidtSq (P*Q-Q*P) =
      2*(Fintype.card A:ℝ)-2*(Q*P*Q.conjTranspose*P.conjTranspose).trace.re := by
  have he : (P*Q-Q*P).conjTranspose*(P*Q-Q*P) =
      Q.conjTranspose*(P.conjTranspose*P)*Q+
        P.conjTranspose*(Q.conjTranspose*Q)*P-
        Q.conjTranspose*P.conjTranspose*Q*P-
        P.conjTranspose*Q.conjTranspose*P*Q := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    noncomm_ring
  have hc : (Q.conjTranspose*P.conjTranspose*Q*P).trace =
      (Q*P*Q.conjTranspose*P.conjTranspose).trace := by
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm (Q.conjTranspose*P.conjTranspose) (Q*P)
  have hs : (P.conjTranspose*Q.conjTranspose*P*Q).trace =
      star ((Q.conjTranspose*P.conjTranspose*Q*P).trace) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  unfold hilbertSchmidtSq
  rw [Matrix.star_eq_conjTranspose,he]
  simp only [hP,hQ,Matrix.mul_one,Matrix.one_mul]
  simp only [Matrix.trace_sub,Matrix.trace_add,Matrix.trace_one,
    Complex.sub_re,Complex.add_re,Complex.natCast_re,hs,hc]
  simp only [Complex.star_def,Complex.conj_re]
  ring

variable {d : ℕ} [NeZero d]

def averagedCommutator (U V : CMatrix (ZMod d)) : ℝ :=
  (∑t : ZMod d, ∑s : ZMod d,
    hilbertSchmidtSq (rotatedClock U t*rotatedClock V s-
      rotatedClock V s*rotatedClock U t)) / ((d:ℝ)^2*(2*d))

theorem phaseOTOC_complement (U V : Matrix.unitaryGroup (ZMod d) ℂ) :
    averagedCommutator (U:CMatrix (ZMod d)) (V:CMatrix (ZMod d)) =
      1-phaseOTOC (U:CMatrix (ZMod d)) (V:CMatrix (ZMod d)) := by
  unfold averagedCommutator
  simp_rw [unitary_commutator _ _ (rotatedClock_isometry U _) (rotatedClock_isometry V _)]
  simp only [ZMod.card,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  unfold phaseOTOC
  have hd : (d:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp
  <;> ring

#print axioms unitary_commutator
#print axioms phaseOTOC_complement
end
end ICO.C6OTOCCommutator

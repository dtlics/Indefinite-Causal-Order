import ICO.C6SwitchTest

/-! The upper bound uses equality of the hidden channels themselves;
it is independent of how their Kraus projectors are ordered or phased. -/
namespace ICO.C6SwitchSameChannel
open Matrix QIT ICO.SwitchObservable ICO.SwitchExperiment ICO.C6SwitchTest
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {A I J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I] [Fintype J]

theorem rawInterference_channel (P : I → CMatrix A) (Q : J → CMatrix A)
    (hP : ∀i,(P i).conjTranspose=P i) :
    rawInterference P Q = ∑i, ((MatrixMap.ofKraus Q) (P i)*P i).trace := by
  simp [rawInterference, hP, MatrixMap.ofKraus, Matrix.sum_mul, Matrix.trace_sum]

theorem same_channel_interference (U V : Matrix.unitaryGroup A ℂ)
    (h : MatrixMap.ofKraus (basisProjection (U:CMatrix A)) =
      MatrixMap.ofKraus (basisProjection (V:CMatrix A))) :
    interference (basisProjection (U:CMatrix A)) (basisProjection (V:CMatrix A))=1 := by
  have he : rawInterference (basisProjection (U:CMatrix A)) (basisProjection (V:CMatrix A))=
      rawInterference (basisProjection (U:CMatrix A)) (basisProjection (U:CMatrix A)) := by
    rw [rawInterference_channel _ _ (basisProjection_hermitian _),
      rawInterference_channel _ _ (basisProjection_hermitian _),←h]
  unfold interference
  rw [he]
  exact hidden_basis_high _ U.property.1 U.property.2

theorem same_channel_probability (U V : Matrix.unitaryGroup A ℂ)
    (h : MatrixMap.ofKraus (basisProjection (U:CMatrix A)) =
      MatrixMap.ofKraus (basisProjection (V:CMatrix A))) :
    (plusProbability U V:ℝ)=1 := by
  unfold plusProbability basisState
  rw [switch_plus_probability, same_channel_interference U V h]
  norm_num

theorem same_channel_four_accepts (U V : Matrix.unitaryGroup A ℂ)
    (h : MatrixMap.ofKraus (basisProjection (U:CMatrix A)) =
      MatrixMap.ofKraus (basisProjection (V:CMatrix A))) :
    acceptSame U V=1 := by
  rw [acceptSame, all_plus_probability, same_channel_probability U V h]
  norm_num

#print axioms same_channel_four_accepts
end
end ICO.C6SwitchSameChannel

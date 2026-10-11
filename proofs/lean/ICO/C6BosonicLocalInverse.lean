import ICO.C6BosonicInverseError
import ICO.C6BosonicQueryAlgebra

/-! The actual finite-Fock inverse replacement bound on the support generated
by a literal private history. All compression estimates are discharged. -/
namespace ICO.C6BosonicLocalInverse
open QIT ICO.C6BosonicInverseError ICO.C6BosonicQueryAlgebra
  ICO.C6BosonicLengthMasks ICO.C6BosonicHistorySupport ICO.C6BosonicFockSupport
  ICO.C6BosonicFockRotated ICO.C6CacheSpanProjection ICO.C6CacheHistorySpan
  ICO.C6PolarFock ICO.C6FockQueryMatrix ICO.C6FockCompressionSharp
  ICO.C6BosonicFreshContraction ICO.MHBoundedRecording ICO.MHFockKnownOperation
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2600000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem oracle_adjoint {t T : ℕ} (h : t+1≤T) :
    (polarOracle (α:=A) h).conjTranspose=inverseExpression (polarLeftOnFock h) (polarRightOnFock h) := by
  simp only [polarOracle,inverseExpression,Matrix.conjTranspose_add,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_conjTranspose]

theorem local_inverse_succ (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T m : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) (hm : m+1<Fintype.card A) :
    ‖((polarOracle h).conjTranspose-freshInverse (polarLeftOnFock h) (polarRightOnFock h)
      (rotatedFresh U S T))*fockSupport (spanProjection U S) T*rightLengthMask (m+1) T‖≤
        compressionBound S.card m (Fintype.card A)+compressionBound S.card (m+1) (Fintype.card A) := by
  let P := queryMatrix (spanProjection U S) T
  let B := fockSupport (spanProjection U S) T
  have hP : IsStarProjection P := query_projection _ (spanProjection_projection U S) T
  have hB : IsStarProjection B := by
    rw [show B=rotatedRecord U S T from fockSupport_rotated U S T]
    exact unitary_projection _ _ (fockRecord_projection S T)
  have hα : ‖(polarRightOnFock h).conjTranspose*rightLengthMask (m+1) T*P‖≤
      compressionBound S.card m (Fintype.card A) := by
    apply (adjoint_target_bound _ P _ (rightLengthMask m T) hP.isSelfAdjoint.star_eq
      (mask_projection (m+1) T) (mask_projection (A:=A) m T).isSelfAdjoint.star_eq
      (mask_family (queryFamily (spanProjection U S)) (m+1) T).symm
      (right_adjoint_predecessor m h)).trans
    exact right_compression_norm U S h m (Nat.lt_of_succ_lt hm)
  have hβ : ‖P*polarRightOnFock h*rightLengthMask (m+1) T‖≤
      compressionBound S.card (m+1) (Fintype.card A) := right_compression_norm U S h (m+1) hm
  have hret : (1-P)*(polarLeftOnFock h).conjTranspose*B=0 := by
    dsimp only [P,B]
    rw [←rotatedFresh_complement,fockSupport_rotated]
    exact rotated_retrieval_zero U S h ht
  rw [oracle_adjoint,rotatedFresh_complement]
  exact inverse_replacement_bound _ _ P B _ _ _
    (polarLeftOnFock_norm_le h ht) (polarRightOnFock_norm_le h ht)
    (ICO.RecordingOracleAlgebra.image_projection _ _ (polarLeftOnFock_gram h ht) (polarLeftOnFock_domain h))
    hB (mask_projection (m+1) T) (left_mask (m+1) h) (left_adjoint_mask (m+1) h)
    (mask_family (supportSector (spanProjection U S)) (m+1) T) hret hα hβ

theorem local_inverse_zero (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) :
    ‖((polarOracle h).conjTranspose-freshInverse (polarLeftOnFock h) (polarRightOnFock h)
      (rotatedFresh U S T))*fockSupport (spanProjection U S) T*rightLengthMask 0 T‖≤
        compressionBound S.card 0 (Fintype.card A) := by
  let P := queryMatrix (spanProjection U S) T
  let B := fockSupport (spanProjection U S) T
  have hB : IsStarProjection B := by
    rw [show B=rotatedRecord U S T from fockSupport_rotated U S T]
    exact unitary_projection _ _ (fockRecord_projection S T)
  have hα : ‖(polarRightOnFock h).conjTranspose*rightLengthMask 0 T*P‖≤0 := by
    rw [right_adjoint_vacuum,Matrix.zero_mul,norm_zero]
  have hβ : ‖P*polarRightOnFock h*rightLengthMask 0 T‖≤
      compressionBound S.card 0 (Fintype.card A) := right_compression_norm U S h 0 Fintype.card_pos
  have hret : (1-P)*(polarLeftOnFock h).conjTranspose*B=0 := by
    dsimp only [P,B]
    rw [←rotatedFresh_complement,fockSupport_rotated]
    exact rotated_retrieval_zero U S h ht
  rw [oracle_adjoint,rotatedFresh_complement]
  simpa only [zero_add] using inverse_replacement_bound _ _ P B _ 0 _
    (polarLeftOnFock_norm_le h ht) (polarRightOnFock_norm_le h ht)
    (ICO.RecordingOracleAlgebra.image_projection _ _ (polarLeftOnFock_gram h ht) (polarLeftOnFock_domain h))
    hB (mask_projection 0 T) (left_mask 0 h) (left_adjoint_mask 0 h)
    (mask_family (supportSector (spanProjection U S)) 0 T) hret hα hβ

theorem compressionBound_mono {k l m d : ℕ} (hkl : k≤l) (hmd : m<d) :
    compressionBound k m d≤compressionBound l m d := by
  apply Real.sqrt_le_sqrt
  have hm : (m:ℝ) ≤ (d:ℝ) := by exact_mod_cast hmd.le
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hm)
  exact_mod_cast Nat.add_le_add_right hkl m

theorem history_inverse_succ {s t T m : ℕ} (v : Fin s → EuclideanSpace ℂ A)
    (h : t+1≤T) (ht : t<Fintype.card A) (hm : m+1<Fintype.card A) :
    ‖((polarOracle h).conjTranspose-freshInverse (polarLeftOnFock h) (polarRightOnFock h)
      (rotatedFresh (historyUnitary v) (historyIndices v) T))*historySupport v T*rightLengthMask (m+1) T‖≤
        compressionBound s m (Fintype.card A)+compressionBound s (m+1) (Fintype.card A) :=
  (local_inverse_succ (historyUnitary v) (historyIndices v) h ht hm).trans
    (add_le_add (compressionBound_mono (history_realization v).2 (Nat.lt_of_succ_lt hm))
      (compressionBound_mono (history_realization v).2 hm))

#print axioms local_inverse_succ

theorem history_inverse_zero {s t T : ℕ} (v : Fin s → EuclideanSpace ℂ A)
    (h : t+1≤T) (ht : t<Fintype.card A) :
    ‖((polarOracle h).conjTranspose-freshInverse (polarLeftOnFock h) (polarRightOnFock h)
      (rotatedFresh (historyUnitary v) (historyIndices v) T))*historySupport v T*rightLengthMask 0 T‖≤
        compressionBound s 0 (Fintype.card A) :=
  (local_inverse_zero (historyUnitary v) (historyIndices v) h ht).trans
    (compressionBound_mono (history_realization v).2 Fintype.card_pos)

theorem empty_history_inverse_exact {t T : ℕ} (v : Fin 0 → EuclideanSpace ℂ A)
    (h : t+1≤T) (ht : t<Fintype.card A) :
    ((polarOracle h).conjTranspose-freshInverse (polarLeftOnFock h) (polarRightOnFock h)
      (rotatedFresh (historyUnitary v) (historyIndices v) T))*historySupport v T*rightLengthMask 0 T=0 := by
  have he := history_inverse_zero v h ht
  simp only [compressionBound,Nat.cast_zero,zero_add,zero_div,Real.sqrt_zero] at he
  exact norm_eq_zero.mp (le_antisymm he (norm_nonneg _))

#print axioms local_inverse_zero
#print axioms history_inverse_succ
#print axioms empty_history_inverse_exact
end
end ICO.C6BosonicLocalInverse

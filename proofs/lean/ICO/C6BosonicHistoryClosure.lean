import ICO.C6BosonicGeometricCreation
import ICO.C6RotatedNumber

/-! Geometric left-label support is preserved by the actual fresh inverse. -/
namespace ICO.C6BosonicHistoryClosure
open QIT ICO.C6BosonicGeometricCreation ICO.C6BosonicQueryAlgebra
  ICO.C6BosonicHistorySupport ICO.C6BosonicFockSupport ICO.C6BosonicFockRotated
  ICO.C6BosonicCacheSupport ICO.C6CacheSpanProjection ICO.C6PolarFock
  ICO.C6FockQueryMatrix ICO.C6BosonicFreshContraction ICO.C6RotatedNumber
  ICO.C6NumberRotationAlgebra ICO.MHFockRotation ICO.MHFockRotationSwap ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem query_record (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (T : ℕ) :
    (fockQuery U T:CMatrix (InputCutoff (α:=A) T))*fockRecord S T=
      fockRecord S T*(fockQuery U T:CMatrix (InputCutoff (α:=A) T)) := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  simp only [fockRecord,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hs : s=s'
  · subst s'
    rw [fockQuery_entry_same]
    by_cases hp : p=p'
    · subst p'; exact mul_comm _ _
    · simp [hp]
  · rw [fockQuery_entry_other U T _ _ hs]
    simp

theorem geometric_retrieval_support (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) :
    fockSupport (spanProjection U S) T*(polarLeftOnFock h).conjTranspose*
      fockSupport (spanProjection U S) T=
      (polarLeftOnFock h).conjTranspose*fockSupport (spanProjection U S) T := by
  let B := fockSupport (spanProjection U S) T
  let P := queryMatrix (spanProjection U S) T
  have hB : IsStarProjection B := by
    rw [show B=rotatedRecord U S T from fockSupport_rotated U S T]
    exact unitary_projection _ _ (fockRecord_projection S T)
  have hb : B.conjTranspose=B := hB.isSelfAdjoint.star_eq
  have hp : P.conjTranspose=P := (query_projection _ (spanProjection_projection U S) T).isSelfAdjoint.star_eq
  have he := congrArg Matrix.conjTranspose (geometric_left_support U S h ht)
  simp only [Matrix.conjTranspose_mul] at he
  change (polarLeftOnFock h).conjTranspose*B.conjTranspose=B.conjTranspose*(P.conjTranspose*(polarLeftOnFock h).conjTranspose) at he
  rw [hb,hp] at he
  change B*(polarLeftOnFock h).conjTranspose*B=(polarLeftOnFock h).conjTranspose*B
  calc
    _ = B*((polarLeftOnFock h).conjTranspose*B) := Matrix.mul_assoc _ _ _
    _ = B*(B*(P*(polarLeftOnFock h).conjTranspose)) := by rw [he]
    _ = _ := by rw [←Matrix.mul_assoc B B,hB.isIdempotentElem.eq,←he]

theorem geometric_image_support (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) :
    fockSupport (spanProjection U S) T*(polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)=
      (polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)*fockSupport (spanProjection U S) T := by
  let B := fockSupport (spanProjection U S) T
  let P := queryMatrix (spanProjection U S) T
  have hB : IsStarProjection B := by
    rw [show B=rotatedRecord U S T from fockSupport_rotated U S T]
    exact unitary_projection _ _ (fockRecord_projection S T)
  have hb : B.conjTranspose=B := hB.isSelfAdjoint.star_eq
  have hp : P.conjTranspose=P := (query_projection _ (spanProjection_projection U S) T).isSelfAdjoint.star_eq
  have he := congrArg Matrix.conjTranspose (geometric_left_support U S h ht)
  simp only [Matrix.conjTranspose_mul] at he
  change (polarLeftOnFock h).conjTranspose*B.conjTranspose=B.conjTranspose*(P.conjTranspose*(polarLeftOnFock h).conjTranspose) at he
  rw [hb,hp] at he
  change B*(polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)=_
  rw [←Matrix.mul_assoc,geometric_left_support U S h ht]
  simp only [Matrix.mul_assoc]
  rw [he,←Matrix.mul_assoc P B,query_support]
  simp only [Matrix.mul_assoc]
  rfl

theorem geometric_birth_support (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) :
    fockSupport (spanProjection U S) T*(rotatedFresh U S T*polarRightOnFock h)=
      (rotatedFresh U S T*polarRightOnFock h)*fockSupport (spanProjection U S) T := by
  have hb : fockRecord S T*(queryFresh S T*polarRightOnFock h)=
      (queryFresh S T*polarRightOnFock h)*fockRecord S T := by
    rw [←Matrix.mul_assoc,fresh_query_support,Matrix.mul_assoc,right_preserves_left]
    simp only [Matrix.mul_assoc]
  have hh := transported_intertwining (rotatedFresh U S T*polarRightOnFock h)
    (queryFresh S T*polarRightOnFock h) (fockRecord S T) (fockRecord S T)
    (fockQ U 1 T) (fockQuery U T*fockQ U 1 T) (fresh_birth_covariance U S h ht) hb
  rw [commuting_conjugate _ _ _ (query_record_rotation U U T) (query_record U S T)] at hh
  simpa only [fockSupport_rotated,rotatedRecord] using hh

theorem geometric_fresh_support (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) :
    fockSupport (spanProjection U S) T*
      freshInverse (polarLeftOnFock h) (polarRightOnFock h) (rotatedFresh U S T)*
      fockSupport (spanProjection U S) T=
      freshInverse (polarLeftOnFock h) (polarRightOnFock h) (rotatedFresh U S T)*
      fockSupport (spanProjection U S) T := by
  let B := fockSupport (spanProjection U S) T
  have hB : B*B=B := by
    rw [show B=rotatedRecord U S T from fockSupport_rotated U S T]
    exact (unitary_projection _ _ (fockRecord_projection S T)).isIdempotentElem.eq
  have hc : B*(1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)=
      (1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)*B := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,geometric_image_support U S h ht,B]
  unfold freshInverse
  simp only [Matrix.mul_add,Matrix.add_mul]
  rw [geometric_retrieval_support U S h ht]
  congr 1
  calc
    _ = ((rotatedFresh U S T*polarRightOnFock h)*B)*
        (1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)*B := by
      rw [←Matrix.mul_assoc B (rotatedFresh U S T*polarRightOnFock h),geometric_birth_support U S h ht]
    _ = _ := by
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc B (1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose),hc]
      simp only [Matrix.mul_assoc]
      rw [hB]

theorem history_fresh_support {s t T : ℕ} (v : Fin s→EuclideanSpace ℂ A)
    (h : t+1≤T) (ht : t<Fintype.card A) :
    historySupport v T*freshInverse (polarLeftOnFock h) (polarRightOnFock h)
      (rotatedFresh (historyUnitary v) (historyIndices v) T)*historySupport v T=
      freshInverse (polarLeftOnFock h) (polarRightOnFock h)
        (rotatedFresh (historyUnitary v) (historyIndices v) T)*historySupport v T :=
  geometric_fresh_support (historyUnitary v) (historyIndices v) h ht

#print axioms geometric_fresh_support
#print axioms history_fresh_support
end
end ICO.C6BosonicHistoryClosure

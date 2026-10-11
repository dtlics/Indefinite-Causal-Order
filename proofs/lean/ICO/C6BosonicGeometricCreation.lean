import ICO.C6BosonicQueryAlgebra

/-! A forward polar insertion adds only the supplied query label to the
geometric left-label support. -/
namespace ICO.C6BosonicGeometricCreation
open QIT ICO.C6BosonicQueryAlgebra ICO.C6BosonicHistorySupport ICO.C6BosonicFockSupport
  ICO.C6BosonicFockRotated ICO.C6CacheSpanProjection ICO.C6CacheHistorySpan
  ICO.C6PolarFock ICO.C6FockQueryMatrix ICO.C6BosonicFreshRotated
  ICO.MHFockRotation ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem input_query_record (S : Finset A) (T : ℕ) :
    fockInput S T=queryMatrix (coordinateProjection S) T*fockRecord S T := by
  rw [coordinateProjection,query_diagonal,fockRecord,Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [fockInput,Matrix.diagonal_apply,Pi.mul_apply]
  by_cases hij : i=j <;> by_cases hi : i.2.1∈S <;>
    by_cases hp : ICO.C6BosonicLabelSupport.LabelsIn S i.2.2 <;> simp_all

theorem coordinate_query_rotation (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (T : ℕ) :
    queryMatrix (coordinateProjection S) T*(fockQ U 1 T:CMatrix (InputCutoff (α:=A) T))=
      (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T))*queryMatrix (coordinateProjection S) T := by
  have h := queryFresh_commutes S U 1 T
  rw [query_complement,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one] at h
  exact sub_right_inj.mp h

theorem geometric_left_support (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) :
    fockSupport (spanProjection U S) T*polarLeftOnFock h=
      polarLeftOnFock h*queryMatrix (spanProjection U S) T*fockSupport (spanProjection U S) T := by
  let R : CMatrix (InputCutoff (α:=A) T) := fockQ U 1 T
  let C : CMatrix (InputCutoff (α:=A) T) := fockQuery U T
  let B := fockRecord S T
  let B' := fockSupport (spanProjection U S) T
  let P := queryMatrix (coordinateProjection S) T
  have hb : B'=R*B*R.conjTranspose := fockSupport_rotated U S T
  have hc : polarLeftOnFock h*(C*R)=R*polarLeftOnFock h := by
    have hh := ICO.C6PolarFockCovariance.left_covariance U 1 h ht
    rw [ICO.C6BosonicFockRotated.query_one,Matrix.one_mul] at hh
    exact hh
  have ha : R.conjTranspose*polarLeftOnFock h=polarLeftOnFock h*R.conjTranspose*C.conjTranspose := by
    have hh := congrArg Matrix.conjTranspose (retrieval_rotation U h ht)
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc] using hh
  have hP : R*P=P*R := (coordinate_query_rotation U S T).symm
  have hB : B'*C.conjTranspose=C.conjTranspose*B' := by
    have hh := query_support (U:CMatrix A).conjTranspose (spanProjection U S) T
    rw [query_adjoint,query_unitary] at hh
    exact hh.symm
  have hrot : C*P*C.conjTranspose=queryMatrix (spanProjection U S) T := by
    rw [spanProjection,query_mul,query_mul,query_adjoint,query_unitary]
  change B'*polarLeftOnFock h=polarLeftOnFock h*queryMatrix (spanProjection U S) T*B'
  calc
    _ = R*B*(R.conjTranspose*polarLeftOnFock h) := by rw [hb]; simp only [Matrix.mul_assoc]
    _ = (R*polarLeftOnFock h)*(P*B)*R.conjTranspose*C.conjTranspose := by
      rw [ha]
      simp only [P,B,Matrix.mul_assoc]
      rw [←Matrix.mul_assoc B (polarLeftOnFock h)]
      change _ = _
      rw [fock_polar_support S h ht,input_query_record]
      simp only [Matrix.mul_assoc]
    _ = polarLeftOnFock h*(C*P)*(R*B*R.conjTranspose)*C.conjTranspose := by
      rw [←hc]
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc R P,hP]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [←hb]
      simp only [Matrix.mul_assoc]
      rw [hB]
      rw [←hrot]
      simp only [Matrix.mul_assoc]

#print axioms geometric_left_support
end
end ICO.C6BosonicGeometricCreation

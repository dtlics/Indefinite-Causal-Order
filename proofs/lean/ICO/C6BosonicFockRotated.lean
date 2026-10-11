import ICO.C6BosonicFockSupport
import ICO.C6PolarFockCovariance
import ICO.MHFockPublicRotation

/-! The actual fresh inverse is contractive on arbitrary rotated label
support, including an arbitrary entangled spectator memory. -/
namespace ICO.C6BosonicFockRotated
open QIT ICO.C6BosonicFockSupport ICO.C6BosonicFreshContraction
  ICO.C6PolarFock ICO.MHFockRotation ICO.MHBoundedRecording ICO.MHFockKnownOperation
  ICO.MHFockSpace ICO.MHSectorCovariance ICO.MHSymmetric
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2300000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem unitary_projection {H : Type*} [Fintype H] [DecidableEq H]
    (U : Matrix.unitaryGroup H ℂ) (P : CMatrix H) (hP : IsStarProjection P) :
    IsStarProjection ((U : CMatrix H)*P*(U : CMatrix H).conjTranspose) := by
  have hu : (U : CMatrix H).conjTranspose*(U : CMatrix H)=1 := U.property.1
  constructor
  · change ((U : CMatrix H)*P*(U : CMatrix H).conjTranspose)*
        ((U : CMatrix H)*P*(U : CMatrix H).conjTranspose)=_
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc (U : CMatrix H).conjTranspose (U : CMatrix H),hu,Matrix.one_mul,
      ←Matrix.mul_assoc P P,hP.isIdempotentElem.eq]
  · change (_ : CMatrix H).conjTranspose=_
    have hp : P.conjTranspose=P := hP.isSelfAdjoint.star_eq
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      hp,Matrix.mul_assoc]

theorem query_one (T : ℕ) :
    (fockQuery (1 : Matrix.unitaryGroup A ℂ) T : CMatrix (InputCutoff (α:=A) T))=1 := by
  change (Matrix.blockDiagonal' (fun s : Lengths T =>
    (queryTurn (1 : Matrix.unitaryGroup A ℂ) s.val.1.val s.val.2.val :
      CMatrix (Sector (α:=A) s.val.1.val s.val.2.val)))).submatrix (sectorEquiv T) (sectorEquiv T)=1
  have hq (n r : ℕ) : (queryTurn (1 : Matrix.unitaryGroup A ℂ) n r :
      CMatrix (Sector (α:=A) n r))=1 := by
    change Matrix.kronecker (Matrix.kronecker (1 : CMatrix A) 1) 1=1
    simp only [Matrix.kronecker]
    rw [Matrix.one_kronecker_one,Matrix.one_kronecker_one]
  simp only [hq]
  have hb : (Matrix.blockDiagonal' (fun s : Lengths T =>
    (1 : CMatrix (Sector (α:=A) s.val.1.val s.val.2.val))))=1 := Matrix.blockDiagonal'_one
  rw [hb,Matrix.submatrix_one_equiv]

theorem queryFresh_commutes (S : Finset A) (C D : Matrix.unitaryGroup A ℂ) (T : ℕ) :
    queryFresh S T*(fockQ C D T : CMatrix (InputCutoff (α:=A) T))=
      (fockQ C D T : CMatrix (InputCutoff (α:=A) T))*queryFresh S T := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  simp only [queryFresh,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hs : s=s'
  · subst s'
    rw [fockQ_entry_same]
    by_cases hx : x=y
    · subst y
      simp only [ite_true]
      split_ifs <;> simp
    · simp [hx]
  · rw [fockQ_entry_other C D T _ _ hs]
    simp

theorem retrieval_rotation (U : Matrix.unitaryGroup A ℂ) {t T : ℕ}
    (h : t+1≤T) (ht : t<Fintype.card A) :
    (polarLeftOnFock h).conjTranspose*(fockQ U 1 T : CMatrix (InputCutoff (α:=A) T))=
      (fockQuery U T : CMatrix (InputCutoff (α:=A) T))*
        (fockQ U 1 T : CMatrix (InputCutoff (α:=A) T))*(polarLeftOnFock h).conjTranspose := by
  let R : CMatrix (InputCutoff (α:=A) T) := fockQ U 1 T
  let C : CMatrix (InputCutoff (α:=A) T) := fockQuery U T
  have hR : R*R.conjTranspose=1 := (fockQ U 1 T).property.2
  have hRi : R.conjTranspose*R=1 := (fockQ U 1 T).property.1
  have hC : C*C.conjTranspose=1 := (fockQuery U T).property.2
  have hc := ICO.C6PolarFockCovariance.left_covariance U 1 h ht
  rw [query_one,Matrix.one_mul] at hc
  change polarLeftOnFock h*(C*R)=R*polarLeftOnFock h at hc
  have hh := congrArg (fun M => C*R*M*R) (congrArg Matrix.conjTranspose hc)
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc] at hh
  rw [←Matrix.mul_assoc R R.conjTranspose,hR,Matrix.one_mul,
    ←Matrix.mul_assoc C C.conjTranspose,hC,Matrix.one_mul,hRi,Matrix.mul_one] at hh
  simpa only [Matrix.mul_assoc] using hh

def rotatedRecord (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (T : ℕ) :
    CMatrix (InputCutoff (α:=A) T) :=
  (fockQ U 1 T : CMatrix (InputCutoff (α:=A) T))*fockRecord S T*
    (fockQ U 1 T : CMatrix (InputCutoff (α:=A) T)).conjTranspose

def rotatedFresh (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (T : ℕ) :
    CMatrix (InputCutoff (α:=A) T) :=
  (fockQuery U T : CMatrix (InputCutoff (α:=A) T))*queryFresh S T*
    (fockQuery U T : CMatrix (InputCutoff (α:=A) T)).conjTranspose

theorem rotated_retrieval_zero (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) :
    rotatedFresh U S T*(polarLeftOnFock h).conjTranspose*rotatedRecord U S T=0 := by
  have hz : queryFresh S T*(polarLeftOnFock h).conjTranspose*fockRecord S T=0 := by
    rw [Matrix.mul_assoc,←fock_polar_adjoint_support S h ht,
      ←Matrix.mul_assoc,queryFresh_fockInput_zero,Matrix.zero_mul]
  have hC : (fockQuery U T : CMatrix (InputCutoff (α:=A) T)).conjTranspose*
      (fockQuery U T : CMatrix (InputCutoff (α:=A) T))=1 := (fockQuery U T).property.1
  unfold rotatedFresh rotatedRecord
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (polarLeftOnFock h).conjTranspose
    (fockQ U 1 T : CMatrix (InputCutoff (α:=A) T)),retrieval_rotation U h ht]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (fockQuery U T : CMatrix (InputCutoff (α:=A) T)).conjTranspose
    (fockQuery U T : CMatrix (InputCutoff (α:=A) T)),hC,Matrix.one_mul]
  rw [←Matrix.mul_assoc (queryFresh S T) (fockQ U 1 T : CMatrix (InputCutoff (α:=A) T)),
    queryFresh_commutes]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (queryFresh S T) (polarLeftOnFock h).conjTranspose,
    ←Matrix.mul_assoc (queryFresh S T*(polarLeftOnFock h).conjTranspose) (fockRecord S T),hz]
  simp

theorem rotated_freshInverse_contraction (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) :
    ‖freshInverse (polarLeftOnFock h) (polarRightOnFock h) (rotatedFresh U S T)*
      rotatedRecord U S T‖≤1 := by
  apply freshInverse_supported_norm
  · exact ICO.RecordingOracleAlgebra.image_projection _ _
      (polarLeftOnFock_gram h ht) (polarLeftOnFock_domain h)
  · exact polarRightOnFock_norm_le h ht
  · exact unitary_projection _ _ (queryFresh_projection S T)
  · exact unitary_projection _ _ (fockRecord_projection S T)
  · exact rotated_retrieval_zero U S h ht

theorem memory_freshInverse_contraction (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A)
    (M : Type*) [Fintype M] [DecidableEq M] :
    ‖Matrix.kronecker (freshInverse (polarLeftOnFock h) (polarRightOnFock h)
      (rotatedFresh U S T)*rotatedRecord U S T) (1 : CMatrix M)‖≤1 :=
  (tensor_identity_norm_le (μ:=M) _).trans (rotated_freshInverse_contraction U S h ht)

#print axioms rotated_retrieval_zero
#print axioms memory_freshInverse_contraction
end
end ICO.C6BosonicFockRotated

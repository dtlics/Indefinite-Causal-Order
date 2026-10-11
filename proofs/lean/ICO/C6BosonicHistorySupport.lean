import ICO.C6BosonicGeometricSupport
import ICO.C6BosonicKnownSupport

/-! Canonical full-Fock label support attached to the actual private history. -/
namespace ICO.C6BosonicHistorySupport
open QIT ICO.C6BosonicGeometricSupport ICO.C6BosonicWordSupport
  ICO.C6CacheSpanProjection ICO.C6CacheHistorySpan ICO.C6BosonicFockSupport
  ICO.C6BosonicFockRotated ICO.MHFockTransport ICO.MHFockBothCovariance
  ICO.MHFockRotation ICO.MHBoundedRecording ICO.MHSymmetric ICO.MHSectorCovariance
  ICO.C6BosonicLabelSupport ICO.MHCreationCovariance ICO.MHRightCovariance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2600000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def supportSector (P : CMatrix A) (n r : ℕ) : CMatrix (Sector (α:=A) n r) :=
  Matrix.kronecker (Matrix.kronecker (1:CMatrix A) (occupationSupport P n))
    (1:CMatrix (TensorPowerProfile (A×A) r))

def fockSupport (P : CMatrix A) (T : ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  inputFamily (supportSector P) T

def coordinateSector (S : Finset A) (n r : ℕ) : CMatrix (Sector (α:=A) n r) :=
  Matrix.kronecker (Matrix.kronecker (1:CMatrix A) (profileSupport S n))
    (1:CMatrix (TensorPowerProfile (A×A) r))

theorem record_family (S : Finset A) (T : ℕ) :
    fockRecord S T=inputFamily (coordinateSector S) T := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  by_cases hs : s=s'
  · subst s'
    rw [inputFamily_same]
    simp only [fockRecord,Matrix.diagonal_apply,coordinateSector,profileSupport,
      Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.diagonal_apply]
    by_cases hx : x=y <;> by_cases hp : p=p' <;> by_cases hq : q=q' <;>
      simp_all [Sigma.mk.inj_iff,Prod.mk.injEq]
    all_goals split_ifs <;> simp_all
  · rw [inputFamily_other _ _ _ _ hs]
    have hn : (⟨⟨s,q⟩,(x,p)⟩ : InputCutoff (α:=A) T)≠⟨⟨s',q'⟩,(y,p')⟩ := by
      intro he
      exact hs (congrArg (fun i : InputCutoff (α:=A) T => i.1.1) he)
    simp [fockRecord,Matrix.diagonal_apply,hn]

theorem sector_conjugate (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (n r : ℕ) :
    (outputTurn U 1 n r:CMatrix (Sector (α:=A) n r))*coordinateSector S n r*
      (outputTurn U 1 n r:CMatrix (Sector (α:=A) n r)).conjTranspose=
      supportSector (spanProjection U S) n r := by
  have hr : occupationRotation (rightEdgeUnitary (1:Matrix.unitaryGroup A ℂ) U⁻¹) r*
      (occupationRotation (rightEdgeUnitary (1:Matrix.unitaryGroup A ℂ) U⁻¹) r).conjTranspose=1 :=
    (symmetricRotation _ r).property.2
  simp only [outputTurn,tensorUnitary,symmetricRotation,coordinateSector,supportSector,
    Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,inv_one,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
    ←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul,Matrix.mul_one,hr]
  have h1 : ((1:Matrix.unitaryGroup A ℂ):CMatrix A)*
      (((1:Matrix.unitaryGroup A ℂ):CMatrix A)).conjTranspose=1 :=
    (1:Matrix.unitaryGroup A ℂ).property.2
  rw [h1,occupationSupport_rotated]

theorem fockSupport_rotated (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (T : ℕ) :
    fockSupport (spanProjection U S) T=rotatedRecord U S T := by
  unfold rotatedRecord
  rw [record_family]
  change fockSupport (spanProjection U S) T=
    inputFamily (fun n r => (outputTurn U 1 n r:CMatrix (Sector (α:=A) n r))) T*
      inputFamily (coordinateSector S) T*
        (inputFamily (fun n r => (outputTurn U 1 n r:CMatrix (Sector (α:=A) n r))) T).conjTranspose
  rw [ICO.MHFockCovariance.inputFamily_adjoint,inputFamily_mul,inputFamily_mul]
  simp only [sector_conjugate]
  rfl

theorem fockSupport_absorption (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    (Q : CMatrix A) (h : Q*spanProjection U S=spanProjection U S) (T : ℕ) :
    fockSupport Q T*fockSupport (spanProjection U S) T=fockSupport (spanProjection U S) T := by
  unfold fockSupport
  rw [inputFamily_mul]
  congr 1
  funext n r
  simp only [supportSector,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
    occupationSupport_absorption U S Q h,Matrix.one_mul,Matrix.one_mul]

def historySupport {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) (T : ℕ) :
    CMatrix (InputCutoff (α:=A) T) := fockSupport (historyProjection v) T

theorem historySupport_rotated {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) (T : ℕ) :
    historySupport v T=rotatedRecord (historyUnitary v) (historyIndices v) T :=
  fockSupport_rotated _ _ _

theorem historySupport_snoc {s : ℕ} (v : Fin s → EuclideanSpace ℂ A)
    (x : EuclideanSpace ℂ A) (T : ℕ) :
    historySupport (Fin.snoc v x) T*historySupport v T=historySupport v T :=
  fockSupport_absorption _ _ _ (historyProjection_snoc v x) T

theorem historySupport_projection {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) (T : ℕ) :
    IsStarProjection (historySupport v T) := by
  rw [historySupport_rotated]
  exact unitary_projection _ _ (fockRecord_projection _ _)

theorem historySupport_known {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) (T : ℕ)
    {M N : Type*} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (K : Matrix (A×N) (A×M) ℂ) :
    Matrix.kronecker (historySupport v T) (1:CMatrix N)*ICO.MHFockKnownOperation.known T K=
      ICO.MHFockKnownOperation.known T K*Matrix.kronecker (historySupport v T) (1:CMatrix M) := by
  rw [historySupport_rotated]
  exact ICO.C6BosonicKnownSupport.known_rotated_record_support _ _ _ K

#print axioms fockSupport_rotated
#print axioms historySupport_snoc
#print axioms historySupport_known
end
end ICO.C6BosonicHistorySupport

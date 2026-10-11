import ICO.C6BosonicLengthMasks
import ICO.C6BosonicHistorySupport

namespace ICO.C6BosonicQueryAlgebra
open QIT ICO.C6FockQueryMatrix ICO.C6BosonicHistorySupport ICO.C6BosonicFockSupport
  ICO.C6BosonicFockRotated ICO.C6CacheSpanProjection ICO.C6BosonicFreshRotated
  ICO.MHFockTransport ICO.MHFockCovariance ICO.MHFockBothCovariance
  ICO.MHFockRotation ICO.MHBoundedRecording ICO.MHSectorCovariance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem query_mul (P Q : CMatrix A) (T : ℕ) :
    queryMatrix (P*Q) T=queryMatrix P T*queryMatrix Q T := by
  unfold queryMatrix
  rw [inputFamily_mul]
  congr 1
  funext n r
  simp only [queryFamily,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.one_mul]

theorem query_adjoint (P : CMatrix A) (T : ℕ) :
    queryMatrix P.conjTranspose T=(queryMatrix P T).conjTranspose := by
  rw [queryMatrix,queryMatrix,inputFamily_adjoint]
  congr 1
  funext n r
  simp [queryFamily,Matrix.conjTranspose_kronecker]

theorem query_unitary (U : Matrix.unitaryGroup A ℂ) (T : ℕ) :
    queryMatrix (U:CMatrix A) T=(fockQuery U T:CMatrix (InputCutoff (α:=A) T)) := rfl

theorem query_one (T : ℕ) : queryMatrix (1:CMatrix A) T=1 :=
  ICO.C6BosonicFockRotated.query_one T

theorem query_sub (P Q : CMatrix A) (T : ℕ) :
    queryMatrix (P-Q) T=queryMatrix P T-queryMatrix Q T := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  by_cases hs : s=s'
  · subst s'
    simp only [Matrix.sub_apply]
    rw [queryMatrix_entry_same (P-Q),queryMatrix_entry_same P,queryMatrix_entry_same Q]
    simp only [Matrix.sub_apply]
    ring
  · simp only [Matrix.sub_apply]
    rw [queryMatrix_entry_other (P-Q) T _ _ hs,queryMatrix_entry_other P T _ _ hs,
      queryMatrix_entry_other Q T _ _ hs,sub_self]

theorem query_projection (P : CMatrix A) (hP : IsStarProjection P) (T : ℕ) :
    IsStarProjection (queryMatrix P T) := by
  constructor
  · change queryMatrix P T*queryMatrix P T=queryMatrix P T
    rw [←query_mul,hP.isIdempotentElem.eq]
  · change (queryMatrix P T).conjTranspose=queryMatrix P T
    have hp : P.conjTranspose=P := hP.isSelfAdjoint.star_eq
    rw [←query_adjoint,hp]

theorem query_diagonal (f : A→ℂ) (T : ℕ) :
    queryMatrix (Matrix.diagonal f) T=Matrix.diagonal (fun i : InputCutoff (α:=A) T => f i.2.1) := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  by_cases hs : s=s'
  · subst s'
    rw [queryMatrix_entry_same]
    simp only [Matrix.diagonal_apply]
    by_cases hx : x=y <;> by_cases hp : p=p' <;> by_cases hq : q=q' <;>
      simp_all [Sigma.mk.inj_iff,Prod.mk.injEq]
  · rw [queryMatrix_entry_other _ _ _ _ hs]
    have hn : (⟨⟨s,q⟩,(x,p)⟩ : InputCutoff (α:=A) T)≠⟨⟨s',q'⟩,(y,p')⟩ := by
      intro he
      exact hs (congrArg (fun i : InputCutoff (α:=A) T => i.1.1) he)
    simp [Matrix.diagonal_apply,hn]

theorem query_complement (S : Finset A) (T : ℕ) :
    queryFresh S T=1-queryMatrix (coordinateProjection S) T := by
  rw [coordinateProjection,query_diagonal]
  ext i j
  simp only [queryFresh,Matrix.diagonal_apply,Matrix.sub_apply,Matrix.one_apply]
  by_cases hij : i=j <;> by_cases hi : i.2.1∈S <;> simp_all

theorem rotatedFresh_complement (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (T : ℕ) :
    rotatedFresh U S T=1-queryMatrix (spanProjection U S) T := by
  unfold rotatedFresh spanProjection
  rw [query_complement,query_mul,query_mul,query_adjoint,query_unitary]
  have hu : (fockQuery U T:CMatrix (InputCutoff (α:=A) T))*
      (fockQuery U T:CMatrix (InputCutoff (α:=A) T)).conjTranspose=1 := (fockQuery U T).property.2
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hu]

theorem query_support (P Q : CMatrix A) (T : ℕ) :
    queryMatrix P T*fockSupport Q T=fockSupport Q T*queryMatrix P T := by
  unfold queryMatrix fockSupport
  rw [inputFamily_mul,inputFamily_mul]
  congr 1
  funext n r
  simp only [queryFamily,supportSector,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
    ←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul,Matrix.mul_one]

theorem mask_family (F : ∀ n r,CMatrix (Sector (α:=A) n r)) (m T : ℕ) :
    rightLengthMask m T*inputFamily F T=inputFamily F T*rightLengthMask m T := by
  rw [rightLengthMask_diagonal]
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hs : s=s'
  · subst s'
    exact mul_comm _ _
  · rw [inputFamily_other _ _ _ _ hs]
    simp

#print axioms rotatedFresh_complement
#print axioms query_support
#print axioms mask_family
end
end ICO.C6BosonicQueryAlgebra

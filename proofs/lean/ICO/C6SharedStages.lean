import ICO.C6SharedBasis
import ICO.DoubleQuerySchedule

/-! Each tagged hidden-basis query is exactly U†, a fixed private-copy
isometry, and U. The unknown Haar unitary acts on A only; the tag is memory. -/
namespace ICO.C6SharedStages
open Matrix QIT ICO.LudersUnitaryStages ICO.RecordingPublicStep
open ICO.C6SharedBasis
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option Elab.async false
variable {A M N E : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
  [Fintype E] [DecidableEq E]

def lift (X : CMatrix (A×Bool)) : CMatrix ((A×Bool)×M) :=
  Matrix.kronecker X (1:CMatrix M)

theorem lift_mul (X Y : CMatrix (A×Bool)) :
    lift (M:=M) (X*Y)=lift (M:=M) X*lift Y := by
  simpa [lift,Matrix.kronecker] using Matrix.mul_kronecker_mul X Y (1:CMatrix M) 1

theorem lift_star (X : CMatrix (A×Bool)) : (lift (M:=M) X)ᴴ=lift (M:=M) Xᴴ := by
  simpa [lift,Matrix.kronecker] using Matrix.conjTranspose_kronecker X (1:CMatrix M)

theorem lift_one : lift (A:=A) (M:=M) 1=1 := by
  exact Matrix.one_kronecker_one

theorem lift_isometry (U : Matrix.unitaryGroup (A×Bool) ℂ) :
    (lift (M:=M) (U:CMatrix (A×Bool)))ᴴ*lift (M:=M) (U:CMatrix (A×Bool))=1 := by
  have hU : (U:CMatrix (A×Bool))ᴴ*(U:CMatrix (A×Bool))=1 := U.property.1
  rw [lift_star,←lift_mul,hU,lift_one]

/-- The new private outcome is the whole (basis index, choice bit) pair. -/
def middle (H : Matrix.unitaryGroup A ℂ) :
    Matrix ((A×Bool)×((A×Bool)×M)) ((A×Bool)×M) ℂ :=
  lift (M:=(A×Bool)×M) (knownBasis H:CMatrix (A×Bool))*
    copyQuery*lift (M:=M) (knownBasis H:CMatrix (A×Bool))ᴴ

theorem middle_isometry (H : Matrix.unitaryGroup A ℂ) :
    (middle (M:=M) H)ᴴ*middle (M:=M) H=1 := by
  have hF := lift_isometry (M:=(A×Bool)×M) (knownBasis H)
  have hFc : (lift (M:=M) (knownBasis H:CMatrix (A×Bool))ᴴ)ᴴ*
      lift (M:=M) (knownBasis H:CMatrix (A×Bool))ᴴ=1 := by
    have hF' : (knownBasis H:CMatrix (A×Bool))*(knownBasis H:CMatrix (A×Bool))ᴴ=1 :=
      (knownBasis H).property.2
    rw [lift_star,Matrix.conjTranspose_conjTranspose,←lift_mul,hF',lift_one]
  simp only [middle,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (lift (M:=(A×Bool)×M) (knownBasis H:CMatrix (A×Bool)))ᴴ,hF,Matrix.one_mul]
  rw [←Matrix.mul_assoc (copyQuery (A:=A×Bool) (M:=M))ᴴ,
    copyQuery_isometry,Matrix.one_mul]
  exact hFc

def step (U H : Matrix.unitaryGroup A ℂ)
    (K : Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ) :
    Matrix ((A×Bool)×(((A×Bool)×E)×N)) ((A×Bool)×(E×M)) ℂ :=
  publicStep (h:=E) K * lift (M:=(A×Bool)×(E×M)) (shared U:CMatrix (A×Bool))*
    middle H*lift (M:=E×M) (shared U:CMatrix (A×Bool))ᴴ

theorem step_eq_luders (U H : Matrix.unitaryGroup A ℂ)
    (K : Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ) :
    step (E:=E) U H K=ICO.PrivateQueryStep.luders (basis U H:CMatrix (A×Bool)) K := by
  rw [←ICO.LudersUnitaryStages.step_eq_luders]
  have hG : (basis U H:CMatrix (A×Bool))=
      (shared U:CMatrix (A×Bool))*(knownBasis H:CMatrix (A×Bool)) :=
    congrArg (fun V : Matrix.unitaryGroup (A×Bool) ℂ => (V:CMatrix (A×Bool))) (basis_factor U H)
  simp only [step,ICO.LudersUnitaryStages.step,hG,Matrix.conjTranspose_mul]
  change _=publicStep (h:=E) K*lift ((shared U:CMatrix (A×Bool))*(knownBasis H:CMatrix (A×Bool)))*
    copyQuery*lift ((knownBasis H:CMatrix (A×Bool))ᴴ*(shared U:CMatrix (A×Bool))ᴴ)
  simp only [lift_mul,middle,Matrix.mul_assoc]

/-- Reassociate the public tag into memory so every unknown query has size d. -/
def regroup (M : Type) : ((A×Bool)×M) ≃ A×(Bool×M) := Equiv.prodAssoc A Bool M

theorem shared_regroup (U : Matrix.unitaryGroup A ℂ) :
    (lift (M:=M) (shared U:CMatrix (A×Bool))).submatrix (regroup M).symm (regroup M).symm =
      Matrix.kronecker (U:CMatrix A) (1:CMatrix (Bool×M)) := by
  ext ⟨a,b,m⟩ ⟨c,e,n⟩
  simp [lift,shared_matrix,regroup,Matrix.submatrix_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Prod.mk.injEq,ite_and]
  split_ifs <;> simp_all

#print axioms step_eq_luders
#print axioms shared_regroup
end
end ICO.C6SharedStages

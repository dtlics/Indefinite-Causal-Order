import ICO.AllChannelDilation
import ICO.SwitchObservable

namespace ICO.LudersDilation
open Matrix QIT ICO.SwitchObservable ICO.ClassicalDilation
open scoped BigOperators
noncomputable section
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
set_option maxHeartbeats 900000

def copyBasis : Matrix (A×A) A ℂ := fun o i => if o.1=i ∧ o.2=i then 1 else 0

def sandwich (U : CMatrix A) : Matrix (A×A) A ℂ :=
  Matrix.kronecker U (1 : CMatrix A) * copyBasis * U.conjTranspose

theorem sandwich_entry (U : CMatrix A) (o j i : A) :
    sandwich U (o,j) i = basisProjection U j o i := by
  simp [sandwich,copyBasis,basisProjection,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.single,
    Matrix.conjTranspose_apply,ite_and]

theorem sandwich_eq_stinespring (U : CMatrix A) :
    sandwich U = MatrixMap.krausStinespringMatrix (basisProjection U) := by
  ext o i
  exact sandwich_entry U o.1 o.2 i

theorem sandwich_isometry (U : Matrix.unitaryGroup A ℂ) :
    (sandwich (U : CMatrix A)).conjTranspose * sandwich (U : CMatrix A)=1 := by
  rw [sandwich_eq_stinespring]
  apply MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
  simpa only [MatrixMap.krausAdjoint,Matrix.mul_one] using
    hidden_basis_kraus_complete (U : CMatrix A) U.property.1 U.property.2

/-- Discarding the inaccessible copied coordinate gives exactly the ordinary
nonselective hidden-basis measurement channel. -/
theorem sandwich_erasure (U : CMatrix A) (X : CMatrix A) :
    partialTraceB (sandwich U * X * (sandwich U).conjTranspose)=
      MatrixMap.ofKraus (basisProjection U) X := by
  rw [sandwich_eq_stinespring]
  ext y y'
  simp [partialTraceB,MatrixMap.ofKraus,MatrixMap.krausStinespringMatrix,
    Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_comm

def memorySandwich (U : CMatrix A) : Matrix ((A×M)×A) (A×M) ℂ :=
  fun o i => sandwich U (o.1.1,o.2) i.1 * (if o.1.2=i.2 then 1 else 0)

theorem memorySandwich_eq_stinespring (U : CMatrix A) :
    memorySandwich (M:=M) U = MatrixMap.krausStinespringMatrix
      (fun j => Matrix.kronecker (basisProjection U j) (1 : CMatrix M)) := by
  ext o i
  simp only [memorySandwich,sandwich_entry,MatrixMap.krausStinespringMatrix,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]

theorem memorySandwich_isometry (U : Matrix.unitaryGroup A ℂ) :
    (memorySandwich (M:=M) (U : CMatrix A)).conjTranspose * memorySandwich (M:=M) (U : CMatrix A)=1 := by
  rw [memorySandwich_eq_stinespring]
  apply MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
  simpa only [MatrixMap.krausAdjoint,Matrix.mul_one] using
    ICO.AllChannelDilation.oracle_complete (M:=M) (basisProjection (U : CMatrix A))
      (hidden_basis_kraus_complete _ U.property.1 U.property.2)

theorem memorySandwich_erasure (U : CMatrix A) (X : CMatrix (A×M)) :
    partialTraceB (memorySandwich U * X * (memorySandwich U).conjTranspose)=
      ICO.AllChannelDilation.oracleMap (basisProjection U) X := by
  rw [memorySandwich_eq_stinespring]
  ext y y'
  simp [partialTraceB,ICO.AllChannelDilation.oracleMap,MatrixMap.ofKraus,
    MatrixMap.krausStinespringMatrix,Matrix.sum_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_comm

#print axioms memorySandwich_erasure
#print axioms memorySandwich_isometry
end
end ICO.LudersDilation

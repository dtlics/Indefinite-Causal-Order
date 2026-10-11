import ICO.ClassicalDilation

/-! # An actual oracle call on a discarded register

The input is retained as private memory, a fresh query register is initialized,
the unknown unitary is applied to that register, and the register is discarded.
The induced channel on the retained input is exactly the identity.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.ClassicalDilation

namespace ICO.OraclePadding

set_option maxHeartbeats 250000
noncomputable section
universe u
variable {A C : Type u}
variable [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]

def tensorVector (v : A → ℂ) : Matrix (A × C) C ℂ :=
  fun ac c => v ac.1 * (1 : CMatrix C) ac.2 c

theorem tensorVector_sandwich (v : A → ℂ) (X : CMatrix C) :
    tensorVector v * X * (tensorVector v).conjTranspose =
      Matrix.kronecker (rankOneMatrix v) X := by
  ext i j
  simp [tensorVector, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, rankOneMatrix_apply,
    apply_ite, ite_mul, mul_ite, eq_comm]
  ring

theorem oracle_tensorVector (U : CMatrix A) (v : A → ℂ) :
    Matrix.kronecker U (1 : CMatrix C) * tensorVector v = tensorVector (U *ᵥ v) := by
  ext i j
  simp [tensorVector, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]

def basisVector (a₀ : A) : A → ℂ := fun a => if a = a₀ then 1 else 0

def pad (a₀ : A) : Matrix (A × C) C ℂ := tensorVector (basisVector a₀)

theorem pad_isometry (a₀ : A) :
    (pad (C := C) a₀).conjTranspose * pad (C := C) a₀ = (1 : CMatrix C) := by
  ext i j
  simp [pad, tensorVector, basisVector, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite, ite_mul, mul_ite]
  aesop

def discardKraus (a : A) : Matrix C (A × C) ℂ :=
  fun c ac => if a = ac.1 then (1 : CMatrix C) c ac.2 else 0

theorem discard_complete :
    (∑ a : A, (discardKraus (C := C) a).conjTranspose * discardKraus a) = 1 := by
  ext i j
  simp [discardKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.one_apply, apply_ite, ite_mul, mul_ite, Prod.ext_iff]
  aesop

theorem discard_apply (X : CMatrix (A × C)) :
    MatrixMap.ofKraus (discardKraus (A := A) (C := C)) X = partialTraceA X := by
  ext i j
  simp [MatrixMap.ofKraus, discardKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.one_apply, Fintype.sum_prod_type, apply_ite,
    ite_mul, mul_ite, partialTraceA]

theorem oracle_basis_trace (U : Matrix.unitaryGroup A ℂ) (a₀ : A) :
    (rankOneMatrix ((U : CMatrix A) *ᵥ basisVector a₀)).trace = 1 := by
  have h := congrFun (congrFun (Matrix.UnitaryGroup.star_mul_self U) a₀) a₀
  simpa [rankOneMatrix_apply, basisVector, Matrix.trace, Matrix.diag_apply,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using h

theorem discarded_oracle_identity (U : Matrix.unitaryGroup A ℂ) (a₀ : A)
    (X : CMatrix C) :
    MatrixMap.ofKraus (discardKraus (A := A) (C := C))
      ((oracleChannel U).map (pad a₀ * X * (pad a₀).conjTranspose)) = X := by
  rw [discard_apply, oracleChannel_apply]
  have hs : Matrix.kronecker (U : CMatrix A) (1 : CMatrix C) *
      (pad a₀ * X * (pad a₀).conjTranspose) *
        (Matrix.kronecker (U : CMatrix A) (1 : CMatrix C)).conjTranspose =
      tensorVector ((U : CMatrix A) *ᵥ basisVector a₀) * X *
        (tensorVector ((U : CMatrix A) *ᵥ basisVector a₀)).conjTranspose := by
    rw [← oracle_tensorVector]
    simp only [pad, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hs, tensorVector_sandwich, partialTraceA_kronecker, oracle_basis_trace]
  exact one_smul ℂ X

def discardChannel : Channel (A × C) C where
  map := MatrixMap.ofKraus (discardKraus (A := A) (C := C))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using (discard_complete (A := A) (C := C)))
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem discarded_oracle_precomposed {B : Type u} [Fintype B] [DecidableEq B]
    (U : Matrix.unitaryGroup A ℂ) (a₀ : A) (W : Matrix C B ℂ) (X : CMatrix B) :
    (discardChannel (A := A) (C := C)).map ((oracleChannel U).map
      ((pad (C := C) a₀ * W) * X * (pad (C := C) a₀ * W).conjTranspose)) =
        W * X * W.conjTranspose := by
  have heq : (pad (C := C) a₀ * W) * X * (pad (C := C) a₀ * W).conjTranspose =
      pad (C := C) a₀ * (W * X * W.conjTranspose) * (pad (C := C) a₀).conjTranspose := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h := congrArg (fun Y : CMatrix (A × C) =>
    (discardChannel (A := A) (C := C)).map ((oracleChannel U).map Y)) heq
  exact h.trans (discarded_oracle_identity U a₀ (W * X * W.conjTranspose))

def paddedIdentity (U : Matrix.unitaryGroup A ℂ) (a₀ : A) : Channel C C :=
  (discardChannel (A := A) (C := C)).comp
    ((oracleChannel U).comp (isometryChannel (pad a₀) (pad_isometry a₀)))

theorem paddedIdentity_map (U : Matrix.unitaryGroup A ℂ) (a₀ : A) :
    (paddedIdentity (C := C) U a₀).map = (Channel.idChannel C).map := by
  ext X i j
  simpa [paddedIdentity, Channel.comp, discardChannel, isometryChannel_apply,
    Channel.idChannel, MatrixMap.ofKraus] using
    congrFun (congrFun (discarded_oracle_identity U a₀ X) i) j

end
end ICO.OraclePadding

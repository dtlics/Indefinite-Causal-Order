import ICO.MHSymmetric

/-! Tensor powers of arbitrary matrices, including projections, in the
literal recursive word register. -/
namespace ICO.C6WordPower
open Matrix QIT
open scoped Matrix
noncomputable section
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A]

def wordPower (M : CMatrix A) : (n : ℕ) → CMatrix (TensorPower A n)
  | 0 => 1
  | n+1 => Matrix.kronecker M (wordPower M n)

@[simp] theorem wordPower_zero (M : CMatrix A) : wordPower M 0 = 1 := rfl
theorem wordPower_succ (M : CMatrix A) (n : ℕ) :
    wordPower M (n+1) = Matrix.kronecker M (wordPower M n) := rfl

theorem wordPower_mul (M N : CMatrix A) (n : ℕ) :
    wordPower (M*N) n = wordPower M n * wordPower N n := by
  induction n with
  | zero => simp [wordPower]
  | succ n ih =>
    simp only [wordPower_succ, ih, Matrix.kronecker]
    exact Matrix.mul_kronecker_mul M N (wordPower M n) (wordPower N n)

@[simp] theorem wordPower_one (n : ℕ) : wordPower (1 : CMatrix A) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x y
    rcases x with ⟨x,xs⟩
    rcases y with ⟨y,ys⟩
    simp only [wordPower_succ, ih, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.mk.injEq, ite_and]
    erw [Matrix.one_apply]
    simp only [Prod.mk.injEq, ite_and]
    split_ifs <;> simp

theorem wordPower_adjoint (M : CMatrix A) (n : ℕ) :
    wordPower M.conjTranspose n = (wordPower M n).conjTranspose := by
  induction n with
  | zero => simp [wordPower]
  | succ n ih =>
    ext x y
    simp [wordPower_succ, ih, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, star_mul, mul_comm]

theorem wordPower_unitary (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    wordPower (U : CMatrix A) n = (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wordPower_succ, ih, unitaryTensorPowerMatrix_succ]

theorem wordPower_projection (P : CMatrix A) (hP : IsStarProjection P) (n : ℕ) :
    IsStarProjection (wordPower P n) := by
  constructor
  · change wordPower P n * wordPower P n = wordPower P n
    rw [← wordPower_mul, hP.isIdempotentElem.eq]
  · change (wordPower P n).conjTranspose = wordPower P n
    have hp : P.conjTranspose=P := hP.isSelfAdjoint.star_eq
    rw [← wordPower_adjoint, hp]

theorem wordPower_absorption (P Q : CMatrix A) (h : P*Q=P) (n : ℕ) :
    wordPower P n * wordPower Q n = wordPower P n := by
  rw [← wordPower_mul, h]

theorem wordPower_conjugate (U : Matrix.unitaryGroup A ℂ) (P : CMatrix A) (n : ℕ) :
    wordPower ((U : CMatrix A)*P*(U : CMatrix A).conjTranspose) n =
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n))*wordPower P n*
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n)).conjTranspose := by
  rw [wordPower_mul, wordPower_mul, wordPower_adjoint, wordPower_unitary]

#print axioms wordPower_projection
#print axioms wordPower_conjugate
#print axioms wordPower_absorption
end
end ICO.C6WordPower

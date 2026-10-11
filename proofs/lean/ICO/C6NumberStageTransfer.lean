import ICO.C6RotatedNumberContinuation
import ICO.MHRectangularAction

namespace ICO.C6NumberStageTransfer
open Matrix QIT ICO.C6RotatedNumberContinuation ICO.C6NumberRotationAlgebra
  ICO.MHFockKnownOperation ICO.MHBoundedRecording ICO.MHRectangularAction
noncomputable section
set_option maxHeartbeats 700000
set_option Elab.async false
variable {A M N:Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem tensor_sandwich {X:Type*} [Fintype X] [DecidableEq X]
    (L P D:CMatrix X) (C:CMatrix M) (h:L*D*P=D*P) :
    Matrix.kronecker L (1:CMatrix M)*Matrix.kronecker D C*
      Matrix.kronecker P (1:CMatrix M)=
        Matrix.kronecker D C*Matrix.kronecker P (1:CMatrix M) := by
  simp only [Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
    ←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one,h]

theorem stage_sandwich (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k l T:ℕ)
    (D:CMatrix (InputCutoff (α:=A) T)) (C:CMatrix M) (K:Matrix (A×N) (A×M) ℂ)
    (h:rotatedNumber U S l T*D*rotatedNumber U S k T=D*rotatedNumber U S k T) :
    Matrix.kronecker (rotatedNumber U S l T) (1:CMatrix N)*
      (known T K*Matrix.kronecker D C)*
        Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix M)=
      (known T K*Matrix.kronecker D C)*
        Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix M) := by
  rw [←Matrix.mul_assoc,known_preserves_rotated_number]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (Matrix.kronecker (rotatedNumber U S l T) (1:CMatrix M)),
    tensor_sandwich _ _ _ _ h]

theorem stage_preserves (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (k T:ℕ)
    (D:CMatrix (InputCutoff (α:=A) T)) (C:CMatrix M) (K:Matrix (A×N) (A×M) ℂ)
    (h:rotatedNumber U S k T*D=D*rotatedNumber U S k T) :
    Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix N)*
      (known T K*Matrix.kronecker D C)=
      (known T K*Matrix.kronecker D C)*
        Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix M) := by
  have he:Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix M)*Matrix.kronecker D C=
      Matrix.kronecker D C*Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix M) := by
    simp only [Matrix.kronecker]
    rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
      Matrix.one_mul,Matrix.mul_one,h]
  rw [←Matrix.mul_assoc,known_preserves_rotated_number,Matrix.mul_assoc,he,
    ←Matrix.mul_assoc]

theorem action_sandwich {X Y:Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (L:CMatrix Y) (P:CMatrix X) (D:Matrix Y X ℂ)
    (h:L*D*P=D*P) (v:EuclideanSpace ℂ X) (hv:rectAct P v=v) :
    rectAct L (rectAct D v)=rectAct D v := by
  calc
    _ = rectAct (L*D*P) v := by rw [rectAct_mul,rectAct_mul,hv]
    _ = rectAct (D*P) v := by rw [h]
    _ = _ := by rw [rectAct_mul,hv]

theorem action_preserves {X Y:Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (L:CMatrix Y) (P:CMatrix X) (D:Matrix Y X ℂ)
    (h:L*D=D*P) (v:EuclideanSpace ℂ X) (hv:rectAct P v=v) :
    rectAct L (rectAct D v)=rectAct D v := by
  rw [←rectAct_mul,h,rectAct_mul,hv]

#print axioms stage_sandwich
end
end ICO.C6NumberStageTransfer

import ICO.C6RotatedNumberContinuation
import ICO.C6BosonicBlocks

/-! Every actual query matrix preserves the private occupation projectors,
including the rank-one measurement and its accessible outcome slices. -/
namespace ICO.C6FlagQueryAlgebra
open Matrix QIT ICO.C6RotatedNumberContinuation ICO.C6NumberRotationAlgebra
  ICO.C6BosonicBlocks ICO.C6FockQueryMatrix ICO.MHFockKnownOperation
  ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 700000
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem query_preserves_rotated_number (U:Matrix.unitaryGroup A ℂ) (S:Finset A)
    (k T:ℕ) (P:CMatrix A) :
    rotatedNumber U S k T*queryMatrix P T=queryMatrix P T*rotatedNumber U S k T := by
  let K:Matrix (A×Unit) (A×Unit) ℂ:=Matrix.kronecker P (1:CMatrix Unit)
  have he:=congrArg (fun M:Matrix (ICO.MHBoundedRecording.InputCutoff (α:=A) T×Unit)
      (ICO.MHBoundedRecording.InputCutoff (α:=A) T×Unit) ℂ=>block M () ())
    (known_preserves_rotated_number U S k T K)
  dsimp only at he
  rw [block_left_tensor] at he
  have hf:Matrix.kronecker (rotatedNumber U S k T) (1:CMatrix Unit)=
      diagonalFamily (fun _:Unit=>rotatedNumber U S k T) := by
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,diagonalFamily]
    split_ifs <;> simp
  rw [hf,block_right_family,known_block] at he
  have hk:(fun a b=>K (a,()) (b,()))=P := by
    ext a b
    simp only [K,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,ite_true,mul_one]
  rwa [hk] at he

#print axioms query_preserves_rotated_number
end
end ICO.C6FlagQueryAlgebra

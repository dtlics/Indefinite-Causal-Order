import ICO.C6RotatedNumberContinuation
import ICO.MHFockEmptyRotation

namespace ICO.C6FlagVacuum
open Matrix QIT ICO.C6RotatedNumberContinuation ICO.C6NumberRotationAlgebra
  ICO.C6FockNumber ICO.C6BosonicCacheSupport ICO.C6BosonicSupport
  ICO.MHFockTrajectory ICO.MHFockEmptyRotation ICO.MHFockRotation ICO.MHSectorCovariance
  ICO.MHFockSpace ICO.MHBoundedRecording
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 800000
set_option Elab.async false
variable {A M:Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M]

theorem labelNumber_le (S:Finset A) {n:ℕ} (p:TensorPowerProfile (A×A) n) :
    labelNumber S p≤n := by
  calc
    _ ≤ ∑z:A×A,p.val z := Finset.sum_le_sum (by intro z hz; split_ifs <;> simp)
    _ = n := tensorPowerTypeProfile_sum_of_mem_profiles n p.property

theorem vacuum_number (S:Finset A) (T:ℕ) (z:A×M→ℂ) :
    Matrix.kronecker (rightNumber S 0 T) (1:CMatrix M)*ᵥinitial T z=initial T z := by
  have hd:Matrix.kronecker (rightNumber S 0 T) (1:CMatrix M)=
      Matrix.diagonal (fun j:InputCutoff (α:=A) T×M=>if labelNumber S j.1.1.2=0 then 1 else 0) := by
    rw [rightNumber,rightDiagonal]
    change Matrix.kronecker (Matrix.diagonal _) (Matrix.diagonal (fun _:M=>(1:ℂ)))=_
    rw [Matrix.kronecker,Matrix.diagonal_kronecker_diagonal]
    simp only [mul_one]
  rw [hd]
  ext i
  rw [Matrix.mulVec_diagonal]
  by_cases hz:initial T z i=0
  · simp [hz]
  · have hg:=initial_grade T z i hz
    have hn:=labelNumber_le S i.1.1.2
    have he:labelNumber S i.1.1.2=0 := by change i.1.1.1.val.1.val+i.1.1.1.val.2.val≤0 at hg; omega
    rw [if_pos he,one_mul]

theorem vacuum_rotated_number (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (T:ℕ) (z:A×M→ℂ) :
    Matrix.kronecker (rotatedNumber U S 0 T) (1:CMatrix M)*ᵥinitial T z=initial T z := by
  let R:CMatrix (InputCutoff (α:=A) T×M):=
    Matrix.kronecker (fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix M)
  have hi:Rᴴ*R=1:=(tensorUnitary (fockQ U 1 T) 1).property.1
  have hf:R*ᵥinitial T z=initial T z:=empty_rotation_fixed U 1 T z
  have ha:Rᴴ*ᵥinitial T z=initial T z := by
    calc
      _ = Rᴴ*ᵥ(R*ᵥinitial T z) := by rw [hf]
      _ = _ := by rw [Matrix.mulVec_mulVec,hi,Matrix.one_mulVec]
  rw [rotated_number_tensor]
  change (R*Matrix.kronecker (rightNumber S 0 T) (1:CMatrix M)*Rᴴ)*ᵥinitial T z=_
  rw [←Matrix.mulVec_mulVec,ha,←Matrix.mulVec_mulVec,vacuum_number,hf]

#print axioms vacuum_rotated_number
end
end ICO.C6FlagVacuum

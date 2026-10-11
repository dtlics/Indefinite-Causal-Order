import ICO.QubitCPTPGauge

namespace ICO.QubitTensorGauge
open ICO.QubitCPTPGauge
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

abbrev SlotCoord := Fin 4 × Fin 4
abbrev TwoSlotTensor := Matrix SlotCoord SlotCoord ℂ

def basisMatrix : Matrix SlotCoord (Fin 13) ℂ := fun s k => pauliBasis k s.1 s.2

def lambdaMatrix : Matrix SlotCoord SlotCoord ℂ := fun s t =>
  ICO.QubitGaugeCertificates.lambdaCoeff s.1.val s.2.val t.1.val t.2.val

theorem lambda_gram : lambdaMatrix = basisMatrix * basisMatrixᴴ := by
  ext s t
  rw [Matrix.mul_apply]
  change (ICO.QubitGaugeCertificates.lambdaCoeff s.1.val s.2.val t.1.val t.2.val : ℂ) = _
  rw [lambdaCoeff_complex]
  apply Finset.sum_congr rfl
  intro k hk
  have h := congrFun (congrFun (pauliBasis_hermitian k).eq t.2) t.1
  simpa [basisMatrix, Matrix.conjTranspose_apply] using congrArg (fun z => pauliBasis k s.1 s.2 * z) h.symm

def contract (C : TwoSlotTensor) (A B : SlotMatrix) : ℂ :=
  ∑ s : SlotCoord, ∑ t : SlotCoord, A s.1 s.2 * C s t * B t.1 t.2

def contraction (C : TwoSlotTensor) : SlotMatrix →ₗ[ℂ] SlotMatrix →ₗ[ℂ] ℂ where
  toFun A :=
    { toFun := contract C A
      map_add' B D := by simp [contract, add_mul, mul_add, Finset.sum_add_distrib]
      map_smul' z B := by simp [contract, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] }
  map_add' A D := by ext B; simp [contract, add_mul, Finset.sum_add_distrib]
  map_smul' z A := by ext B; simp [contract, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem channel_transpose (J : SlotMatrix) (h : IsChannelChoi J) : IsChannelChoi Jᵀ := by
  refine ⟨h.1.transpose, ?_⟩
  intro i j
  simpa [traceOutput, Matrix.transpose_apply, eq_comm] using h.2 j i

def transposedContraction (C : TwoSlotTensor) : SlotMatrix →ₗ[ℂ] SlotMatrix →ₗ[ℂ] ℂ where
  toFun A :=
    { toFun := fun B => contract C Aᵀ Bᵀ
      map_add' B D := by simp [contract, Matrix.transpose_add, add_mul, mul_add, Finset.sum_add_distrib]
      map_smul' z B := by simp [contract, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] }
  map_add' A D := by ext B; simp [contract, Matrix.transpose_add, add_mul, Finset.sum_add_distrib]
  map_smul' z A := by ext B; simp [contract, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem middle_entry (C : TwoSlotTensor) (k l : Fin 13) :
    (basisMatrixᴴ * C * basisMatrixᴴᵀ) k l =
      contract C (pauliBasis k)ᵀ (pauliBasis l)ᵀ := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    basisMatrix, contract, Finset.sum_mul]
  have hstar (j : Fin 13) (s : SlotCoord) :
      star (pauliBasis j s.1 s.2) = pauliBasis j s.2 s.1 :=
    congrFun (congrFun (pauliBasis_hermitian j).eq s.2) s.1
  simp_rw [hstar]
  exact Finset.sum_comm

/-- Equality against every pair of genuine CPTP qubit inputs kills the
concrete two-slot trace-preserving projection. The matrix on the left is
16 times Lambda_A Lambda_B, in matrix-coordinate tensor order. -/
theorem gauge_zero_of_channel_tests (C : TwoSlotTensor)
    (h : ∀ A B, IsChannelChoi A → IsChannelChoi B → contract C A B = 0) :
    lambdaMatrix * C * lambdaMatrixᵀ = 0 := by
  have hmiddle : basisMatrixᴴ * C * basisMatrixᴴᵀ = 0 := by
    ext k l
    rw [middle_entry]
    apply bilinear_vanishes_on_basis (transposedContraction C)
    intro A B hA hB
    exact h _ _ (channel_transpose A hA) (channel_transpose B hB)
  rw [lambda_gram, Matrix.transpose_mul]
  calc
    _ = basisMatrix * (basisMatrixᴴ * C * basisMatrixᴴᵀ) * basisMatrixᵀ := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hmiddle, Matrix.mul_zero, Matrix.zero_mul]

end
end ICO.QubitTensorGauge

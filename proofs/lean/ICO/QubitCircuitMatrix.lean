import ICO.CausalTensorRows
import ICO.TensorBitOrder

namespace ICO.QubitCircuitMatrix
open ICO.CausalTensorRows ICO.OrderedCombSemantics ICO.PositiveSupport
open Matrix
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

def encode6 (x : SixWires (Fin 2) (Fin 2) (Fin 4)) : Fin 128 :=
  ⟨64*x.1.1.1.1.1.val+32*x.1.1.1.1.2.val+16*x.1.1.1.2.val+
    8*x.1.1.2.val+4*x.1.2.val+x.2.val, by omega⟩

theorem decode_encode (x : SixWires (Fin 2) (Fin 2) (Fin 4)) : decode6 (encode6 x).val = x := by
  rcases x with ⟨⟨⟨⟨⟨p,ai⟩,ao⟩,bi⟩,bo⟩,f⟩
  ext <;> dsimp [encode6, decode6, decode5, decode4, decode3, decode2, bit, quad] <;> omega

theorem encode_decode (i : Fin 128) : encode6 (decode6 i.val) = i := by
  apply Fin.ext
  dsimp [encode6, decode6, decode5, decode4, decode3, decode2, bit, quad]
  omega

def wireEquiv : SixWires (Fin 2) (Fin 2) (Fin 4) ≃ Fin 128 where
  toFun := encode6
  invFun i := decode6 i.val
  left_inv := decode_encode
  right_inv := encode_decode

theorem decode_mod128 (i : Nat) : decode6 (i%128) = decode6 i := by
  ext <;> dsimp [decode6, decode5, decode4, decode3, decode2, bit, quad] <;> omega

def swapWires (x : SixWires (Fin 2) (Fin 2) (Fin 4)) : SixWires (Fin 2) (Fin 2) (Fin 4) :=
  (((((x.1.1.1.1.1,x.1.1.2),x.1.2),x.1.1.1.1.2),x.1.1.1.2),x.2)

theorem swapWires_twice (x : SixWires (Fin 2) (Fin 2) (Fin 4)) :
    swapWires (swapWires x) = x := by
  rcases x with ⟨⟨⟨⟨⟨p,ai⟩,ao⟩,bi⟩,bo⟩,f⟩
  rfl

theorem decode_swap (i : Nat) :
    decode6 (ICO.ExactTensorCertificates.swapSlots i) = swapWires (decode6 i) := by
  have h : ICO.ExactTensorCertificates.swapSlots i = (encode6 (swapWires (decode6 i))).val := by
    dsimp [ICO.ExactTensorCertificates.swapSlots, encode6, swapWires,
      decode6, decode5, decode4, decode3, decode2, bit, quad]
    norm_num only [Nat.div_div_eq_div_mul]
    ring
  rw [h, decode_encode]

variable {M N K : Type*} [Fintype M] [Fintype N] [Fintype K]
  [DecidableEq M] [DecidableEq N] [DecidableEq K]

def circuitMatrix (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) : Matrix (Fin 128) (Fin 128) ℂ :=
  fun i j => circuitComb pre mid post (decode6 i.val) (decode6 j.val)

def circuitVectors (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) (k : K) : Fin 128 → ℂ :=
  fun i => (postLift post k *ᵥ preMiddle pre mid) (decode6 i.val)

theorem matrix_decomposition (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) :
    circuitMatrix pre mid post = ∑ k, rankOne (circuitVectors pre mid post k) := by
  ext i j
  simp [circuitMatrix, circuitComb_decomposition, circuitVectors, rankOne,
    Matrix.vecMulVec_apply, Matrix.sum_apply]

theorem periodic_matrix (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) :
    TensorBitOrder.periodicTensor (circuitMatrix pre mid post) = circuitTensor pre mid post := by
  ext i j
  simp [TensorBitOrder.periodicTensor, TensorBitOrder.modIndex, circuitMatrix,
    circuitTensor, decode_mod128]

theorem matrix_abRows (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (hmid : midᴴ * mid = 1) (hpost : postᴴ * post = 1) (k : Nat) :
    TensorRowOperators.abRow k (TensorBitOrder.periodicTensor (circuitMatrix pre mid post)) = 0 := by
  rw [periodic_matrix]
  exact circuitTensor_rows pre mid post hmid hpost k

def reverseMatrix (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) : Matrix (Fin 128) (Fin 128) ℂ :=
  fun i j => circuitComb pre mid post (swapWires (decode6 i.val)) (swapWires (decode6 j.val))

def reverseVectors (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) (k : K) : Fin 128 → ℂ :=
  fun i => (postLift post k *ᵥ preMiddle pre mid) (swapWires (decode6 i.val))

theorem reverse_decomposition (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) :
    reverseMatrix pre mid post = ∑ k, rankOne (reverseVectors pre mid post k) := by
  ext i j
  simp [reverseMatrix, circuitComb_decomposition, reverseVectors, rankOne,
    Matrix.vecMulVec_apply, Matrix.sum_apply]

theorem matrix_baRows (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (hmid : midᴴ * mid = 1) (hpost : postᴴ * post = 1) (k : Nat) :
    TensorRowOperators.baRow k (TensorBitOrder.periodicTensor (reverseMatrix pre mid post)) = 0 := by
  have hh : TensorRowOperators.swapSlots (TensorBitOrder.periodicTensor (reverseMatrix pre mid post)) =
      circuitTensor pre mid post := by
    ext i j
    simp [TensorRowOperators.swapSlots, TensorBitOrder.periodicTensor, TensorBitOrder.modIndex,
      reverseMatrix, circuitTensor, decode_mod128, decode_swap, swapWires_twice]
  rw [TensorRowOperators.baRow, LinearMap.comp_apply, hh]
  exact circuitTensor_rows pre mid post hmid hpost k

#print axioms matrix_abRows
#print axioms matrix_decomposition
#print axioms matrix_baRows
end
end ICO.QubitCircuitMatrix

import ICO.OrderedCombSemantics
import ICO.TensorRowOperators
import Mathlib.Logic.Equiv.Fin.Basic

namespace ICO.CausalTensorRows
open ICO.OrderedCombSemantics ICO.TensorRowOperators ICO.PositiveSupport Matrix
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

variable {R : Type*} [CommRing R]

theorem traceDiscard_group (m n i j : Nat) (C : Tensor R) :
    traceDiscard (m*n) i j C =
      ∑ a : Fin m, traceDiscard n (m*i+a.val) (m*j+a.val) C := by
  simp only [traceDiscard_apply]
  have h := (finProdFinEquiv (m := m) (n := n)).sum_comp
    (fun h : Fin (m*n) => C ((m*n)*i+h.val) ((m*n)*j+h.val))
  rw [← h, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 1 <;> simp only [finProdFinEquiv_apply_val] <;> ring

/-- Hierarchical comb equations imply both eliminated homogeneous rows. -/
theorem rows_from_traces (C D E : Tensor R)
    (hC : ∀ i j, traceDiscard 4 i j C = if i%2 = j%2 then D (i/2) (j/2) else 0)
    (hD : ∀ i j, traceDiscard 2 i j D = if i%2 = j%2 then E (i/2) (j/2) else 0)
    (k : Nat) : abRow k C = 0 := by
  have ht8 (i j : Nat) : traceDiscard 8 i j C = 2*D i j := by
    rw [show 8 = 2*4 from rfl, traceDiscard_group]
    simp only [hC, Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
    have h0 (r : Nat) : 2*r%2 = 0 ∧ 2*r/2 = r := by omega
    have h1 (r : Nat) : (2*r+1)%2 = 1 ∧ (2*r+1)/2 = r := by omega
    simp [h0, h1]
    ring
  have ht16 (i j : Nat) : traceDiscard 16 i j C =
      if i%2 = j%2 then 2*E (i/2) (j/2) else 0 := by
    rw [show 16 = 2*8 from rfl, traceDiscard_group]
    simp only [ht8, ← Finset.mul_sum]
    change 2 * traceDiscard 2 i j D = _
    rw [hD]
    split_ifs <;> ring
  have ht32 (i j : Nat) : traceDiscard 32 i j C = 4*E i j := by
    rw [show 32 = 2*16 from rfl, traceDiscard_group]
    simp only [ht16, Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
    have h0 (r : Nat) : 2*r%2 = 0 ∧ 2*r/2 = r := by omega
    have h1 (r : Nat) : (2*r+1)%2 = 1 ∧ (2*r+1)/2 = r := by omega
    simp [h0, h1]
    ring
  unfold abRow causalRow
  split_ifs
  · simp only [causalOne, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      ite_apply, LinearMap.zero_apply, beq_iff_eq, hC, ht8]
    split_ifs <;> simp only [ht8, LinearMap.zero_apply] <;> ring
  · simp only [causalTwo, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      ite_apply, LinearMap.zero_apply, beq_iff_eq, ht16, ht32]
    split_ifs <;> simp only [ht32, LinearMap.zero_apply] <;> ring

def bit (i : Nat) : Fin 2 := ⟨i%2, Nat.mod_lt _ (by decide)⟩
def quad (i : Nat) : Fin 4 := ⟨i%4, Nat.mod_lt _ (by decide)⟩
def decode2 (i : Nat) : Fin 2 × Fin 2 := (bit (i/2), bit i)
def decode3 (i : Nat) : (Fin 2 × Fin 2) × Fin 2 := (decode2 (i/2), bit i)
def decode4 (i : Nat) : FourWires (Fin 2) (Fin 2) := (decode3 (i/2), bit i)
def decode5 (i : Nat) : FourWires (Fin 2) (Fin 2) × Fin 2 := (decode4 (i/2), bit i)
def decode6 (i : Nat) : SixWires (Fin 2) (Fin 2) (Fin 4) := (decode5 (i/4), quad i)

def circuitTensor {M N K : Type*} [Fintype M] [Fintype N] [Fintype K]
    [DecidableEq M] [DecidableEq N] [DecidableEq K]
    (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) : Tensor ℂ :=
  fun i j => circuitComb pre mid post (decode6 i) (decode6 j)

theorem decode6_shift (i : Nat) (f : Fin 4) :
    decode6 (4*i+f.val) = (decode5 i,f) := by
  unfold decode6
  congr 1
  · congr 1; omega
  · apply Fin.ext; dsimp [quad]; omega

theorem decode4_shift (i : Nat) (f : Fin 2) :
    decode4 (2*i+f.val) = (decode3 i,f) := by
  unfold decode4
  congr 1
  · congr 1; omega
  · apply Fin.ext; dsimp [bit]; omega

theorem bit_eq_iff (i j : Nat) : bit i = bit j ↔ i%2 = j%2 := Fin.ext_iff

/-- Every actual ordered qubit circuit obeys all 1088 certificate rows.
The theorem needs no normalization condition on its initial branch. -/
theorem circuitTensor_rows {M N K : Type*} [Fintype M] [Fintype N] [Fintype K]
    [DecidableEq M] [DecidableEq N] [DecidableEq K]
    (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (hmid : midᴴ * mid = 1) (hpost : postᴴ * post = 1) (k : Nat) :
    abRow k (circuitTensor pre mid post) = 0 := by
  let D : Tensor ℂ := fun i j => partialTrace (rankOne (preMiddle pre mid)) (decode4 i) (decode4 j)
  let E : Tensor ℂ := fun i j => preComb pre (decode2 i) (decode2 j)
  apply rows_from_traces _ D E
  · intro i j
    simp only [traceDiscard_apply, circuitTensor, decode6_shift]
    change partialTrace (circuitComb pre mid post) (decode5 i) (decode5 j) = _
    rw [circuitComb_trace pre mid post hpost]
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, decode5, D, bit_eq_iff]
  · intro i j
    simp only [traceDiscard_apply, D, decode4_shift]
    change partialTrace (partialTrace (rankOne (preMiddle pre mid))) (decode3 i) (decode3 j) = _
    rw [preMiddle_trace pre mid hmid]
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, decode3, E, bit_eq_iff]

#print axioms circuitTensor_rows
end
end ICO.CausalTensorRows

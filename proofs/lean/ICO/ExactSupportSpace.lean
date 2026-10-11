import ICO.ExactSupportRank
import ICO.ExactSupportIndependence
import ICO.SupportBasisCollection

/-! The actual finite support constraints have kernel equal to the range of
the tensor-defined 128-by-25 matrix E. This file does not yet interpret the
constraints as unitary-link tests. -/

namespace ICO.ExactSupportSpace
open ICO.ExactTensorCertificates ICO.SupportModularTree ICO.ExactSupportRank
open ICO.ExactSupportIndependence
open Matrix
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

def complexStack : Matrix (Fin 128) (Fin 128) ℂ :=
  GaussianInt.toComplex.mapMatrix stackedMatrix

def supportMatrix : Matrix (Fin 128) (Fin 25) ℂ :=
  fun r b => basisEntry r.val b.val

def tailMatrix : Matrix (Fin 128) (Fin 25) ℂ :=
  fun r b => if r.val = 103 + b.val then 1 else 0

theorem sumBelow_complex (n : Nat) (f : Nat → Int) :
    (sumBelow n f : ℂ) = ∑ k : Fin n, (f k.val : ℂ) := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp [sumBelow, Fin.sum_univ_castSucc, ih, Int.cast_add]

theorem stack_entry (r c : Fin 128) :
    complexStack r c = (gaussianEntry r.val c.val).1 +
      (gaussianEntry r.val c.val).2 * Complex.I := by
  rfl

theorem stack_basis_entry (r : Fin 128) (b : Fin 25) :
    (complexStack * supportMatrix) r b =
      (basisProductRe r.val b.val : ℂ) +
      (basisProductIm r.val b.val : ℂ) * Complex.I := by
  simp only [Matrix.mul_apply, stack_entry, supportMatrix,
    basisProductRe, basisProductIm, sumBelow_complex, Int.cast_mul,
    add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem stack_basis : complexStack * supportMatrix = tailMatrix := by
  ext r b
  rw [stack_basis_entry, (all_basis_entries r b).1, (all_basis_entries r b).2]
  simp [tailMatrix]

def tailIndex (b : Fin 25) : Fin 128 := ⟨103 + b.val, by omega⟩

theorem tail_mul_at_tail (x : Fin 25 → ℂ) (b : Fin 25) :
    (tailMatrix *ᵥ x) (tailIndex b) = x b := by
  simp [Matrix.mulVec, dotProduct, tailMatrix, tailIndex, Fin.val_inj]

theorem tail_mul_at_head (x : Fin 25 → ℂ) (r : Fin 128) (hr : r.val < 103) :
    (tailMatrix *ᵥ x) r = 0 := by
  have hne (b : Fin 25) : r.val ≠ 103 + b.val := by omega
  simp [Matrix.mulVec, dotProduct, tailMatrix, hne]

theorem encode_eq_mulVec (x : Fin 25 → ℂ) : encode x = supportMatrix *ᵥ x := rfl

/-- Exactly the vectors in the asserted support satisfy the concrete 103
Gaussian-integer annihilator constraints. -/
theorem support_of_constraints (v : Fin 128 → ℂ)
    (hv : ∀ r : Fin 128, r.val < 103 → (complexStack *ᵥ v) r = 0) :
    ∃ x : Fin 25 → ℂ, encode x = v := by
  let x : Fin 25 → ℂ := fun b => (complexStack *ᵥ v) (tailIndex b)
  refine ⟨x, ?_⟩
  apply stacked_complex_injective
  change complexStack *ᵥ encode x = complexStack *ᵥ v
  rw [encode_eq_mulVec, Matrix.mulVec_mulVec, stack_basis]
  funext r
  by_cases hr : r.val < 103
  · rw [tail_mul_at_head x r hr, hv r hr]
  · let b : Fin 25 := ⟨r.val - 103, by omega⟩
    have hb : tailIndex b = r := by apply Fin.ext; dsimp [tailIndex, b]; omega
    rw [← hb, tail_mul_at_tail]

theorem constraints_of_support (x : Fin 25 → ℂ) (r : Fin 128) (hr : r.val < 103) :
    (complexStack *ᵥ encode x) r = 0 := by
  rw [encode_eq_mulVec, Matrix.mulVec_mulVec, stack_basis]
  exact tail_mul_at_head x r hr

end
end ICO.ExactSupportSpace

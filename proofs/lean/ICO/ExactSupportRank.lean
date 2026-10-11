import ICO.SupportModularTree
import ICO.SupportProductCollection
import ICO.ModularRankTransport
import Mathlib.Algebra.BigOperators.Fin

/-! Kernel-checked injectivity of the concrete complex stacked support matrix.
No claim about the unitary interpretation of its first 103 rows is made here. -/

namespace ICO.ExactSupportRank
open ICO.ExactTensorCertificates ICO.SupportModularTree ICO.ModularRankTransport
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable section

def stackedMatrix : Matrix (Fin 128) (Fin 128) GaussianInt := fun r c =>
  ⟨(gaussianEntry r.val c.val).1, (gaussianEntry r.val c.val).2⟩

def inverseMatrix : Matrix (Fin 128) (Fin 128) (ZMod 5) := fun r c =>
  inverseEntry r.val c.val

theorem reduction_entry (r c : Fin 128) :
    reduceModFive (stackedMatrix r c) = (modularEntry r.val c.val : ZMod 5) := by
  have generic (a b : Int) : reduceModFive (⟨a, b⟩ : GaussianInt) =
      (((a + 2*b) % (5 : Nat) : Int) : ZMod 5) := by
    rw [ZMod.intCast_mod]
    simp [reduceModFive, Zsqrtd.lift_apply_apply, mul_comm]
  exact generic _ _

theorem sumBelow_cast (n : Nat) (f : Nat → Int) :
    (sumBelow n f : ZMod 5) = ∑ k : Fin n, (f k.val : ZMod 5) := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    simp [sumBelow, Fin.sum_univ_castSucc, ih, Int.cast_add]

theorem modular_right_inverse :
    reduceModFive.mapMatrix stackedMatrix * inverseMatrix = 1 := by
  ext r c
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    reduction_entry, inverseMatrix]
  have h := congrArg (fun z : Int => (z : ZMod 5)) (product_entries_fin r c)
  dsimp only at h
  have product_cast (rr cc : Nat) : (productEntry rr cc : ZMod 5) =
      ∑ k : Fin 128, (modularEntry rr k.val : ZMod 5) *
        (inverseEntry k.val cc : ZMod 5) := by
    unfold productEntry
    rw [show (5 : Int) = ((5 : Nat) : Int) from rfl, ZMod.intCast_mod]
    rw [sumBelow_cast]
    simp only [Int.cast_mul]
  rw [product_cast] at h
  simp only [Int.cast_mul,
    Int.cast_ite, Int.cast_one, Int.cast_zero] at h
  simpa only [Matrix.one_apply] using h

theorem stacked_complex_injective :
    Function.Injective (GaussianInt.toComplex.mapMatrix stackedMatrix).mulVec := by
  exact complex_mulVec_injective_of_modular_inverse stackedMatrix inverseMatrix
    modular_right_inverse

end
end ICO.ExactSupportRank

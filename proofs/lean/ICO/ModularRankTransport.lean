import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum

/-!
# Transporting a finite modular rank certificate to complex scalars

The Gaussian integer i is sent to 2 modulo 5. A checked modular right inverse
therefore witnesses a nonzero Gaussian-integer determinant, and injectivity of
the standard Gaussian-integer embedding transfers this to the complex numbers.
No unproved rank-reduction principle is assumed.
-/

namespace ICO.ModularRankTransport

noncomputable section

def reduceModFive : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift ⟨(2 : ZMod 5), by decide +kernel⟩

theorem complex_det_ne_zero_of_modular_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n GaussianInt) (B : Matrix n n (ZMod 5))
    (h : reduceModFive.mapMatrix A * B = 1) :
    (GaussianInt.toComplex.mapMatrix A).det ≠ 0 := by
  have hm : (reduceModFive.mapMatrix A).det * B.det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  have hmod : reduceModFive A.det ≠ 0 := by
    rw [reduceModFive.map_det]
    intro hz
    rw [hz, zero_mul] at hm
    exact (by decide : (0 : ZMod 5) ≠ 1) hm
  have hA : A.det ≠ 0 := by
    intro hz
    apply hmod
    rw [hz, map_zero]
  rw [← GaussianInt.toComplex.map_det]
  intro hz
  apply hA
  apply GaussianInt.toComplex_injective
  simpa only [map_zero] using hz

theorem complex_mulVec_injective_of_modular_inverse {n : Type*}
    [Fintype n] [DecidableEq n]
    (A : Matrix n n GaussianInt) (B : Matrix n n (ZMod 5))
    (h : reduceModFive.mapMatrix A * B = 1) :
    Function.Injective (GaussianInt.toComplex.mapMatrix A).mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (complex_det_ne_zero_of_modular_inverse A B h)

end
end ICO.ModularRankTransport

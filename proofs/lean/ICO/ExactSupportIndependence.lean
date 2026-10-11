import ICO.ExactTensorDefinitions
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A kernel-checked integer left inverse of the support matrix

This proves that the 25 columns of the physical tensor-defined matrix E are
linearly independent over the complex numbers.  The left inverse has only 44
nonzero integer entries.  Its data are checked against E, not assumed.
This does not yet prove that the common unitary-link support has dimension 25.
-/

namespace ICO.ExactSupportIndependence
open ICO.ExactTensorCertificates
open scoped BigOperators

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftRows (a : Fin 25) : List (Fin 128 × Int) :=
  match a.val with
  | 0 => [(0, 1), (5, -1), (17, -1)]
  | 1 => [(69, 1)]
  | 2 => [(8, 1), (25, -1)]
  | 3 => [(5, 1), (7, -1), (12, 1), (29, -1)]
  | 4 => [(4, 1), (16, 1), (21, -1), (69, -1)]
  | 5 => [(20, 1)]
  | 6 => [(5, -1), (7, 1), (24, 1)]
  | 7 => [(28, 1)]
  | 8 => [(32, 1), (37, -1)]
  | 9 => [(36, 1)]
  | 10 => [(40, 1)]
  | 11 => [(44, 1)]
  | 12 => [(48, 1), (53, -1)]
  | 13 => [(52, 1)]
  | 14 => [(56, 1)]
  | 15 => [(60, 1)]
  | 16 => [(17, 1)]
  | 17 => [(4, 1), (69, -1)]
  | 18 => [(25, 1)]
  | 19 => [(5, -1), (7, 1), (29, 1)]
  | 20 => [(7, 1)]
  | 21 => [(4, -1), (21, 1), (69, 1)]
  | 22 => [(37, 1)]
  | 23 => [(53, 1)]
  | 24 => [(5, 1), (7, -1)]
  | _ => []

theorem integer_left_inverse : ∀ a b : Fin 25,
    ((leftRows a).map (fun kc => kc.2 * basisEntry kc.1.val b.val)).sum =
      if a = b then 1 else 0 := by
  decide +kernel

def encode (x : Fin 25 → ℂ) (i : Fin 128) : ℂ :=
  ∑ b, (basisEntry i.val b.val : ℂ) * x b

def recover (a : Fin 25) (v : Fin 128 → ℂ) : ℂ :=
  ((leftRows a).map (fun kc => (kc.2 : ℂ) * v kc.1)).sum

theorem finite_expansion (data : List (Fin 128 × Int)) (x : Fin 25 → ℂ) :
    (data.map (fun kc => (kc.2 : ℂ) * encode x kc.1)).sum =
      ∑ b, ((data.map (fun kc => kc.2 * basisEntry kc.1.val b.val)).sum : Int) * x b := by
  induction data with
  | nil => simp
  | cons kc rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp [Int.cast_add, Int.cast_mul, add_mul, Finset.sum_add_distrib,
      encode, Finset.mul_sum, mul_assoc]

theorem recover_encode (a : Fin 25) (x : Fin 25 → ℂ) : recover a (encode x) = x a := by
  unfold recover
  rw [finite_expansion]
  simp_rw [integer_left_inverse]
  simp

/-- The actual 128-by-25 support matrix has trivial kernel over ℂ. -/
theorem encode_injective : Function.Injective encode := by
  intro x y h
  funext a
  have h' := congrArg (recover a) h
  simpa only [recover_encode] using h'

theorem support_kernel_trivial (x : Fin 25 → ℂ)
    (h : ∀ i, encode x i = 0) : x = 0 := by
  apply encode_injective
  funext i
  rw [h]
  simp [encode]

end
end ICO.ExactSupportIndependence

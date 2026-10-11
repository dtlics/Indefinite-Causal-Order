import ICO.ExactTensorDefinitions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-! Scalar-generic linear tensor rows. These are actual partial traces and
trace-and-replace maps, with proved agreement with the integer certificate
definitions. `R = ℝ` and `R = ℂ` share exactly the same operators. -/
namespace ICO.TensorRowOperators
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

variable {R : Type*} [CommRing R]
abbrev Tensor (R : Type*) := Nat → Nat → R

def evalAt (i j : Nat) : Tensor R →ₗ[R] R where
  toFun C := C i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def traceDiscard (n i j : Nat) : Tensor R →ₗ[R] R :=
  ∑ h : Fin n, evalAt (n*i+h.val) (n*j+h.val)

@[simp] theorem traceDiscard_apply (n i j : Nat) (C : Tensor R) :
    traceDiscard n i j C = ∑ h : Fin n, C (n*i+h.val) (n*j+h.val) := by
  simp [traceDiscard, evalAt]

def causalOne (k : Nat) : Tensor R →ₗ[R] R :=
  (2 : R) • traceDiscard 4 (k/32) (k%32) -
    if (k/32)%2 == (k%32)%2 then traceDiscard 8 ((k/32)/2) ((k%32)/2) else 0

def causalTwo (k : Nat) : Tensor R →ₗ[R] R :=
  (2 : R) • traceDiscard 16 (k/8) (k%8) -
    if (k/8)%2 == (k%8)%2 then traceDiscard 32 ((k/8)/2) ((k%8)/2) else 0

def causalRow (k : Nat) : Tensor R →ₗ[R] R :=
  if k < 1024 then causalOne k else causalTwo (k-1024)

def swapSlots : Tensor R →ₗ[R] Tensor R where
  toFun C := fun i j => C (ICO.ExactTensorCertificates.swapSlots i)
    (ICO.ExactTensorCertificates.swapSlots j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def abRow (k : Nat) : Tensor R →ₗ[R] R := causalRow k
def baRow (k : Nat) : Tensor R →ₗ[R] R := (causalRow k).comp swapSlots

def traceReplace (unit size : Nat) : Tensor R →ₗ[R] Tensor R where
  toFun C := fun i j =>
    if i/unit%size == j/unit%size then
      ∑ h : Fin size,
        C (i/(unit*size)*(unit*size)+h.val*unit+i%unit)
          (j/(unit*size)*(unit*size)+h.val*unit+j%unit)
    else 0
  map_add' C D := by
    ext i j
    split_ifs <;> simp_all [Finset.sum_add_distrib]
  map_smul' z C := by
    ext i j
    split_ifs <;> simp_all [Finset.mul_sum]

def projectA4 : Tensor R →ₗ[R] Tensor R :=
  (4 : R) • LinearMap.id - (2 : R) • traceReplace 16 2 + traceReplace 16 4

def projectB4 : Tensor R →ₗ[R] Tensor R :=
  (4 : R) • LinearMap.id - (2 : R) • traceReplace 4 2 + traceReplace 4 4

def gaugeRow (k : Nat) : Tensor R →ₗ[R] R :=
  (evalAt (k%128) (k/128)).comp (projectA4.comp projectB4)

def intCastTensor (C : Nat → Nat → Int) : Tensor R := fun i j => C i j

theorem sumBelow_cast (n : Nat) (f : Nat → Int) :
    (ICO.ExactTensorCertificates.sumBelow n f : R) =
      ∑ h : Fin n, (f h.val : R) := by
  induction n with
  | zero => simp [ICO.ExactTensorCertificates.sumBelow]
  | succ n ih =>
    simp [ICO.ExactTensorCertificates.sumBelow, Fin.sum_univ_castSucc, ih, Int.cast_add]

theorem traceReplace_cast (unit size : Nat) (C : Nat → Nat → Int) (i j : Nat) :
    (ICO.ExactTensorCertificates.traceReplace unit size C i j : R) =
      traceReplace unit size (intCastTensor C) i j := by
  simp only [ICO.ExactTensorCertificates.traceReplace, traceReplace,
    LinearMap.coe_mk, AddHom.coe_mk, intCastTensor]
  split_ifs <;> simp [sumBelow_cast]

theorem projectA4_cast (C : Nat → Nat → Int) :
    intCastTensor (ICO.ExactTensorCertificates.projectA4 C) =
      projectA4 (intCastTensor C : Tensor R) := by
  ext i j
  simp [intCastTensor, ICO.ExactTensorCertificates.projectA4, projectA4,
    traceReplace_cast]

theorem projectB4_cast (C : Nat → Nat → Int) :
    intCastTensor (ICO.ExactTensorCertificates.projectB4 C) =
      projectB4 (intCastTensor C : Tensor R) := by
  ext i j
  simp [intCastTensor, ICO.ExactTensorCertificates.projectB4, projectB4,
    traceReplace_cast]

theorem causalOne_cast (C : Nat → Nat → Int) (k : Nat) :
    (ICO.ExactTensorCertificates.causalOne C k : R) =
      causalOne k (intCastTensor C) := by
  unfold ICO.ExactTensorCertificates.causalOne causalOne
  split_ifs <;> simp_all [sumBelow_cast, intCastTensor]

theorem causalTwo_cast (C : Nat → Nat → Int) (k : Nat) :
    (ICO.ExactTensorCertificates.causalTwo C k : R) =
      causalTwo k (intCastTensor C) := by
  unfold ICO.ExactTensorCertificates.causalTwo causalTwo
  split_ifs <;> simp_all [sumBelow_cast, intCastTensor]

theorem abRow_cast (a b k : Nat) :
    (ICO.ExactTensorCertificates.rowAB k a b : R) =
      abRow k (intCastTensor (ICO.ExactTensorCertificates.choiCoefficient a b)) := by
  unfold ICO.ExactTensorCertificates.rowAB abRow
    ICO.ExactTensorCertificates.causalRow causalRow
  split_ifs <;> simp [causalOne_cast, causalTwo_cast]

theorem baRow_cast (a b k : Nat) :
    (ICO.ExactTensorCertificates.rowBA k a b : R) =
      baRow k (intCastTensor (ICO.ExactTensorCertificates.choiCoefficient a b)) := by
  unfold ICO.ExactTensorCertificates.rowBA baRow
  simp only [LinearMap.comp_apply, swapSlots, LinearMap.coe_mk, AddHom.coe_mk]
  unfold ICO.ExactTensorCertificates.causalRow causalRow
  split_ifs <;> simp [causalOne_cast, causalTwo_cast, intCastTensor] <;> rfl

theorem gaugeRow_cast (a b k : Nat) :
    (ICO.ExactTensorCertificates.rowGauge16 k a b : R) =
      gaugeRow k (intCastTensor (ICO.ExactTensorCertificates.choiCoefficient a b)) := by
  unfold ICO.ExactTensorCertificates.rowGauge16 gaugeRow
  change intCastTensor (ICO.ExactTensorCertificates.projectA4
    (ICO.ExactTensorCertificates.projectB4 (ICO.ExactTensorCertificates.choiCoefficient a b)))
      (k%128) (k/128) = _
  rw [projectA4_cast, projectB4_cast]
  rfl

end ICO.TensorRowOperators

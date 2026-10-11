import ICO.TensorRowOperators
import Mathlib.Data.Complex.BigOperators

namespace ICO.TensorRowOperators
open scoped BigOperators

def realPart (C : Tensor ℂ) : Tensor ℝ := fun i j => (C i j).re

theorem realPart_traceReplace (unit size : Nat) (C : Tensor ℂ) :
    realPart (traceReplace unit size C) = traceReplace unit size (realPart C) := by
  ext i j
  simp only [realPart, traceReplace, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> simp [Complex.re_sum]

theorem realPart_projectA4 (C : Tensor ℂ) :
    realPart (projectA4 C) = projectA4 (realPart C) := by
  ext i j
  have h2 := congrFun (congrFun (realPart_traceReplace 16 2 C) i) j
  have h4 := congrFun (congrFun (realPart_traceReplace 16 4 C) i) j
  simp only [realPart] at h2 h4
  simp [projectA4, realPart, Complex.mul_re, h2, h4]

theorem realPart_projectB4 (C : Tensor ℂ) :
    realPart (projectB4 C) = projectB4 (realPart C) := by
  ext i j
  have h2 := congrFun (congrFun (realPart_traceReplace 4 2 C) i) j
  have h4 := congrFun (congrFun (realPart_traceReplace 4 4 C) i) j
  simp only [realPart] at h2 h4
  simp [projectB4, realPart, Complex.mul_re, h2, h4]

theorem causalOne_realPart (C : Tensor ℂ) (k : Nat) :
    (causalOne k C).re = causalOne k (realPart C) := by
  unfold causalOne
  split_ifs <;> simp_all [traceDiscard, evalAt, realPart, Complex.re_sum, Complex.mul_re]

theorem causalTwo_realPart (C : Tensor ℂ) (k : Nat) :
    (causalTwo k C).re = causalTwo k (realPart C) := by
  unfold causalTwo
  split_ifs <;> simp_all [traceDiscard, evalAt, realPart, Complex.re_sum, Complex.mul_re]

theorem abRow_realPart (C : Tensor ℂ) (k : Nat) :
    (abRow k C).re = abRow k (realPart C) := by
  unfold abRow causalRow
  split_ifs <;> simp [causalOne_realPart, causalTwo_realPart]

theorem baRow_realPart (C : Tensor ℂ) (k : Nat) :
    (baRow k C).re = baRow k (realPart C) := by
  unfold baRow
  simp only [LinearMap.comp_apply]
  change (abRow k (swapSlots C)).re = abRow k (swapSlots (realPart C))
  rw [abRow_realPart]
  rfl

theorem gaugeRow_realPart (C : Tensor ℂ) (k : Nat) :
    (gaugeRow k C).re = gaugeRow k (realPart C) := by
  change realPart (projectA4 (projectB4 C)) (k%128) (k/128) = _
  rw [realPart_projectA4, realPart_projectB4]
  rfl

end ICO.TensorRowOperators

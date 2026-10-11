import ICO.MHPurifiedOracle
import Mathlib.Analysis.Fourier.ZMod

/-! An actual unitary Fourier transform on all ternary phase functions. -/
namespace ICO.MHTernaryFourier
open Matrix QIT
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev Phase (A : Type*) := A → ZMod 3

def pairing (f z : Phase A) : ZMod 3 := ∑ x, f x*z x

def character (f : Phase A) : AddChar (Phase A) ℂ where
  toFun z := ZMod.stdAddChar (pairing f z)
  map_zero_eq_one' := by simp [pairing]
  map_add_eq_mul' z w := by
    simp only [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib,
      AddChar.map_add_eq_mul]

theorem character_single (f : Phase A) (x : A) :
    character f (Pi.single x 1) = ZMod.stdAddChar (f x) := by
  simp [character,pairing,Pi.single_apply]

theorem character_nontrivial {f : Phase A} (hf : f ≠ 0) : character f ≠ 1 := by
  obtain ⟨x,hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (funext h)
  apply AddChar.ne_one_iff.mpr
  refine ⟨Pi.single x 1,?_⟩
  rw [character_single]
  intro h
  apply hx
  apply ZMod.injective_stdAddChar
  simpa using h

theorem character_sum (f : Phase A) :
    (∑ z,character f z) = if f=0 then (Fintype.card (Phase A) : ℂ) else 0 := by
  by_cases hf : f=0
  · subst f
    simp [character,pairing]
  · rw [if_neg hf]
    exact AddChar.sum_eq_zero_of_ne_one (character_nontrivial hf)

theorem character_star_mul (f g z : Phase A) :
    star (character f z)*character g z = character (g-f) z := by
  have hs : star (ZMod.stdAddChar (pairing f z)) = ZMod.stdAddChar (-pairing f z) := by
    simpa [Complex.star_def] using
      (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := 3)) (pairing f z)).symm
  change star (ZMod.stdAddChar (pairing f z))*ZMod.stdAddChar (pairing g z) = _
  rw [hs,← AddChar.map_add_eq_mul]
  change ZMod.stdAddChar (-pairing f z+pairing g z)=ZMod.stdAddChar (pairing (g-f) z)
  congr 1
  change -(∑ x, f x*z x) + ∑ x, g x*z x = ∑ x, (g x-f x)*z x
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

def coefficient : ℂ := (((Real.sqrt (Fintype.card (Phase A) : ℝ))⁻¹ : ℝ) : ℂ)

theorem coefficient_star : star (coefficient (A := A)) = coefficient (A := A) := by
  simp [coefficient]

theorem coefficient_square : coefficient (A := A)*coefficient (A := A) =
    (Fintype.card (Phase A) : ℂ)⁻¹ := by
  have hs := Real.sq_sqrt (show 0 ≤ (Fintype.card (Phase A) : ℝ) by positivity)
  have hr : (Real.sqrt (Fintype.card (Phase A) : ℝ))⁻¹ *
      (Real.sqrt (Fintype.card (Phase A) : ℝ))⁻¹ = (Fintype.card (Phase A) : ℝ)⁻¹ := by
    rw [← mul_inv,← pow_two,hs]
  simpa [coefficient] using congrArg (fun x : ℝ => (x : ℂ)) hr

def fourierMatrix : CMatrix (Phase A) := fun f z => coefficient (A := A) * character f z

theorem pairing_comm (f z : Phase A) : pairing f z = pairing z f := by
  simp only [pairing,mul_comm]

theorem fourier_isometry :
    (fourierMatrix (A := A)).conjTranspose * fourierMatrix (A := A) = 1 := by
  ext f g
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,fourierMatrix,star_mul,coefficient_star]
  have hchar (z h : Phase A) : character z h = character h z := by
    exact congrArg ZMod.stdAddChar (pairing_comm z h)
  have ht (z : Phase A) : (star (character z f) * coefficient (A := A)) *
      (coefficient (A := A) * character z g) =
        (Fintype.card (Phase A) : ℂ)⁻¹ * character (g-f) z := by
    rw [hchar z f,hchar z g]
    rw [show (star (character f z) * coefficient (A := A)) *
      (coefficient (A := A) * character g z) = (coefficient (A := A)*coefficient (A := A))*
        (star (character f z)*character g z) by ring]
    rw [coefficient_square,character_star_mul]
  simp_rw [ht]
  rw [← Finset.mul_sum,character_sum]
  by_cases hfg : f=g
  · subst g
    simp [Matrix.one_apply,Fintype.card_ne_zero]
  · have hne : g-f ≠ 0 := sub_ne_zero.mpr (Ne.symm hfg)
    simp [hne,Matrix.one_apply,hfg]

def fourierUnitary : Matrix.unitaryGroup (Phase A) ℂ :=
  ⟨fourierMatrix,Matrix.mem_unitaryGroup_iff'.mpr fourier_isometry⟩

theorem character_shift (f z : Phase A) (x : A) :
    character f (z+Pi.single x 1) = character f z * ZMod.stdAddChar (f x) := by
  rw [AddChar.map_add_eq_mul,character_single]

#print axioms fourier_isometry
end
end ICO.MHTernaryFourier

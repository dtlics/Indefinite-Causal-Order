import ICO.HaarFamily

/-! Exact Haar absorption of a fixed hidden phase-permutation unitary. -/
namespace ICO.MHHaarAbsorption
open Matrix QIT MeasureTheory
open scoped BigOperators
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
abbrev Unitary (A : Type*) [Fintype A] [DecidableEq A] := Matrix.unitaryGroup A ℂ

theorem fixed_absorption_map (D Q : Unitary A) :
    Measure.map (fun C : Unitary A => D*Q*C) (unitaryHaarMeasure (a := A)) =
      unitaryHaarMeasure (a := A) :=
  MeasureTheory.map_mul_left_eq_self _ (D*Q)

theorem fixed_absorption {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D Q : Unitary A) (f : Unitary A → E) :
    (∫ C, f (D*Q*C) ∂unitaryHaarMeasure (a := A)) =
      ∫ U, f U ∂unitaryHaarMeasure (a := A) :=
  integral_mul_left_eq_self f (D*Q)

theorem two_sided_absorption {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : Unitary A) (f : Unitary A → E) :
    (∫ D, ∫ C, f (D*Q*C) ∂unitaryHaarMeasure (a := A)
      ∂unitaryHaarMeasure (a := A)) =
      ∫ U, f U ∂unitaryHaarMeasure (a := A) := by
  simp_rw [fixed_absorption]
  simp

theorem finite_mixture_absorption {I E : Type*} [Fintype I] [Nonempty I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : I → Unitary A) (f : Unitary A → E) :
    (Fintype.card I : ℝ)⁻¹ •
      (∑ i, ∫ D, ∫ C, f (D*Q i*C) ∂unitaryHaarMeasure (a := A)
        ∂unitaryHaarMeasure (a := A)) =
      ∫ U, f U ∂unitaryHaarMeasure (a := A) := by
  simp_rw [two_sided_absorption]
  simp [← Nat.cast_smul_eq_nsmul ℝ,Fintype.card_ne_zero]

#print axioms fixed_absorption_map
#print axioms finite_mixture_absorption
end
end ICO.MHHaarAbsorption

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# Uniform fresh outputs

The uniform distribution outside a proper finite forbidden set is at total
variation distance exactly `|S|/d` from the uniform distribution on all `d`
labels. This is a finite classical distribution theorem, not a theorem about
operator-valued memory blocks or partial traces of a quantum recording oracle.
-/

namespace ICO.FreshOutputDistance

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

def uniformOutside (s : Finset α) (x : α) : ℝ :=
  if x ∈ s then 0 else 1 / ((Fintype.card α : ℝ) - (s.card : ℝ))

theorem sum_two_values (s : Finset α) (a b : ℝ) :
    (∑ x : α, if x ∈ s then a else b) =
      (s.card : ℝ) * a + ((Fintype.card α : ℝ) - (s.card : ℝ)) * b := by
  have h := Finset.sum_piecewise (Finset.univ : Finset α) s (fun _ => a) (fun _ => b)
  simpa [Finset.piecewise, Finset.sum_const, nsmul_eq_mul,
    Finset.card_sdiff_of_subset (Finset.subset_univ s),
    Nat.cast_sub (Finset.card_le_univ s)] using h

theorem uniformOutside_nonneg (s : Finset α) (x : α)
    (hs : s.card < Fintype.card α) : 0 ≤ uniformOutside s x := by
  have h : (s.card : ℝ) < Fintype.card α := by exact_mod_cast hs
  have hden : (0 : ℝ) < (Fintype.card α : ℝ) - (s.card : ℝ) := by linarith
  unfold uniformOutside
  split_ifs <;> positivity

theorem uniformOutside_sum (s : Finset α) (hs : s.card < Fintype.card α) :
    ∑ x : α, uniformOutside s x = 1 := by
  have h : (s.card : ℝ) < Fintype.card α := by exact_mod_cast hs
  have hne : (Fintype.card α : ℝ) - (s.card : ℝ) ≠ 0 := by linarith
  unfold uniformOutside
  rw [sum_two_values]
  field_simp
  ring

/-- Exact total variation distance for a forbidden-label distribution. -/
theorem totalVariation_uniformOutside (s : Finset α)
    (hs : s.card < Fintype.card α) :
    (∑ x : α, |uniformOutside s x - 1 / (Fintype.card α : ℝ)|) / 2 =
      (s.card : ℝ) / (Fintype.card α : ℝ) := by
  have hlt : (s.card : ℝ) < Fintype.card α := by exact_mod_cast hs
  have hk : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hd : (0 : ℝ) < Fintype.card α := by linarith
  have hden : (0 : ℝ) < (Fintype.card α : ℝ) - (s.card : ℝ) := by linarith
  have hrecip : 1 / (Fintype.card α : ℝ) ≤
      1 / ((Fintype.card α : ℝ) - (s.card : ℝ)) :=
    one_div_le_one_div_of_le hden (by linarith)
  have hpoint (x : α) :
      |uniformOutside s x - 1 / (Fintype.card α : ℝ)| =
        if x ∈ s then 1 / (Fintype.card α : ℝ)
        else 1 / ((Fintype.card α : ℝ) - (s.card : ℝ)) -
          1 / (Fintype.card α : ℝ) := by
    by_cases hx : x ∈ s
    · simp [uniformOutside, hx]
    · simp only [uniformOutside, if_neg hx]
      exact abs_of_nonneg (sub_nonneg.mpr hrecip)
  simp_rw [hpoint]
  rw [sum_two_values]
  field_simp
  ring

/-- The fresh-output error is bounded by any upper bound on the forbidden
    number of labels, in particular the intermediate recording-size bound. -/
theorem totalVariation_uniformOutside_le (s : Finset α) (m : ℕ)
    (hs : s.card < Fintype.card α) (hm : s.card ≤ m) :
    (∑ x : α, |uniformOutside s x - 1 / (Fintype.card α : ℝ)|) / 2 ≤
      (m : ℝ) / (Fintype.card α : ℝ) := by
  rw [totalVariation_uniformOutside s hs]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hm) (Nat.cast_nonneg _)

end

end ICO.FreshOutputDistance

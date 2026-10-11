import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-! Positive output states bound control coherence by their two branch
populations. This is a quantum-state statement, independent of any order
decomposition or a priori branch weights. -/

namespace ICO.PositiveCoherence

open Matrix
open scoped InnerProductSpace ComplexOrder

noncomputable section

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem coherence_sq_le (ρ : Matrix a a ℂ) (hρ : ρ.PosSemidef)
    (x y : a → ℂ) :
    Complex.normSq (star x ⬝ᵥ (ρ *ᵥ y)) ≤
      (star x ⬝ᵥ (ρ *ᵥ x)).re * (star y ⬝ᵥ (ρ *ᵥ y)).re := by
  let iSemi := ρ.toSeminormedAddCommGroup hρ
  let iInner : @InnerProductSpace ℂ (a → ℂ) _ iSemi := ρ.toInnerProductSpace hρ
  let nx := @norm (a → ℂ) iSemi.toNorm x
  let ny := @norm (a → ℂ) iSemi.toNorm y
  have h := @norm_inner_le_norm ℂ (a → ℂ) _ iSemi iInner x y
  have hx : nx ^ 2 = (star x ⬝ᵥ (ρ *ᵥ x)).re := by
    rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ (a → ℂ) _ iSemi iInner x]
    change ((ρ *ᵥ x) ⬝ᵥ star x).re = _
    rw [dotProduct_comm]
  have hy : ny ^ 2 = (star y ⬝ᵥ (ρ *ᵥ y)).re := by
    rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ (a → ℂ) _ iSemi iInner y]
    change ((ρ *ᵥ y) ⬝ᵥ star y).re = _
    rw [dotProduct_comm]
  have hi : @inner ℂ (a → ℂ) iInner.toInner x y = star x ⬝ᵥ (ρ *ᵥ y) := by
    change (ρ *ᵥ y) ⬝ᵥ star x = _
    exact dotProduct_comm _ _
  rw [hi] at h
  change ‖star x ⬝ᵥ (ρ *ᵥ y)‖ ≤ nx * ny at h
  have hn : 0 ≤ nx * ny := mul_nonneg (@norm_nonneg _ iSemi.toSeminormedAddGroup x)
    (@norm_nonneg _ iSemi.toSeminormedAddGroup y)
  have hs := (sq_le_sq₀ (norm_nonneg _) hn).2 h
  rw [mul_pow, hx, hy, Complex.sq_norm] at hs
  exact hs

#print axioms coherence_sq_le

end
end ICO.PositiveCoherence

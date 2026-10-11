import ICO.CompositionMoment
import ICO.GramNorm

/-! # Normalized composition columns and their Gram entries -/

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarFamily ICO.GramWitness ICO.CircuitOutput

namespace ICO.CompositionGram
set_option maxHeartbeats 500000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

def coefficient : ℂ := (((Real.sqrt (Fintype.card A : ℝ))⁻¹ : ℝ) : ℂ)

theorem coefficient_star : star (coefficient (A := A)) = coefficient (A := A) := by
  simp [coefficient]

theorem coefficient_square : coefficient (A := A) * coefficient (A := A) =
    (Fintype.card A : ℂ)⁻¹ := by
  have hd : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hs := Real.sq_sqrt (le_of_lt hd)
  have hn : Real.sqrt (Fintype.card A : ℝ) ≠ 0 := by positivity
  have he : (Real.sqrt (Fintype.card A : ℝ))⁻¹ *
      (Real.sqrt (Fintype.card A : ℝ))⁻¹ = (Fintype.card A : ℝ)⁻¹ := by
    rw [← mul_inv, ← pow_two, hs]
  unfold coefficient
  rw [← Complex.ofReal_mul, he]
  simp

def columns {r s : ℕ} (U : Fin r → Unitary (A := A)) (V : Fin s → Unitary (A := A)) :
    Matrix (A × A) (Fin r × Fin s) ℂ :=
  fun pf ij => coefficient (A := A) * targetVector ((V ij.2 : CMatrix A) * (U ij.1 : CMatrix A)) pf

theorem targetVector_inner (S T : CMatrix A) :
    star (targetVector S) ⬝ᵥ targetVector T = (S.conjTranspose * T).trace := by
  simp [dotProduct, targetVector, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]

theorem gram_entry {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) (ij kl : Fin r × Fin s) :
    gram (columns U V) ij kl = (Fintype.card A : ℂ)⁻¹ *
      ((((V ij.2 : CMatrix A) * (U ij.1 : CMatrix A)).conjTranspose) *
        ((V kl.2 : CMatrix A) * (U kl.1 : CMatrix A))).trace := by
  rw [← targetVector_inner]
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, columns, star_mul,
    coefficient_star, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← coefficient_square]
  simp only [Pi.star_apply]
  ring

theorem gram_diagonal {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) (ij : Fin r × Fin s) :
    gram (columns U V) ij ij = 1 := by
  rw [gram_entry]
  have h := Matrix.UnitaryGroup.star_mul_self (V ij.2 * U ij.1)
  change (((V ij.2 : CMatrix A) * (U ij.1 : CMatrix A)).conjTranspose) *
    ((V ij.2 : CMatrix A) * (U ij.1 : CMatrix A)) = 1 at h
  rw [h, Matrix.trace_one]
  exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

theorem gram_entry_normSq {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) (ij kl : Fin r × Fin s) :
    Complex.normSq (gram (columns U V) ij kl) =
      (Fintype.card A : ℝ)⁻¹ ^ 2 *
        ICO.CompositionMoment.compositionOverlap U V ij.1 kl.1 ij.2 kl.2 := by
  rw [gram_entry, Complex.normSq_mul]
  simp [ICO.CompositionMoment.compositionOverlap, Complex.normSq_inv,
    Complex.normSq_natCast, pow_two]

theorem columns_continuous {r s : ℕ} :
    Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      columns UV.1 UV.2) := by
  apply continuous_pi
  intro pf
  apply continuous_pi
  intro ij
  apply Continuous.const_mul
  exact ((continuous_subtype_val.comp ((continuous_apply ij.2).comp continuous_snd)).matrix_mul
    (continuous_subtype_val.comp ((continuous_apply ij.1).comp continuous_fst))).matrix_elem pf.2 pf.1

end
end ICO.CompositionGram

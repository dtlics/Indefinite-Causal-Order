import ICO.CompositionGramAverage

/-! # The opposite composition order with the same column labels -/

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarFamily ICO.GramWitness ICO.CompositionGram
open ICO.CompositionGramAverage

namespace ICO.ReverseCompositionGram
set_option maxHeartbeats 500000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

def reverseColumns {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) : Matrix (A × A) (Fin r × Fin s) ℂ :=
  fun pf ij => columns V U pf ij.swap

theorem reverse_gram_entry {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) (ij kl : Fin r × Fin s) :
    gram (reverseColumns U V) ij kl = gram (columns V U) ij.swap kl.swap := rfl

theorem reverse_gram_diagonal {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) (ij : Fin r × Fin s) :
    gram (reverseColumns U V) ij ij = 1 := gram_diagonal V U ij.swap

theorem reverse_defect_entry {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) (ij kl : Fin r × Fin s) :
    (gram (reverseColumns U V) - 1) ij kl =
      (gram (columns V U) - 1) ij.swap kl.swap := by
  simp [Matrix.sub_apply, reverse_gram_entry, Matrix.one_apply]

theorem reverseColumns_continuous {r s : ℕ} :
    Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      reverseColumns UV.1 UV.2) := by
  apply continuous_pi
  intro pf
  apply continuous_pi
  intro ij
  exact (columns_continuous.comp continuous_swap).matrix_elem pf ij.swap

theorem reverse_gram_continuous {r s : ℕ} :
    Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      gram (reverseColumns UV.1 UV.2)) :=
  reverseColumns_continuous.matrix_conjTranspose.matrix_mul reverseColumns_continuous

theorem reverse_defect_entry_average_le {r s : ℕ} (ij kl : Fin (r + 1) × Fin (s + 1)) :
    (∫ UV, Complex.normSq ((gram (reverseColumns UV.1 UV.2) - 1) ij kl)
      ∂ensembleMeasure (A := A) r s) ≤ (Fintype.card A : ℝ)⁻¹ ^ 2 := by
  simp_rw [reverse_defect_entry]
  unfold ensembleMeasure
  have hs := integral_prod_swap (μ := familyMeasure (A := A) (s + 1))
    (ν := familyMeasure (A := A) (r + 1))
    (fun VU : (Fin (s + 1) → Unitary (A := A)) ×
    (Fin (r + 1) → Unitary (A := A)) =>
      Complex.normSq ((gram (columns VU.1 VU.2) - 1) ij.swap kl.swap))
  exact hs.trans_le (defect_entry_average_le ij.swap kl.swap)

theorem reverse_defect_norm_average_le (r s : ℕ) :
    (∫ UV, ‖gram (reverseColumns UV.1 UV.2) - 1‖ ∂ensembleMeasure (A := A) r s) ≤
      ((r + 1) * (s + 1) : ℕ) / (Fintype.card A : ℝ) := by
  have hf : Integrable (fun UV => ‖gram (reverseColumns UV.1 UV.2) - 1‖)
      (ensembleMeasure (A := A) r s) :=
    (reverse_gram_continuous.sub continuous_const).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi (ij kl : Fin (r + 1) × Fin (s + 1)) :
      Integrable (fun UV => Complex.normSq ((gram (reverseColumns UV.1 UV.2) - 1) ij kl))
      (ensembleMeasure (A := A) r s) :=
    (Complex.continuous_normSq.comp
      ((reverse_gram_continuous.sub continuous_const).matrix_elem ij kl)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hd : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have h := matrix_norm_average_of_entries (ensembleMeasure (A := A) r s)
    (fun UV => gram (reverseColumns UV.1 UV.2) - 1) (Fintype.card A : ℝ)⁻¹
    (by positivity) hf hi (fun ij kl => reverse_defect_entry_average_le ij kl)
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, div_eq_mul_inv] using h

end
end ICO.ReverseCompositionGram

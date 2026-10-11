import ICO.HaarFamily

/-! # The exact off-diagonal Haar moment for compositions of two random families -/

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarFamily

namespace ICO.CompositionMoment
set_option maxHeartbeats 500000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

def compositionOverlap {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) (i k : Fin r) (j l : Fin s) : ℝ :=
  Complex.normSq ((((V j : CMatrix A) * (U i : CMatrix A)).conjTranspose) *
    ((V l : CMatrix A) * (U k : CMatrix A))).trace

theorem compositionOverlap_continuous {r s : ℕ} (i k : Fin r) (j l : Fin s) :
    Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      compositionOverlap UV.1 UV.2 i k j l) := by
  apply Complex.continuous_normSq.comp
  apply Continuous.matrix_trace
  apply Continuous.matrix_mul
  · apply Continuous.matrix_conjTranspose
    exact (continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)).matrix_mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst))
  · exact (continuous_subtype_val.comp ((continuous_apply l).comp continuous_snd)).matrix_mul
      (continuous_subtype_val.comp ((continuous_apply k).comp continuous_fst))

theorem compositionOverlap_left_average {r s : ℕ} (V : Fin s → Unitary (A := A))
    (i k : Fin (r + 1)) (j l : Fin s) (hik : i ≠ k) :
    (∫ U, compositionOverlap U V i k j l ∂familyMeasure (A := A) (r + 1)) = 1 := by
  apply integral_of_coordinate_average i _
    ((compositionOverlap_continuous i k j l).comp (continuous_id.prodMk continuous_const))
  intro rest
  obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq (Ne.symm hik)
  subst k
  have hp (W : Unitary (A := A)) :
      compositionOverlap (i.insertNth W rest) V i (i.succAbove k') j l =
        Complex.normSq ((W : CMatrix A).conjTranspose *
          ((V j)⁻¹ * V l * rest k' : Unitary (A := A))).trace := by
    simp [compositionOverlap, Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  calc
    _ = ∫ W : Unitary (A := A),
        Complex.normSq ((W : CMatrix A).conjTranspose *
          ((V j)⁻¹ * V l * rest k' : Unitary (A := A))).trace
        ∂unitaryHaarMeasure (a := A) := integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = 1 := adjoint_trace_average _

theorem compositionOverlap_same_left {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) (i : Fin r) (j l : Fin s) :
    compositionOverlap U V i i j l =
      Complex.normSq ((V j : CMatrix A).conjTranspose * (V l : CMatrix A)).trace := by
  unfold compositionOverlap
  have hp : (((V j : CMatrix A) * (U i : CMatrix A)).conjTranspose *
      ((V l : CMatrix A) * (U i : CMatrix A))).trace =
      ((V j : CMatrix A).conjTranspose * (V l : CMatrix A)).trace := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = ((U i : CMatrix A).conjTranspose *
          ((V j : CMatrix A).conjTranspose * (V l : CMatrix A)) * (U i : CMatrix A)).trace := by
        simp only [Matrix.mul_assoc]
      _ = ((U i : CMatrix A) * ((U i : CMatrix A).conjTranspose *
          ((V j : CMatrix A).conjTranspose * (V l : CMatrix A)))).trace :=
            Matrix.trace_mul_comm _ _
      _ = _ := by
        have hU : (U i : CMatrix A) * (U i : CMatrix A).conjTranspose = 1 := (U i).property.2
        rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [hp]

theorem distinct_pair_trace_average {r : ℕ} (j l : Fin (r + 1)) (hjl : j ≠ l) :
    (∫ V : Fin (r + 1) → Unitary (A := A),
      Complex.normSq ((V j : CMatrix A).conjTranspose * (V l : CMatrix A)).trace
      ∂familyMeasure (A := A) (r + 1)) = 1 := by
  have hc : Continuous (fun V : Fin (r + 1) → Unitary (A := A) =>
      Complex.normSq ((V j : CMatrix A).conjTranspose * (V l : CMatrix A)).trace) :=
    Complex.continuous_normSq.comp
      (((continuous_subtype_val.comp (continuous_apply j)).matrix_conjTranspose.matrix_mul
        (continuous_subtype_val.comp (continuous_apply l))).matrix_trace)
  apply integral_of_coordinate_average j _ hc
  intro rest
  obtain ⟨l', hl'⟩ := Fin.exists_succAbove_eq (Ne.symm hjl)
  subst l
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  exact adjoint_trace_average _

theorem compositionOverlap_average {r s : ℕ} (i k : Fin (r + 1)) (j l : Fin (s + 1))
    (hne : (i,j) ≠ (k,l)) :
    (∫ UV : (Fin (r + 1) → Unitary (A := A)) × (Fin (s + 1) → Unitary (A := A)),
      compositionOverlap UV.1 UV.2 i k j l
      ∂(familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1))) = 1 := by
  have hint := (compositionOverlap_continuous i k j l).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
    (μ := (familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1)))
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := by intro h; exact hne (Prod.ext rfl h)
    rw [integral_prod _ hint]
    simp_rw [compositionOverlap_same_left, distinct_pair_trace_average j l hjl]
    simp
  · rw [integral_prod_symm _ hint]
    simp_rw [compositionOverlap_left_average _ i k j l hik]
    simp

end
end ICO.CompositionMoment

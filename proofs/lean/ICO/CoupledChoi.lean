import ICO.SamplingOrdinary
import ICO.SamplingTrace
import ICO.CommonPartDistance
import ICO.ChoiWitnessState

/-! The total-call birthday coupling for actual normalized physical Choi states. -/

namespace ICO.CoupledChoi
open Matrix QIT ICO.TreeCoherence ICO.ChoiWitnessState ICO.FreshSamplingMaps
open ICO.SamplingCP ICO.SamplingOrderCore ICO.SamplingOrdinary ICO.SamplingTrace
open scoped ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 800000
variable {A M Z : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype Z] [DecidableEq Z]

def normalizedMapChoi (f : MatrixMap A (A × Z)) : CMatrix ((A × A) × Z) :=
  (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) • groupedMapChoi f

theorem normalizedMapChoi_sub (f g : MatrixMap A (A × Z)) :
    normalizedMapChoi (f-g) = normalizedMapChoi f - normalizedMapChoi g := by
  ext i j
  simp [normalizedMapChoi, groupedMapChoi, MatrixMap.choi, smul_sub]
  ring

theorem normalizedMapChoi_pos (f : MatrixMap A (A × Z))
    (hf : MatrixMap.IsCompletelyPositive f) : (normalizedMapChoi f).PosSemidef := by
  apply (hf.submatrix _).smul
  exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card A)) : (0 : ℝ) ≤ (Fintype.card A : ℝ)⁻¹)

theorem normalizedMapChoi_trace (f : MatrixMap A (A × Z)) :
    (normalizedMapChoi f).trace.re = (Fintype.card A : ℝ)⁻¹ * (f 1).trace.re := by
  have he : (groupedMapChoi f).trace = (MatrixMap.choi f).trace := by
    simp [groupedMapChoi, Matrix.trace, Matrix.diag_apply, Matrix.submatrix, Fintype.sum_prod_type]
  simp only [normalizedMapChoi, Matrix.trace_smul, he, ICO.ChoiMass.choi_trace_eq_apply_one]
  simp [Complex.mul_re]

def freshChannel {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Z) q A)
    (oracles : Fin r ⊕ Fin r → Channel (A × M) (A × M)) (hq : q ≤ r) : Channel A (A × Z) :=
  (ICO.FreshBudgetCompile.fresh tree Finset.univ Finset.univ (by simpa using hq) (by simpa using hq)).channel oracles

theorem freshChannel_map {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Z) q A)
    (oracles : Fin r ⊕ Fin r → Channel (A × M) (A × M)) (hq : q ≤ r) :
    (freshChannel tree oracles hq).map = freshMap tree oracles Finset.univ Finset.univ :=
  fresh_compile_map _ _ _ _ _ _

theorem normalized_choi_distance_le {q r : ℕ} [NeZero r]
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Z) q A)
    (oracles : Fin r ⊕ Fin r → Channel (A × M) (A × M)) (hq : q ≤ r) :
    (normalizedChoiState (ordinaryChannel tree oracles)).normalizedTraceDistance
      (normalizedChoiState (freshChannel tree oracles hq)) ≤ (q : ℝ) * (q-1) / (2*r) := by
  let C := normalizedMapChoi (commonMap tree oracles Finset.univ Finset.univ)
  have hOrd : ((normalizedChoiState (ordinaryChannel tree oracles)).matrix - C).PosSemidef := by
    change (normalizedMapChoi (ordinaryChannel tree oracles).map - normalizedMapChoi _).PosSemidef
    rw [← normalizedMapChoi_sub]
    exact normalizedMapChoi_pos _ (ordinary_sub_common_cp tree oracles _ _)
  have hFresh : ((normalizedChoiState (freshChannel tree oracles hq)).matrix - C).PosSemidef := by
    change (normalizedMapChoi (freshChannel tree oracles hq).map - normalizedMapChoi _).PosSemidef
    rw [← normalizedMapChoi_sub, freshChannel_map]
    exact normalizedMapChoi_pos _ (fresh_sub_common_cp tree oracles _ _)
  apply (ICO.CommonPartDistance.distance_le_missing_trace _ _ C hOrd hFresh).trans
  change 1 - (normalizedMapChoi _).trace.re ≤ _
  rw [normalizedMapChoi_trace]
  have hLoss := initial_trace_loss tree oracles (Nat.pos_of_ne_zero (NeZero.ne r))
    (X := (1 : CMatrix A)) Matrix.PosSemidef.one
  simp only [Matrix.trace_one, Complex.natCast_re] at hLoss
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (Fintype.card A : ℝ)⁻¹ * ((Fintype.card A : ℝ) -
        (commonMap tree oracles Finset.univ Finset.univ 1).trace.re) := by field_simp
    _ ≤ (Fintype.card A : ℝ)⁻¹ * (((q : ℝ)*(q-1)/(2*r)) * Fintype.card A) :=
      mul_le_mul_of_nonneg_left hLoss (by positivity)
    _ = _ := by field_simp

#print axioms normalized_choi_distance_le
end
end ICO.CoupledChoi

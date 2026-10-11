import ICO.ControlOutcomeReverse
import QIT.States.TraceNorm.Spectral

/-! # Exact branch mass and elementary Choi score bounds -/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.CausalReverse ICO.CircuitOutput ICO.ClassicalDilation

namespace ICO.ChoiMass

set_option maxHeartbeats 200000
noncomputable section

universe u
variable {A B M Z : Type u}
variable [Fintype A] [Fintype B] [Fintype M] [Fintype Z]
variable [DecidableEq A] [DecidableEq B] [DecidableEq M] [DecidableEq Z]

theorem choi_trace_eq_apply_one (Φ : MatrixMap A B) :
    (MatrixMap.choi Φ).trace = (Φ 1).trace := by
  calc
    _ = ∑ a : A, (Φ (Matrix.single a a 1)).trace := by
      simp only [Matrix.trace, Matrix.diag_apply, MatrixMap.choi, Fintype.sum_prod_type]
    _ = (Φ (∑ a : A, Matrix.single a a 1)).trace := by
      rw [map_sum, Matrix.trace_sum]
    _ = _ := by rw [Matrix.sum_single_one]

/-- All operations after the actual preprocessing branch preserve its Choi
mass, even when its probability depends on the input state. -/
theorem fullBranchChoi_trace
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) :
    (MatrixMap.choi (ICO.ControlOutcomeReverse.fullBranchMap R pre U V)).trace =
      (pre.conjTranspose * pre).trace := by
  rw [choi_trace_eq_apply_one]
  unfold ICO.ControlOutcomeReverse.fullBranchMap
  simp only [LinearMap.comp_apply, ICO.AdaptiveReverse.preparedMap_apply]
  rw [(R.channel (oracleChannel V)).tracePreserving, (oracleChannel U).tracePreserving]
  rw [Matrix.mul_one, Matrix.trace_mul_comm]

theorem target_rankOne_trace (T : CMatrix A) (hT : T.conjTranspose * T = 1) :
    (rankOneMatrix (targetVector T)).trace = (Fintype.card A : ℂ) := by
  have heq : (rankOneMatrix (targetVector T)).trace = (T.conjTranspose * T).trace := by
    simp [Matrix.trace, rankOneMatrix_apply, targetVector, Fintype.sum_prod_type,
      Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
  rw [heq, hT]
  simp

theorem target_rankOne_le_card_one (T : CMatrix A) (hT : T.conjTranspose * T = 1) :
    rankOneMatrix (targetVector T) ≤ (Fintype.card A : ℂ) • (1 : CMatrix (A × A)) := by
  have h := State.posSemidef_le_trace_re_smul_one (rankOneMatrix_pos (targetVector T))
  rw [target_rankOne_trace T hT] at h
  simpa using h

theorem choi_target_score_le_mass [Nonempty A]
    (C : CMatrix (A × A)) (hC : C.PosSemidef)
    (T : CMatrix A) (hT : T.conjTranspose * T = 1) :
    ((Fintype.card A : ℝ) ^ 2)⁻¹ * tracePair C (rankOneMatrix (targetVector T)) ≤
      C.trace.re / (Fintype.card A : ℝ) := by
  have h := tracePair_mono_right hC (target_rankOne_le_card_one T hT)
  have hreal : (Fintype.card A : ℂ) = ((Fintype.card A : ℝ) : ℂ) := by simp
  rw [hreal, ICO.ReverseFidelity.tracePair_real_smul_right,
    ICO.ReverseFidelity.tracePair_identity] at h
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ((Fintype.card A : ℝ) ^ 2)⁻¹ * ((Fintype.card A : ℝ) * C.trace.re) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp [hd]

theorem rankOne_score_le_mass [Nonempty A]
    {N : Type u} [Fintype N] [DecidableEq N]
    (C : CMatrix N) (hC : C.PosSemidef) (v : N → ℂ)
    (htrace : (rankOneMatrix v).trace = (Fintype.card A : ℂ)) :
    ((Fintype.card A : ℝ) ^ 2)⁻¹ * tracePair C (rankOneMatrix v) ≤
      C.trace.re / (Fintype.card A : ℝ) := by
  have hp := State.posSemidef_le_trace_re_smul_one (rankOneMatrix_pos v)
  rw [htrace] at hp
  have h := tracePair_mono_right hC hp
  rw [ICO.ReverseFidelity.tracePair_real_smul_right,
    ICO.ReverseFidelity.tracePair_identity] at h
  simp only [Complex.natCast_re] at h
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ((Fintype.card A : ℝ) ^ 2)⁻¹ * ((Fintype.card A : ℝ) * C.trace.re) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp [hd]

end
end ICO.ChoiMass

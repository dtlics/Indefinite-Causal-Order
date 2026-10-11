import ICO.VaryingCoherence
import ICO.AverageCoherence
import ICO.FirstQueryInstrument
import Mathlib.MeasureTheory.Integral.Prod

/-! # Haar average of the physical control coherence -/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.CausalReverse ICO.CircuitOutput
open ICO.ClassicalDilation ICO.AverageCoherence
open ICO.ControlCoherence (controlVector)
open ICO.VaryingMemoryReverse ICO.VaryingCoherence

namespace ICO.VaryingAverage

set_option maxHeartbeats 350000
noncomputable section
universe u
variable {A M N Z : Type u}
variable [Fintype A] [Fintype M] [Fintype N] [Fintype Z]
variable [DecidableEq A] [DecidableEq M] [DecidableEq N] [DecidableEq Z]

theorem fullBranchMap_apply_continuous
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (X : CMatrix A) :
    Continuous (fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      fullBranchMap R pre UV.1 UV.2 X) := by
  simp only [fullBranchMap, LinearMap.comp_apply, ICO.AdaptiveReverse.preparedMap_apply]
  simp_rw [ICO.OneQueryTree.NormalForm.channel_apply, oracleChannel_apply]
  apply continuous_finset_sum
  intro j hj
  apply (R.post j).map.continuous_of_finiteDimensional.comp
  have hU : Continuous (fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      Matrix.kronecker (UV.1 : CMatrix A) (1 : CMatrix M)) :=
    kronecker_one_continuous (continuous_subtype_val.comp continuous_fst)
  have hV : Continuous (fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      Matrix.kronecker (UV.2 : CMatrix A) (1 : CMatrix N)) :=
    kronecker_one_continuous (continuous_subtype_val.comp continuous_snd)
  exact (hV.matrix_mul ((continuous_const.matrix_mul
    ((hU.matrix_mul continuous_const).matrix_mul hU.matrix_conjTranspose)).matrix_mul
      continuous_const)).matrix_mul hV.matrix_conjTranspose

theorem groupedChoi_continuous
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) :
    Continuous (fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      groupedChoi R pre UV.1 UV.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (fullBranchMap_apply_continuous R pre (Matrix.single i.1.1 j.1.1 1)).matrix_elem
    (i.1.2, i.2) (j.1.2, j.2)

theorem selectedOverlap_continuous
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (z : Z)
    {T : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ → CMatrix A}
    (hT : Continuous T) :
    Continuous (fun UV => selectedOverlap R pre (UV.1 : CMatrix A)
      (UV.2 : CMatrix A) z (T UV)) := by
  simp_rw [selectedOverlap_eq_quadratic]
  apply Continuous.const_mul
  apply Complex.continuous_re.comp
  have hv := controlVector_continuous hT z
  exact hv.star.dotProduct ((groupedChoi_continuous R pre).matrix_mulVec hv)

theorem controlCoherence_continuous
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (z z' : Z)
    {T S : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ → CMatrix A}
    (hT : Continuous T) (hS : Continuous S) :
    Continuous (fun UV => controlCoherence R pre UV.1 UV.2 z z' (T UV) (S UV)) := by
  unfold controlCoherence
  apply Continuous.const_mul
  exact (controlVector_continuous hT z).star.dotProduct
    ((groupedChoi_continuous R pre).matrix_mulVec (controlVector_continuous hS z'))

/-- The physical retained control coherence between forward and reverse
targets has Haar-average norm at most the actual branch weight times δ. -/
theorem average_controlCoherence_bound [Nontrivial A]
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (z z' : Z) :
    (∫ U : Matrix.unitaryGroup A ℂ, ∫ V : Matrix.unitaryGroup A ℂ,
      ‖controlCoherence R pre U V z z'
        ((V : CMatrix A) * (U : CMatrix A))
        ((U : CMatrix A) * (V : CMatrix A))‖
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
      ICO.FirstQueryInstrument.krausWeight pre * reverseFactor (A := A) := by
  let μ := unitaryHaarMeasure (a := A)
  let T := fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
    (UV.2 : CMatrix A) * (UV.1 : CMatrix A)
  let S := fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
    (UV.1 : CMatrix A) * (UV.2 : CMatrix A)
  let f := fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
    ‖controlCoherence R pre UV.1 UV.2 z z' (T UV) (S UV)‖
  let r := fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
    selectedOverlap R pre (UV.1 : CMatrix A) (UV.2 : CMatrix A) z' (S UV)
  have hU := continuous_subtype_val.comp
    (continuous_fst : Continuous (Prod.fst : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ → _))
  have hV := continuous_subtype_val.comp
    (continuous_snd : Continuous (Prod.snd : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ → _))
  have hT : Continuous T := hV.matrix_mul hU
  have hS : Continuous S := hU.matrix_mul hV
  have hf : Integrable f (μ.prod μ) :=
    (controlCoherence_continuous R pre z z' hT hS).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr : Integrable r (μ.prod μ) :=
    (selectedOverlap_continuous R pre z' hS).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint (UV) : f UV ^ 2 ≤ ICO.FirstQueryInstrument.krausWeight pre * r UV := by
    rw [show f UV ^ 2 = Complex.normSq
      (controlCoherence R pre UV.1 UV.2 z z' (T UV) (S UV)) by exact Complex.sq_norm _]
    exact (controlCoherence_sq_le R pre UV.1 UV.2 z z' (T UV) (S UV)).trans
      (mul_le_mul_of_nonneg_right
        (selectedOverlap_le_branchWeight R pre UV.1 UV.2 z (T UV)
          (product_unitary UV.2 UV.1))
        (selectedOverlap_nonneg R pre UV.1 UV.2 z' (S UV)))
  have hmean : (∫ UV, r UV ∂μ.prod μ) ≤
      ICO.FirstQueryInstrument.krausWeight pre * reverseFactor (A := A) ^ 2 := by
    rw [integral_prod _ hr]
    exact selected_control_reverse_bound R pre z'
  have h := integral_norm_of_square_bound (μ.prod μ) hf hr
    (ICO.FirstQueryInstrument.krausWeight_nonneg pre) reverseFactor_pos
    (fun UV => selectedOverlap_nonneg R pre UV.1 UV.2 z' (S UV)) hpoint hmean
  rw [integral_prod _ hf] at h
  exact h

end
end ICO.VaryingAverage


import ICO.ControlCoherence
import ICO.FirstQueryInstrument
import Mathlib.MeasureTheory.Integral.Prod

/-! # Haar average of the physical control coherence -/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.CausalReverse ICO.CircuitOutput
open ICO.ControlOutcomeReverse ICO.ControlCoherence ICO.ClassicalDilation

namespace ICO.AverageCoherence

set_option maxHeartbeats 350000
noncomputable section
universe u
variable {A M Z : Type u}
variable [Fintype A] [Fintype M] [Fintype Z]
variable [DecidableEq A] [DecidableEq M] [DecidableEq Z]

local instance integrationCMatrixContinuousENorm {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

instance unitaryGroupSecondCountableTopology :
    SecondCountableTopology (Matrix.unitaryGroup A ℂ) := by
  haveI : SecondCountableTopology (CMatrix A) := by
    change SecondCountableTopology (A → A → ℂ)
    infer_instance
  change SecondCountableTopology ({x // x ∈ (Matrix.unitaryGroup A ℂ : Set (CMatrix A))})
  infer_instance

theorem kronecker_one_continuous {X : Type*} [TopologicalSpace X]
    {f : X → CMatrix A} (hf : Continuous f) :
    Continuous (fun x => Matrix.kronecker (f x) (1 : CMatrix M)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (hf.matrix_elem i.1 j.1).mul continuous_const

theorem fullBranchMap_apply_continuous
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
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
      Matrix.kronecker (UV.2 : CMatrix A) (1 : CMatrix M)) :=
    kronecker_one_continuous (continuous_subtype_val.comp continuous_snd)
  exact (hV.matrix_mul ((continuous_const.matrix_mul
    ((hU.matrix_mul continuous_const).matrix_mul hU.matrix_conjTranspose)).matrix_mul
      continuous_const)).matrix_mul hV.matrix_conjTranspose

theorem groupedChoi_continuous
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) :
    Continuous (fun UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      groupedChoi R pre UV.1 UV.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (fullBranchMap_apply_continuous R pre (Matrix.single i.1.1 j.1.1 1)).matrix_elem
    (i.1.2, i.2) (j.1.2, j.2)

theorem controlVector_continuous {X : Type*} [TopologicalSpace X]
    {f : X → CMatrix A} (hf : Continuous f) (z : Z) :
    Continuous (fun x => controlVector (targetVector (f x)) z) := by
  refine continuous_pi fun i => ?_
  by_cases hi : i.2 = z
  · simpa [controlVector, hi, targetVector] using hf.matrix_elem i.1.2 i.1.1
  · simpa [controlVector, hi] using (continuous_const : Continuous (fun _ : X => (0 : ℂ)))

theorem selectedOverlap_continuous
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
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
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (z z' : Z)
    {T S : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ → CMatrix A}
    (hT : Continuous T) (hS : Continuous S) :
    Continuous (fun UV => controlCoherence R pre UV.1 UV.2 z z' (T UV) (S UV)) := by
  unfold controlCoherence
  apply Continuous.const_mul
  exact (controlVector_continuous hT z).star.dotProduct
    ((groupedChoi_continuous R pre).matrix_mulVec (controlVector_continuous hS z'))

theorem scalar_young_bound {p r c δ : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (h : c ^ 2 ≤ p * r) :
    2 * δ * c ≤ p * δ ^ 2 + r := by
  by_cases hp0 : p = 0
  · subst p
    have hc : c = 0 := by nlinarith [sq_nonneg c]
    simp_all
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    nlinarith [sq_nonneg (c - p * δ)]

theorem integral_norm_of_square_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f r : Ω → ℝ} {p δ : ℝ} (hf : Integrable f μ) (hr : Integrable r μ)
    (hp : 0 ≤ p) (hδ : 0 < δ) (hr0 : ∀ x, 0 ≤ r x)
    (hpoint : ∀ x, f x ^ 2 ≤ p * r x)
    (hmean : (∫ x, r x ∂μ) ≤ p * δ ^ 2) :
    (∫ x, f x ∂μ) ≤ p * δ := by
  have hi := integral_mono (hf.const_mul (2 * δ)) ((integrable_const (p * δ ^ 2)).add hr)
    (fun x => scalar_young_bound hp (hr0 x) (hpoint x) (δ := δ))
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (integrable_const _) hr] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  nlinarith

def reverseFactor : ℝ :=
  (Fintype.card A : ℝ)⁻¹ + (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)

theorem reverseFactor_pos [Nontrivial A] : 0 < reverseFactor (A := A) := by
  have hd : 1 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := A)
  have hd0 : 0 < (Fintype.card A : ℝ) := by linarith
  have hden : 0 < (Fintype.card A : ℝ) ^ 2 - 1 := by nlinarith
  exact add_pos (inv_pos.mpr hd0) (div_pos hd0 hden)

theorem product_unitary (U V : Matrix.unitaryGroup A ℂ) :
    ((U : CMatrix A) * (V : CMatrix A)).conjTranspose *
      ((U : CMatrix A) * (V : CMatrix A)) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U : CMatrix A).conjTranspose]
  have hU : (U : CMatrix A).conjTranspose * (U : CMatrix A) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  have hV : (V : CMatrix A).conjTranspose * (V : CMatrix A) = 1 :=
    Matrix.UnitaryGroup.star_mul_self V
  simpa [hU] using hV

/-- The physical retained control coherence between forward and reverse
targets has Haar-average norm at most the actual branch weight times δ. -/
theorem average_controlCoherence_bound [Nontrivial A]
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
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
end ICO.AverageCoherence

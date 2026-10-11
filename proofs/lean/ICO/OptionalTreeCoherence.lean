import ICO.OptionalTwoQuery
import ICO.TreeCoherence

/-! # Coherence of a genuine adaptive two-query tree

The order branches are extracted from the operator-valued quantum instrument.
Their weights and exact sum are derived from its completeness relation.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.CausalReverse ICO.CircuitOutput ICO.ClassicalDilation
open ICO.VaryingMemoryReverse ICO.VaryingCoherence ICO.AverageCoherence ICO.VaryingAverage
open ICO.TreeCoherence (mapCoherence mapCoherence_sum hermitian_pairing_star)
open ICO.FirstQueryInstrument

namespace ICO.OptionalTreeCoherence

set_option maxHeartbeats 400000
noncomputable section
universe u
variable {A M Z N J : Type u}
variable [Fintype A] [Fintype M] [Fintype Z] [Fintype N] [Fintype J]
variable [DecidableEq A] [DecidableEq M] [DecidableEq Z] [DecidableEq N] [DecidableEq J]

theorem controlCoherence_star
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ)
    (z z' : Z) (T S : CMatrix A) :
    star (controlCoherence R pre U V z z' T S) =
      controlCoherence R pre U V z' z S T := by
  unfold controlCoherence
  rw [star_mul, hermitian_pairing_star _ (groupedChoi_pos R pre U V).isHermitian]
  simp [mul_comm]

theorem controlCoherence_norm_swap
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ)
    (z z' : Z) (T S : CMatrix A) :
    ‖controlCoherence R pre U V z z' T S‖ =
      ‖controlCoherence R pre U V z' z S T‖ := by
  calc
    _ = ‖star (controlCoherence R pre U V z z' T S)‖ := (norm_star _).symm
    _ = _ := congrArg norm (controlCoherence_star R pre U V z z' T S)

def canonicalCoherence
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (z z' : Z)
    (UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ) : ℂ :=
  controlCoherence R pre UV.1 UV.2 z z'
    ((UV.2 : CMatrix A) * (UV.1 : CMatrix A))
    ((UV.1 : CMatrix A) * (UV.2 : CMatrix A))

theorem canonicalCoherence_continuous
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (z z' : Z) :
    Continuous (canonicalCoherence R pre z z') := by
  apply ICO.VaryingAverage.controlCoherence_continuous
  · exact (continuous_subtype_val.comp continuous_snd).matrix_mul
      (continuous_subtype_val.comp continuous_fst)
  · exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)

theorem canonicalCoherence_average [Nontrivial A]
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (z z' : Z) :
    (∫ UV, ‖canonicalCoherence R pre z z' UV‖
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))) ≤
      krausWeight pre * reverseFactor (A := A) := by
  have hf := (canonicalCoherence_continuous R pre z z').norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
      (μ := (unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A)))
  rw [integral_prod _ hf]
  exact ICO.VaryingAverage.average_controlCoherence_bound R pre z z'

def branchMap
    (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z)) (j : R.Branch)
    (U V : Matrix.unitaryGroup A ℂ) : MatrixMap A (A × Z) :=
  match R.order j with
  | .firstThenSecond => fullBranchMap (R.rest j) (R.pre j) U V
  | .secondThenFirst => fullBranchMap (R.rest j) (R.pre j) V U

theorem normalForm_map_sum
    (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z))
    (U V : Matrix.unitaryGroup A ℂ) :
    R.map U V = ∑ j, branchMap R j U V := by
  ext X a b
  rw [ICO.OptionalTwoQuery.NormalForm.map_apply]
  simp only [LinearMap.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  cases hjorder : R.order j <;>
    simp [branchMap, hjorder, ICO.OptionalTwoQuery.firstUnitary,
      ICO.OptionalTwoQuery.secondUnitary, fullBranchMap, ICO.AdaptiveReverse.preparedMap_apply]

theorem normalForm_weights_sum [Nonempty A]
    (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z)) :
    (∑ j, krausWeight (R.pre j)) = 1 := by
  have h := congrArg (fun X : CMatrix A => X.trace.re) R.complete
  have hs : (∑ j, ((R.pre j).conjTranspose * R.pre j).trace.re) =
      (Fintype.card A : ℝ) := by
    simpa [Matrix.trace_sum] using h
  simp only [krausWeight, ← Finset.sum_div, hs]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)
def branchCoherence (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z))
    (j : R.Branch) (z z' : Z)
    (UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ) : ℂ :=
  mapCoherence (branchMap R j UV.1 UV.2) z z'
    ((UV.2 : CMatrix A) * (UV.1 : CMatrix A))
    ((UV.1 : CMatrix A) * (UV.2 : CMatrix A))

theorem branchCoherence_order
    (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z)) (j : R.Branch)
    (z z' : Z) (UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ) :
    branchCoherence R j z z' UV =
      match R.order j with
      | .firstThenSecond => canonicalCoherence (R.rest j) (R.pre j) z z' UV
      | .secondThenFirst => star (canonicalCoherence (R.rest j) (R.pre j) z' z UV.swap) := by
  cases hj : R.order j
  · simp only [branchCoherence, branchMap, hj]
    rfl
  · unfold branchCoherence branchMap
    rw [hj]
    exact (controlCoherence_star _ _ _ _ _ _ _ _).symm

theorem branchCoherence_continuous
    (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z)) (j : R.Branch) (z z' : Z) :
    Continuous (branchCoherence R j z z') := by
  cases ho : R.order j
  · convert canonicalCoherence_continuous (R.rest j) (R.pre j) z z' using 1
    funext UV
    rw [branchCoherence_order, ho]
  · convert ((canonicalCoherence_continuous (R.rest j) (R.pre j) z' z).comp
      continuous_swap).star using 1
    funext UV
    rw [branchCoherence_order, ho]
    rfl

theorem branchCoherence_average [Nontrivial A]
    (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z)) (j : R.Branch) (z z' : Z) :
    (∫ UV, ‖branchCoherence R j z z' UV‖
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))) ≤
      krausWeight (R.pre j) * reverseFactor (A := A) := by
  simp_rw [branchCoherence_order]
  cases R.order j
  · exact canonicalCoherence_average _ _ _ _
  · simp only [norm_star]
    rw [integral_prod_swap (fun UV => ‖canonicalCoherence (R.rest j) (R.pre j) z' z UV‖)]
    exact canonicalCoherence_average _ _ _ _

def normalFormCoherence (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z))
    (z z' : Z) (UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ) : ℂ :=
  mapCoherence (R.map UV.1 UV.2) z z'
    ((UV.2 : CMatrix A) * (UV.1 : CMatrix A))
    ((UV.1 : CMatrix A) * (UV.2 : CMatrix A))

theorem normalFormCoherence_sum
    (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z)) (z z' : Z)
    (UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ) :
    normalFormCoherence R z z' UV = ∑ j, branchCoherence R j z z' UV := by
  unfold normalFormCoherence branchCoherence
  rw [normalForm_map_sum, mapCoherence_sum]

/-- Both causal orders and all internal adaptive instruments are included in
the theorem; only the actual two-query operational tree is supplied. -/
theorem normalForm_average_bound [Nontrivial A]
    (R : ICO.OptionalTwoQuery.NormalForm A A (A × Z)) (z z' : Z) :
    (∫ UV, ‖normalFormCoherence R z z' UV‖
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))) ≤
      reverseFactor (A := A) := by
  let μ := (unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))
  have hj (j : R.Branch) : Integrable (fun UV => ‖branchCoherence R j z z' UV‖) μ :=
    (branchCoherence_continuous R j z z').norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : Continuous (fun UV => ∑ j, branchCoherence R j z z' UV) :=
    continuous_finsetSum _ (fun j _ => branchCoherence_continuous R j z z')
  have hs : Integrable (fun UV => ‖∑ j, branchCoherence R j z z' UV‖) μ :=
    hc.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [normalFormCoherence_sum]
  calc
    _ ≤ ∫ UV, ∑ j, ‖branchCoherence R j z z' UV‖ ∂μ :=
      integral_mono hs (integrable_finset_sum _ (fun j _ => hj j))
        (fun UV => norm_sum_le _ _)
    _ = ∑ j, ∫ UV, ‖branchCoherence R j z z' UV‖ ∂μ :=
      integral_finset_sum _ (fun j _ => hj j)
    _ ≤ ∑ j, krausWeight (R.pre j) * reverseFactor (A := A) :=
      Finset.sum_le_sum (fun j _ => branchCoherence_average R j z z')
    _ = _ := by rw [← Finset.sum_mul, normalForm_weights_sum R, one_mul]

theorem queryTree_average_bound [Nontrivial A] [Nonempty M] [Nonempty Z]
    (a₀ : A) (tree : ICO.OptionalTwoQuery.QueryTree A M (A × Z) A) (z z' : Z) :
    (∫ UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ,
      ‖mapCoherence (tree.channel (oracleChannel UV.1) (oracleChannel UV.2)).map z z'
        ((UV.2 : CMatrix A) * (UV.1 : CMatrix A))
        ((UV.1 : CMatrix A) * (UV.2 : CMatrix A))‖
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))) ≤
      reverseFactor (A := A) := by
  have h := normalForm_average_bound (tree.normalForm a₀) z z'
  simpa only [normalFormCoherence, ICO.OptionalTwoQuery.QueryTree.normalForm_correct] using h

end
end ICO.OptionalTreeCoherence


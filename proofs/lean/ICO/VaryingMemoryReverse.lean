import ICO.ControlOutcomeReverse
import ICO.ChoiMass

/-! # Reverse-composition with different memory at the two query cuts

This adapter allows a missing query to be inserted on a fresh discarded
register while retaining the entire earlier query space as private memory.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT MeasureTheory ICO.CausalReverse ICO.CircuitComb ICO.CircuitOutput
open ICO.OrderedCircuit ICO.ClassicalDilation ICO.ControlOutcomeReverse
open ICO.InstrumentCompression

namespace ICO.VaryingMemoryReverse

set_option maxHeartbeats 300000
noncomputable section
universe u
variable {A M N Z K J : Type u}
variable [Fintype A] [Fintype M] [Fintype N] [Fintype Z] [Fintype K] [Fintype J]
variable [DecidableEq A] [DecidableEq M] [DecidableEq N] [DecidableEq Z]
variable [DecidableEq K] [DecidableEq J]

def stackMid (instrument : Instrument (A × M) (A × N) J) :
    Matrix (A × (N × J)) (A × M) ℂ :=
  fun anj bm => instrument.op anj.2.2 (anj.1, anj.2.1) bm

theorem stackMid_complete (instrument : Instrument (A × M) (A × N) J) :
    (stackMid instrument).conjTranspose * stackMid instrument = 1 := by
  ext i j
  have h := congrFun (congrFun instrument.complete i) j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type] at h
  change (∑ anj : A × (N × J),
    star (instrument.op anj.2.2 (anj.1, anj.2.1) i) *
      instrument.op anj.2.2 (anj.1, anj.2.1) j) = _
  simp only [Fintype.sum_prod_type]
  have hswap :
      (∑ a : A, ∑ n : N, ∑ k : J,
        star (instrument.op k (a, n) i) * instrument.op k (a, n) j) =
      ∑ k : J, ∑ a : A, ∑ n : N,
        star (instrument.op k (a, n) i) * instrument.op k (a, n) j := by
    simpa only [Fintype.sum_prod_type] using
      (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun (an : A × N) (k : J) =>
          star (instrument.op k an i) * instrument.op k an j))
  rw [hswap]
  exact h

theorem controlledPost_oracle_stack (W : J → Matrix (A × K) (A × N) ℂ)
    (instrument : Instrument (A × M) (A × N) J) (V : CMatrix A) (k : K) (j : J) :
    postKraus (controlledPost W) (k, j) *
      Matrix.kronecker V (1 : CMatrix (N × J)) * stackMid instrument =
        postKraus (W j) k * Matrix.kronecker V (1 : CMatrix N) * instrument.op j := by
  ext f i
  conv_lhs => rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp_rw [ICO.ClassicalDilation.controlledPost_oracle_entry]
  conv_rhs => rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [stackMid, Fintype.sum_prod_type, ite_mul]

theorem circuitKraus_controlled (pre : Matrix (A × M) A ℂ)
    (instrument : Instrument (A × M) (A × N) J)
    (W : J → Matrix (A × K) (A × N) ℂ) (U V : CMatrix A) (k : K) (j : J) :
    circuitKraus pre (stackMid instrument) (controlledPost W) U V (k, j) =
      postKraus (W j) k * Matrix.kronecker V (1 : CMatrix N) *
        instrument.op j * Matrix.kronecker U (1 : CMatrix M) * pre := by
  unfold circuitKraus
  rw [controlledPost_oracle_stack]

def normalControlPost (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z)) :
    Matrix (A × ((Z × ((A × N) × (A × Z))) × R.Branch)) (A × (N × R.Branch)) ℂ :=
  controlledPost (fun j => forgetControlIsometry (R.post j))

theorem normalControlPost_complete
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z)) :
    (normalControlPost R).conjTranspose * normalControlPost R = 1 :=
  controlledPost_complete _ (fun j => forgetControlIsometry_complete (R.post j))

def selectedKraus (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : CMatrix A) (z : Z)
    (kj : ((A × N) × (A × Z)) × R.Branch) : CMatrix A :=
  outcomeKraus (R.post kj.2) z kj.1 * Matrix.kronecker V (1 : CMatrix N) *
    R.pre.op kj.2 * Matrix.kronecker U (1 : CMatrix M) * pre

def selectedMap (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : CMatrix A) (z : Z) : MatrixMap A A :=
  MatrixMap.ofKraus (selectedKraus R pre U V z)

def fullBranchMap (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) : MatrixMap A (A × Z) :=
  ((R.channel (oracleChannel V)).map.comp (oracleChannel U).map).comp
    (ICO.AdaptiveReverse.preparedMap pre)

theorem fullBranchMap_cp (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) :
    MatrixMap.IsCompletelyPositive (fullBranchMap R pre U V) := by
  apply MatrixMap.isCompletelyPositive_comp
  · exact MatrixMap.isCompletelyPositive_comp _ _
      (R.channel (oracleChannel V)).completelyPositive (oracleChannel U).completelyPositive
  · exact MatrixMap.ofKraus_completelyPositive _

theorem fullBranchChoi_trace
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) :
    (MatrixMap.choi (fullBranchMap R pre U V)).trace =
      (pre.conjTranspose * pre).trace := by
  rw [ICO.ChoiMass.choi_trace_eq_apply_one]
  unfold fullBranchMap
  simp only [LinearMap.comp_apply, ICO.AdaptiveReverse.preparedMap_apply]
  rw [(R.channel (oracleChannel V)).tracePreserving, (oracleChannel U).tracePreserving]
  rw [Matrix.mul_one, Matrix.trace_mul_comm]

/-- The selected map is exactly the diagonal block of the actual retained
output control register, not a chosen dilation of an already-forgotten control. -/
theorem selectedMap_eq_controlSlice
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (z : Z) (X : CMatrix A) :
    selectedMap R pre (U : CMatrix A) (V : CMatrix A) z X =
      controlSlice ((R.channel (oracleChannel V)).map
        ((oracleChannel U).map (pre * X * pre.conjTranspose))) z := by
  rw [ICO.OneQueryTree.NormalForm.channel_apply, oracleChannel_apply, controlSlice_sum]
  simp_rw [oracleChannel_apply, channel_controlSlice]
  simp only [selectedMap, selectedKraus, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The selected Choi matrix is the literal diagonal block of the full retained
control Choi matrix. This is the interface to positive-block coherence bounds. -/
theorem selectedChoi_eq_controlBlock
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (z : Z) :
    MatrixMap.choi (selectedMap R pre (U : CMatrix A) (V : CMatrix A) z) =
      (MatrixMap.choi (fullBranchMap R pre U V)).submatrix
        (fun pa : A × A => (pa.1, (pa.2, z))) (fun pa : A × A => (pa.1, (pa.2, z))) := by
  ext i j
  have h := congrFun (congrFun
    (selectedMap_eq_controlSlice R pre U V z (Matrix.single i.1 j.1 1)) i.2) j.2
  simpa [MatrixMap.choi, Matrix.submatrix, fullBranchMap, controlSlice,
    ICO.AdaptiveReverse.preparedMap_apply] using h

def controlOutcomes (z : Z) : Finset ((Z × K) × J) :=
  Finset.univ.filter (fun kj => kj.1.1 = z)

theorem sum_controlOutcomes {B : Type*} [AddCommMonoid B]
    (z : Z) (g : ((Z × K) × J) → B) :
    (∑ kj ∈ controlOutcomes (K := K) (J := J) z, g kj) =
      ∑ k : K, ∑ j : J, g ((z, k), j) := by
  simp [controlOutcomes, Finset.sum_filter, Fintype.sum_prod_type, ite_and]
  rw [Finset.sum_eq_single z]
  · simp
  · intro z' hz' hne
    simp [hne]
  · simp

def selectedComb (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (z : Z) : CMatrix (SixWires A) :=
  outcomeComb (normalControlPost R) (rankOneMatrix (preMiddleVector pre (stackMid R.pre)))
    (controlOutcomes z)

theorem selectedComb_outputChoi
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : CMatrix A) (z : Z) :
    outputChoi (selectedComb R pre z) U V = MatrixMap.choi (selectedMap R pre U V z) := by
  unfold selectedComb
  rw [outputChoi_outcome_eq_circuit, sum_controlOutcomes]
  unfold selectedMap
  rw [MatrixMap.choi_ofKraus]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  unfold normalControlPost
  rw [circuitKraus_controlled]
  rfl

def selectedOverlap (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : CMatrix A) (z : Z) (T : CMatrix A) : ℝ :=
  ((Fintype.card A : ℝ) ^ 2)⁻¹ *
    tracePair (MatrixMap.choi (selectedMap R pre U V z)) (rankOneMatrix (targetVector T))

theorem selectedOverlap_eq_outcomeOverlap
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : CMatrix A) (z : Z) (T : CMatrix A) :
    selectedOverlap R pre U V z T = outputOverlap (selectedComb R pre z) U V T := by
  unfold selectedOverlap outputOverlap
  rw [selectedComb_outputChoi]

/-- The selected final-control population obeys the reverse bound with the
completed preprocessing branch's actual weight. -/
theorem selected_control_reverse_bound [Nontrivial A]
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × N) (A × Z))
    (pre : Matrix (A × M) A ℂ) (z : Z) :
    (∫ U : Matrix.unitaryGroup A ℂ, ∫ V : Matrix.unitaryGroup A ℂ,
      selectedOverlap R pre (U : CMatrix A) (V : CMatrix A) z
        ((U : CMatrix A) * (V : CMatrix A))
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
      ((pre.conjTranspose * pre).trace.re / (Fintype.card A : ℝ)) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  simp_rw [selectedOverlap_eq_outcomeOverlap]
  let B := rankOneMatrix (preMiddleVector pre (stackMid R.pre))
  let C := circuitComb pre (stackMid R.pre) (normalControlPost R)
  have hparent : selectedComb R pre z ≤ C :=
    outcomeComb_le_parent (normalControlPost R) (rankOneMatrix_pos _) (controlOutcomes z)
  have h := outcome_outputOverlap_bound (selectedComb R pre z) C (partialTraceB B)
    hparent (circuitComb_pos _ _ _) (partialTraceB_posSemidef (rankOneMatrix_pos _))
    (circuitComb_causal _ _ _ (normalControlPost_complete R))
  dsimp [C] at h
  rw [circuitComb_trace pre (stackMid R.pre) (stackMid_complete R.pre)
    (normalControlPost R) (normalControlPost_complete R)] at h
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hweight : (Fintype.card A : ℝ) ^ 2 * (pre.conjTranspose * pre).trace.re /
      (Fintype.card A : ℝ) ^ 3 =
      (pre.conjTranspose * pre).trace.re / (Fintype.card A : ℝ) := by
    field_simp [hd]
    <;> ring
  simpa only [hweight] using h

end
end ICO.VaryingMemoryReverse



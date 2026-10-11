import ICO.ClassicalDilation
import ICO.TwoQueryTree

/-! # Reverse-composition bound for an actual adaptive continuation

The Haar bound is transferred to a recursive adaptive query tree via its proved
normal form and the explicit history-register circuit realization.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT MeasureTheory ICO.CausalReverse ICO.CircuitOutput
open ICO.ClassicalDilation ICO.OrderedCircuit

namespace ICO.AdaptiveReverse

set_option maxHeartbeats 200000
noncomputable section

universe u
variable {A M : Type u} [Fintype A] [Fintype M] [DecidableEq A] [DecidableEq M]

def preparedMap (pre : Matrix (A × M) A ℂ) : MatrixMap A (A × M) :=
  MatrixMap.ofKraus (fun (_ : PUnit.{u + 1}) => pre)

theorem preparedMap_apply (pre : Matrix (A × M) A ℂ) (X : CMatrix A) :
    preparedMap pre X = pre * X * pre.conjTranspose := by
  simp [preparedMap, MatrixMap.ofKraus]

def branchMap (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A)
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) : MatrixMap A A :=
  ((R.channel (oracleChannel V)).map.comp (oracleChannel U).map).comp (preparedMap pre)

theorem branchMap_eq_circuit (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A)
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) :
    branchMap R pre U V = MatrixMap.ofKraus
      (circuitKraus pre (normalMid R) (normalPost R) (U : CMatrix A) (V : CMatrix A)) := by
  apply LinearMap.ext
  intro X
  simpa [branchMap, preparedMap_apply] using (normalForm_circuit_map R pre U V X).symm

/-- Choi overlap of the actual adaptive branch, normalizing input and target. -/
def branchOverlap (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A)
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (T : CMatrix A) : ℝ :=
  ((Fintype.card A : ℝ) ^ 2)⁻¹ * tracePair (MatrixMap.choi (branchMap R pre U V))
    (rankOneMatrix (targetVector T))

theorem branchOverlap_eq_circuit (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A)
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (T : CMatrix A) :
    branchOverlap R pre U V T =
      circuitOverlap pre (normalMid R) (normalPost R) (U : CMatrix A) (V : CMatrix A) T := by
  unfold branchOverlap
  rw [branchMap_eq_circuit, MatrixMap.choi_ofKraus]
  rfl

theorem adaptive_branch_reverse_bound [Nontrivial A]
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) A)
    (pre : Matrix (A × M) A ℂ) :
    (∫ U : Matrix.unitaryGroup A ℂ, ∫ V : Matrix.unitaryGroup A ℂ,
      branchOverlap R pre U V ((U : CMatrix A) * (V : CMatrix A))
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
      ((pre.conjTranspose * pre).trace.re / (Fintype.card A : ℝ)) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  simp_rw [branchOverlap_eq_circuit]
  exact circuit_reverse_bound pre (normalMid R) (normalMid_complete R)
    (normalPost R) (normalPost_complete R)

def treeBranchMap (tree : ICO.OneQueryTree.QueryTree (A × M) A (A × M))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) : MatrixMap A A :=
  ((tree.channel (oracleChannel V)).map.comp (oracleChannel U).map).comp (preparedMap pre)

def treeBranchOverlap (tree : ICO.OneQueryTree.QueryTree (A × M) A (A × M))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (T : CMatrix A) : ℝ :=
  ((Fintype.card A : ℝ) ^ 2)⁻¹ * tracePair (MatrixMap.choi (treeBranchMap tree pre U V))
    (rankOneMatrix (targetVector T))

/-- The reverse bound for a genuine recursive adaptive strategy after its
first selected query. No normal-form or circuit-representation hypothesis is
required from the caller. -/
theorem queryTree_reverse_bound [Nontrivial A]
    (tree : ICO.OneQueryTree.QueryTree (A × M) A (A × M))
    (pre : Matrix (A × M) A ℂ) :
    (∫ U : Matrix.unitaryGroup A ℂ, ∫ V : Matrix.unitaryGroup A ℂ,
      treeBranchOverlap tree pre U V ((U : CMatrix A) * (V : CMatrix A))
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
      ((pre.conjTranspose * pre).trace.re / (Fintype.card A : ℝ)) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  have heq (U V : Matrix.unitaryGroup A ℂ) (T : CMatrix A) :
      treeBranchOverlap tree pre U V T = branchOverlap tree.normalForm pre U V T := by
    unfold treeBranchOverlap branchOverlap treeBranchMap branchMap
    rw [ICO.OneQueryTree.QueryTree.normalForm_correct]
  simp_rw [heq]
  exact adaptive_branch_reverse_bound tree.normalForm pre

end
end ICO.AdaptiveReverse

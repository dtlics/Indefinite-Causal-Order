import ICO.CoupledChoi
import ICO.GramContinuity
import ICO.BudgetContinuity
import ICO.AtMostFamilyCoherence

/-! Physical Haar instances of the adaptive simulation lower bound. -/

namespace ICO.C4PhysicalEnsemble
open Matrix QIT MeasureTheory ICO.HaarFamily ICO.CompositionGram ICO.ReverseCompositionGram
open ICO.CompositionGramAverage ICO.GramWitness ICO.CoupledChoi ICO.ChoiWitnessState
open ICO.AtMostFamilyCoherence ICO.TreeCoherence ICO.AverageCoherence
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

abbrev Sample (A : Type) [Fintype A] [DecidableEq A] (r : ℕ) :=
  (Fin (r+1) → Unitary (A := A)) × (Fin (r+1) → Unitary (A := A))

def sampledFreshTree {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r+1) :=
  ICO.FreshBudgetCompile.fresh (r := r+1) tree Finset.univ Finset.univ
    (by simpa using hq) (by simpa using hq)

def ordinary {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A)
    (UV : Sample A r) : State ((A × A) × Bool) :=
  normalizedChoiState (ICO.SamplingOrdinary.ordinaryChannel tree (familyChannels UV.1 UV.2))

def fresh {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A)
    (hq : q ≤ r+1) (UV : Sample A r) : State ((A × A) × Bool) :=
  normalizedChoiState ((sampledFreshTree tree hq).channel (familyChannels UV.1 UV.2))

theorem ordinary_matrix_continuous {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) :
    Continuous (fun UV : Sample A r => (ordinary tree UV).matrix) := by
  have hfirst : Continuous (fun UV : Sample A r => MatrixMap.choi
      (ICO.SamplingOrdinary.uniformChannel (fun i => familyChannels (M := M) UV.1 UV.2 (.inl i))).map) := by
    apply ICO.BudgetQueryTree.uniformChannel_choi_continuous
    intro i
    exact oracleChoi_continuous.comp ((continuous_apply i).comp continuous_fst)
  have hsecond : Continuous (fun UV : Sample A r => MatrixMap.choi
      (ICO.SamplingOrdinary.uniformChannel (fun j => familyChannels (M := M) UV.1 UV.2 (.inr j))).map) := by
    apply ICO.BudgetQueryTree.uniformChannel_choi_continuous
    intro j
    exact oracleChoi_continuous.comp ((continuous_apply j).comp continuous_snd)
  have hC := tree.channel_choi_continuous _ _ hfirst hsecond
  exact (hC.matrix_submatrix _ _).const_smul _

theorem fresh_matrix_continuous {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r+1) :
    Continuous (fun UV : Sample A r => (fresh tree hq UV).matrix) := by
  have hC := treeChoi_continuous (sampledFreshTree tree hq)
  have he (UV : Sample A r) : MatrixMap.choi
      ((sampledFreshTree tree hq).channel (familyChannels UV.1 UV.2)).map =
      MatrixMap.choi ((sampledFreshTree tree hq).map (fun k => (familyChannels UV.1 UV.2 k).map)) := by
    rw [ICO.AtMostLabelledQueryTree.Tree.channel_map]
  have h : Continuous (fun UV : Sample A r =>
      ((((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ)) • groupedMapChoi
        ((sampledFreshTree tree hq).map (fun k => (familyChannels UV.1 UV.2 k).map))) :=
    (hC.matrix_submatrix _ _).const_smul _
  simpa only [fresh, normalizedChoiState, groupedMapChoi, he] using h

theorem fresh_cross_eq {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r+1)
    (UV : Sample A r) :
    crossNormSum (columns UV.1 UV.2) (reverseColumns UV.1 UV.2) (fresh tree hq UV) =
      ∑ ij : Fin (r+1) × Fin (r+1), ‖familyCoherence (sampledFreshTree tree hq) ij.1 ij.2 false true UV‖ := by
  unfold crossNormSum fresh
  apply Finset.sum_congr rfl
  intro ij hij
  rw [columns_cross_eq_coherence]
  simp only [familyCoherence, ICO.AtMostLabelledQueryTree.Tree.channel_map]

theorem cross_integrable {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r+1) :
    Integrable (fun UV : Sample A r => crossNormSum (columns UV.1 UV.2)
      (reverseColumns UV.1 UV.2) (fresh tree hq UV)) (ensembleMeasure (A := A) r r) := by
  simp_rw [fresh_cross_eq]
  apply Continuous.integrable_of_hasCompactSupport
  · apply continuous_finset_sum
    intro ij hij
    exact (familyCoherence_continuous (sampledFreshTree tree hq) ij.1 ij.2 false true).norm
  · exact HasCompactSupport.of_compactSpace _

theorem cross_mean_bound {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r+1) :
    (∫ UV : Sample A r, crossNormSum (columns UV.1 UV.2)
      (reverseColumns UV.1 UV.2) (fresh tree hq UV) ∂ensembleMeasure (A := A) r r) ≤
        (((r+1)*(r+1) : ℕ) : ℝ) * reverseFactor (A := A) := by
  simp_rw [fresh_cross_eq]
  exact total_coherence_average_bound (sampledFreshTree tree hq) false true

theorem ordinary_fresh_coupling {q r : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A) (hq : q ≤ r+1)
    (UV : Sample A r) :
    (ordinary tree UV).normalizedTraceDistance (fresh tree hq UV) ≤
      (q : ℝ)*(q-1)/(2*(r+1)) := by
  exact_mod_cast normalized_choi_distance_le tree (familyChannels UV.1 UV.2) hq

end
end ICO.C4PhysicalEnsemble

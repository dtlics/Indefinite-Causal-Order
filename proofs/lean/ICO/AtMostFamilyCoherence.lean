import ICO.AtMostSelectedQueryTree
import ICO.AtMostLabelledContinuity
import ICO.HaarFamilyPair
import QIT.Core.Map.ChoiCharacterization

/-! # Full Haar-family coherence for a circuit with distinct oracle labels -/

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarFamily ICO.ClassicalDilation
open ICO.TreeCoherence ICO.AverageCoherence ICO.ControlCoherence ICO.CircuitOutput

namespace ICO.AtMostFamilyCoherence
set_option maxHeartbeats 600000
noncomputable section
variable {A M Z : Type} [Fintype A] [Fintype M] [Fintype Z]
variable [DecidableEq A] [DecidableEq M] [DecidableEq Z]
variable [Nontrivial A] [Nonempty M] [Nonempty Z]

def familyChannels {r s : ℕ} (U : Fin r → Unitary (A := A))
    (V : Fin s → Unitary (A := A)) : Fin r ⊕ Fin s → Channel (A × M) (A × M) :=
  Sum.elim (fun i => oracleChannel (U i)) (fun j => oracleChannel (V j))

theorem oracleChoi_continuous : Continuous (fun U : Unitary (A := A) =>
    MatrixMap.choi (oracleChannel (M := M) U).map) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [MatrixMap.choi, oracleChannel_apply]
  exact (((kronecker_one_continuous continuous_subtype_val).matrix_mul continuous_const).matrix_mul
    (kronecker_one_continuous continuous_subtype_val).matrix_conjTranspose).matrix_elem i.2 j.2

theorem familyChoi_continuous {r s : ℕ} : Continuous
    (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      fun k => MatrixMap.choi ((familyChannels (M := M) UV.1 UV.2) k).map) := by
  apply continuous_pi
  intro k
  cases k with
  | inl i => exact oracleChoi_continuous.comp ((continuous_apply i).comp continuous_fst)
  | inr j => exact oracleChoi_continuous.comp ((continuous_apply j).comp continuous_snd)

theorem treeChoi_continuous {r s : ℕ} {labels : Finset (Fin r ⊕ Fin s)}
    (tree : ICO.AtMostLabelledQueryTree.Tree (Fin r ⊕ Fin s) (A × M) (A × Z) labels A) :
    Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      MatrixMap.choi (tree.map (fun k => (familyChannels UV.1 UV.2 k).map))) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h := tree.eval_continuous
    (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      fun k => MatrixMap.choi ((familyChannels UV.1 UV.2) k).map)
    familyChoi_continuous (fun _ => Matrix.single i.1 j.1 (1 : ℂ)) continuous_const
  simpa only [MatrixMap.ofChoiMatrix_choi, MatrixMap.choi] using h.matrix_elem i.2 j.2

def familyCoherence {r s : ℕ} {labels : Finset (Fin r ⊕ Fin s)}
    (tree : ICO.AtMostLabelledQueryTree.Tree (Fin r ⊕ Fin s) (A × M) (A × Z) labels A)
    (i : Fin r) (j : Fin s) (z z' : Z)
    (UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A))) : ℂ :=
  mapCoherence (tree.map (fun k => (familyChannels UV.1 UV.2 k).map)) z z'
    ((UV.2 j : CMatrix A) * (UV.1 i : CMatrix A))
    ((UV.1 i : CMatrix A) * (UV.2 j : CMatrix A))

theorem familyCoherence_continuous {r s : ℕ} {labels : Finset (Fin r ⊕ Fin s)}
    (tree : ICO.AtMostLabelledQueryTree.Tree (Fin r ⊕ Fin s) (A × M) (A × Z) labels A)
    (i : Fin r) (j : Fin s) (z z' : Z) : Continuous (familyCoherence tree i j z z') := by
  have hU : Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      (UV.1 i : CMatrix A)) := continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
  have hV : Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) =>
      (UV.2 j : CMatrix A)) := continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)
  have hG : Continuous (fun UV : (Fin r → Unitary (A := A)) × (Fin s → Unitary (A := A)) => groupedMapChoi
      (tree.map (fun k => (familyChannels UV.1 UV.2 k).map))) := by
    exact (treeChoi_continuous tree).matrix_submatrix _ _
  unfold familyCoherence mapCoherence
  apply Continuous.const_mul
  exact (controlVector_continuous (hV.matrix_mul hU) z).star.dotProduct
    (hG.matrix_mulVec (controlVector_continuous (hU.matrix_mul hV) z'))

theorem inserted_assignment {r s : ℕ} (i : Fin (r + 1)) (j : Fin (s + 1))
    (RU : Fin r → Unitary (A := A)) (RV : Fin s → Unitary (A := A))
    (U V : Unitary (A := A)) :
    (fun k => (familyChannels (M := M) (i.insertNth U RU) (j.insertNth V RV) k).map) =
      ICO.AtMostSelectedQueryTree.twoAssignment
        (familyChannels (i.insertNth 1 RU) (j.insertNth 1 RV)) (.inl i) (.inr j)
        (oracleChannel U).map (oracleChannel V).map := by
  funext k
  cases k with
  | inl k =>
    by_cases hk : k = i
    · subst k; simp [familyChannels, ICO.AtMostSelectedQueryTree.twoAssignment]
    · obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hk
      subst k
      simp [familyChannels, ICO.AtMostSelectedQueryTree.twoAssignment]
  | inr k =>
    by_cases hk : k = j
    · subst k; simp [familyChannels, ICO.AtMostSelectedQueryTree.twoAssignment]
    · obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hk
      subst k
      simp [familyChannels, ICO.AtMostSelectedQueryTree.twoAssignment]

theorem familyCoherence_average_bound {r s : ℕ}
    {labels : Finset (Fin (r + 1) ⊕ Fin (s + 1))}
    (tree : ICO.AtMostLabelledQueryTree.Tree (Fin (r + 1) ⊕ Fin (s + 1))
      (A × M) (A × Z) labels A) (i : Fin (r + 1)) (j : Fin (s + 1)) (z z' : Z) :
    (∫ UV, ‖familyCoherence tree i j z z' UV‖
      ∂(familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1))) ≤
        reverseFactor (A := A) := by
  apply ICO.HaarFamilyPair.integral_coordinate_pair_le i j _
    (familyCoherence_continuous tree i j z z').norm (fun _ => norm_nonneg _) (reverseFactor (A := A))
  intro RU RV
  simp only [familyCoherence, inserted_assignment, Fin.insertNth_apply_same]
  have h := ICO.AtMostSelectedQueryTree.selected_mean_coherence_bound tree
    (familyChannels (i.insertNth 1 RU) (j.insertNth 1 RV)) (.inl i) (.inr j) (by simp) z z'
  have hf : Continuous (fun UV : Unitary (A := A) × Unitary (A := A) =>
      ‖familyCoherence tree i j z z' (i.insertNth UV.1 RU, j.insertNth UV.2 RV)‖) :=
    (familyCoherence_continuous tree i j z z').norm.comp
    ((Continuous.finInsertNth (A := fun _ => Unitary (A := A)) i continuous_fst continuous_const).prodMk
      (Continuous.finInsertNth (A := fun _ => Unitary (A := A)) j continuous_snd continuous_const))
  have hint := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A)))
  simp only [familyCoherence, inserted_assignment, Fin.insertNth_apply_same] at hint
  rw [integral_prod _ hint] at h
  exact h

theorem total_coherence_average_bound {r s : ℕ}
    {labels : Finset (Fin (r + 1) ⊕ Fin (s + 1))}
    (tree : ICO.AtMostLabelledQueryTree.Tree (Fin (r + 1) ⊕ Fin (s + 1))
      (A × M) (A × Z) labels A) (z z' : Z) :
    (∫ UV, ∑ ij : Fin (r + 1) × Fin (s + 1), ‖familyCoherence tree ij.1 ij.2 z z' UV‖
      ∂(familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1))) ≤
        (((r + 1) * (s + 1) : ℕ) : ℝ) * reverseFactor (A := A) := by
  have hint (ij : Fin (r + 1) × Fin (s + 1)) :
      Integrable (fun UV => ‖familyCoherence tree ij.1 ij.2 z z' UV‖)
        ((familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1))) :=
    (familyCoherence_continuous tree ij.1 ij.2 z z').norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun ij _ => hint ij)]
  calc
    _ ≤ ∑ _ij : Fin (r + 1) × Fin (s + 1), reverseFactor (A := A) :=
      Finset.sum_le_sum fun ij _ => familyCoherence_average_bound tree ij.1 ij.2 z z'
    _ = _ := by simp

end
end ICO.AtMostFamilyCoherence


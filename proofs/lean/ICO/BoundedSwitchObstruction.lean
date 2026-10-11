import ICO.FiniteQuerySwitchObstruction
import ICO.DimensionCircuitReduction
import ICO.QubitSwitchConvention
import ICO.PadTwoOracleCircuit
import ICO.BudgetLabelReduction

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.AllChannelDilation ICO.LabelledCircuitComposition
open ICO.EmbeddingSwitchChannels ICO.QubitChoiIndex

namespace ICO.BoundedSwitchObstruction
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
variable {M : Type} [Fintype M] [DecidableEq M]

theorem no_labelled {d m n : Nat} (hd : 2≤d)
    (tree : ICO.LabelledQueryTree.Tree (Fin m ⊕ Fin n) (Fin d × M)
      (Fin 2 × Fin d) Finset.univ (Fin d)) :
    ¬ ICO.DimensionCircuitReduction.RealizesSwitch tree := by
  intro h
  let c := ICO.DimensionCircuitReduction.compress hd tree
  have hc : ICO.DimensionCircuitReduction.RealizesSwitch c :=
    ICO.DimensionCircuitReduction.compress_correct hd tree h
  let final := append c ICO.QubitSwitchConvention.permutationChannel
  apply ICO.FiniteQuerySwitchObstruction.no_finite_budget final
  intro I J _ _ _ _ U V hU hV
  have ht := hc I J U V hU hV
  rw [ICO.LabelledQueryTree.Tree.channel_map] at ht
  simp only [ICO.QueryOracleMaps.channel_sum_elim] at ht ⊢
  change c.map (Sum.elim (fun _ => oracleMap U) (fun _ => oracleMap V)) = switchMap U V at ht
  change flatten (MatrixMap.choi (final.map _)) = _
  rw [show final=append c ICO.QubitSwitchConvention.permutationChannel from rfl,append_map,ht]
  exact ICO.QubitSwitchConvention.flattened_switch U V

def AtMostRealizesSwitch {d m n : Nat}
    (tree : ICO.AtMostLabelledQueryTree.Tree (Fin m ⊕ Fin n) (Fin d × M)
      (Fin 2 × Fin d) Finset.univ (Fin d)) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d))
      (hU : ∑ i,(U i)ᴴ*U i=1) (hV : ∑ j,(V j)ᴴ*V j=1),
      (tree.channel (Sum.elim (fun _ => oracleChannel U hU)
        (fun _ => oracleChannel V hV))).map = switchMap U V

theorem no_atMost [Nonempty M] {d m n : Nat} (hd : 2≤d)
    (tree : ICO.AtMostLabelledQueryTree.Tree (Fin m ⊕ Fin n) (Fin d × M)
      (Fin 2 × Fin d) Finset.univ (Fin d)) : ¬ AtMostRealizesSwitch tree := by
  intro h
  let a₀ : Fin d := ⟨0,by omega⟩
  let m₀ : M := Classical.choice inferInstance
  let o₀ : Fin 2 × Fin d := (0,a₀)
  apply no_labelled hd (ICO.PadLabelledCircuit.compile a₀ m₀ o₀ tree)
  intro I J _ _ _ _ U V hU hV
  have ht := h I J U V hU hV
  rw [ICO.AtMostLabelledQueryTree.Tree.channel_map] at ht
  rw [ICO.LabelledQueryTree.Tree.channel_map]
  simp only [ICO.QueryOracleMaps.channel_sum_elim] at ht ⊢
  change (ICO.PadLabelledCircuit.compile a₀ m₀ o₀ tree).map
    (Sum.elim (fun _ => oracleMap U) (fun _ => oracleMap V)) = _
  rw [ICO.PadTwoOracleCircuit.compile_map a₀ m₀ o₀ tree U V hU hV]
  exact ht

/-- Exact retained-control switch simulation by an actual adaptive circuit
with a total finite query budget, including outcome-dependent stopping. -/
def RealizesSwitch {d q : Nat}
    (tree : ICO.BudgetQueryTree.Tree (Fin d × M) (Fin 2 × Fin d) q (Fin d)) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d))
      (hU : ∑ i,(U i)ᴴ*U i=1) (hV : ∑ j,(V j)ᴴ*V j=1),
      (tree.channel (oracleChannel U hU) (oracleChannel V hV)).map = switchMap U V

/-- No bounded finite-dimensional classically adaptive circuit exactly
realizes the quantum switch on every pair of noisy channels in dimension d>=2.
All branch instruments, oracle uses, padding, and dimensional reductions are
represented by actual completely positive trace-preserving maps. -/
theorem no_bounded_circuit [Nonempty M] {d q : Nat} (hd : 2≤d)
    (tree : ICO.BudgetQueryTree.Tree (Fin d × M) (Fin 2 × Fin d) q (Fin d)) :
    ¬ RealizesSwitch tree := by
  intro h
  apply no_atMost hd (ICO.BudgetLabelReduction.compile tree)
  intro I J _ _ _ _ U V hU hV
  rw [ICO.BudgetLabelReduction.compile_map]
  exact h I J U V hU hV

#print axioms no_bounded_circuit
end
end ICO.BoundedSwitchObstruction


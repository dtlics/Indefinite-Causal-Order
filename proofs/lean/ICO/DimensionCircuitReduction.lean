import ICO.EmbeddingSwitchChannels
import ICO.LabelledCircuitComposition
import ICO.QueryOracleMaps

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.LabelledQueryTree ICO.LabelledCircuitComposition
open ICO.EmbeddingChannels ICO.EmbeddingSwitchChannels ICO.AllChannelDilation

namespace ICO.DimensionCircuitReduction
set_option maxHeartbeats 700000
noncomputable section
variable {M : Type} [Fintype M] [DecidableEq M]

def RealizesSwitch {d m n : Nat}
    (tree : Tree (Fin m ⊕ Fin n) (Fin d × M) (Fin 2 × Fin d) Finset.univ (Fin d)) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d))
      (hU : ∑ i,(U i)ᴴ*U i=1) (hV : ∑ j,(V j)ᴴ*V j=1),
      (tree.channel (Sum.elim (fun _ => oracleChannel U hU)
        (fun _ => oracleChannel V hV))).map = switchMap U V

/-- Fixed channel wrappers reduce the oracle dimension without changing
the finite label set, its budget, or its adaptive classical control. -/
def compress {d m n : Nat} (hd : 2≤d)
    (tree : Tree (Fin m ⊕ Fin n) (Fin d × M) (Fin 2 × Fin d) Finset.univ (Fin d)) :
    Tree (Fin m ⊕ Fin n) (Fin 2 × M) (Fin 2 × Fin 2) Finset.univ (Fin 2) :=
  append (prepend (encodeChannel hd)
    (wrapOracles tree (decodeMemory hd) (encodeMemory hd))) (outputDecodeChannel hd)

theorem compress_map {d m n : Nat} (hd : 2≤d)
    (tree : Tree (Fin m ⊕ Fin n) (Fin d × M) (Fin 2 × Fin d) Finset.univ (Fin d))
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (U : I → CMatrix (Fin 2)) (V : J → CMatrix (Fin 2)) :
    (compress hd tree).map (Sum.elim (fun _ => oracleMap U) (fun _ => oracleMap V)) =
      (outputDecodeChannel hd).map.comp
        ((tree.map (Sum.elim (fun _ => oracleMap (extendedFamily hd U))
          (fun _ => oracleMap (extendedFamily hd V)))).comp (encodeChannel hd).map) := by
  rw [compress,append_map,prepend_map,wrapOracles_map]
  congr 2
  apply tree.map_congr
  intro i hi
  cases i <;> simp only [Sum.elim_inl,Sum.elim_inr,extended_oracle_map]

/-- A purported universal higher-dimensional realization induces an actual
qubit realization, with exact equality of the retained-control channel. -/
theorem compress_correct {d m n : Nat} (hd : 2≤d)
    (tree : Tree (Fin m ⊕ Fin n) (Fin d × M) (Fin 2 × Fin d) Finset.univ (Fin d))
    (h : RealizesSwitch tree) : RealizesSwitch (compress hd tree) := by
  intro I J _ _ _ _ U V hU hV
  have ht := h (I × Option (Fin d)) (J × Option (Fin d))
    (extendedFamily hd U) (extendedFamily hd V)
    (extendedFamily_complete hd U hU) (extendedFamily_complete hd V hV)
  rw [Tree.channel_map] at ht ⊢
  simp only [ICO.QueryOracleMaps.channel_sum_elim] at ht ⊢
  change tree.map (Sum.elim (fun _ => oracleMap (extendedFamily hd U))
    (fun _ => oracleMap (extendedFamily hd V))) =
      switchMap (extendedFamily hd U) (extendedFamily hd V) at ht
  change (compress hd tree).map (Sum.elim (fun _ => oracleMap U)
    (fun _ => oracleMap V)) = _
  rw [compress_map]
  change (outputDecodeChannel hd).map.comp
    ((tree.map (Sum.elim (fun _ => oracleMap (extendedFamily hd U))
      (fun _ => oracleMap (extendedFamily hd V)))).comp (encodeChannel hd).map) = _
  rw [ht,decoded_switchMap]

#print axioms compress_correct
end
end ICO.DimensionCircuitReduction

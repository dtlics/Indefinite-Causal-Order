import ICO.InstrumentProtocol
import ICO.CoincidentBudgetLabels

namespace ICO.AdaptiveSequentialProtocol
open Matrix QIT ICO.SequentialIsometry ICO.LabelledQueryTree ICO.FirstLabelledQuery
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
universe u
variable {L A M B O I : Type u} [DecidableEq L]
  [Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
  [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
  [Fintype I] [DecidableEq I]

def compile {s : Finset L} (tree : Tree L (A×M) O s B) (q : ℕ)
    (hq : s.card=q) : Protocol A B O q := by
  induction q generalizing B s with
  | zero =>
    let channel := tree.channel (fun _ => Channel.idChannel (A×M))
    exact .stop (ICO.ClassicalDilation.channelIsometry channel)
      (ICO.ClassicalDilation.channelIsometry_complete channel)
  | succ q ih =>
    have hs : s.Nonempty := Finset.card_pos.mp (by omega)
    let cut := first tree hs
    exact Protocol.instrumentQuery cut.pre (fun j =>
      ih (cut.post j) (by rw [Finset.card_erase_of_mem (cut.member j),hq]; omega))

theorem compile_map {s : Finset L} (tree : Tree L (A×M) O s B) (q : ℕ)
    (hq : s.card=q) (U : I → CMatrix A) (X : CMatrix B) :
    (compile tree q hq).map U X=tree.map (fun _ => ICO.AllChannelDilation.oracleMap U) X := by
  induction q generalizing B s with
  | zero =>
    change MatrixMap.ofKraus (erasedKraus (ICO.ClassicalDilation.channelIsometry
      (tree.channel (fun _ => Channel.idChannel (A×M))))) X = _
    rw [erasedKraus_apply,ICO.ClassicalDilation.channelIsometry_output,Tree.channel_map]
    apply congrArg (fun f : MatrixMap B O => f X)
    apply Tree.map_congr
    intro i hi
    have hs : s=∅ := Finset.card_eq_zero.mp hq
    simp [hs] at hi
  | succ q ih =>
    have hs : s.Nonempty := Finset.card_pos.mp (by omega)
    let cut := first tree hs
    change (Protocol.instrumentQuery cut.pre (fun j =>
      compile (cut.post j) q (by rw [Finset.card_erase_of_mem (cut.member j),hq]; omega))).map U X = _
    rw [Protocol.instrumentQuery_map]
    rw [←first_map tree hs]
    simp only [Cut.map,LinearMap.sum_apply,LinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih]

end

section Budget
variable {A M B O I : Type} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype B] [DecidableEq B]
  [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

/-- All adaptive total-budget circuits have an oracle-independent sequential
isometric implementation. Missing calls are physically padded and erased. -/
noncomputable def budget {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O q B) : Protocol A B O q :=
  compile (ICO.CoincidentBudgetLabels.exactQueries a₀ m₀ o₀ tree) q (by simp)

theorem budget_map {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O q B)
    (U : I → CMatrix A) (hU : ∑ i,(U i).conjTranspose*U i=1) (X : CMatrix B) :
    (budget a₀ m₀ o₀ tree).map U X =
      (tree.channel (ICO.AllChannelDilation.oracleChannel U hU)
        (ICO.AllChannelDilation.oracleChannel U hU)).map X := by
  rw [budget,compile_map,ICO.CoincidentBudgetLabels.exactQueries_map _ _ _ _ U hU]

#print axioms budget_map
#print axioms compile_map
end Budget
end ICO.AdaptiveSequentialProtocol

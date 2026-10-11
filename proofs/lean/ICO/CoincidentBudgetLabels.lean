import ICO.BudgetQueryTree
import ICO.AtMostLabelledQueryTree
import ICO.PadLabelledCircuit

namespace ICO.CoincidentBudgetLabels
open Matrix QIT ICO.InstrumentCompression ICO.AllChannelDilation
noncomputable section
variable {L H O B : Type} [DecidableEq L] [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
set_option maxHeartbeats 1000000

def label {q : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B) :
    (s : Finset L) → q≤s.card → ICO.AtMostLabelledQueryTree.Tree L H O s B := by
  induction tree with
  | stop after => exact fun _ _ => .terminal after
  | @query q second after ih =>
    intro s hs
    have hn : s.Nonempty := Finset.card_pos.mp (by omega)
    exact .query hn.choose hn.choose_spec
      (ih (s.erase hn.choose) (by rw [Finset.card_erase_of_mem hn.choose_spec]; omega))
  | node I next ih => exact fun s hs => .node I (fun l => ih l s hs)

theorem label_map {q : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (U : Channel H H) (s : Finset L) (hs : q≤s.card) :
    (label tree s hs).map (fun _ => U.map)=(tree.channel U U).map := by
  induction tree generalizing s with
  | stop after => rfl
  | @query q second after ih =>
    let hn : s.Nonempty := Finset.card_pos.mp (show 0<s.card by omega)
    change ((label after (s.erase hn.choose) _).map _).comp U.map=_
    rw [ih]
    cases second <;> rfl
  | node I next ih =>
    change (∑ l,((label (next l) s hs).map _).comp (branchMap I l))=_
    simp_rw [ih]
    rfl

variable {A M I : Type} [Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
  [Fintype I] [DecidableEq I]

/-- Coincident oracle names and outcome-dependent stopping are compiled into
exactly q actual channel calls, including physical discarded-register padding. -/
def exactQueries {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O q B) :
    ICO.LabelledQueryTree.Tree (Fin q) (A×(M⊕O)) O Finset.univ B :=
  ICO.PadLabelledCircuit.compile a₀ m₀ o₀ (label tree Finset.univ (by simp))

theorem exactQueries_map {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O q B)
    (U : I → CMatrix A) (hU : ∑ i,(U i).conjTranspose*U i=1) :
    (exactQueries a₀ m₀ o₀ tree).map (fun _ => oracleMap U)=
      (tree.channel (oracleChannel U hU) (oracleChannel U hU)).map := by
  rw [exactQueries,ICO.PadLabelledCircuit.compile_map _ _ _ _ (fun _ => U) (fun _ => hU)]
  exact label_map tree (oracleChannel U hU) _ _

#print axioms exactQueries_map
end
end ICO.CoincidentBudgetLabels

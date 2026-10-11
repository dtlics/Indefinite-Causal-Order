import ICO.BudgetQueryTree
import ICO.UniformInstrument
import ICO.AtMostLabelledQueryTree

/-! # Compiling fresh-label sampling into a genuine adaptive quantum circuit -/

open Matrix QIT ICO.InstrumentCompression

namespace ICO.FreshBudgetCompile
set_option maxHeartbeats 600000
noncomputable section
variable {H O B : Type} [Fintype H] [Fintype O] [Fintype B]
variable [DecidableEq H] [DecidableEq O] [DecidableEq B]

theorem erase_left {r : ℕ} (S T : Finset (Fin r)) (a : Fin r) :
    (S.erase a).disjSum T = (S.disjSum T).erase (.inl a) := by
  ext k
  cases k <;> simp

theorem erase_right {r : ℕ} (S T : Finset (Fin r)) (b : Fin r) :
    S.disjSum (T.erase b) = (S.disjSum T).erase (.inr b) := by
  ext k
  cases k <;> simp

def fresh {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (S T : Finset (Fin r)) (hS : q ≤ S.card) (hT : q ≤ T.card) :
    ICO.AtMostLabelledQueryTree.Tree (Fin r ⊕ Fin r) H O (S.disjSum T) B := by
  induction tree generalizing S T with
  | stop after => exact .terminal after
  | @query q second after ih =>
    cases second
    · have hspos : 0 < S.card := by omega
      letI : Nonempty ↥S := by
        obtain ⟨a, ha⟩ := Finset.card_pos.mp hspos
        exact ⟨⟨a, ha⟩⟩
      refine .node (ICO.UniformInstrument.instrument (H := H) (I := ↥S)) (fun a => ?_)
      refine .query (.inl a.val) (by simp [a.property]) ?_
      have hS' : q ≤ (S.erase a.val).card := by
        rw [Finset.card_erase_of_mem a.property]
        omega
      have hT' : q ≤ T.card := by omega
      have hc := ih (S.erase a.val) T hS' hT'
      exact (erase_left S T a.val) ▸ hc
    · have htpos : 0 < T.card := by omega
      letI : Nonempty ↥T := by
        obtain ⟨b, hb⟩ := Finset.card_pos.mp htpos
        exact ⟨⟨b, hb⟩⟩
      refine .node (ICO.UniformInstrument.instrument (H := H) (I := ↥T)) (fun b => ?_)
      refine .query (.inr b.val) (by simp [b.property]) ?_
      have hS' : q ≤ S.card := by omega
      have hT' : q ≤ (T.erase b.val).card := by
        rw [Finset.card_erase_of_mem b.property]
        omega
      have hc := ih S (T.erase b.val) hS' hT'
      exact (erase_right S T b.val) ▸ hc
  | node I next ih => exact .node I (fun l => ih l S T hS hT)

end
end ICO.FreshBudgetCompile

import ICO.FreshSamplingMaps

open Matrix QIT ICO.InstrumentCompression ICO.FreshSamplingMaps

namespace ICO.BudgetLabelReduction
set_option maxHeartbeats 700000
noncomputable section
variable {H O B : Type} [Fintype H] [Fintype O] [Fintype B]
  [DecidableEq H] [DecidableEq O] [DecidableEq B]

theorem freshMap_constant {q r : Nat} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (U V : Channel H H) (S T : Finset (Fin r)) (hS : q≤S.card) (hT : q≤T.card) :
    freshMap tree (Sum.elim (fun _ => U) (fun _ => V)) S T = (tree.channel U V).map := by
  induction tree generalizing S T with
  | stop after => rfl
  | @query q second after ih =>
    cases second
    · rw [fresh_left]
      have ht (a : ↥S) : freshMap after (Sum.elim (fun _ => U) (fun _ => V))
          (S.erase a.val) T = (after.channel U V).map :=
        ih (S.erase a.val) T (by rw [Finset.card_erase_of_mem a.property]; omega) (by omega)
      simp_rw [ht]
      have hcard : (S.card : ℂ)≠0 := by exact_mod_cast (show S.card≠0 by omega)
      simp [ICO.BudgetQueryTree.Tree.channel,Channel.comp,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,hcard]
    · rw [fresh_right]
      have ht (a : ↥T) : freshMap after (Sum.elim (fun _ => U) (fun _ => V))
          S (T.erase a.val) = (after.channel U V).map :=
        ih S (T.erase a.val) (by omega) (by rw [Finset.card_erase_of_mem a.property]; omega)
      simp_rw [ht]
      have hcard : (T.card : ℂ)≠0 := by exact_mod_cast (show T.card≠0 by omega)
      simp [ICO.BudgetQueryTree.Tree.channel,Channel.comp,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,hcard]
  | node I next ih =>
    change (∑ l,(freshMap (next l) _ S T).comp (branchMap I l)) = _
    simp_rw [ih _ S T hS hT]
    rfl

theorem univ_disjSum (q : Nat) :
    (Finset.univ : Finset (Fin q)).disjSum (Finset.univ : Finset (Fin q)) = Finset.univ := by
  ext i
  cases i <;> simp

/-- A total-budget circuit becomes a finite labelled circuit by sampling
unused labels. With the same channel at all labels of each type, the actual
channel is unchanged, including every early stopping branch. -/
def compile {q : Nat} (tree : ICO.BudgetQueryTree.Tree H O q B) :
    ICO.AtMostLabelledQueryTree.Tree (Fin q ⊕ Fin q) H O Finset.univ B :=
  (univ_disjSum q) ▸ ICO.FreshBudgetCompile.fresh tree Finset.univ Finset.univ
    (by simp) (by simp)

theorem compile_map {q : Nat} (tree : ICO.BudgetQueryTree.Tree H O q B) (U V : Channel H H) :
    ((compile tree).channel (Sum.elim (fun _ => U) (fun _ => V))).map =
      (tree.channel U V).map := by
  unfold compile
  have hc := channel_cast (r:=q) (univ_disjSum q)
    (ICO.FreshBudgetCompile.fresh tree Finset.univ Finset.univ (by simp) (by simp))
    (Sum.elim (fun _ => U) (fun _ => V))
  refine hc.trans ?_
  rw [fresh_compile_map]
  exact freshMap_constant tree U V _ _ (by simp) (by simp)

#print axioms compile_map
end
end ICO.BudgetLabelReduction

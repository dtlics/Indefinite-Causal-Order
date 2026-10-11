import ICO.C6FlagCount
import ICO.C6HistoryCoordinates

/-! The literal true-flag subsequence, with the newest accepted birth first. -/
namespace ICO.C6AcceptedIndices
open ICO.C6FlagCount ICO.C6HistoryCoordinates ICO.RecordingPurifiedProtocol
noncomputable section
set_option maxHeartbeats 700000
set_option Elab.async false

def selected : (n:ℕ)→(κ:History Bool n)→Fin (flagCount n κ)→Fin n
  | 0,_=>Fin.elim0
  | n+1,(false,κ)=>by
      simpa only [flagCount_false] using (fun i:Fin (flagCount n κ)=>(selected n κ i).castSucc)
  | n+1,(true,κ)=>by
      simpa only [flagCount_true] using Fin.cons (α:=fun _:Fin (flagCount n κ+1)=>Fin (n+1)) (Fin.last n)
        (fun i:Fin (flagCount n κ)=>(selected n κ i).castSucc)

theorem selected_false (n:ℕ) (κ:History Bool n) (i:Fin (flagCount n κ)) :
    selected (n+1) (false,κ) (Fin.cast (flagCount_false n κ).symm i)=
      (selected n κ i).castSucc := rfl

theorem selected_true (n:ℕ) (κ:History Bool n) (i:Fin (flagCount n κ+1)) :
    selected (n+1) (true,κ) (Fin.cast (flagCount_true n κ).symm i)=
      Fin.cons (α:=fun _:Fin (flagCount n κ+1)=>Fin (n+1)) (Fin.last n) (fun j=>(selected n κ j).castSucc) i := rfl

theorem selected_injective (n:ℕ) (κ:History Bool n) : Function.Injective (selected n κ) := by
  induction n with
  | zero=>intro i; exact Fin.elim0 i
  | succ n ih=>
    rcases κ with ⟨b,κ⟩
    cases b with
    | false=>
      intro i j he
      have hh:=ih κ (Fin.castSucc_injective n he)
      exact hh
    | true=>
      intro i j he
      change Fin (flagCount n κ+1) at i j
      change Fin.cons (α:=fun _:Fin (flagCount n κ+1)=>Fin (n+1)) (Fin.last n) (fun k=>(selected n κ k).castSucc) i=
        Fin.cons (α:=fun _:Fin (flagCount n κ+1)=>Fin (n+1)) (Fin.last n) (fun k=>(selected n κ k).castSucc) j at he
      cases i using Fin.cases with
      | zero=>
        cases j using Fin.cases with
        | zero=>rfl
        | succ j=>
          simp only [Fin.cons_zero,Fin.cons_succ] at he
          exact False.elim ((Fin.castSucc_ne_last _) he.symm)
      | succ i=>
        cases j using Fin.cases with
        | zero=>
          simp only [Fin.cons_zero,Fin.cons_succ] at he
          exact False.elim ((Fin.castSucc_ne_last _) he)
        | succ j=>
          simp only [Fin.cons_succ] at he
          exact congrArg Fin.succ (ih κ (Fin.castSucc_injective n he))

theorem selected_flag (n:ℕ) (κ:History Bool n) (i:Fin (flagCount n κ)) :
    historyEquiv Bool n κ (selected n κ i)=true := by
  induction n with
  | zero=>exact Fin.elim0 i
  | succ n ih=>
    rcases κ with ⟨b,κ⟩
    cases b with
    | false=>
      change Fin.snoc (α:=fun _:Fin (n+1)=>Bool) (historyEquiv Bool n κ) false ((selected n κ i).castSucc)=true
      rw [Fin.snoc_castSucc]
      exact ih κ i
    | true=>
      change Fin (flagCount n κ+1) at i
      change Fin.snoc (α:=fun _:Fin (n+1)=>Bool) (historyEquiv Bool n κ) true
        (Fin.cons (α:=fun _:Fin (flagCount n κ+1)=>Fin (n+1)) (Fin.last n) (fun k=>(selected n κ k).castSucc) i)=true
      cases i using Fin.cases with
      | zero=>simp only [Fin.cons_zero,Fin.snoc_last]
      | succ i=>rw [Fin.cons_succ,Fin.snoc_castSucc]; exact ih κ i

theorem selected_range (n:ℕ) (κ:History Bool n) (i:Fin n)
    (hi:historyEquiv Bool n κ i=true) : ∃j,selected n κ j=i := by
  induction n with
  | zero=>exact Fin.elim0 i
  | succ n ih=>
    rcases κ with ⟨b,κ⟩
    cases i using Fin.lastCases with
    | last=>
      change Fin.snoc (α:=fun _:Fin (n+1)=>Bool) (historyEquiv Bool n κ) b (Fin.last n)=true at hi
      rw [Fin.snoc_last] at hi
      subst b
      exact ⟨⟨0,by rw [flagCount_true]; omega⟩,rfl⟩
    | cast i=>
      change Fin.snoc (α:=fun _:Fin (n+1)=>Bool) (historyEquiv Bool n κ) b i.castSucc=true at hi
      rw [Fin.snoc_castSucc] at hi
      obtain ⟨j,hj⟩:=ih κ i hi
      cases b with
      | false=>exact ⟨j,congrArg Fin.castSucc hj⟩
      | true=>exact ⟨j.succ,congrArg Fin.castSucc hj⟩

#print axioms selected_injective
#print axioms selected_flag
#print axioms selected_range
end
end ICO.C6AcceptedIndices

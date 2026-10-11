import ICO.LabelledQueryTree

/-! Oracle types with no labels cannot influence a physical query tree. -/
namespace ICO.AbsentOracle
open QIT ICO.LabelledQueryTree
noncomputable section
universe u
variable {H O A F : Type u} [Fintype H] [DecidableEq H] [Fintype O]
  [DecidableEq O] [Fintype A] [DecidableEq A] [DecidableEq F]

theorem zero_first_map {s : Finset (Fin 0 ⊕ F)}
    (tree : Tree (Fin 0 ⊕ F) H O s A) (X Y Z : MatrixMap H H) :
    tree.map (Sum.elim (fun _ => X) (fun _ => Z)) =
      tree.map (Sum.elim (fun _ => Y) (fun _ => Z)) := by
  apply congrArg tree.map
  funext l
  cases l with
  | inl i => exact Fin.elim0 i
  | inr i => rfl

theorem zero_second_map {s : Finset (F ⊕ Fin 0)}
    (tree : Tree (F ⊕ Fin 0) H O s A) (X Y Z : MatrixMap H H) :
    tree.map (Sum.elim (fun _ => Z) (fun _ => X)) =
      tree.map (Sum.elim (fun _ => Z) (fun _ => Y)) := by
  apply congrArg tree.map
  funext l
  cases l with
  | inl i => rfl
  | inr i => exact Fin.elim0 i

theorem zero_first_channel {s : Finset (Fin 0 ⊕ F)}
    (tree : Tree (Fin 0 ⊕ F) H O s A) (X Y Z : Channel H H) :
    tree.channel (Sum.elim (fun _ => X) (fun _ => Z)) =
      tree.channel (Sum.elim (fun _ => Y) (fun _ => Z)) := by
  apply congrArg tree.channel
  funext l
  cases l with
  | inl i => exact Fin.elim0 i
  | inr i => rfl

theorem zero_second_channel {s : Finset (F ⊕ Fin 0)}
    (tree : Tree (F ⊕ Fin 0) H O s A) (X Y Z : Channel H H) :
    tree.channel (Sum.elim (fun _ => Z) (fun _ => X)) =
      tree.channel (Sum.elim (fun _ => Z) (fun _ => Y)) := by
  apply congrArg tree.channel
  funext l
  cases l with
  | inl i => rfl
  | inr i => exact Fin.elim0 i

#print axioms zero_first_channel
#print axioms zero_second_map
end
end ICO.AbsentOracle

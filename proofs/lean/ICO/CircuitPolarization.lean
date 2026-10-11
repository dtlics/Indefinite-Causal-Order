import ICO.LabelledQueryContinuity
import ICO.SelectedQueryTree
import ICO.TwoSlotPolarization
import Mathlib.Analysis.Matrix.Normed

open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise
open Matrix QIT ICO.LabelledQueryTree ICO.SelectedQueryTree

namespace ICO.CircuitPolarization
set_option maxHeartbeats 600000
noncomputable section

variable {H O A : Type} [Fintype H] [Fintype O] [Fintype A]
  [DecidableEq H] [DecidableEq O] [DecidableEq A]

theorem ofChoi_choi (f : MatrixMap H H) : MatrixMap.ofChoiMatrix (MatrixMap.choi f) = f :=
  MatrixMap.choi_inj (MatrixMap.choi_ofChoiMatrix (MatrixMap.choi f))

theorem continuousMultilinear_apply {L : Type} [Fintype L] [DecidableEq L]
    (tree : Tree L H O Finset.univ A) (J : L → CMatrix (H × H)) :
    tree.continuousMultilinear J =
      MatrixMap.choi (tree.map (fun i => MatrixMap.ofChoiMatrix (J i))) := rfl

theorem continuousMultilinear_choi {L : Type} [Fintype L] [DecidableEq L]
    (tree : Tree L H O Finset.univ A) (f : L → MatrixMap H H) :
    tree.continuousMultilinear (fun i => MatrixMap.choi (f i)) = MatrixMap.choi (tree.map f) := by
  rw [continuousMultilinear_apply]
  simp only [ofChoi_choi]

theorem choi_affine (t : ℝ) (f g : MatrixMap H H) :
    MatrixMap.choi (f+t • (g-f)) = MatrixMap.choi f+t • (MatrixMap.choi g-MatrixMap.choi f) := rfl

def selected {m n : Nat} (tree : Tree (Fin m ⊕ Fin n) H O Finset.univ A)
    (i : Fin m) (j : Fin n) : ICO.TwoQueryTree.QueryTree H O A :=
  twoSelect tree (Sum.inl i) (Sum.inr j) (by simp) (by simp) (by simp)

theorem selected_choi {m n : Nat} (tree : Tree (Fin m ⊕ Fin n) H O Finset.univ A)
    (i : Fin m) (j : Fin n) (U V : Channel H H) :
    MatrixMap.choi (((selected tree i j).channel U V).map) =
      tree.continuousMultilinear (Sum.elim
        (Function.update (fun _ => MatrixMap.choi (LinearMap.id : MatrixMap H H)) i (MatrixMap.choi U.map))
        (Function.update (fun _ => MatrixMap.choi (LinearMap.id : MatrixMap H H)) j (MatrixMap.choi V.map))) := by
  rw [selected,twoSelect_map]
  have hh : Sum.elim
        (Function.update (fun _ => MatrixMap.choi (LinearMap.id : MatrixMap H H)) i (MatrixMap.choi U.map))
        (Function.update (fun _ => MatrixMap.choi (LinearMap.id : MatrixMap H H)) j (MatrixMap.choi V.map)) =
      fun l => MatrixMap.choi (twoAssignment (Sum.inl i) (Sum.inr j) U.map V.map l) := by
    funext l
    cases l with
    | inl k => by_cases hk : k=i <;> simp [Function.update_apply,twoAssignment,hk]
    | inr k => by_cases hk : k=j <;> simp [Function.update_apply,twoAssignment,hk]
  rw [hh,continuousMultilinear_choi]

/-- Every repeated-query realization of a bilinear target yields, by uniform
selection of two labelled slots, the precise positive identity dilution.
The multilinearity and the ordinary two-query realizations are derived from
the concrete adaptive tree, rather than assumed. -/
theorem average_selected {m n : Nat} (hm : 0<m) (hn : 0<n)
    (tree : Tree (Fin m ⊕ Fin n) H O Finset.univ A) (U V : Channel H H)
    (u00 u10 u01 u11 : CMatrix (A × O))
    (h : ∀ t s : ℝ, t ∈ Set.Icc 0 1 → s ∈ Set.Icc 0 1 →
      MatrixMap.choi (tree.map (Sum.elim
        (fun _ => LinearMap.id+t • (U.map-LinearMap.id))
        (fun _ => LinearMap.id+s • (V.map-LinearMap.id)))) =
        (u00+s • (u01-u00)) + t • ((u10+s • (u11-u10)) - (u00+s • (u01-u00)))) :
    (1/((m : ℝ)*(n : ℝ))) • (∑ i : Fin m, ∑ j : Fin n,
      MatrixMap.choi (((selected tree i j).channel U V).map)) =
      ((1/(m : ℝ))*(1/(n : ℝ))) • u11 +
      ((1/(m : ℝ))*(1-1/(n : ℝ))) • u10 +
      ((1-1/(m : ℝ))*(1/(n : ℝ))) • u01 +
      ((1-1/(m : ℝ))*(1-1/(n : ℝ))) • u00 := by
  simp_rw [selected_choi]
  apply ICO.TwoSlotPolarization.average_one_each hm hn
    (tree.continuousMultilinear.restrictScalars ℝ)
    (MatrixMap.choi (LinearMap.id : MatrixMap H H)) (MatrixMap.choi U.map) (MatrixMap.choi V.map)
    u00 u10 u01 u11
  intro t s ht hs
  change tree.continuousMultilinear _ = _
  have hh : Sum.elim
      (fun _ : Fin m => MatrixMap.choi (LinearMap.id : MatrixMap H H)+t •
        (MatrixMap.choi U.map-MatrixMap.choi LinearMap.id))
      (fun _ : Fin n => MatrixMap.choi (LinearMap.id : MatrixMap H H)+s •
        (MatrixMap.choi V.map-MatrixMap.choi LinearMap.id)) =
      fun l => MatrixMap.choi (Sum.elim
        (fun _ : Fin m => LinearMap.id+t • (U.map-LinearMap.id))
        (fun _ : Fin n => LinearMap.id+s • (V.map-LinearMap.id)) l) := by
    funext l
    cases l <;> rfl
  rw [hh,continuousMultilinear_choi]
  exact h t s ht hs

#print axioms average_selected
end
end ICO.CircuitPolarization

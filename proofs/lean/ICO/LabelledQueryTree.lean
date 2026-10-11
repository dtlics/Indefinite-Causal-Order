import ICO.InstrumentCompression
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Finite adaptive circuits with explicitly distinct oracle labels.
Each query consumes its label, so every root-to-leaf path uses every remaining
label exactly once. Instruments may change all non-query memory spaces. -/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression

namespace ICO.LabelledQueryTree
set_option maxHeartbeats 600000
noncomputable section
universe u

inductive Tree (L H O : Type u) [DecidableEq L] [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] :
    Finset L → (A : Type u) → [Fintype A] → [DecidableEq A] → Type (u+1) where
  | terminal {A : Type u} [Fintype A] [DecidableEq A]
      (channel : Channel A O) : Tree L H O ∅ A
  | query {s : Finset L} (i : L) (hi : i ∈ s)
      (after : Tree L H O (s.erase i) H) : Tree L H O s H
  | node {s : Finset L} {A B K : Type u} [Fintype A] [Fintype B] [Fintype K]
      [DecidableEq A] [DecidableEq B] [DecidableEq K]
      (instrument : Instrument A B K) (next : K → Tree L H O s B) : Tree L H O s A

variable {L H O A : Type u} [DecidableEq L] [Fintype H] [Fintype O]
  [DecidableEq H] [DecidableEq O] [Fintype A] [DecidableEq A]

def Tree.map {s : Finset L} (tree : Tree L H O s A)
    (oracles : L → MatrixMap H H) : MatrixMap A O := by
  induction tree with
  | terminal channel => exact channel.map
  | query i hi after ih => exact ih.comp (oracles i)
  | node instrument next ih => exact ∑ k, (ih k).comp (branchMap instrument k)

theorem Tree.map_terminal (channel : Channel A O) (oracles : L → MatrixMap H H) :
    (Tree.terminal channel : Tree L H O ∅ A).map oracles = channel.map := rfl

theorem Tree.map_query {s : Finset L} (i : L) (hi : i ∈ s)
    (after : Tree L H O (s.erase i) H) (oracles : L → MatrixMap H H) :
    (Tree.query i hi after).map oracles = (after.map oracles).comp (oracles i) := rfl

theorem Tree.map_node {s : Finset L} {B K : Type u} [Fintype B] [Fintype K]
    [DecidableEq B] [DecidableEq K]
    (instrument : Instrument A B K) (next : K → Tree L H O s B)
    (oracles : L → MatrixMap H H) :
    (Tree.node instrument next).map oracles =
      ∑ k, ((next k).map oracles).comp (branchMap instrument k) := rfl

/-- Consumed and absent labels cannot affect the denotation. -/
theorem Tree.map_congr {s : Finset L} (tree : Tree L H O s A)
    (f g : L → MatrixMap H H) (h : ∀ i ∈ s, f i = g i) : tree.map f = tree.map g := by
  induction tree with
  | terminal channel => rfl
  | query i hi after ih =>
    simp only [Tree.map_query]
    rw [h i hi, ih (fun j hj => h j (Finset.mem_of_mem_erase hj))]
  | node instrument next ih =>
    simp only [Tree.map_node]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih k h]

theorem Tree.map_update_of_not_mem {s : Finset L} (tree : Tree L H O s A)
    (f : L → MatrixMap H H) (i : L) (hi : i ∉ s) (x : MatrixMap H H) :
    tree.map (Function.update f i x) = tree.map f := by
  apply tree.map_congr
  intro j hj
  exact Function.update_of_ne (by intro h; subst j; exact hi hj) _ _

/-- Separate additivity follows from actual channel-map composition and
classical branch summation, without an assumed multilinearity premise. -/
theorem Tree.map_update_add {s : Finset L} (tree : Tree L H O s A)
    (f : L → MatrixMap H H) (i : L) (hi : i ∈ s) (x y : MatrixMap H H) :
    tree.map (Function.update f i (x+y)) =
      tree.map (Function.update f i x) + tree.map (Function.update f i y) := by
  induction tree with
  | terminal channel => simp at hi
  | @query s j hj after ih =>
    simp only [Tree.map_query]
    by_cases hij : i=j
    · subst j
      simp only [Function.update_self]
      rw [after.map_update_of_not_mem f i (by simp),
        after.map_update_of_not_mem f i (by simp),
        after.map_update_of_not_mem f i (by simp)]
      exact LinearMap.comp_add _ _ _
    · have his : i ∈ s.erase j := Finset.mem_erase.mpr ⟨hij,hi⟩
      rw [ih his]
      simp only [Function.update_of_ne (Ne.symm hij), LinearMap.add_comp]
  | node instrument next ih =>
    simp only [Tree.map_node]
    simp_rw [ih _ hi, LinearMap.add_comp]
    exact Finset.sum_add_distrib

theorem Tree.map_update_smul {s : Finset L} (tree : Tree L H O s A)
    (f : L → MatrixMap H H) (i : L) (hi : i ∈ s) (z : ℂ) (x : MatrixMap H H) :
    tree.map (Function.update f i (z • x)) = z • tree.map (Function.update f i x) := by
  induction tree with
  | terminal channel => simp at hi
  | @query s j hj after ih =>
    simp only [Tree.map_query]
    by_cases hij : i=j
    · subst j
      simp only [Function.update_self]
      rw [after.map_update_of_not_mem f i (by simp),
        after.map_update_of_not_mem f i (by simp)]
      exact LinearMap.comp_smul _ _ _
    · have his : i ∈ s.erase j := Finset.mem_erase.mpr ⟨hij,hi⟩
      rw [ih his]
      simp only [Function.update_of_ne (Ne.symm hij), LinearMap.smul_comp]
  | node instrument next ih =>
    simp only [Tree.map_node]
    simp_rw [ih _ hi, LinearMap.smul_comp]
    exact (Finset.smul_sum ..).symm

/-- The actual denotation of any finite labelled adaptive circuit is a
multilinear map in its distinct oracle slots. -/
def Tree.multilinear [Fintype L] (tree : Tree L H O Finset.univ A) :
    MultilinearMap ℂ (fun _ : L => MatrixMap H H) (MatrixMap A O) :=
  MultilinearMap.mk' tree.map
    (fun f i x y => tree.map_update_add f i (Finset.mem_univ i) x y)
    (fun f i z x => tree.map_update_smul f i (Finset.mem_univ i) z x)

def Tree.channel {s : Finset L} (tree : Tree L H O s A)
    (oracles : L → Channel H H) : Channel A O := by
  induction tree with
  | terminal channel => exact channel
  | query i hi after ih => exact ih.comp (oracles i)
  | node instrument next ih => exact adaptiveChannel instrument ih

theorem Tree.channel_map {s : Finset L} (tree : Tree L H O s A)
    (oracles : L → Channel H H) :
    (tree.channel oracles).map = tree.map (fun i => (oracles i).map) := by
  induction tree with
  | terminal channel => rfl
  | query i hi after ih => exact congrArg (fun f => f.comp (oracles i).map) ih
  | node instrument next ih =>
    change (∑ k, ((next k).channel oracles).map.comp (branchMap instrument k)) = _
    simp_rw [ih]
    rfl

#print axioms Tree.multilinear
#print axioms Tree.channel_map
end
end ICO.LabelledQueryTree

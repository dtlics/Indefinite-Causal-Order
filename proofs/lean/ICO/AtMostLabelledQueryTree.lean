import ICO.InstrumentCompression
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Finite adaptive circuits with explicitly distinct oracle labels.
Each query consumes its label; a terminal may leave any of the remaining
labels unused. Instruments may change all non-query memory spaces. -/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression

namespace ICO.AtMostLabelledQueryTree
set_option maxHeartbeats 600000
noncomputable section
universe u

inductive Tree (L H O : Type u) [DecidableEq L] [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] :
    Finset L → (A : Type u) → [Fintype A] → [DecidableEq A] → Type (u+1) where
  | terminal {A : Type u} [Fintype A] [DecidableEq A]
      {s : Finset L} (channel : Channel A O) : Tree L H O s A
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


#print axioms Tree.channel_map
end
end ICO.AtMostLabelledQueryTree


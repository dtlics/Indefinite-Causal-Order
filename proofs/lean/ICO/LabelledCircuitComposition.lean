import ICO.LabelledQueryTree
import ICO.ClassicalDilation

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.ClassicalDilation

namespace ICO.LabelledCircuitComposition
set_option maxHeartbeats 500000
noncomputable section
universe u
variable {L A B H G O O' : Type u} [DecidableEq L]
variable [Fintype A] [Fintype B] [Fintype H] [Fintype G] [Fintype O] [Fintype O']
  [DecidableEq A] [DecidableEq B] [DecidableEq H] [DecidableEq G]
  [DecidableEq O] [DecidableEq O']

def channelInstrument (C : Channel A B) : Instrument A B (A × B) where
  op := channelKraus C
  complete := by
    have ht : MatrixMap.IsTracePreserving (MatrixMap.ofKraus (channelKraus C)) := by
      rw [← channelKraus_map]
      exact C.tracePreserving
    simpa [MatrixMap.krausAdjoint] using MatrixMap.krausAdjoint_one_of_tracePreserving _ ht

def prepend {s : Finset L} (C : Channel A B)
    (tree : ICO.LabelledQueryTree.Tree L H O s B) : ICO.LabelledQueryTree.Tree L H O s A :=
  .node (channelInstrument C) (fun _ => tree)

theorem prepend_map {s : Finset L} (C : Channel A B)
    (tree : ICO.LabelledQueryTree.Tree L H O s B) (f : L → MatrixMap H H) :
    (prepend C tree).map f = (tree.map f).comp C.map := by
  ext X i j
  simp only [prepend,ICO.LabelledQueryTree.Tree.map_node,LinearMap.sum_apply,LinearMap.comp_apply]
  simp only [branchMap_apply,channelInstrument]
  rw [channelKraus_map]
  simp [MatrixMap.ofKraus,map_sum,Matrix.sum_apply]

def append {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A)
    (C : Channel O O') : ICO.LabelledQueryTree.Tree L H O' s A := by
  induction tree with
  | terminal channel => exact .terminal (C.comp channel)
  | query i hi after ih => exact .query i hi ih
  | node instrument next ih => exact .node instrument ih

theorem append_map {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A)
    (C : Channel O O') (f : L → MatrixMap H H) :
    (append tree C).map f = C.map.comp (tree.map f) := by
  induction tree with
  | terminal channel => rfl
  | query i hi after ih =>
    change ((append after C).map f).comp (f i) = _
    rw [ih]
    rfl
  | node instrument next ih =>
    change (∑ k,((append (next k) C).map f).comp (branchMap instrument k)) = _
    simp_rw [ih]
    ext X i j
    simp [ICO.LabelledQueryTree.Tree.map_node,LinearMap.sum_apply,LinearMap.comp_apply,map_sum]

/-- Replace every oracle use by fixed channels around one new oracle use.
Classical outcomes remain ordinary instrument branches; labels are unchanged. -/
def wrapOracles {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A)
    (pre : Channel H G) (post : Channel G H) : ICO.LabelledQueryTree.Tree L G O s A := by
  induction tree with
  | terminal channel => exact .terminal channel
  | query i hi after ih => exact prepend pre (.query i hi (prepend post ih))
  | node instrument next ih => exact .node instrument ih

theorem wrapOracles_map {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A)
    (pre : Channel H G) (post : Channel G H) (f : L → MatrixMap G G) :
    (wrapOracles tree pre post).map f =
      tree.map (fun i => post.map.comp ((f i).comp pre.map)) := by
  induction tree with
  | terminal channel => rfl
  | query i hi after ih =>
    change (prepend pre (ICO.LabelledQueryTree.Tree.query i hi (prepend post (wrapOracles after pre post)))).map f = _
    rw [prepend_map,ICO.LabelledQueryTree.Tree.map_query,prepend_map,ih]
    rfl
  | node instrument next ih =>
    change (∑ k,((wrapOracles (next k) pre post).map f).comp (branchMap instrument k)) = _
    simp_rw [ih]
    rfl

#print axioms wrapOracles_map
#print axioms append_map
end
end ICO.LabelledCircuitComposition

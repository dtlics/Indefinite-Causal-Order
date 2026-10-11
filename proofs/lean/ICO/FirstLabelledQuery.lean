import ICO.LabelledQueryTree
import ICO.OneQueryTree

namespace ICO.FirstLabelledQuery
open Matrix QIT ICO.InstrumentCompression ICO.LabelledQueryTree
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 900000

structure Cut (Label H O : Type u) [DecidableEq Label] [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] (s : Finset Label)
    (A : Type u) [Fintype A] [DecidableEq A] where
  Branch : Type u
  [finite : Fintype Branch]
  [decide : DecidableEq Branch]
  pre : Instrument A H Branch
  label : Branch → Label
  member : ∀ j,label j∈s
  post : (j : Branch) → Tree Label H O (s.erase (label j)) H
attribute [instance] Cut.finite Cut.decide
variable {Label A B H O K : Type u} [DecidableEq Label]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
  [Fintype K] [DecidableEq K] {s : Finset Label}

def Cut.map (R : Cut Label H O s A) (oracles : Label → MatrixMap H H) : MatrixMap A O :=
  ∑ j:R.Branch, ((R.post j).map oracles).comp ((oracles (R.label j)).comp (branchMap R.pre j))

def Cut.immediate (i : Label) (hi : i∈s) (post : Tree Label H O (s.erase i) H) :
    Cut Label H O s H where
  Branch := PUnit
  pre := {op := fun _ => 1, complete := by simp}
  label := fun _ => i
  member := fun _ => hi
  post := fun _ => post

theorem Cut.immediate_map (i : Label) (hi : i∈s) (post : Tree Label H O (s.erase i) H)
    (oracles : Label → MatrixMap H H) :
    (Cut.immediate i hi post).map oracles = post.map oracles ∘ₗ oracles i := by
  ext X a b
  simp [Cut.map,Cut.immediate,branchMap_apply]

/-- Refine a root outcome and the child's preprocessing outcome to one actual
Kraus outcome. Its completeness follows from both instruments' equations. -/
def Cut.prepend (I : Instrument A B K) (next : K → Cut Label H O s B) :
    Cut Label H O s A where
  Branch := (l : K) × (next l).Branch
  finite := Sigma.instFintype
  decide := inferInstance
  pre :=
    { op := fun j => (next j.1).pre.op j.2 * I.op j.1
      complete := by
        rw [Fintype.sum_sigma]
        have hinner (l : K) :
            (∑ j : (next l).Branch,
              ((next l).pre.op j * I.op l).conjTranspose *
                ((next l).pre.op j * I.op l)) =
              (I.op l).conjTranspose * I.op l := by
          calc
            _ = (I.op l).conjTranspose *
                (∑ j : (next l).Branch,
                  ((next l).pre.op j).conjTranspose * (next l).pre.op j) * I.op l := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
                Matrix.mul_assoc]
            _ = _ := by rw [(next l).pre.complete]; simp
        simp_rw [hinner]
        exact I.complete }
  label := fun j => (next j.1).label j.2
  member := fun j => (next j.1).member j.2
  post := fun j => (next j.1).post j.2


theorem Cut.prepend_map (I : Instrument A B K) (next : K → Cut Label H O s B)
    (oracles : Label → MatrixMap H H) :
    (Cut.prepend I next).map oracles = ∑ l, ((next l).map oracles).comp (branchMap I l) := by
  ext X a b
  simp only [Cut.map,Cut.prepend,Fintype.sum_sigma,LinearMap.sum_apply,
    LinearMap.comp_apply,Matrix.sum_apply,branchMap_apply,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  exact Fintype.sum_sigma _

def first {s : Finset Label} (tree : Tree Label H O s A) (hs : s.Nonempty) : Cut Label H O s A := by
  induction tree with
  | terminal channel => exact (Finset.not_nonempty_empty hs).elim
  | query i hi after ih => exact Cut.immediate i hi after
  | node instrument next ih => exact Cut.prepend instrument (fun j => ih j hs)

theorem first_map {s : Finset Label} (tree : Tree Label H O s A) (hs : s.Nonempty)
    (oracles : Label → MatrixMap H H) : (first tree hs).map oracles=tree.map oracles := by
  induction tree with
  | terminal channel => exact (Finset.not_nonempty_empty hs).elim
  | query i hi after ih => exact Cut.immediate_map i hi after oracles
  | node instrument next ih =>
    change (Cut.prepend instrument (fun j => first (next j) hs)).map oracles=_
    rw [Cut.prepend_map]
    simp_rw [ih]
    rfl

#print axioms first_map
end
end ICO.FirstLabelledQuery


import ICO.InstrumentCompression

/-! # Extracting the unique oracle cut of a finite adaptive tree

The preprocessing instrument and the outcome-dependent postprocessing channels
are constructed from the tree. The tree may change its finite private memory
dimension and use arbitrary finite instruments before the unique query.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression

namespace ICO.OneQueryTree

set_option maxHeartbeats 200000
noncomputable section

universe u

structure NormalForm (A H O : Type u) [Fintype A] [Fintype H] [Fintype O]
    [DecidableEq A] [DecidableEq H] [DecidableEq O] where
  Branch : Type u
  [finite : Fintype Branch]
  [decide : DecidableEq Branch]
  pre : Instrument A H Branch
  post : Branch → Channel H O

attribute [instance] NormalForm.finite NormalForm.decide

variable {A B H O L : Type u}
variable [Fintype A] [Fintype B] [Fintype H] [Fintype O] [Fintype L]
variable [DecidableEq A] [DecidableEq B] [DecidableEq H] [DecidableEq O] [DecidableEq L]

theorem adaptiveChannel_apply (I : Instrument A B L) (next : L → Channel B O)
    (X : CMatrix A) :
    (adaptiveChannel I next).map X =
      ∑ l : L, (next l).map (I.op l * X * (I.op l).conjTranspose) :=
  adaptiveMap_apply I next X

def NormalForm.channel (R : NormalForm A H O) (oracle : Channel H H) : Channel A O :=
  adaptiveChannel R.pre (fun j => (R.post j).comp oracle)

theorem NormalForm.channel_apply (R : NormalForm A H O) (oracle : Channel H H)
    (X : CMatrix A) :
    (R.channel oracle).map X = ∑ j : R.Branch,
      (R.post j).map (oracle.map (R.pre.op j * X * (R.pre.op j).conjTranspose)) := by
  rw [NormalForm.channel, adaptiveChannel_apply]
  rfl

def NormalForm.immediate (post : Channel H O) : NormalForm H H O where
  Branch := PUnit
  pre := { op := fun _ => 1, complete := by simp }
  post := fun _ => post

theorem NormalForm.immediate_map (post : Channel H O) (oracle : Channel H H) :
    ((NormalForm.immediate post).channel oracle).map = (post.comp oracle).map := by
  ext X i j
  simp [NormalForm.channel_apply, NormalForm.immediate, Channel.comp]

/-- Refine a root outcome and the child's preprocessing outcome to one actual
Kraus outcome. Its completeness follows from both instruments' equations. -/
def NormalForm.prepend (I : Instrument A B L) (next : L → NormalForm B H O) :
    NormalForm A H O where
  Branch := (l : L) × (next l).Branch
  pre :=
    { op := fun j => (next j.1).pre.op j.2 * I.op j.1
      complete := by
        rw [Fintype.sum_sigma]
        have hinner (l : L) :
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
  post := fun j => (next j.1).post j.2

theorem NormalForm.prepend_map (I : Instrument A B L) (next : L → NormalForm B H O)
    (oracle : Channel H H) :
    ((NormalForm.prepend I next).channel oracle).map =
      (adaptiveChannel I (fun l => (next l).channel oracle)).map := by
  ext X i j
  simp only [NormalForm.channel_apply, adaptiveChannel_apply, NormalForm.prepend,
    Fintype.sum_sigma, Matrix.sum_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

inductive QueryTree (H O : Type u) [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] :
    (A : Type u) → [Fintype A] → [DecidableEq A] → Type (u + 1) where
  | call (after : ICO.InstrumentCompression.Tree O H) : QueryTree H O H
  | node {A B L : Type u} [Fintype A] [Fintype B] [Fintype L]
      [DecidableEq A] [DecidableEq B] [DecidableEq L]
      (instrument : Instrument A B L) (next : L → QueryTree H O B) : QueryTree H O A

def QueryTree.channel {H O : Type u} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] {A : Type u} [Fintype A] [DecidableEq A]
    (tree : QueryTree H O A) (oracle : Channel H H) : Channel A O := by
  induction tree with
  | call after => exact after.toChannel.comp oracle
  | node instrument next ih => exact adaptiveChannel instrument ih

def QueryTree.normalForm {H O : Type u} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] {A : Type u} [Fintype A] [DecidableEq A]
    (tree : QueryTree H O A) : NormalForm A H O := by
  induction tree with
  | call after => exact NormalForm.immediate after.toChannel
  | node instrument next ih => exact NormalForm.prepend instrument ih

/-- The extracted instrument and postprocessing reproduce the full adaptive
tree for every possible oracle channel, rather than only for a chosen input. -/
theorem QueryTree.normalForm_correct {H O : Type u} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] {A : Type u} [Fintype A] [DecidableEq A]
    (tree : QueryTree H O A) (oracle : Channel H H) :
    (tree.normalForm.channel oracle).map = (tree.channel oracle).map := by
  induction tree with
  | call after => exact NormalForm.immediate_map after.toChannel oracle
  | node instrument next ih =>
    change ((NormalForm.prepend instrument (fun l => (next l).normalForm)).channel oracle).map = _
    rw [NormalForm.prepend_map]
    change (adaptiveChannel instrument (fun l => (next l).normalForm.channel oracle)).map =
      (adaptiveChannel instrument (fun l => (next l).channel oracle)).map
    ext X i j
    simp only [adaptiveChannel_apply, ih]

end
end ICO.OneQueryTree

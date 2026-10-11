import ICO.OneQueryTree

/-! # Extracting both causal orders from a finite adaptive two-query tree

Each branch uses each of the two oracle channels exactly once. The first oracle
is chosen by the tree's actual quantum instrument. Extraction retains its
operator-valued preprocessing branch and all intermediate classical history.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression

namespace ICO.TwoQueryTree

set_option maxHeartbeats 200000
noncomputable section

universe u

inductive Order where
  | firstThenSecond
  | secondThenFirst
  deriving DecidableEq

def firstOracle {H : Type u} [Fintype H] [DecidableEq H]
    (order : Order) (first second : Channel H H) : Channel H H :=
  match order with
  | .firstThenSecond => first
  | .secondThenFirst => second

def secondOracle {H : Type u} [Fintype H] [DecidableEq H]
    (order : Order) (first second : Channel H H) : Channel H H :=
  match order with
  | .firstThenSecond => second
  | .secondThenFirst => first

structure NormalForm (A H O : Type u) [Fintype A] [Fintype H] [Fintype O]
    [DecidableEq A] [DecidableEq H] [DecidableEq O] where
  Branch : Type u
  [finite : Fintype Branch]
  [decide : DecidableEq Branch]
  pre : Instrument A H Branch
  order : Branch → Order
  rest : Branch → ICO.OneQueryTree.NormalForm H H O

attribute [instance] NormalForm.finite NormalForm.decide

variable {A B H O L : Type u}
variable [Fintype A] [Fintype B] [Fintype H] [Fintype O] [Fintype L]
variable [DecidableEq A] [DecidableEq B] [DecidableEq H] [DecidableEq O] [DecidableEq L]

def NormalForm.channel (R : NormalForm A H O) (first second : Channel H H) : Channel A O :=
  adaptiveChannel R.pre (fun j =>
    ((R.rest j).channel (secondOracle (R.order j) first second)).comp
      (firstOracle (R.order j) first second))

theorem NormalForm.channel_apply (R : NormalForm A H O) (first second : Channel H H)
    (X : CMatrix A) :
    (R.channel first second).map X = ∑ j : R.Branch,
      ((R.rest j).channel (secondOracle (R.order j) first second)).map
        ((firstOracle (R.order j) first second).map
          (R.pre.op j * X * (R.pre.op j).conjTranspose)) := by
  rw [NormalForm.channel, ICO.OneQueryTree.adaptiveChannel_apply]
  rfl

def NormalForm.immediate (order : Order) (rest : ICO.OneQueryTree.NormalForm H H O) :
    NormalForm H H O where
  Branch := PUnit
  pre := { op := fun _ => 1, complete := by simp }
  order := fun _ => order
  rest := fun _ => rest

theorem NormalForm.immediate_map (order : Order) (rest : ICO.OneQueryTree.NormalForm H H O)
    (first second : Channel H H) :
    ((NormalForm.immediate order rest).channel first second).map =
      ((rest.channel (secondOracle order first second)).comp
        (firstOracle order first second)).map := by
  ext X i j
  simp [NormalForm.channel_apply, NormalForm.immediate, Channel.comp]

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
  order := fun j => (next j.1).order j.2
  rest := fun j => (next j.1).rest j.2

theorem NormalForm.prepend_map (I : Instrument A B L) (next : L → NormalForm B H O)
    (first second : Channel H H) :
    ((NormalForm.prepend I next).channel first second).map =
      (adaptiveChannel I (fun l => (next l).channel first second)).map := by
  ext X i j
  simp only [NormalForm.channel_apply, ICO.OneQueryTree.adaptiveChannel_apply,
    NormalForm.prepend, Fintype.sum_sigma, Matrix.sum_apply,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A fully adaptive finite tree with exactly one use of each oracle. Query
register plus private memory is `H`; all non-query memory types may vary. -/
inductive QueryTree (H O : Type u) [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] :
    (A : Type u) → [Fintype A] → [DecidableEq A] → Type (u + 1) where
  | first (order : Order) (after : ICO.OneQueryTree.QueryTree H O H) : QueryTree H O H
  | node {A B L : Type u} [Fintype A] [Fintype B] [Fintype L]
      [DecidableEq A] [DecidableEq B] [DecidableEq L]
      (instrument : Instrument A B L) (next : L → QueryTree H O B) : QueryTree H O A

def QueryTree.channel {H O : Type u} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] {A : Type u} [Fintype A] [DecidableEq A]
    (tree : QueryTree H O A) (first second : Channel H H) : Channel A O := by
  induction tree with
  | first order after => exact
      (after.channel (secondOracle order first second)).comp (firstOracle order first second)
  | node instrument next ih => exact adaptiveChannel instrument ih

def QueryTree.normalForm {H O : Type u} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] {A : Type u} [Fintype A] [DecidableEq A]
    (tree : QueryTree H O A) : NormalForm A H O := by
  induction tree with
  | first order after => exact NormalForm.immediate order after.normalForm
  | node instrument next ih => exact NormalForm.prepend instrument ih

theorem QueryTree.normalForm_correct {H O : Type u} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] {A : Type u} [Fintype A] [DecidableEq A]
    (tree : QueryTree H O A) (first second : Channel H H) :
    (tree.normalForm.channel first second).map = (tree.channel first second).map := by
  induction tree with
  | first order after =>
    change ((NormalForm.immediate order after.normalForm).channel first second).map = _
    rw [NormalForm.immediate_map]
    change (after.normalForm.channel (secondOracle order first second)).map.comp
        (firstOracle order first second).map =
      (after.channel (secondOracle order first second)).map.comp
        (firstOracle order first second).map
    rw [ICO.OneQueryTree.QueryTree.normalForm_correct]
  | node instrument next ih =>
    change ((NormalForm.prepend instrument (fun l => (next l).normalForm)).channel first second).map = _
    rw [NormalForm.prepend_map]
    change (adaptiveChannel instrument (fun l => (next l).normalForm.channel first second)).map =
      (adaptiveChannel instrument (fun l => (next l).channel first second)).map
    ext X i j
    simp only [ICO.OneQueryTree.adaptiveChannel_apply, ih]

end
end ICO.TwoQueryTree

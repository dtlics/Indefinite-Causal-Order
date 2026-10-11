import ICO.OptionalOneQuery
import ICO.VaryingAverage

/-! # Operator-valued causal branches for at-most-one-use-each adaptive trees -/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.ClassicalDilation ICO.OraclePadding

namespace ICO.OptionalTwoQuery

set_option maxHeartbeats 350000
noncomputable section
universe u

structure NormalForm (A B O : Type u) [Fintype A] [Fintype B] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq O] where
  Branch : Type u
  [finite : Fintype Branch]
  [decide : DecidableEq Branch]
  FirstMemory : Branch → Type u
  SecondMemory : Branch → Type u
  [firstFinite : ∀ j, Fintype (FirstMemory j)]
  [secondFinite : ∀ j, Fintype (SecondMemory j)]
  [firstDecide : ∀ j, DecidableEq (FirstMemory j)]
  [secondDecide : ∀ j, DecidableEq (SecondMemory j)]
  pre : (j : Branch) → Matrix (A × FirstMemory j) B ℂ
  complete : ∑ j, (pre j).conjTranspose * pre j = 1
  order : Branch → ICO.TwoQueryTree.Order
  rest : (j : Branch) → ICO.OneQueryTree.NormalForm (A × FirstMemory j) (A × SecondMemory j) O

attribute [instance] NormalForm.finite NormalForm.decide NormalForm.firstFinite
  NormalForm.secondFinite NormalForm.firstDecide NormalForm.secondDecide

variable {A B C M O L : Type u}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype M] [Fintype O] [Fintype L]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq M]
variable [DecidableEq O] [DecidableEq L]

def firstUnitary (order : ICO.TwoQueryTree.Order) (U V : Matrix.unitaryGroup A ℂ) :
    Matrix.unitaryGroup A ℂ :=
  match order with
  | .firstThenSecond => U
  | .secondThenFirst => V

def secondUnitary (order : ICO.TwoQueryTree.Order) (U V : Matrix.unitaryGroup A ℂ) :
    Matrix.unitaryGroup A ℂ :=
  match order with
  | .firstThenSecond => V
  | .secondThenFirst => U

def NormalForm.branchMap (R : NormalForm A B O) (j : R.Branch)
    (U V : Matrix.unitaryGroup A ℂ) : MatrixMap B O :=
  (((R.rest j).channel (oracleChannel (secondUnitary (R.order j) U V))).map.comp
    (oracleChannel (firstUnitary (R.order j) U V)).map).comp
      (MatrixMap.ofKraus (fun (_ : PUnit.{u + 1}) => R.pre j))

def NormalForm.map (R : NormalForm A B O) (U V : Matrix.unitaryGroup A ℂ) : MatrixMap B O :=
  ∑ j, R.branchMap j U V

theorem NormalForm.map_apply (R : NormalForm A B O) (U V : Matrix.unitaryGroup A ℂ)
    (X : CMatrix B) :
    R.map U V X = ∑ j,
      ((R.rest j).channel (oracleChannel (secondUnitary (R.order j) U V))).map
        ((oracleChannel (firstUnitary (R.order j) U V)).map
          (R.pre j * X * (R.pre j).conjTranspose)) := by
  simp [NormalForm.map, NormalForm.branchMap, MatrixMap.ofKraus]

def NormalForm.first (order : ICO.TwoQueryTree.Order)
    (after : ICO.OptionalOneQuery.NormalForm A (A × M) O) : NormalForm A (A × M) O where
  Branch := PUnit
  FirstMemory := fun _ => M
  SecondMemory := fun _ => after.Memory
  pre := fun _ => 1
  complete := by simp
  order := fun _ => order
  rest := fun _ => after.form

theorem NormalForm.first_map (order : ICO.TwoQueryTree.Order)
    (after : ICO.OptionalOneQuery.NormalForm A (A × M) O)
    (U V : Matrix.unitaryGroup A ℂ) :
    (NormalForm.first order after).map U V =
      (after.form.channel (oracleChannel (secondUnitary order U V))).map.comp
        (oracleChannel (firstUnitary order U V)).map := by
  ext X i j
  simp [NormalForm.map_apply, NormalForm.first]

def NormalForm.prepend (I : Instrument B C L) (next : L → NormalForm A C O) :
    NormalForm A B O where
  Branch := (l : L) × (next l).Branch
  FirstMemory := fun j => (next j.1).FirstMemory j.2
  SecondMemory := fun j => (next j.1).SecondMemory j.2
  pre := fun j => (next j.1).pre j.2 * I.op j.1
  complete := by
    rw [Fintype.sum_sigma]
    have hinner (l : L) :
        (∑ j : (next l).Branch,
          ((next l).pre j * I.op l).conjTranspose * ((next l).pre j * I.op l)) =
          (I.op l).conjTranspose * I.op l := by
      calc
        _ = (I.op l).conjTranspose *
            (∑ j : (next l).Branch, ((next l).pre j).conjTranspose * (next l).pre j) *
              I.op l := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
            Matrix.mul_assoc]
        _ = _ := by rw [(next l).complete]; simp
    simp_rw [hinner]
    exact I.complete
  order := fun j => (next j.1).order j.2
  rest := fun j => (next j.1).rest j.2

theorem NormalForm.prepend_apply (I : Instrument B C L) (next : L → NormalForm A C O)
    (U V : Matrix.unitaryGroup A ℂ) (X : CMatrix B) :
    (NormalForm.prepend I next).map U V X =
      ∑ l, (next l).map U V (I.op l * X * (I.op l).conjTranspose) := by
  simp only [NormalForm.map_apply, NormalForm.prepend, Fintype.sum_sigma,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

def NormalForm.terminal [Nonempty O] (a₀ : A) (Φ : Channel B O) : NormalForm A B O where
  Branch := B × O
  FirstMemory := fun _ => O
  SecondMemory := fun _ => O
  pre := ICO.OptionalOneQuery.terminalOp a₀ Φ
  complete := ICO.OptionalOneQuery.terminalOp_complete a₀ Φ
  order := fun _ => .firstThenSecond
  rest := fun _ => (ICO.OptionalOneQuery.NormalForm.terminal a₀
    (discardChannel (A := A) (C := O))).form

theorem NormalForm.terminal_map [Nonempty O] (a₀ : A) (Φ : Channel B O)
    (U V : Matrix.unitaryGroup A ℂ) :
    (NormalForm.terminal a₀ Φ).map U V = Φ.map := by
  ext X i j
  rw [NormalForm.map_apply]
  simp only [NormalForm.terminal, firstUnitary, secondUnitary,
    ICO.OptionalOneQuery.NormalForm.terminal_map]
  conv_rhs => rw [channelKraus_map Φ]
  simp only [ICO.OptionalOneQuery.terminalOp, MatrixMap.ofKraus,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have h := congrArg (fun F : MatrixMap (A × O) O => F
      ((oracleChannel U).map ((pad (C := O) a₀ * channelKraus Φ k) * X *
        (pad (C := O) a₀ * channelKraus Φ k).conjTranspose)) i j)
    (ICO.OptionalOneQuery.NormalForm.terminal_map a₀
      (discardChannel (A := A) (C := O)) V)
  exact h.trans (congrFun (congrFun
    (discarded_oracle_precomposed U a₀ (channelKraus Φ k) X) i) j)

/-- A finite adaptive circuit that uses each of two selected oracles at most
once. Other fixed channels can occur in every instrument block. -/
inductive QueryTree (A M O : Type u) [Fintype A] [Fintype M] [Fintype O]
    [DecidableEq A] [DecidableEq M] [DecidableEq O] :
    (B : Type u) → [Fintype B] → [DecidableEq B] → Type (u + 1) where
  | stop {B : Type u} [Fintype B] [DecidableEq B] (after : Channel B O) : QueryTree A M O B
  | first (order : ICO.TwoQueryTree.Order)
      (after : ICO.OptionalOneQuery.QueryTree A M O (A × M)) : QueryTree A M O (A × M)
  | node {B C L : Type u} [Fintype B] [Fintype C] [Fintype L]
      [DecidableEq B] [DecidableEq C] [DecidableEq L]
      (I : Instrument B C L) (next : L → QueryTree A M O C) : QueryTree A M O B

def QueryTree.channel (tree : QueryTree A M O B)
    (first second : Channel (A × M) (A × M)) : Channel B O := by
  induction tree with
  | stop after => exact after
  | first order after =>
    exact
      (after.channel (ICO.TwoQueryTree.secondOracle order first second)).comp
        (ICO.TwoQueryTree.firstOracle order first second)
  | node I next ih => exact adaptiveChannel I ih

def QueryTree.normalForm [Nonempty M] [Nonempty O] (a₀ : A) (tree : QueryTree A M O B) :
    NormalForm A B O := by
  induction tree with
  | stop after => exact NormalForm.terminal a₀ after
  | first order after => exact NormalForm.first order (after.normalForm a₀)
  | node I next ih => exact NormalForm.prepend I ih

theorem QueryTree.normalForm_correct [Nonempty M] [Nonempty O] (a₀ : A)
    (tree : QueryTree A M O B) (U V : Matrix.unitaryGroup A ℂ) :
    (tree.normalForm a₀).map U V =
      (tree.channel (oracleChannel U) (oracleChannel V)).map := by
  induction tree with
  | stop after => exact NormalForm.terminal_map a₀ after U V
  | first order after =>
    change (NormalForm.first order (after.normalForm a₀)).map U V = _
    rw [NormalForm.first_map]
    cases order <;>
      simp only [firstUnitary, secondUnitary, ICO.OptionalOneQuery.QueryTree.normalForm_correct,
        QueryTree.channel, ICO.TwoQueryTree.firstOracle, ICO.TwoQueryTree.secondOracle,
        Channel.comp]
  | node I next ih =>
    change (NormalForm.prepend I (fun l => (next l).normalForm a₀)).map U V = _
    ext X i j
    simp only [NormalForm.prepend_apply, ih, QueryTree.channel,
      ICO.OneQueryTree.adaptiveChannel_apply]

end
end ICO.OptionalTwoQuery

import ICO.AllChannelDilation
import ICO.TwoQueryTree

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.TwoQueryTree ICO.AllChannelDilation

namespace ICO.TwoQueryDilation
set_option maxHeartbeats 600000
noncomputable section
universe u
variable {A M P O I T : Type u}
variable [Fintype A] [Fintype M] [Fintype P] [Fintype O] [Fintype I] [Fintype T]
variable [DecidableEq A] [DecidableEq M] [DecidableEq P] [DecidableEq O]
  [DecidableEq I] [DecidableEq T]

def branchMap (R : ICO.TwoQueryTree.NormalForm P (A × M) O) (b : R.Branch)
    (U V : CMatrix A) : MatrixMap P O :=
  match R.order b with
  | .firstThenSecond => MatrixMap.ofKraus
      (circuitKraus (R.pre.op b) (normalMid (R.rest b)) (normalPost (R.rest b)) U V)
  | .secondThenFirst => MatrixMap.ofKraus
      (circuitKraus (R.pre.op b) (normalMid (R.rest b)) (normalPost (R.rest b)) V U)

theorem branchMap_channel (R : ICO.TwoQueryTree.NormalForm P (A × M) O) (b : R.Branch)
    (U : I → CMatrix A) (V : T → CMatrix A)
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) (X : CMatrix P) :
    (∑ i, ∑ j, branchMap R b (U i) (V j) X) =
      ((R.rest b).channel (secondOracle (R.order b) (oracleChannel U hU) (oracleChannel V hV))).map
        ((firstOracle (R.order b) (oracleChannel U hU) (oracleChannel V hV)).map
          (R.pre.op b * X * (R.pre.op b)ᴴ)) := by
  cases ho : R.order b with
  | firstThenSecond =>
    simpa only [branchMap,ho,firstOracle,secondOracle] using
      normalForm_channel_map (R.rest b) (R.pre.op b) U V hU hV X
  | secondThenFirst =>
    simp only [branchMap,ho,firstOracle,secondOracle]
    rw [Finset.sum_comm]
    exact normalForm_channel_map (R.rest b) (R.pre.op b) V U hV hU X

/-- The full extracted instrument tree is the sum of actual isometric circuit
branches in both orders, including arbitrary channels and retained output. -/
theorem normalForm_channel (R : ICO.TwoQueryTree.NormalForm P (A × M) O)
    (U : I → CMatrix A) (V : T → CMatrix A)
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) (X : CMatrix P) :
    (R.channel (oracleChannel U hU) (oracleChannel V hV)).map X =
      ∑ b : R.Branch, ∑ i, ∑ j, branchMap R b (U i) (V j) X := by
  rw [ICO.TwoQueryTree.NormalForm.channel_apply]
  apply Finset.sum_congr rfl
  intro b hb
  exact (branchMap_channel R b U V hU hV X).symm

theorem tree_channel (tree : ICO.TwoQueryTree.QueryTree (A × M) O P)
    (U : I → CMatrix A) (V : T → CMatrix A)
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) (X : CMatrix P) :
    (tree.channel (oracleChannel U hU) (oracleChannel V hV)).map X =
      ∑ b : tree.normalForm.Branch, ∑ i, ∑ j, branchMap tree.normalForm b (U i) (V j) X := by
  rw [← ICO.TwoQueryTree.QueryTree.normalForm_correct]
  exact normalForm_channel tree.normalForm U V hU hV X

#print axioms tree_channel
end
end ICO.TwoQueryDilation

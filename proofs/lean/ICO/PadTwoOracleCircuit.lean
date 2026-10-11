import ICO.PadLabelledCircuit

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.AllChannelDilation

namespace ICO.PadTwoOracleCircuit
set_option maxHeartbeats 600000
noncomputable section
variable {A M O B I J L R : Type}
  [Fintype A] [Fintype M] [Fintype O] [Fintype B] [Fintype I] [Fintype J]
  [DecidableEq A] [DecidableEq M] [DecidableEq O] [DecidableEq B]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq R]

def leftFamily (U : I → CMatrix A) : I ⊕ J → CMatrix A := Sum.elim U (fun _ => 0)
def rightFamily (V : J → CMatrix A) : I ⊕ J → CMatrix A := Sum.elim (fun _ => 0) V

theorem left_complete (U : I → CMatrix A) (hU : ∑ i,(U i)ᴴ*U i=1) :
    (∑ k,(leftFamily (J:=J) U k)ᴴ*leftFamily U k)=1 := by
  simpa [Fintype.sum_sum_type,leftFamily] using hU

theorem right_complete (V : J → CMatrix A) (hV : ∑ j,(V j)ᴴ*V j=1) :
    (∑ k,(rightFamily (I:=I) V k)ᴴ*rightFamily V k)=1 := by
  simpa [Fintype.sum_sum_type,rightFamily] using hV

@[simp] theorem left_map (U : I → CMatrix A) :
    oracleMap (M:=M) (leftFamily (J:=J) U)=oracleMap U := by
  ext X i j
  simp [oracleMap,MatrixMap.ofKraus,leftFamily,Fintype.sum_sum_type]

@[simp] theorem right_map (V : J → CMatrix A) :
    oracleMap (M:=M) (rightFamily (I:=I) V)=oracleMap V := by
  ext X i j
  simp [oracleMap,MatrixMap.ofKraus,rightFamily,Fintype.sum_sum_type]

theorem separated_maps (U : I → CMatrix A) (V : J → CMatrix A) :
    (fun l : L ⊕ R => oracleMap (M:=M)
      (Sum.elim (fun _ => leftFamily (J:=J) U) (fun _ => rightFamily (I:=I) V) l)) =
        Sum.elim (fun _ => oracleMap U) (fun _ => oracleMap V) := by
  funext l
  cases l <;> simp

theorem compile_map (a₀ : A) (m₀ : M) (o₀ : O) {s : Finset (L ⊕ R)}
    (tree : ICO.AtMostLabelledQueryTree.Tree (L ⊕ R) (A × M) O s B)
    (U : I → CMatrix A) (V : J → CMatrix A)
    (hU : ∑ i,(U i)ᴴ*U i=1) (hV : ∑ j,(V j)ᴴ*V j=1) :
    (ICO.PadLabelledCircuit.compile a₀ m₀ o₀ tree).map
      (Sum.elim (fun _ => oracleMap U) (fun _ => oracleMap V)) =
    tree.map (Sum.elim (fun _ => oracleMap U) (fun _ => oracleMap V)) := by
  let F : L ⊕ R → I ⊕ J → CMatrix A :=
    Sum.elim (fun _ => leftFamily U) (fun _ => rightFamily V)
  have hF (l : L ⊕ R) : (∑ k,(F l k)ᴴ*F l k)=1 := by
    cases l with
    | inl l => exact left_complete U hU
    | inr r => exact right_complete V hV
  have h := ICO.PadLabelledCircuit.compile_map a₀ m₀ o₀ tree F hF
  change (ICO.PadLabelledCircuit.compile a₀ m₀ o₀ tree).map
    (fun l => oracleMap (Sum.elim (fun _ => leftFamily U) (fun _ => rightFamily V) l)) =
    tree.map (fun l => oracleMap (Sum.elim (fun _ => leftFamily U) (fun _ => rightFamily V) l)) at h
  simpa only [separated_maps] using h

#print axioms compile_map
end
end ICO.PadTwoOracleCircuit

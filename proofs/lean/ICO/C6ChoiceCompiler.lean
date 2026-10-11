import ICO.C6ChoiceOracle

/-! Exact compilation of two named noisy oracles to one tagged oracle.
The public choice is prepared at each actual query and its discarded outcome
is retained privately by the tagged oracle's Kraus family. -/
namespace ICO.C6ChoiceCompiler
open Matrix QIT ICO.InstrumentCompression ICO.ClassicalDilation ICO.BudgetQueryTree
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A M B C H O I : Type} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

def prepend {q : ℕ} (channel : Channel B C) (tree : Tree H O q C) : Tree H O q B :=
  .node (ICO.LabelledCircuitComposition.channelInstrument channel) (fun _ => tree)

theorem prepend_map {q : ℕ} (channel : Channel B C) (tree : Tree H O q C)
    (first second : Channel H H) :
    ((prepend channel tree).channel first second).map =
      (tree.channel first second).map.comp channel.map := by
  change (∑l, (tree.channel first second).map.comp
    (branchMap (ICO.LabelledCircuitComposition.channelInstrument channel) l))=_
  ext X i j
  rw [channelKraus_map channel]
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,branchMap_apply,
    ICO.LabelledCircuitComposition.channelInstrument,MatrixMap.ofKraus,
    LinearMap.coe_mk,AddHom.coe_mk,map_sum,Matrix.sum_apply]

def compile {q : ℕ} (tree : Tree (A×M) O q B) : Tree ((A×Bool)×M) O q B := by
  induction tree with
  | stop after => exact .stop after
  | query b after ih =>
    exact prepend (ICO.C6ChoiceOracle.embedChoice b)
      (.query false (prepend ICO.C6ChoiceOracle.eraseChoice ih))
  | node instrument next ih => exact .node instrument ih

theorem compile_map {q : ℕ} (tree : Tree (A×M) O q B)
    (K : Bool→I→CMatrix A) (hK : ∀b,∑i,(K b i)ᴴ*K b i=1) :
    ((compile tree).channel
      (ICO.AllChannelDilation.oracleChannel (ICO.C6ChoiceOracle.taggedKraus K)
        (ICO.C6ChoiceOracle.tagged_complete K hK))
      (ICO.AllChannelDilation.oracleChannel (ICO.C6ChoiceOracle.taggedKraus K)
        (ICO.C6ChoiceOracle.tagged_complete K hK))).map =
    (tree.channel (ICO.AllChannelDilation.oracleChannel (K false) (hK false))
      (ICO.AllChannelDilation.oracleChannel (K true) (hK true))).map := by
  induction tree with
  | stop after => rfl
  | query b after ih =>
    change ((prepend (ICO.C6ChoiceOracle.embedChoice b)
      (Tree.query false (prepend ICO.C6ChoiceOracle.eraseChoice (compile after)))).channel _ _).map = _
    rw [prepend_map,Tree.query_map,prepend_map,ih]
    simp only [Bool.false_eq_true,ite_false]
    have hr := ICO.C6ChoiceOracle.tagged_retraction (M:=M) K b
    cases b <;> ext X i j <;>
      simpa only [LinearMap.comp_apply,ICO.AllChannelDilation.oracleChannel] using
        congrFun (congrFun (congrArg (fun f => (after.channel
          (ICO.AllChannelDilation.oracleChannel (K false) (hK false))
          (ICO.AllChannelDilation.oracleChannel (K true) (hK true))).map (f X)) hr) i) j
  | node instrument next ih =>
    change (∑j, ((compile (next j)).channel _ _).map.comp (branchMap instrument j)) = _
    simp_rw [ih]
    rfl

def sequential {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : Tree (A×M) O q B) : ICO.SequentialIsometry.Protocol (A×Bool) B O q :=
  ICO.AdaptiveSequentialProtocol.budget (a₀,false) m₀ o₀ (compile tree)

theorem sequential_map {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : Tree (A×M) O q B) (K : Bool→I→CMatrix A)
    (hK : ∀b,∑i,(K b i)ᴴ*K b i=1) (X : CMatrix B) :
    (sequential a₀ m₀ o₀ tree).map (ICO.C6ChoiceOracle.taggedKraus K) X =
      (tree.channel (ICO.AllChannelDilation.oracleChannel (K false) (hK false))
        (ICO.AllChannelDilation.oracleChannel (K true) (hK true))).map X := by
  rw [sequential,ICO.AdaptiveSequentialProtocol.budget_map _ _ _ _ _
    (ICO.C6ChoiceOracle.tagged_complete K hK),compile_map]

#print axioms sequential_map
end
end ICO.C6ChoiceCompiler

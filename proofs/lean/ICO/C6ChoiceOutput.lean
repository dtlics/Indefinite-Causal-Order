import ICO.C6ChoiceCompiler
import ICO.C6SharedBasis
import ICO.ProtocolLudersTrajectory

/-! Exact physical semantics of the shared-hidden-unitary representation of
an arbitrary adaptive two-channel circuit, including early stopping. -/
namespace ICO.C6ChoiceOutput
open Matrix QIT ICO.SequentialIsometry ICO.C6SharedBasis
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option Elab.async false
variable {A M B O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype B] [DecidableEq B]
  [Fintype O] [DecidableEq O]

theorem protocol_map_tagged {q:ℕ} (p : Protocol (A×Bool) B O q)
    (U H : Matrix.unitaryGroup A ℂ) :
    p.map (ICO.C6ChoiceOracle.taggedKraus (kraus U H))=
      p.map (ICO.SwitchObservable.basisProjection (basis U H:CMatrix (A×Bool))) := by
  induction p with
  | stop post hpost => rfl
  | query pre hpre after ih =>
    change (after.map _).comp ((ICO.AllChannelDilation.oracleMap _).comp (singleMap pre))=_
    rw [ih,oracleMap_tagged]
    rfl

theorem sequential_map {q:ℕ} (a₀:A) (m₀:M) (o₀:O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O q B) (U H : Matrix.unitaryGroup A ℂ)
    (X:CMatrix B) :
    (ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ tree).map
      (ICO.SwitchObservable.basisProjection (basis U H:CMatrix (A×Bool))) X =
      (tree.channel
        (ICO.AllChannelDilation.oracleChannel (kraus U H false) (kraus_complete U H false))
        (ICO.AllChannelDilation.oracleChannel (kraus U H true) (kraus_complete U H true))).map X := by
  rw [←protocol_map_tagged,ICO.C6ChoiceCompiler.sequential_map]

theorem output_map {q:ℕ} (a₀:A) (m₀:M) (o₀:O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O (q+1) B) (U H : Matrix.unitaryGroup A ℂ)
    (v:B→ℂ) :
    ICO.ProtocolLudersTrajectory.output (ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ tree)
      (basis U H:CMatrix (A×Bool)) v =
      (tree.channel
        (ICO.AllChannelDilation.oracleChannel (kraus U H false) (kraus_complete U H false))
        (ICO.AllChannelDilation.oracleChannel (kraus U H true) (kraus_complete U H true))).map
          (rankOneMatrix v) := by
  rw [ICO.ProtocolLudersTrajectory.output_map,sequential_map]

#print axioms sequential_map
#print axioms output_map
end
end ICO.C6ChoiceOutput

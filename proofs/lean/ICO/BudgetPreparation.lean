import ICO.BudgetKnownOracle

/-! A fixed initial channel can be absorbed into an adaptive strategy without
using an oracle call. This includes preparation of an arbitrary mixed state. -/
namespace ICO.BudgetPreparation
open Matrix QIT ICO.InstrumentCompression ICO.BudgetQueryTree
open scoped BigOperators Matrix
noncomputable section
universe u
set_option maxHeartbeats 1800000
variable {H O B C : Type u} [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

def kraus (Φ : Channel C B) : C×B→Matrix B C ℂ :=
  Classical.choose (MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive)

theorem kraus_map (Φ : Channel C B) : MatrixMap.ofKraus (kraus Φ)=Φ.map :=
  (Classical.choose_spec (MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive)).symm

def instrument (Φ : Channel C B) : Instrument C B (C×B) where
  op := kraus Φ
  complete := by
    have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus (kraus Φ)) := by
      rw [kraus_map]
      exact Φ.tracePreserving
    simpa only [MatrixMap.krausAdjoint,Matrix.mul_one] using
      MatrixMap.krausAdjoint_one_of_tracePreserving (kraus Φ) hTP

def precompose {q : ℕ} (tree : Tree H O q B) (Φ : Channel C B) : Tree H O q C :=
  .node (instrument Φ) (fun _ => tree)

theorem precompose_map {q : ℕ} (tree : Tree H O q B) (Φ : Channel C B)
    (first second : Channel H H) :
    ((precompose tree Φ).channel first second).map=
      (tree.channel first second).map.comp Φ.map := by
  ext X i j
  change adaptiveMap (instrument Φ) (fun _ => tree.channel first second) X i j=_
  rw [adaptiveMap_apply]
  change (∑ l,(tree.channel first second).map (kraus Φ l*X*(kraus Φ l).conjTranspose)) i j=
    (tree.channel first second).map (Φ.map X) i j
  rw [←map_sum,←kraus_map Φ]
  rfl

theorem channel_eq_of_map_eq {Φ Ψ : Channel C O} (h : Φ.map = Ψ.map) : Φ = Ψ := by
  cases Φ
  cases Ψ
  cases h
  rfl

def _root_.ICO.BudgetQueryTree.Tree.prepare {q : ℕ} (tree : Tree H O q B)
    (W : Matrix B C ℂ) (hW : W.conjTranspose * W = 1) : Tree H O q C :=
  precompose tree (ICO.ClassicalDilation.isometryChannel W hW)

theorem _root_.ICO.BudgetQueryTree.Tree.prepare_channel {q : ℕ} (tree : Tree H O q B)
    (W : Matrix B C ℂ) (hW : W.conjTranspose * W = 1) (first second : Channel H H) :
    (tree.prepare W hW).channel first second =
      (tree.channel first second).comp (ICO.ClassicalDilation.isometryChannel W hW) :=
  channel_eq_of_map_eq (precompose_map tree (ICO.ClassicalDilation.isometryChannel W hW) first second)

def prepare {q : ℕ} (tree : Tree H O q B) (ρ : State B) : Tree H O q PUnit :=
  precompose tree (Channel.prepare (fun _ : PUnit => ρ))

theorem prepare_output {q : ℕ} (tree : Tree H O q B) (ρ : State B)
    (first second : Channel H H) :
    ((prepare tree ρ).channel first second).map (rankOneMatrix (fun _ : PUnit => (1:ℂ)))=
      (tree.channel first second).map ρ.matrix := by
  rw [prepare,precompose_map]
  change (tree.channel first second).map
    ((Channel.prepare (fun _ : PUnit => ρ)).map (rankOneMatrix (fun _ => (1:ℂ))))=_
  congr 1
  simp [Channel.prepare,Channel.prepareMap,rankOneMatrix,Matrix.vecMulVec]

theorem initial_norm : ‖WithLp.toLp 2 (fun _ : PUnit => (1:ℂ))‖≤1 := by
  simp [PiLp.norm_eq_of_L2]

theorem initial_mass : (rankOneMatrix (fun _ : PUnit => (1:ℂ))).trace.re=1 := by
  simp [rankOneMatrix,Matrix.trace,Matrix.vecMulVec]

#print axioms prepare_output
end
end ICO.BudgetPreparation

import ICO.BudgetHaarBound

/-! Absorbing either fixed oracle into known adaptive operations, preserving
the original total budget and the exact physical output channel. -/
namespace ICO.BudgetKnownOracle
open Matrix QIT ICO.InstrumentCompression ICO.BudgetQueryTree
open scoped BigOperators Matrix
noncomputable section
universe u
set_option maxHeartbeats 2000000
variable {H O B : Type u} [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]

def channelKraus (Φ : Channel H H) : H×H→CMatrix H :=
  Classical.choose (MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive)

theorem channelKraus_map (Φ : Channel H H) : MatrixMap.ofKraus (channelKraus Φ)=Φ.map :=
  (Classical.choose_spec (MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive)).symm

def channelInstrument (Φ : Channel H H) : Instrument H H (H×H) where
  op := channelKraus Φ
  complete := by
    have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus (channelKraus Φ)) := by
      rw [channelKraus_map]
      exact Φ.tracePreserving
    have hh := MatrixMap.krausAdjoint_one_of_tracePreserving (channelKraus Φ) hTP
    simpa only [MatrixMap.krausAdjoint,Matrix.mul_one] using hh

theorem fixed_adaptive_map (Φ : Channel H H) (Ψ : Channel H O) :
    (adaptiveChannel (channelInstrument Φ) (fun _ => Ψ)).map=Ψ.map.comp Φ.map := by
  ext X i j
  change adaptiveMap (channelInstrument Φ) (fun _ => Ψ) X i j=_
  rw [adaptiveMap_apply]
  change (∑ l, Ψ.map (channelKraus Φ l*X*(channelKraus Φ l).conjTranspose)) i j=
    Ψ.map (Φ.map X) i j
  rw [←map_sum]
  rw [←channelKraus_map Φ]
  rfl

def _root_.ICO.BudgetQueryTree.Tree.addOne {q : ℕ} (tree : Tree H O q B) : Tree H O (q+1) B := by
  induction tree with
  | stop after => exact .stop after
  | query b after ih => exact .query b ih
  | node instrument next ih => exact .node instrument ih

theorem _root_.ICO.BudgetQueryTree.Tree.addOne_map {q : ℕ} (tree : Tree H O q B) (first second : Channel H H) :
    (tree.addOne.channel first second).map=(tree.channel first second).map := by
  induction tree with
  | stop after => rfl
  | query b after ih =>
    change (after.addOne.channel first second).map.comp (if b then second else first).map=_
    rw [ih]
    rfl
  | node instrument next ih =>
    change (∑ j,((next j).addOne.channel first second).map.comp (branchMap instrument j))=_
    simp_rw [ih]
    rfl

def _root_.ICO.BudgetQueryTree.Tree.fixKnown {q : ℕ} (tree : Tree H O q B) (knownLabel : Bool) (Φ : Channel H H) :
    Tree H O q B := by
  induction tree with
  | stop after => exact .stop after
  | query b after ih =>
    exact if b=knownLabel then .node (channelInstrument Φ) (fun _ => ih.addOne)
      else .query false ih
  | node instrument next ih => exact .node instrument ih

theorem _root_.ICO.BudgetQueryTree.Tree.fixKnown_map {q : ℕ} (tree : Tree H O q B)
    (knownLabel : Bool) (Φ U : Channel H H) :
    ((tree.fixKnown knownLabel Φ).channel U U).map=
      (tree.channel (if knownLabel then U else Φ) (if knownLabel then Φ else U)).map := by
  induction tree with
  | stop after => rfl
  | query b after ih =>
    by_cases hb : b=knownLabel
    · subst b
      simp only [Tree.fixKnown,if_pos rfl]
      have hc : (if knownLabel then (if knownLabel then Φ else U) else (if knownLabel then U else Φ))=Φ := by
        cases knownLabel <;> rfl
      change (adaptiveChannel (channelInstrument Φ)
        (fun _ => ((after.fixKnown knownLabel Φ).addOne.channel U U))).map=
        (after.channel (if knownLabel then U else Φ) (if knownLabel then Φ else U)).map.comp
          (if knownLabel then (if knownLabel then Φ else U) else (if knownLabel then U else Φ)).map
      rw [hc,fixed_adaptive_map,Tree.addOne_map,ih]
    · simp only [Tree.fixKnown,hb,if_neg]
      have hc : (if b then (if knownLabel then Φ else U) else (if knownLabel then U else Φ))=U := by
        cases b <;> cases knownLabel <;> simp_all
      change ((after.fixKnown knownLabel Φ).channel U U).map.comp U.map=
        (after.channel (if knownLabel then U else Φ) (if knownLabel then Φ else U)).map.comp
          (if b then (if knownLabel then Φ else U) else (if knownLabel then U else Φ)).map
      rw [hc,ih]
  | node instrument next ih =>
    change (∑ j,(((next j).fixKnown knownLabel Φ).channel U U).map.comp (branchMap instrument j))=_
    simp_rw [ih]
    rfl

#print axioms Tree.fixKnown_map
end
end ICO.BudgetKnownOracle

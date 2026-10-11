import ICO.AtMostLabelledQueryTree
import ICO.OptionalTreeCoherence

/-! # Extract two selected oracle labels while retaining all other fixed channels -/

open Matrix QIT ICO.InstrumentCompression ICO.ClassicalDilation

namespace ICO.AtMostSelectedQueryTree
set_option maxHeartbeats 600000
noncomputable section
universe u
variable {L A M O B H C : Type u} [DecidableEq L]
variable [Fintype A] [Fintype M] [Fintype O] [Fintype B] [Fintype H] [Fintype C]
variable [DecidableEq A] [DecidableEq M] [DecidableEq O] [DecidableEq B]
variable [DecidableEq H] [DecidableEq C]

def channelInstrument (Φ : Channel H H) : Instrument H H (H × H) where
  op := channelKraus Φ
  complete := by
    have h := MatrixMap.krausAdjoint_one_of_tracePreserving (channelKraus Φ)
      (by rw [← channelKraus_map]; exact Φ.tracePreserving)
    simpa [MatrixMap.krausAdjoint] using h

theorem channelInstrument_sum (Φ : Channel H H) :
    (∑ k, branchMap (channelInstrument Φ) k) = Φ.map := by
  rw [channelKraus_map]
  ext X i j
  simp [branchMap_apply, channelInstrument, MatrixMap.ofKraus, Matrix.sum_apply]

theorem channelInstrument_continue (Φ : Channel H H) (F : MatrixMap H C) :
    (∑ k, F.comp (branchMap (channelInstrument Φ) k)) = F.comp Φ.map := by
  conv_rhs => rw [← channelInstrument_sum Φ]
  ext X i j
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Matrix.sum_apply]

def oneAssignment (g : L → Channel (A × M) (A × M)) (b : L)
    (V : MatrixMap (A × M) (A × M)) : L → MatrixMap (A × M) (A × M) :=
  fun i => if i = b then V else (g i).map

def twoAssignment (g : L → Channel (A × M) (A × M)) (a b : L)
    (U V : MatrixMap (A × M) (A × M)) : L → MatrixMap (A × M) (A × M) :=
  fun i => if i = a then U else if i = b then V else (g i).map

def oneSelect {s : Finset L} (tree : ICO.AtMostLabelledQueryTree.Tree L (A × M) O s B)
    (g : L → Channel (A × M) (A × M)) (b : L) :
    ICO.OptionalOneQuery.QueryTree A M O B := by
  induction tree with
  | terminal Φ => exact .stop Φ
  | query i hi after ih =>
    by_cases h : i = b
    · exact .call (.terminal (after.channel g))
    · exact .node (channelInstrument (g i)) (fun _ => ih)
  | node I next ih => exact .node I ih

theorem oneSelect_map {s : Finset L} (tree : ICO.AtMostLabelledQueryTree.Tree L (A × M) O s B)
    (g : L → Channel (A × M) (A × M)) (b : L) (V : Channel (A × M) (A × M)) :
    ((oneSelect tree g b).channel V).map = tree.map (oneAssignment g b V.map) := by
  induction tree with
  | terminal Φ => rfl
  | @query s i hi after ih =>
    by_cases h : i = b
    · subst i
      simp only [oneSelect, dif_pos rfl]
      change (after.channel g).map.comp V.map =
        (after.map (oneAssignment g b V.map)).comp ((oneAssignment g b V.map) b)
      rw [ICO.AtMostLabelledQueryTree.Tree.channel_map]
      congr 1
      · apply after.map_congr
        intro i hi
        simp [oneAssignment, (Finset.mem_erase.mp hi).1]
      · simp [oneAssignment]
    · simp only [oneSelect, dif_neg h]
      change (∑ k, ((oneSelect after g b).channel V).map.comp
        (branchMap (channelInstrument (g i)) k)) = _
      rw [channelInstrument_continue, ih]
      simp [ICO.AtMostLabelledQueryTree.Tree.map_query, oneAssignment, h]
  | node I next ih =>
    change (∑ k, ((oneSelect (next k) g b).channel V).map.comp (branchMap I k)) = _
    simp_rw [ih]
    rfl

def twoSelect {s : Finset L} (tree : ICO.AtMostLabelledQueryTree.Tree L (A × M) O s B)
    (g : L → Channel (A × M) (A × M)) (a b : L) :
    ICO.OptionalTwoQuery.QueryTree A M O B := by
  induction tree with
  | terminal Φ => exact .stop Φ
  | query i hi after ih =>
    by_cases hia : i = a
    · exact .first .firstThenSecond (oneSelect after g b)
    · by_cases hib : i = b
      · exact .first .secondThenFirst (oneSelect after g a)
      · exact .node (channelInstrument (g i)) (fun _ => ih)
  | node I next ih => exact .node I ih

theorem twoSelect_map {s : Finset L} (tree : ICO.AtMostLabelledQueryTree.Tree L (A × M) O s B)
    (g : L → Channel (A × M) (A × M)) (a b : L) (hab : a ≠ b)
    (U V : Channel (A × M) (A × M)) :
    ((twoSelect tree g a b).channel U V).map = tree.map (twoAssignment g a b U.map V.map) := by
  induction tree with
  | terminal Φ => rfl
  | @query s i hi after ih =>
    by_cases hia : i = a
    · subst i
      simp only [twoSelect, dif_pos rfl]
      change ((oneSelect after g b).channel V).map.comp U.map =
        (after.map (twoAssignment g a b U.map V.map)).comp ((twoAssignment g a b U.map V.map) a)
      rw [oneSelect_map]
      congr 1
      · apply after.map_congr
        intro i hi
        simp [twoAssignment, oneAssignment, (Finset.mem_erase.mp hi).1]
      · simp [twoAssignment]
    · by_cases hib : i = b
      · subst i
        simp only [twoSelect, dif_neg hia, dif_pos rfl]
        change ((oneSelect after g a).channel U).map.comp V.map =
          (after.map (twoAssignment g a b U.map V.map)).comp ((twoAssignment g a b U.map V.map) b)
        rw [oneSelect_map]
        congr 1
        · apply after.map_congr
          intro i hi
          simp [twoAssignment, oneAssignment, (Finset.mem_erase.mp hi).1]
        · simp [twoAssignment, Ne.symm hab]
      · simp only [twoSelect, dif_neg hia, dif_neg hib]
        change (∑ k, ((twoSelect after g a b).channel U V).map.comp
          (branchMap (channelInstrument (g i)) k)) = _
        rw [channelInstrument_continue, ih]
        simp [ICO.AtMostLabelledQueryTree.Tree.map_query, twoAssignment, hia, hib]
  | node I next ih =>
    change (∑ k, ((twoSelect (next k) g a b).channel U V).map.comp (branchMap I k)) = _
    simp_rw [ih]
    rfl

open MeasureTheory ICO.TreeCoherence ICO.AverageCoherence

theorem selected_mean_coherence_bound {Z : Type u} [Fintype Z] [DecidableEq Z]
    [Nonempty Z] [Nonempty M] [Nontrivial A] {s : Finset L}
    (tree : ICO.AtMostLabelledQueryTree.Tree L (A × M) (A × Z) s A)
    (g : L → Channel (A × M) (A × M)) (a b : L) (hab : a ≠ b)
    (z z' : Z) :
    (∫ UV : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ,
      ‖mapCoherence (tree.map (twoAssignment g a b
          (oracleChannel UV.1).map (oracleChannel UV.2).map)) z z'
        ((UV.2 : CMatrix A) * (UV.1 : CMatrix A))
        ((UV.1 : CMatrix A) * (UV.2 : CMatrix A))‖
      ∂(unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))) ≤
      reverseFactor (A := A) := by
  have h := ICO.OptionalTreeCoherence.queryTree_average_bound (Classical.arbitrary A)
    (twoSelect tree g a b) z z'
  simpa only [twoSelect_map _ _ _ _ hab] using h

end
end ICO.AtMostSelectedQueryTree


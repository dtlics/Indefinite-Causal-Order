import ICO.LabelledQueryTree
import ICO.TwoQueryTree

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.LabelledQueryTree ICO.InstrumentCompression

namespace ICO.SelectedQueryTree
set_option maxHeartbeats 600000
noncomputable section
universe u
variable {L H O A : Type u} [DecidableEq L] [Fintype H] [Fintype O]
  [DecidableEq H] [DecidableEq O] [Fintype A] [DecidableEq A]

theorem idChannel_map : (Channel.idChannel H).map = LinearMap.id := by
  ext X i j
  simp [Channel.idChannel,MatrixMap.ofKraus]

/-- Physically remove all identity calls from a labelled tree. -/
def zeroSelect {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A) :
    ICO.InstrumentCompression.Tree O A := by
  induction tree with
  | terminal channel => exact .terminal channel
  | query i hi after ih => exact ih
  | node instrument next ih => exact .node instrument ih

theorem zeroSelect_map {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A) :
    (zeroSelect tree).toChannel.map = tree.map (fun _ => LinearMap.id) := by
  induction tree with
  | terminal channel => rfl
  | query i hi after ih => simpa [zeroSelect,ICO.LabelledQueryTree.Tree.map_query] using ih
  | node instrument next ih =>
    change (∑ k, (zeroSelect (next k)).toChannel.map.comp (branchMap instrument k)) = _
    simp_rw [ih]
    rfl

def oneAssignment (b : L) (V : MatrixMap H H) : L → MatrixMap H H :=
  fun i => if i=b then V else LinearMap.id

def twoAssignment (a b : L) (U V : MatrixMap H H) : L → MatrixMap H H :=
  fun i => if i=a then U else if i=b then V else LinearMap.id

def oneSelect {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A)
    (b : L) (hb : b ∈ s) : ICO.OneQueryTree.QueryTree H O A := by
  induction tree with
  | terminal channel => simp at hb
  | @query s i hi after ih =>
    by_cases h : i=b
    · exact .call (zeroSelect after)
    · exact ih (Finset.mem_erase.mpr ⟨Ne.symm h,hb⟩)
  | node instrument next ih => exact .node instrument (fun k => ih k hb)

theorem oneSelect_map {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A)
    (b : L) (hb : b ∈ s) (V : Channel H H) :
    ((oneSelect tree b hb).channel V).map = tree.map (oneAssignment b V.map) := by
  induction tree with
  | terminal channel => simp at hb
  | @query s i hi after ih =>
    by_cases h : i=b
    · subst i
      simp only [oneSelect,dif_pos rfl]
      change (zeroSelect after).toChannel.map.comp V.map =
        (after.map (oneAssignment b V.map)).comp ((oneAssignment b V.map) b)
      rw [zeroSelect_map]
      congr 1
      · apply after.map_congr
        intro i hi
        simp [oneAssignment,(Finset.mem_erase.mp hi).1]
      · simp [oneAssignment]
    · simp only [oneSelect,dif_neg h]
      change ((oneSelect after b (Finset.mem_erase.mpr ⟨Ne.symm h,hb⟩)).channel V).map = _
      rw [ih]
      simp [ICO.LabelledQueryTree.Tree.map_query,oneAssignment,h]
  | node instrument next ih =>
    change (∑ k, ((oneSelect (next k) b hb).channel V).map.comp (branchMap instrument k)) = _
    simp_rw [ih]
    rfl

def twoSelect {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A)
    (a b : L) (hab : a≠b) (ha : a∈s) (hb : b∈s) : ICO.TwoQueryTree.QueryTree H O A := by
  induction tree with
  | terminal channel => simp at ha
  | @query s i hi after ih =>
    by_cases hia : i=a
    · exact .first .firstThenSecond
        (oneSelect after b (Finset.mem_erase.mpr ⟨by simpa [hia] using Ne.symm hab,hb⟩))
    · by_cases hib : i=b
      · exact .first .secondThenFirst
          (oneSelect after a (Finset.mem_erase.mpr ⟨by simpa [hib] using hab,ha⟩))
      · exact ih (Finset.mem_erase.mpr ⟨Ne.symm hia,ha⟩)
          (Finset.mem_erase.mpr ⟨Ne.symm hib,hb⟩)
  | node instrument next ih => exact .node instrument (fun k => ih k ha hb)

/-- The extracted ordinary two-query adaptive circuit has exactly the same
map as the original circuit with all other labels replaced by identity. This
holds for arbitrary channels, not only unitary oracles. -/
theorem twoSelect_map {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L H O s A)
    (a b : L) (hab : a≠b) (ha : a∈s) (hb : b∈s) (U V : Channel H H) :
    ((twoSelect tree a b hab ha hb).channel U V).map =
      tree.map (twoAssignment a b U.map V.map) := by
  induction tree with
  | terminal channel => simp at ha
  | @query s i hi after ih =>
    by_cases hia : i=a
    · subst i
      simp only [twoSelect,dif_pos rfl]
      change ((oneSelect after b _).channel V).map.comp U.map =
        (after.map (twoAssignment a b U.map V.map)).comp ((twoAssignment a b U.map V.map) a)
      rw [oneSelect_map]
      congr 1
      · apply after.map_congr
        intro i hi
        simp [twoAssignment,oneAssignment,(Finset.mem_erase.mp hi).1]
      · simp [twoAssignment]
    · by_cases hib : i=b
      · subst i
        simp only [twoSelect,dif_neg hia,dif_pos rfl]
        change ((oneSelect after a _).channel U).map.comp V.map =
          (after.map (twoAssignment a b U.map V.map)).comp ((twoAssignment a b U.map V.map) b)
        rw [oneSelect_map]
        congr 1
        · apply after.map_congr
          intro i hi
          simp [twoAssignment,oneAssignment,(Finset.mem_erase.mp hi).1]
        · simp [twoAssignment,Ne.symm hab]
      · simp only [twoSelect,dif_neg hia,dif_neg hib]
        change ((twoSelect after a b hab (Finset.mem_erase.mpr ⟨Ne.symm hia,ha⟩)
          (Finset.mem_erase.mpr ⟨Ne.symm hib,hb⟩)).channel U V).map = _
        rw [ih]
        simp [ICO.LabelledQueryTree.Tree.map_query,twoAssignment,hia,hib]
  | node instrument next ih =>
    change (∑ k, ((twoSelect (next k) a b hab ha hb).channel U V).map.comp
      (branchMap instrument k)) = _
    simp_rw [ih]
    rfl

#print axioms twoSelect_map
end
end ICO.SelectedQueryTree

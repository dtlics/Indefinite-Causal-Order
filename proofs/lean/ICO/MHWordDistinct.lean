import ICO.MHBellProjectors

/-! Actual distinctness projectors on finite ordered record words. Splitting
one record coordinate exhibits exactly the forbidden-label Bell blocks. -/
namespace ICO.MHWordDistinct
open Matrix QIT ICO.MHBellBlocks ICO.MHBellProjectors
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {A J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype J] [DecidableEq J]

abbrev WordBasis (A J : Type*) := A × (J → A × A)
abbrev Other (i : J) := {j : J // j ≠ i}
abbrev Spectator (A : Type*) (i : J) := A × (Other i → A × A)

def assemble (i : J) (g : Spectator A i) (z : A) : J → A × A :=
  fun j => if h : j = i then (z,g.1) else g.2 ⟨j,h⟩

@[simp] theorem assemble_at (i : J) (g : Spectator A i) (z : A) :
    assemble i g z i = (z,g.1) := by simp [assemble]

@[simp] theorem assemble_other (i : J) (g : Spectator A i) (z : A) (j : Other i) :
    assemble i g z j.val = g.2 j := by simp [assemble, j.property]

def slotEquiv (i : J) : WordBasis A J ≃ (Spectator A i × (A × A)) where
  toFun v := ⟨((v.2 i).2, fun j => v.2 j.val), (v.1,(v.2 i).1)⟩
  invFun v := (v.2.1, assemble i v.1 v.2.2)
  left_inv v := by
    change (v.1, assemble i ((v.2 i).2, fun j => v.2 j.val) (v.2 i).1) = (v.1,v.2)
    apply Prod.ext
    · rfl
    · funext j
      by_cases h : j = i
      · subst j; simp [assemble]
      · simp [assemble,h]
  right_inv v := by
    rcases v with ⟨⟨y,w⟩,x,z⟩
    simp only [assemble_at, assemble_other]

def distinct (w : J → A × A) : Prop :=
  Function.Injective (fun j => (w j).1) ∧ Function.Injective (fun j => (w j).2)

def spectatorGood (i : J) (g : Spectator A i) : Prop :=
  Function.Injective (fun j : Other i => (g.2 j).1) ∧
    Function.Injective (fun j : J => if h : j = i then g.1 else (g.2 ⟨j,h⟩).2)

local instance spectatorGoodDecidable (i : J) : DecidablePred (spectatorGood (A := A) i) :=
  Classical.decPred _

theorem assemble_snd (i : J) (g : Spectator A i) (z : A) :
    (fun j => (assemble i g z j).2) =
      (fun j => if h : j = i then g.1 else (g.2 ⟨j,h⟩).2) := by
  funext j
  simp only [assemble]
  split_ifs <;> rfl

def forbidden (i : J) (g : Spectator A i) : Finset A :=
  Finset.univ.image (fun j : Other i => (g.2 j).1)

theorem forbidden_card_le (i : J) (g : Spectator A i) :
    (forbidden i g).card ≤ Fintype.card J := by
  exact (Finset.card_image_le).trans (by
    simpa using Fintype.card_subtype_le (fun j : J => j ≠ i))

theorem distinct_assemble_iff (i : J) (g : Spectator A i) (z : A) :
    distinct (assemble i g z) ↔ spectatorGood i g ∧ z ∉ forbidden i g := by
  classical
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j k hjk
      apply Subtype.ext
      apply h.1
      simpa using hjk
    · simpa only [assemble_snd] using h.2
    · intro hz
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hz
      have he : (assemble i g z j.val).1 = (assemble i g z i).1 := by simpa using hj
      exact j.property (h.1 he)
  · rintro ⟨hg,hz⟩
    refine ⟨?_, ?_⟩
    · intro j k hjk
      by_cases hj : j = i
      · subst j
        by_cases hk : k = i
        · exact hk.symm
        · exfalso
          apply hz
          refine Finset.mem_image.mpr ⟨⟨k,hk⟩,Finset.mem_univ _,?_⟩
          simpa [assemble,hk] using hjk.symm
      · by_cases hk : k = i
        · subst k
          exfalso
          apply hz
          refine Finset.mem_image.mpr ⟨⟨j,hj⟩,Finset.mem_univ _,?_⟩
          simpa [assemble,hj] using hjk
        · have he := hg.1 (show (g.2 ⟨j,hj⟩).1 = (g.2 ⟨k,hk⟩).1 by
            simpa [assemble,hj,hk] using hjk)
          exact congrArg Subtype.val he
    · rw [assemble_snd]
      exact hg.2

def distinctProjection : CMatrix (WordBasis A J) := by
  classical
  exact Matrix.diagonal (fun v => if distinct v.2 then 1 else 0)

def slotEquality (i : J) : CMatrix (WordBasis A J) :=
  (equalityProjection (A := A) (Γ := Spectator A i)).submatrix (slotEquiv i) (slotEquiv i)

def slotBell (i : J) : CMatrix (WordBasis A J) :=
  (bellProjection (A := A) (Γ := Spectator A i)).submatrix (slotEquiv i) (slotEquiv i)

theorem distinctProjection_split (i : J) :
    distinctProjection (A := A) (J := J) =
      (recordProjection (spectatorGood i) (forbidden i) (A := A)).submatrix (slotEquiv i) (slotEquiv i) := by
  classical
  have he (v : WordBasis A J) :
      distinct v.2 ↔ spectatorGood i ((slotEquiv i v).1) ∧
        (slotEquiv i v).2.2 ∉ forbidden i ((slotEquiv i v).1) := by
    have h := distinct_assemble_iff i (slotEquiv i v).1 (slotEquiv i v).2.2
    have hw : assemble i (slotEquiv i v).1 (slotEquiv i v).2.2 = v.2 := by
      have hh := congrArg Prod.snd ((slotEquiv (A := A) i).left_inv v)
      exact hh
    rwa [hw] at h
  ext v w
  simp only [distinctProjection, recordProjection, Matrix.diagonal_apply, Matrix.submatrix_apply]
  by_cases hvw : v = w
  · subst w; simp [he]
  · have hsplit : slotEquiv i v ≠ slotEquiv i w := fun h => hvw ((slotEquiv i).injective h)
    simp [hvw,hsplit]

theorem submatrix_order {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (e : K → H) {X Y : CMatrix H} (h : X ≤ Y) :
    X.submatrix e e ≤ Y.submatrix e e := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.submatrix_sub] using (Matrix.le_iff.mp h).submatrix e

theorem word_record_compression (i : J) :
    distinctProjection (A := A) (J := J) * (slotEquality i - slotBell i) * distinctProjection ≤
      (slotEquality i - slotBell i) +
        (2 * Real.sqrt ((Fintype.card J : ℝ)/Fintype.card A)) •
          (1 : CMatrix (WordBasis A J)) := by
  classical
  have hh := record_compression_le (A := A) (spectatorGood i) (forbidden i)
    (Fintype.card J) (forbidden_card_le i)
  have h := submatrix_order (slotEquiv (A := A) i) hh
  rw [← Matrix.submatrix_mul_equiv _ _ (slotEquiv i) (slotEquiv i) (slotEquiv i),
    ← Matrix.submatrix_mul_equiv _ _ (slotEquiv i) (slotEquiv i) (slotEquiv i)] at h
  rw [distinctProjection_split i]
  change (recordProjection (spectatorGood i) (forbidden i) (A := A)).submatrix
      (slotEquiv i) (slotEquiv i) *
      ((equalityProjection (A := A) (Γ := Spectator A i)).submatrix (slotEquiv i) (slotEquiv i) -
       (bellProjection (A := A) (Γ := Spectator A i)).submatrix (slotEquiv i) (slotEquiv i)) *
      (recordProjection (spectatorGood i) (forbidden i) (A := A)).submatrix (slotEquiv i) (slotEquiv i) ≤
    (equalityProjection (A := A) (Γ := Spectator A i)).submatrix (slotEquiv i) (slotEquiv i) -
      (bellProjection (A := A) (Γ := Spectator A i)).submatrix (slotEquiv i) (slotEquiv i) +
      (2 * Real.sqrt ((Fintype.card J : ℝ)/Fintype.card A)) •
        ((1 : CMatrix (Spectator A i × (A × A))).submatrix (slotEquiv i) (slotEquiv i)) at h
  rw [Matrix.submatrix_one_equiv] at h
  exact h

#print axioms word_record_compression

theorem diagonal_projection {H : Type*} [Fintype H] [DecidableEq H]
    (p : H → Prop) [DecidablePred p] :
    IsStarProjection (Matrix.diagonal (fun h => if p h then (1 : ℂ) else 0)) := by
  constructor
  · show _ * _ = _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext h
    split_ifs <;> simp
  · show star _ = _
    ext h k
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases he : h = k
    · subst k; simp
    · simp [he,Ne.symm he]

theorem distinct_projection : IsStarProjection (distinctProjection (A := A) (J := J)) := by
  classical
  exact diagonal_projection _

theorem slotEquality_diagonal (i : J) :
    slotEquality (A := A) i = Matrix.diagonal (fun v : WordBasis A J =>
      if v.1 = (v.2 i).1 then 1 else 0) := by
  ext v w
  simp only [slotEquality, equalityProjection, Matrix.submatrix_apply, Matrix.diagonal_apply]
  by_cases he : v = w
  · subst w; simp [slotEquiv]
  · have hs : slotEquiv i v ≠ slotEquiv i w := fun h => he ((slotEquiv i).injective h)
    simp [he,hs]

theorem equality_compression (i : J) :
    distinctProjection (A := A) (J := J) * slotEquality i * distinctProjection ≤ (slotEquality (A := A) i) := by
  classical
  have hQ : IsStarProjection (slotEquality (A := A) i) := by
    rw [slotEquality_diagonal]
    exact diagonal_projection _
  have hc : distinctProjection * slotEquality i = slotEquality i *
      (distinctProjection (A := A) (J := J)) := by
    rw [slotEquality_diagonal]
    simp only [distinctProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext v
    exact mul_comm _ _
  have hh := ICO.MHProjectionCompression.compression_le_of_commutator_le
    (distinctProjection (A := A) (J := J)) (slotEquality i) distinct_projection hQ 0
    (by rw [hc,sub_self,norm_zero])
  simpa using hh

def freshProjection : CMatrix (WordBasis A J) := by
  classical
  exact Matrix.diagonal (fun v => if ∀ j, v.1 ≠ (v.2 j).1 then 1 else 0)

theorem collision_union_bound :
    (1 : CMatrix (WordBasis A J)) - freshProjection ≤ ∑ j : J, slotEquality j := by
  classical
  apply Matrix.le_iff.mpr
  simp_rw [slotEquality_diagonal]
  have hsum : (∑ x : J, Matrix.diagonal (fun v : WordBasis A J =>
      if v.1 = (v.2 x).1 then (1 : ℂ) else 0)) =
      Matrix.diagonal (fun v : WordBasis A J => ∑ x : J,
        if v.1 = (v.2 x).1 then (1 : ℂ) else 0) := by
    ext v w
    by_cases h : v = w <;> simp [Matrix.sum_apply,Matrix.diagonal_apply,h]
  rw [hsum, freshProjection, ← Matrix.diagonal_one,
    Matrix.diagonal_sub, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro v
  change (0 : ℂ) ≤ (∑ x : J, if v.1 = (v.2 x).1 then 1 else 0) -
    (1 - if ∀ j, v.1 ≠ (v.2 j).1 then 1 else 0)
  by_cases hf : ∀ j, v.1 ≠ (v.2 j).1
  · simp [hf]
  · obtain ⟨j,hj⟩ := not_forall.mp hf
    have hj' : v.1 = (v.2 j).1 := not_not.mp hj
    have hs : (1 : ℂ) ≤ ∑ k : J, if v.1 = (v.2 k).1 then 1 else 0 := by
      have hh := Finset.single_le_sum
        (s := Finset.univ) (f := fun k : J => if v.1 = (v.2 k).1 then (1 : ℂ) else 0)
        (fun k _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ j)
      simpa [hj'] using hh
    simp only [hf,if_false,sub_zero]
    exact sub_nonneg.mpr hs

#print axioms collision_union_bound
end
end ICO.MHWordDistinct

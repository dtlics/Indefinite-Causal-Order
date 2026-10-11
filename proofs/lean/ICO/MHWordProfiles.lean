import ICO.MHBijectionProfiles
import ICO.MHSymmetric
import ICO.MHWordDistinct

/-! Exact transport of distinct-word projections to occupation-profile coordinates. -/
namespace ICO.MHWordProfiles
open Matrix QIT ICO.MHSymmetric ICO.MHOccupationCounts ICO.MHBijectionProfiles
  ICO.MHWordDistinct
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def enumeration {J a : Type*} [Fintype J] (w : J → a) : Multiset a :=
  Finset.univ.val.map w

theorem enumeration_nodup {J a : Type*} [Fintype J] (w : J → a) :
    (enumeration w).Nodup ↔ Function.Injective w := by
  classical
  simpa [enumeration,Function.Injective] using
    (Multiset.nodup_map_iff_inj_on (f := w) (Finset.univ (α := J)).nodup)

def wordProfile {a : Type*} [Fintype a] [DecidableEq a] {n : ℕ}
    (w : TensorPower a n) : TensorPowerProfile a n :=
  ⟨tensorPowerTypeProfile n w,tensorPowerTypeProfile_mem_profiles n w⟩

theorem wordProfile_multiset {a : Type*} [Fintype a] [DecidableEq a] {n : ℕ}
    (w : TensorPower a n) :
    (occupationMultiset n (wordProfile w) : Multiset a) = enumeration (tensorPowerEquiv n w) := by
  apply Multiset.ext.mpr
  intro z
  rw [occupationMultiset_count]
  change Fintype.card {i : Fin n // tensorPowerEquiv n w i = z} =
    Multiset.count z (Finset.univ.val.map (tensorPowerEquiv n w))
  rw [Multiset.count_map,Fintype.card_subtype]
  change (Finset.univ.filter (fun i : Fin n => tensorPowerEquiv n w i = z)).card =
    (Finset.univ.filter (fun i : Fin n => z = tensorPowerEquiv n w i)).card
  congr 1
  ext i
  simp [eq_comm]

def leftWord {l r : ℕ} (w : Fin l ⊕ Fin r → A × A) : TensorPower (A × A) l :=
  (tensorPowerEquiv l).symm (fun i => w (.inl i))

def rightWord {l r : ℕ} (w : Fin l ⊕ Fin r → A × A) : TensorPower (A × A) r :=
  (tensorPowerEquiv r).symm (fun i => w (.inr i))

theorem enumeration_sum {l r : ℕ} (w : Fin l ⊕ Fin r → A × A) :
    enumeration w = enumeration (tensorPowerEquiv l (leftWord w)) +
      enumeration (tensorPowerEquiv r (rightWord w)) := by
  simp only [leftWord,rightWord,Equiv.apply_symm_apply]
  change ((Finset.univ.disjSum Finset.univ).val.map w) = _
  simp only [Finset.val_disjSum,Multiset.disjSum,Multiset.map_add,Multiset.map_map,
    Function.comp_def,enumeration]

theorem distinct_iff_profiles {l r : ℕ} (w : Fin l ⊕ Fin r → A × A) :
    distinct w ↔ BijProfile (wordProfile (leftWord w)) (wordProfile (rightWord w)) := by
  simp only [BijProfile,wordProfile_multiset,BijMultiset,← enumeration_sum]
  have hfst : ((enumeration w).map Prod.fst).Nodup ↔ Function.Injective (fun i => (w i).1) := by
    simpa [enumeration,Multiset.map_map,Function.comp_def] using
      (enumeration_nodup (fun i => (w i).1))
  have hsnd : ((enumeration w).map Prod.snd).Nodup ↔ Function.Injective (fun i => (w i).2) := by
    simpa [enumeration,Multiset.map_map,Function.comp_def] using
      (enumeration_nodup (fun i => (w i).2))
  exact (and_congr hfst hsnd).symm

abbrev ProfileBasis (A : Type*) [Fintype A] [DecidableEq A] (l r : ℕ) :=
  A × TensorPowerProfile (A × A) l × TensorPowerProfile (A × A) r

def wordEmbedding (l r : ℕ) : Matrix (WordBasis A (Fin l ⊕ Fin r)) (ProfileBasis A l r) ℂ :=
  fun w p => (if w.1=p.1 then 1 else 0) * occupationEmbedding l (leftWord w.2) p.2.1 *
    occupationEmbedding r (rightWord w.2) p.2.2

def profileProjection (l r : ℕ) : CMatrix (ProfileBasis A l r) := by
  classical
  exact Matrix.diagonal (fun p => if BijProfile p.2.1 p.2.2 then 1 else 0)

theorem wordProfile_of_mem {a : Type*} [Fintype a] [DecidableEq a] {n : ℕ}
    (p : TensorPowerProfile a n) (w : TensorPower a n) (hw : w ∈ tensorPowerProfileClass p) :
    wordProfile w = p := by
  apply Subtype.ext
  exact (mem_tensorPowerProfileClass p w).mp hw

theorem support_profiles {l r : ℕ} (w : WordBasis A (Fin l ⊕ Fin r))
    (p : ProfileBasis A l r) (h : wordEmbedding l r w p ≠ 0) :
    distinct w.2 ↔ BijProfile p.2.1 p.2.2 := by
  have hl : leftWord w.2 ∈ tensorPowerProfileClass p.2.1 := by
    by_contra hn
    apply h
    simp [wordEmbedding,occupationEmbedding,tensorPowerProfileUnitVector,hn]
  have hr : rightWord w.2 ∈ tensorPowerProfileClass p.2.2 := by
    by_contra hn
    apply h
    simp [wordEmbedding,occupationEmbedding,tensorPowerProfileUnitVector,hn]
  rw [distinct_iff_profiles,wordProfile_of_mem _ _ hl,wordProfile_of_mem _ _ hr]

/-- The literal injectivity projector on both coordinate words is precisely
the bijection-profile projector under the normalized symmetric embedding. -/
theorem distinct_projection_intertwining (l r : ℕ) :
    distinctProjection (A := A) (J := Fin l ⊕ Fin r) * wordEmbedding l r =
      wordEmbedding l r * profileProjection l r := by
  classical
  ext w p
  rw [distinctProjection,profileProjection,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases h : wordEmbedding l r w p = 0
  · simp [h]
  · have he := support_profiles w p h
    simp only [he]
    split_ifs <;> simp

#print axioms distinct_iff_profiles
#print axioms distinct_projection_intertwining
end
end ICO.MHWordProfiles

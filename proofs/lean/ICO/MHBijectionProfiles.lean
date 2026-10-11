import ICO.MHFockLabels
import ICO.MHWPartial

/-! Bijection records in arbitrary-multiset occupation coordinates. The
condition is exact coordinate multiplicity at most one. -/

namespace ICO.MHBijectionProfiles

open QIT ICO.MHFockLabels ICO.MHOccupationCounts ICO.RecordingMultisetBridge
  ICO.PathRecordingSupport ICO.MHWPartial
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 2000000

variable {α : Type*} [Fintype α] [DecidableEq α]

def BijMultiset (L R : Multiset (α × α)) : Prop :=
  ((L+R).map Prod.fst).Nodup ∧ ((L+R).map Prod.snd).Nodup

def BijProfile {n r : ℕ} (p : TensorPowerProfile (α × α) n)
    (q : TensorPowerProfile (α × α) r) : Prop :=
  BijMultiset (α := α) (occupationMultiset n p : Multiset (α × α))
    (occupationMultiset r q : Multiset (α × α))

theorem bijMultiset_counts (L R : Multiset (α × α)) : BijMultiset L R ↔
    (∀ x, ((L+R).map Prod.fst).count x ≤ 1) ∧
    (∀ y, ((L+R).map Prod.snd).count y ≤ 1) := by
  exact and_congr Multiset.nodup_iff_count_le_one Multiset.nodup_iff_count_le_one

theorem bijMultiset_nodup {L R : Multiset (α × α)} (h : BijMultiset L R) : L.Nodup ∧ R.Nodup := by
  have hs := Multiset.nodup_add.mp (Multiset.Nodup.of_map Prod.fst h.1)
  exact ⟨hs.1,hs.2.1⟩

theorem mem_val_add (L R : Finset (α × α)) (z : α × α) :
    z ∈ L.val+R.val ↔ z ∈ L∪R := by simp

theorem bijMultiset_sets (L R : Finset (α × α)) : BijMultiset L.val R.val ↔ BijRecord L R := by
  constructor
  · intro h
    have hsum := Multiset.Nodup.of_map Prod.fst h.1
    have hd := (Multiset.nodup_add.mp hsum).2.2
    refine ⟨?_,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro z hzL hzR
      exact Multiset.disjoint_left.mp hd hzL hzR
    · intro x y z hy hz
      have he := Multiset.inj_on_of_nodup_map h.1 (x,y) ((mem_val_add L R _).mpr hy)
        (x,z) ((mem_val_add L R _).mpr hz) rfl
      exact congrArg Prod.snd he
    · intro x z y hx hz
      have he := Multiset.inj_on_of_nodup_map h.2 (x,y) ((mem_val_add L R _).mpr hx)
        (z,y) ((mem_val_add L R _).mpr hz) rfl
      exact congrArg Prod.fst he
  · rintro ⟨hd,hL,hR⟩
    have hdm : Disjoint L.val R.val := by
      apply Multiset.disjoint_left.mpr
      intro z hzL hzR
      exact Finset.disjoint_left.mp hd hzL hzR
    have hn : (L.val+R.val).Nodup := Multiset.nodup_add.mpr ⟨L.nodup,R.nodup,hdm⟩
    constructor
    · apply Multiset.Nodup.map_on ?_ hn
      intro a ha b hb he
      rcases a with ⟨x,y⟩
      rcases b with ⟨z,w⟩
      dsimp only at he
      subst z
      exact Prod.ext rfl (hL ((mem_val_add L R _).mp ha) ((mem_val_add L R _).mp hb))
    · apply Multiset.Nodup.map_on ?_ hn
      intro a ha b hb he
      rcases a with ⟨x,y⟩
      rcases b with ⟨z,w⟩
      dsimp only at he
      subst w
      exact Prod.ext (hR ((mem_val_add L R _).mp ha) ((mem_val_add L R _).mp hb)) rfl

theorem bijProfile_sets (L R : Finset (α × α)) : BijProfile (setProfile L) (setProfile R) ↔ BijRecord L R := by
  unfold BijProfile
  rw [setProfile_multiset,setProfile_multiset]
  exact bijMultiset_sets L R

theorem domainLabels_mem (L R : Multiset (α × α)) (x : α) :
    x ∈ domainLabels L R ↔ x ∈ (L+R).map Prod.fst := by
  simp only [domainLabels,Finset.mem_image,Finset.mem_union,Multiset.mem_toFinset,
    Multiset.mem_map,Multiset.mem_add]

theorem imageLabels_mem (L R : Multiset (α × α)) (y : α) :
    y ∈ imageLabels L R ↔ y ∈ (L+R).map Prod.snd := by
  simp only [imageLabels,Finset.mem_image,Finset.mem_union,Multiset.mem_toFinset,
    Multiset.mem_map,Multiset.mem_add]

theorem bijMultiset_cons_right (L R : Multiset (α × α)) (x y : α) :
    BijMultiset L ((x,y)::ₘR) ↔ BijMultiset L R ∧ x ∉ domainLabels L R ∧ y ∉ imageLabels L R := by
  simp only [BijMultiset,Multiset.add_cons,Multiset.map_cons,Multiset.nodup_cons,
    ← domainLabels_mem,← imageLabels_mem]
  tauto

theorem bijProfile_increment_right {n r : ℕ} (p : TensorPowerProfile (α × α) n)
    (q : TensorPowerProfile (α × α) r) (x y : α) :
    BijProfile p (incrementProfile (x,y) q) ↔ BijProfile p q ∧
      x ∉ domainLabels (occupationMultiset n p) (occupationMultiset r q) ∧
      y ∉ imageLabels (occupationMultiset n p) (occupationMultiset r q) := by
  unfold BijProfile
  rw [incrementProfile_multiset,bijMultiset_cons_right]

end
end ICO.MHBijectionProfiles

import ICO.MHFockSpace
import ICO.RecordingMultisetBridge

/-! The actual occupation register and the relation-labelled recording
register are related by a canonical, injective label map. -/

namespace ICO.MHFockLabels

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHOccupationCounts
  ICO.MHOccupationSupport ICO.RecordingMultisetBridge ICO.RecordingOperatorSupport
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 1500000

variable {a : Type*} [Fintype a] [DecidableEq a]

def setProfile (s : Finset a) : TensorPowerProfile a s.card :=
  (occupationMultiset s.card).symm (Sym.mk s.val rfl)

theorem setProfile_multiset (s : Finset a) :
    (occupationMultiset s.card (setProfile s) : Multiset a) = s.val := by
  simp [setProfile]

theorem setProfile_count (s : Finset a) (z : a) :
    (setProfile s).val z = if z ∈ s then 1 else 0 := by
  rw [← occupationMultiset_count, setProfile_multiset]
  exact Multiset.count_eq_of_nodup s.nodup

theorem profile_multiset_card {n : ℕ} (p : TensorPowerProfile a n) :
    (occupationMultiset n p : Multiset a).card = n := Sym.card_coe

variable {α : Type*} [Fintype α] [DecidableEq α]

def fockLabel {T : ℕ} (v : InputCutoff (α := α) T) : MultisetBasis α :=
  (v.2.1, occupationMultiset _ v.2.2, occupationMultiset _ v.1.2)

theorem fockLabel_injective (T : ℕ) : Function.Injective (fockLabel (α := α) (T := T)) := by
  intro v w he
  apply input_ext v w
  · have hc := congrArg (fun z : MultisetBasis α => z.2.1.card) he
    simpa only [fockLabel, profile_multiset_card] using hc
  · have hc := congrArg (fun z : MultisetBasis α => z.2.2.card) he
    simpa only [fockLabel, profile_multiset_card] using hc
  · exact congrArg (fun z : MultisetBasis α => z.1) he
  · funext z
    have hc := congrArg (fun v : MultisetBasis α => v.2.1.count z) he
    simpa only [fockLabel, occupationMultiset_count] using hc
  · funext z
    have hc := congrArg (fun v : MultisetBasis α => v.2.2.count z) he
    simpa only [fockLabel, occupationMultiset_count] using hc

def labelFock {T : ℕ} (v : MultisetBasis α) (hv : v.2.1.card + v.2.2.card ≤ T) :
    InputCutoff (α := α) T :=
  ⟨⟨⟨(⟨v.2.1.card, by omega⟩, ⟨v.2.2.card, by omega⟩),hv⟩,
    (occupationMultiset v.2.2.card).symm (Sym.mk v.2.2 rfl)⟩,
    (v.1, (occupationMultiset v.2.1.card).symm (Sym.mk v.2.1 rfl))⟩

theorem fockLabel_labelFock {T : ℕ} (v : MultisetBasis α) (hv : v.2.1.card + v.2.2.card ≤ T) :
    fockLabel (labelFock v hv) = v := by
  dsimp only [fockLabel, labelFock]
  rw [(occupationMultiset v.2.1.card).apply_symm_apply,
    (occupationMultiset v.2.2.card).apply_symm_apply]
  rfl

theorem labelFock_fockLabel {T : ℕ} (v : InputCutoff (α := α) T)
    (hv : (fockLabel v).2.1.card + (fockLabel v).2.2.card ≤ T) :
    labelFock (fockLabel v) hv = v := by
  apply fockLabel_injective T
  exact fockLabel_labelFock _ _

def setFock {T : ℕ} (v : Basis α) (hv : v.2.1.card + v.2.2.card ≤ T) :
    InputCutoff (α := α) T := labelFock (embed v) hv

theorem setFock_label {T : ℕ} (v : Basis α) (hv : v.2.1.card + v.2.2.card ≤ T) :
    fockLabel (setFock v hv) = embed v := fockLabel_labelFock _ _

theorem setFock_injective {T : ℕ} (v w : Basis α)
    (hv : v.2.1.card + v.2.2.card ≤ T) (hw : w.2.1.card + w.2.2.card ≤ T)
    (he : setFock v hv = setFock w hw) : v = w := by
  apply embed_injective
  have hh := congrArg fockLabel he
  simpa only [setFock_label] using hh

theorem outputMultiplicity_pos_iff {n : ℕ} (p : TensorPowerProfile (α × α) n) (y : α) :
    0 < outputMultiplicity p y ↔ ∃ x, 0 < p.val (x,y) := by
  unfold outputMultiplicity
  constructor
  · intro hp
    by_contra hn
    push Not at hn
    have hz : ∑ x : α, p.val (x,y) = 0 :=
      Finset.sum_eq_zero (fun x _ => Nat.eq_zero_of_le_zero (hn x))
    omega
  · rintro ⟨x,hx⟩
    exact lt_of_lt_of_le hx (Finset.single_le_sum (fun z _ => Nat.zero_le (p.val (z,y))) (Finset.mem_univ x))

theorem usedOutputs_multisets {n r : ℕ} (p : TensorPowerProfile (α × α) n)
    (q : TensorPowerProfile (α × α) r) :
    usedOutputs p q = imageLabels (occupationMultiset n p) (occupationMultiset r q) := by
  ext y
  rw [mem_usedOutputs, Nat.add_pos_iff_pos_or_pos, outputMultiplicity_pos_iff, outputMultiplicity_pos_iff]
  simp only [imageLabels, Finset.mem_image, Finset.mem_union, Multiset.mem_toFinset]
  constructor
  · rintro (⟨x,hx⟩ | ⟨x,hx⟩)
    · exact ⟨(x,y), Or.inl (Multiset.count_pos.mp (by rwa [occupationMultiset_count])), rfl⟩
    · exact ⟨(x,y), Or.inr (Multiset.count_pos.mp (by rwa [occupationMultiset_count])), rfl⟩
  · rintro ⟨⟨x,z⟩,hz,he⟩
    dsimp only at he
    subst z
    rcases hz with hp | hq
    · exact Or.inl ⟨x, by simpa only [occupationMultiset_count] using Multiset.count_pos.mpr hp⟩
    · exact Or.inr ⟨x, by simpa only [occupationMultiset_count] using Multiset.count_pos.mpr hq⟩

theorem usedOutputs_sets (L R : Finset (α × α)) :
    usedOutputs (setProfile L) (setProfile R) = (L ∪ R).image Prod.snd := by
  rw [usedOutputs_multisets, setProfile_multiset, setProfile_multiset]
  simp [imageLabels]

end
end ICO.MHFockLabels

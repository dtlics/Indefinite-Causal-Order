import ICO.RecordingOperatorSupport
import ICO.RecordingDistance

/-!
# Relation labels and the multiset recording oracle

The published recording oracle has orthonormal labels indexed by arbitrary
multisets. Our finite matrices use the invariant sector in which each relation
has no repeated edge. This file checks equality of its insertion coefficients
under the canonical label embedding. It does not assert the Haar-oracle
comparison theorem, which requires further analytic arguments.
-/

namespace ICO.RecordingMultisetBridge

open ICO.PathRecordingSupport ICO.RecordingOperatorSupport QIT
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev MultisetBasis (α : Type*) :=
  α × Multiset (α × α) × Multiset (α × α)

def embed (i : Basis α) : MultisetBasis α := (i.1, i.2.1.val, i.2.2.val)

omit [Fintype α] [DecidableEq α] in
theorem embed_injective : Function.Injective (embed (α := α)) := by
  intro i j h
  have hx := congrArg (fun v : MultisetBasis α => v.1) h
  have hL := congrArg (fun v : MultisetBasis α => v.2.1) h
  have hR := congrArg (fun v : MultisetBasis α => v.2.2) h
  exact Prod.ext hx (Prod.ext (Finset.val_injective hL) (Finset.val_injective hR))

/-- The union in the source formula is a multiset sum. Its image and domain
    discard multiplicities, whereas the cutoff counts both records in full. -/
def imageLabels (L R : Multiset (α × α)) : Finset α :=
  (L.toFinset ∪ R.toFinset).image Prod.snd

def domainLabels (L R : Multiset (α × α)) : Finset α :=
  (L.toFinset ∪ R.toFinset).image Prod.fst

def MultisetLeftStep (i o : MultisetBasis α) : Prop :=
  o.2.2 = i.2.2 ∧ o.1 ∉ imageLabels i.2.1 i.2.2 ∧
    o.2.1 = (i.1, o.1) ::ₘ i.2.1

def MultisetRightStep (i o : MultisetBasis α) : Prop :=
  o.2.1 = i.2.1 ∧ o.1 ∉ domainLabels i.2.1 i.2.2 ∧
    o.2.2 = (o.1, i.1) ::ₘ i.2.2

def multisetLeftInsertion : Matrix (MultisetBasis α) (MultisetBasis α) ℂ := by
  classical
  exact fun o i => if i.2.1.card + i.2.2.card < Fintype.card α ∧ MultisetLeftStep i o
    then (((Real.sqrt ((Fintype.card α : ℝ) -
      (imageLabels i.2.1 i.2.2).card))⁻¹ : ℝ) : ℂ) else 0

def multisetRightInsertion : Matrix (MultisetBasis α) (MultisetBasis α) ℂ := by
  classical
  exact fun o i => if i.2.1.card + i.2.2.card < Fintype.card α ∧ MultisetRightStep i o
    then (((Real.sqrt ((Fintype.card α : ℝ) -
      (domainLabels i.2.1 i.2.2).card))⁻¹ : ℝ) : ℂ) else 0

omit [Fintype α] in
theorem freshRight_iff_not_mem_image (x : α) (s : Relation α α) :
    FreshRight x s ↔ x ∉ s.image Prod.snd := by
  simp only [FreshRight, Finset.mem_image]
  constructor
  · intro h ⟨p, hp, hx⟩
    exact h p.1 (hx ▸ hp)
  · intro h y hy
    exact h ⟨(y, x), hy, rfl⟩

omit [Fintype α] in
theorem freshLeft_iff_not_mem_domain (x : α) (s : Relation α α) :
    FreshLeft x s ↔ x ∉ s.image Prod.fst := by
  simp only [FreshLeft, Finset.mem_image]
  constructor
  · intro h ⟨p, hp, hx⟩
    exact h p.2 (hx ▸ hp)
  · intro h y hy
    exact h ⟨(x, y), hy, rfl⟩

omit [Fintype α] in
theorem embedded_left_step (i o : Basis α) :
    MultisetLeftStep (embed i) (embed o) ↔ LeftStep i o := by
  simp only [MultisetLeftStep, embed, imageLabels, Finset.val_toFinset,
    Finset.val_inj, LeftStep, ← freshRight_iff_not_mem_image]
  constructor
  · rintro ⟨hR, hf, hL⟩
    refine ⟨hR, hf, ?_⟩
    have hh := congrArg Multiset.toFinset hL
    simpa only [Finset.val_toFinset, Multiset.toFinset_cons] using hh
  · rintro ⟨hR, hf, hL⟩
    refine ⟨hR, hf, ?_⟩
    have hn : (i.1, o.1) ∉ i.2.1 := fun h => hf i.1 (Finset.mem_union_left _ h)
    rw [hL, Finset.insert_val_of_notMem hn]

omit [Fintype α] in
theorem embedded_right_step (i o : Basis α) :
    MultisetRightStep (embed i) (embed o) ↔ RightStep i o := by
  simp only [MultisetRightStep, embed, domainLabels, Finset.val_toFinset,
    Finset.val_inj, RightStep, ← freshLeft_iff_not_mem_domain]
  constructor
  · rintro ⟨hL, hf, hR⟩
    refine ⟨hL, hf, ?_⟩
    have hh := congrArg Multiset.toFinset hR
    simpa only [Finset.val_toFinset, Multiset.toFinset_cons] using hh
  · rintro ⟨hL, hf, hR⟩
    refine ⟨hL, hf, ?_⟩
    have hn : (o.1, i.1) ∉ i.2.2 := fun h => hf i.1 (Finset.mem_union_right _ h)
    rw [hR, Finset.insert_val_of_notMem hn]

/-- The normalized coefficients, including the total-size cutoff, agree
    exactly with the multiset-label formula from the recording oracle. -/
theorem embedded_left_coefficient (i o : Basis α) :
    multisetLeftInsertion (embed o) (embed i) = leftInsertion o i := by
  unfold multisetLeftInsertion
  rw [embedded_left_step]
  simp only [leftInsertion,
    embed, imageLabels, Finset.val_toFinset, Finset.card]
  rfl

theorem embedded_right_coefficient (i o : Basis α) :
    multisetRightInsertion (embed o) (embed i) = rightInsertion o i := by
  unfold multisetRightInsertion
  rw [embedded_right_step]
  simp only [rightInsertion,
    embed, domainLabels, leftDomain, Finset.val_toFinset, Finset.card]
  rfl

def NodupLabel (i : MultisetBasis α) : Prop := i.2.1.Nodup ∧ i.2.2.Nodup

omit [Fintype α] [DecidableEq α] in
theorem embedded_nodup (i : Basis α) : NodupLabel (embed i) :=
  ⟨i.2.1.nodup, i.2.2.nodup⟩

omit [Fintype α] [DecidableEq α] in
theorem nodup_iff_embedded (i : MultisetBasis α) :
    NodupLabel i ↔ ∃ j : Basis α, embed j = i := by
  constructor
  · intro h
    exact ⟨(i.1, ⟨i.2.1, h.1⟩, ⟨i.2.2, h.2⟩), rfl⟩
  · rintro ⟨j, rfl⟩
    exact embedded_nodup j

omit [Fintype α] in
theorem multiset_left_preserves_nodup {i o : MultisetBasis α}
    (hi : NodupLabel i) (h : MultisetLeftStep i o) : NodupLabel o := by
  obtain ⟨hR, hf, hL⟩ := h
  constructor
  · rw [hL, Multiset.nodup_cons]
    refine ⟨?_, hi.1⟩
    intro he
    exact hf (Finset.mem_image.mpr ⟨(i.1, o.1),
      Finset.mem_union_left _ (Multiset.mem_toFinset.mpr he), rfl⟩)
  · rw [hR]
    exact hi.2

omit [Fintype α] in
theorem multiset_right_preserves_nodup {i o : MultisetBasis α}
    (hi : NodupLabel i) (h : MultisetRightStep i o) : NodupLabel o := by
  obtain ⟨hL, hf, hR⟩ := h
  constructor
  · rw [hL]
    exact hi.1
  · rw [hR, Multiset.nodup_cons]
    refine ⟨?_, hi.2⟩
    intro he
    exact hf (Finset.mem_image.mpr ⟨(o.1, i.1),
      Finset.mem_union_right _ (Multiset.mem_toFinset.mpr he), rfl⟩)

omit [Fintype α] in
theorem multiset_left_reverse_preserves_nodup {i o : MultisetBasis α}
    (hi : NodupLabel i) (h : MultisetLeftStep o i) : NodupLabel o := by
  obtain ⟨hR, _, hL⟩ := h
  refine ⟨?_, hR ▸ hi.2⟩
  have h := hi.1
  rw [hL] at h
  exact (Multiset.nodup_cons.mp h).2

omit [Fintype α] in
theorem multiset_right_reverse_preserves_nodup {i o : MultisetBasis α}
    (hi : NodupLabel i) (h : MultisetRightStep o i) : NodupLabel o := by
  obtain ⟨hL, _, hR⟩ := h
  refine ⟨hL ▸ hi.1, ?_⟩
  have h := hi.2
  rw [hR] at h
  exact (Multiset.nodup_cons.mp h).2

/-- The compressed dephased-Gram bound controls an expectation even when
    the two recording registers are coherent and entangled with memory. -/
theorem compressed_gram_expectation_le {μ : Type*} [Fintype μ] [DecidableEq μ]
    (m : ℕ) (hm : m < Fintype.card α)
    (ρ : CMatrix ((α × BoundedPair (α := α) (β := α) m) × μ))
    (hρ : ρ.PosSemidef) :
    ((Matrix.kronecker (fullCompressedDephasedGram (α := α) (β := α) m)
      (1 : CMatrix μ) * ρ).trace).re ≤
      (1 / ((Fintype.card α : ℝ) - (m : ℝ))) * ρ.trace.re := by
  apply ICO.RecordingDistance.bounded_effect_with_memory _ _ _ ρ hρ
  simpa only [Matrix.smul_one_eq_diagonal] using
    fullCompressedDephasedGram_le_scalar (α := α) (β := α) m hm

end
end ICO.RecordingMultisetBridge

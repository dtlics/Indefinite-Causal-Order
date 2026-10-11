import ICO.MHBijectionProfiles

/-! Canonical coefficients of the actual finite-set partial oracle W. -/

namespace ICO.MHFiniteWCanonical

open QIT ICO.MHBijectionProfiles ICO.MHWPartial ICO.PathRecordingSupport
  ICO.RecordingOperatorSupport ICO.RecordingMultisetBridge
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 2000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem domain_card_bij {L R : Relation α α} (h : BijRecord L R) :
    (leftDomain (L∪R)).card=L.card+R.card := by
  unfold leftDomain
  rw [Finset.card_image_of_injOn,Finset.card_union_of_disjoint h.1]
  intro a ha b hb he
  rcases a with ⟨x,y⟩
  rcases b with ⟨z,w⟩
  dsimp only at he
  subst z
  exact Prod.ext rfl (h.2.1 ha hb)

theorem right_step_bijection (i o : Basis α) (hs : RightStep i o) :
    BijRecord o.2.1 o.2.2 ↔ BijRecord i.2.1 i.2.2 ∧ FreshRight i.1 (i.2.1∪i.2.2) := by
  have hn : (o.1,i.1) ∉ i.2.2 := fun he => hs.2.1 i.1 (Finset.mem_union_right _ he)
  rw [hs.1,hs.2.2,← bijMultiset_sets,Finset.insert_val_of_notMem hn,bijMultiset_cons_right,
    bijMultiset_sets]
  simp only [domainLabels,imageLabels,Finset.val_toFinset]
  rw [← ICO.RecordingMultisetBridge.freshLeft_iff_not_mem_domain,
    ← ICO.RecordingMultisetBridge.freshRight_iff_not_mem_image]
  simp only [hs.2.1,true_and]

theorem rightW_coefficient (o i : Basis α) :
    rightW o i = if i.2.1.card+i.2.2.card<Fintype.card α ∧ RightStep i o ∧ BijRecord o.2.1 o.2.2 then
      (((Real.sqrt ((Fintype.card α : ℝ)-i.2.1.card-i.2.2.card))⁻¹ : ℝ) : ℂ) else 0 := by
  simp only [rightW,rightProjection,predicateProjection,Matrix.mul_diagonal]
  by_cases hs : RightStep i o
  · have hb := right_step_bijection i o hs
    by_cases hp : rightPredicate i
    · have hc := domain_card_bij hp.1
      have ho : BijRecord o.2.1 o.2.2 := hb.mpr ⟨hp.1,hp.2.1⟩
      have hc1 : i.2.1.card+i.2.2.card<Fintype.card α ∧ RightStep i o := ⟨hp.2.2,hs⟩
      have hc2 : i.2.1.card+i.2.2.card<Fintype.card α ∧ RightStep i o ∧ BijRecord o.2.1 o.2.2 := ⟨hp.2.2,hs,ho⟩
      rw [if_pos hp,mul_one,rightInsertion,if_pos hc1,if_pos hc2,hc]
      simp only [Nat.cast_add,sub_add_eq_sub_sub]
    · have hnot : ¬(i.2.1.card+i.2.2.card<Fintype.card α ∧ RightStep i o ∧ BijRecord o.2.1 o.2.2) := by
        rintro ⟨hd,_,ho⟩
        exact hp ⟨(hb.mp ho).1,(hb.mp ho).2,hd⟩
      simp [hp,hnot]
  · simp [rightInsertion,hs]

end
end ICO.MHFiniteWCanonical

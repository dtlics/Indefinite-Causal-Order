import ICO.MHCompressedQuery
import ICO.MHWPartial

namespace ICO.MHRecordCard
open Matrix QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport ICO.MHWPartial
  ICO.MHTernaryCompression ICO.MHCompressedQuery
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 600000

theorem rightImage_card (R : Relation A A) (hR : RightUnique R) :
    (R.image Prod.snd).card=R.card := by
  apply Finset.card_image_of_injOn
  intro e he f hf hh
  rcases e with ⟨a,b⟩
  rcases f with ⟨c,d⟩
  change b=d at hh
  subst d
  exact Prod.ext (hR he hf) rfl

theorem leftImage_card (R : Relation A A) (hR : LeftUnique R) :
    (R.image Prod.fst).card=R.card := by
  apply Finset.card_image_of_injOn
  intro e he f hf hh
  rcases e with ⟨a,b⟩
  rcases f with ⟨c,d⟩
  change a=c at hh
  subst c
  exact Prod.ext rfl (hR he hf)

theorem valid_card_le (R : Record A) : (R.val.1∪R.val.2).card≤Fintype.card A := by
  rw [←rightImage_card _ R.property.2.2]
  exact Finset.card_le_univ _

theorem coefficient_rightImage (R : Record A) :
    stepCoefficient R =
      (((Real.sqrt ((Fintype.card A : ℝ)-(((R.val.1∪R.val.2).image Prod.snd).card : ℝ)))⁻¹ : ℝ) : ℂ) := by
  unfold stepCoefficient
  rw [rightImage_card _ R.property.2.2,Nat.cast_sub (valid_card_le R)]

theorem coefficient_leftDomain (R : Record A) :
    stepCoefficient R =
      (((Real.sqrt ((Fintype.card A : ℝ)-((leftDomain (R.val.1∪R.val.2)).card : ℝ)))⁻¹ : ℝ) : ℂ) := by
  unfold stepCoefficient leftDomain
  rw [leftImage_card _ R.property.2.1,Nat.cast_sub (valid_card_le R)]

#print axioms coefficient_rightImage
end
end ICO.MHRecordCard

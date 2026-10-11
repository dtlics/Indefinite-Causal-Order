import ICO.MHCreatorEmbedding
import ICO.MHWordSlots

/-! The symmetric creator image in occupation coordinates is precisely the
compression of the sum of literal query/record Bell projections. -/
namespace ICO.MHOccupationBell
open QIT ICO.MHSymmetric ICO.MHCreatorEmbedding ICO.MHOccupationCovariance
  ICO.MHWordRightImage ICO.MHWordBellSum ICO.MHWordSlots
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem querySymmetry_embedding (n : ℕ) :
    querySymmetry n*queryOccupationEmbedding (α := α) n=queryOccupationEmbedding n := by
  rw [show querySymmetry (A := α) n=queryOccupationEmbedding n*(queryOccupationEmbedding (α := α) n).conjTranspose
    from (queryOccupation_image n).symm]
  rw [Matrix.mul_assoc,queryOccupation_gram,Matrix.mul_one]

theorem embedding_querySymmetry (n : ℕ) :
    (queryOccupationEmbedding (α := α) n).conjTranspose*querySymmetry n=
      (queryOccupationEmbedding (α := α) n).conjTranspose := by
  rw [show querySymmetry (A := α) n=queryOccupationEmbedding n*(queryOccupationEmbedding (α := α) n).conjTranspose
    from (queryOccupation_image n).symm]
  rw [← Matrix.mul_assoc,queryOccupation_gram,Matrix.one_mul]

theorem occupationRightCreator_bell_image (r : ℕ) :
    occupationRightCreator (α := α) r*(occupationRightCreator (α := α) r).conjTranspose=
      (Fintype.card α : ℂ) • ((queryOccupationEmbedding (α := α) (r+1)).conjTranspose*
        (∑ j : Fin (r+1), slotMatrix (A := α) (r+1) j)*queryOccupationEmbedding (r+1)) := by
  rw [occupationRightCreator_image,rightCreator_image_sum,Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  rw [← Matrix.mul_assoc (queryOccupationEmbedding (α := α) (r+1)).conjTranspose,
    ← Matrix.mul_assoc (queryOccupationEmbedding (α := α) (r+1)).conjTranspose,
    embedding_querySymmetry,Matrix.mul_assoc _ (querySymmetry (r+1)),querySymmetry_embedding,
    bellSum_eq_slots]

end
end ICO.MHOccupationBell

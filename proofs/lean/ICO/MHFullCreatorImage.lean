import ICO.MHWordBellSpectator
import ICO.MHOccupationBell
import ICO.MHWRightFactor

/-! The full two-record symmetric creation image, including coherent left
spectators, is exactly the compressed sum of right-record Bell slots. -/
namespace ICO.MHFullCreatorImage
open QIT ICO.MHSymmetric ICO.MHWordProfiles ICO.MHWordDistinct ICO.MHWordSlots
  ICO.MHWordBellSpectator ICO.MHCreatorEmbedding ICO.MHOccupationBell ICO.MHWRightFactor
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2500000
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def sectorWordEmbedding (l r : ℕ) :=
  (wordEmbedding (A := α) l r).submatrix id (rightProfileEquiv l r)

theorem right_slot_compression (l r : ℕ) (j : Fin r) :
    (sectorWordEmbedding (α := α) l r).conjTranspose*slotBell (Sum.inr j)*sectorWordEmbedding l r=
      Matrix.kronecker ((queryOccupationEmbedding (α := α) r).conjTranspose*
        slotMatrix (A := α) r j*queryOccupationEmbedding r)
          (1 : CMatrix (TensorPowerProfile (α×α) l)) := by
  rw [sectorWordEmbedding,wordEmbedding_right,right_slot_spectator,
    Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  simp only [Matrix.submatrix_id_id,rightWordEmbedding,Matrix.kronecker,
    Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one,occupationEmbedding_gram]

theorem sectorCreator_image_bells (l r : ℕ) :
    sectorCreator (α := α) l r*(sectorCreator (α := α) l r).conjTranspose=
      (Fintype.card α : ℂ) • ((sectorWordEmbedding (α := α) l (r+1)).conjTranspose*
        (∑ j : Fin (r+1),slotBell (A := α) (J := Fin l⊕Fin (r+1)) (Sum.inr j))*
        sectorWordEmbedding l (r+1)) := by
  rw [sectorCreator_tensor]
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul,Matrix.mul_one,occupationRightCreator_bell_image]
  simp only [Matrix.mul_sum,Matrix.sum_mul,right_slot_compression]
  ext o i
  simp only [Matrix.kroneckerMap_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,
    Matrix.mul_sum,Matrix.sum_mul,Matrix.sum_apply]
  simp only [Matrix.kronecker,Matrix.kroneckerMap_apply]
  rw [mul_assoc,Finset.sum_mul]

end
end ICO.MHFullCreatorImage

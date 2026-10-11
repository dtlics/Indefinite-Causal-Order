import ICO.MHFullCreatorImage

/-! The right part of the actual partial-oracle domain is the normalized
word Bell model, with both bijection projections included. -/
namespace ICO.MHActualRightDomain
open QIT ICO.MHSymmetric ICO.MHWordProfiles ICO.MHWordDistinct ICO.MHWordSlots
  ICO.MHWordBellSpectator ICO.MHFullCreatorImage ICO.MHWRightFactor ICO.MHWRightSector
  ICO.MHWOccupation ICO.MHWRecordEntries ICO.RecordingCopyIdentity
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2400000
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem sectorBij_reindex (l r : ℕ) : sectorBij (α := α) l r=
    (profileProjection (A := α) l r).submatrix (rightProfileEquiv l r) (rightProfileEquiv l r) := by
  simp only [sectorBij,bijRightProjection,Matrix.blockDiagonal_diagonal,
    profileProjection,Matrix.submatrix_diagonal_equiv]
  rfl

theorem sectorBij_adjoint (l r : ℕ) :
    (sectorBij (α := α) l r).conjTranspose=sectorBij l r := by
  simp only [sectorBij,Matrix.blockDiagonal_conjTranspose,bijRightProjection_adjoint]

theorem distinct_sector_intertwining (l r : ℕ) :
    distinctProjection*sectorWordEmbedding (α := α) l r=
      sectorWordEmbedding l r*sectorBij l r := by
  rw [sectorWordEmbedding,sectorBij_reindex]
  change (distinctProjection (A := α) (J := Fin l⊕Fin r)).submatrix id
      (Equiv.refl (WordBasis α (Fin l⊕Fin r))) *
      (wordEmbedding l r).submatrix (Equiv.refl _) (rightProfileEquiv l r)=_
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,distinct_projection_intertwining]

theorem distinct_sector_sandwich (l r : ℕ) (X : CMatrix (WordBasis α (Fin l⊕Fin r))) :
    sectorBij l r*((sectorWordEmbedding (α := α) l r).conjTranspose*X*sectorWordEmbedding l r)*sectorBij l r=
      (sectorWordEmbedding l r).conjTranspose*(distinctProjection*X*distinctProjection)*sectorWordEmbedding l r := by
  have hP : (distinctProjection (A := α) (J := Fin l⊕Fin r)).conjTranspose=distinctProjection :=
    distinct_projection.isSelfAdjoint.star_eq
  have hj := congrArg Matrix.conjTranspose (distinct_sector_intertwining (α := α) l r)
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hP,sectorBij_adjoint] at hj
  simp only [Matrix.mul_assoc]
  rw [distinct_sector_intertwining]
  simp only [← Matrix.mul_assoc]
  rw [hj]

theorem actual_right_domain {n r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : n+r≤T) (ho : n+(r+1)≤T) (hsize : n+r<Fintype.card α) :
    (basisEmbedding (rightSectorEmbed (α := α) ho)).conjTranspose*
        (recordRightW hT*(recordRightW hT).conjTranspose)*basisEmbedding (rightSectorEmbed ho)=
      ((Fintype.card α : ℝ)/((Fintype.card α : ℝ)-n-r)) •
        ((sectorWordEmbedding (α := α) n (r+1)).conjTranspose*
          (distinctProjection*(∑ j : Fin (r+1),slotBell (A := α) (J := Fin n⊕Fin (r+1)) (Sum.inr j))*distinctProjection)*
          sectorWordEmbedding n (r+1)) := by
  rw [actual_right_image_factor hT hi ho hsize,sectorCreator_image_bells,
    Matrix.mul_smul,Matrix.smul_mul,smul_smul,distinct_sector_sandwich]
  ext o i
  simp only [Matrix.smul_apply,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_sub,Complex.ofReal_natCast,Complex.ofReal_inv]
  ring

end
end ICO.MHActualRightDomain

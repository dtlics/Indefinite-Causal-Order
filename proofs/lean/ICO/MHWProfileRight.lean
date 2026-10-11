import ICO.MHActualRightDomain
import ICO.MHWProfileLeft

/-! The actual right-domain model in the same profile coordinates used by
the physical left-domain compression and the Haar word rotation. -/
namespace ICO.MHWProfileRight
open QIT ICO.MHWordProfiles ICO.MHWordDistinct ICO.MHWordBellSpectator
  ICO.MHFullCreatorImage ICO.MHActualRightDomain ICO.MHWRightSector ICO.MHWProfileLeft
  ICO.MHWRecordEntries ICO.RecordingCopyIdentity
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2100000
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem sectorWord_compression_reindex (l r : ℕ) (X : CMatrix (WordBasis α (Fin l⊕Fin r))) :
    ((sectorWordEmbedding (α := α) l r).conjTranspose*X*sectorWordEmbedding l r).submatrix
      (rightProfileEquiv l r).symm (rightProfileEquiv l r).symm=
      (wordEmbedding l r).conjTranspose*X*wordEmbedding l r := by
  ext o i
  simp only [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    sectorWordEmbedding,Matrix.submatrix_apply,id_eq,Equiv.apply_symm_apply]

theorem record_right_compression {l r T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (hi : l+r≤T) (ho : l+(r+1)≤T) (hsize : l+r<Fintype.card α) :
    (basisEmbedding (profileEmbed (A := α) ho)).conjTranspose*
      (recordRightW hT*(recordRightW hT).conjTranspose)*basisEmbedding (profileEmbed ho)=
      ((Fintype.card α : ℝ)/((Fintype.card α : ℝ)-l-r)) •
        ((wordEmbedding (A := α) l (r+1)).conjTranspose*
          (distinctProjection*(∑ j : Fin (r+1),slotBell (A := α) (J := Fin l⊕Fin (r+1)) (Sum.inr j))*distinctProjection)*
          wordEmbedding l (r+1)) := by
  have hh := actual_right_domain hT hi ho hsize
  rw [basisEmbedding_compression] at hh
  have he := congrArg (fun M => M.submatrix (rightProfileEquiv (α := α) l (r+1)).symm
    (rightProfileEquiv l (r+1)).symm) hh
  dsimp only at he
  simp only [Matrix.submatrix_smul,Pi.smul_apply] at he
  rw [sectorWord_compression_reindex] at he
  rw [basisEmbedding_compression]
  exact he

end
end ICO.MHWProfileRight

import ICO.MHFockPublicRotation

/-! An explicit unitary witness for the private-record factor of Q. -/
namespace ICO.MHFockRecordUnitary
open QIT ICO.MHFockPublicRotation ICO.MHFockKnownOperation ICO.MHFockRotation
  ICO.MHBoundedRecording ICO.MHSymmetric ICO.MHSectorCovariance
  ICO.MHCreationCovariance ICO.MHRightCovariance
open scoped Matrix
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def privateUnitary (C D : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    Matrix.unitaryGroup (Records (α := α) T) ℂ :=
  blockUnitary (fun s : Lengths T => tensorUnitary
    (symmetricRotation (leftEdgeUnitary C D) s.val.1.val)
    (symmetricRotation (rightEdgeUnitary D⁻¹ C⁻¹) s.val.2.val))

theorem privateUnitary_coe (C D : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    (privateUnitary C D T : CMatrix (Records (α := α) T))=recordRotation C D T := rfl

theorem recordRotation_gram (C D : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    (recordRotation C D T).conjTranspose*recordRotation C D T=1 :=
  Matrix.mem_unitaryGroup_iff'.mp (privateUnitary C D T).property

#print axioms recordRotation_gram
end
end ICO.MHFockRecordUnitary

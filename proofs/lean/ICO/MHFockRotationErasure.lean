import ICO.MHFockRecordUnitary
import ICO.MHDecompressionErasure
import QIT.States.Schatten

/-! The actual record rotation is invisible to the accessible query and
memory, for arbitrary vectors and density matrices. -/
namespace ICO.MHFockRotationErasure
open Matrix QIT ICO.MHFockRecordUnitary ICO.MHFockPublicRotation ICO.MHFockRotation
  ICO.MHFockKnownOperation ICO.MHDecompressionErasure ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 512
variable {α μ : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype μ] [DecidableEq μ]

theorem rotation_visible (C D : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (v : InputCutoff (α := α) T×μ→ℂ) :
    fockVisible T (Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T))
      (1 : CMatrix μ)*ᵥv)=fockVisible T v := by
  rw [fockVisible,rotation_tensor,Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id]
  exact private_erasure (recordRotation C D T) _
    (by simp only [recordRotation_gram,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.one_mulVec])

def visibleMatrix (T : ℕ) (ρ : CMatrix (InputCutoff (α := α) T×μ)) : CMatrix (α×μ) :=
  partialTraceB (ρ.submatrix (queryMemoryFirst T μ).symm (queryMemoryFirst T μ).symm)

theorem visible_rankOne (T : ℕ) (v : InputCutoff (α := α) T×μ→ℂ) :
    visibleMatrix T (rankOneMatrix v)=fockVisible T v := rfl

theorem rotation_visibleMatrix (C D : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (ρ : CMatrix (InputCutoff (α := α) T×μ)) :
    visibleMatrix T (Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T))
      (1 : CMatrix μ)*ρ*
      (Matrix.kronecker (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ)).conjTranspose)=
        visibleMatrix T ρ := by
  rw [visibleMatrix,rotation_tensor]
  simp only [Matrix.conjTranspose_submatrix]
  rw [←Matrix.submatrix_mul_equiv _ _ _ (queryMemoryFirst T μ).symm,
    ←Matrix.submatrix_mul_equiv _ _ _ (queryMemoryFirst T μ).symm]
  simp only [Matrix.submatrix_submatrix,Equiv.self_comp_symm,Matrix.submatrix_id_id]
  have hh := partialTraceB_right_unitary_conj
    (ρ.submatrix (queryMemoryFirst T μ).symm (queryMemoryFirst T μ).symm)
    (privateUnitary C D T)⁻¹
  simpa only [Matrix.UnitaryGroup.inv_val,Matrix.star_eq_conjTranspose,
    privateUnitary_coe,Matrix.kronecker,Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one,Matrix.conjTranspose_conjTranspose] using hh

theorem reindex_apply {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a≃b) (ρ : CMatrix a) :
    (Channel.reindex e).map ρ=ρ.submatrix e.symm e.symm := by
  simp only [Channel.reindex,MatrixMap.ofReferenceIsometry_apply]
  have he : (ReferenceIsometry.ofEquiv e).matrix=(1 : CMatrix a).submatrix e.symm (Equiv.refl a) := by
    ext i j
    have hh : e.symm i=j ↔ i=e j := by
      constructor
      · intro h; simpa only [e.apply_symm_apply] using congrArg e h
      · intro h; simpa only [e.symm_apply_apply] using congrArg e.symm h
    simp only [ReferenceIsometry.ofEquiv,Matrix.submatrix_apply,Matrix.one_apply,
      Equiv.refl_apply,hh]
  rw [he,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_one,
    Matrix.one_submatrix_mul,Matrix.mul_submatrix_one]
  rfl

def visibleChannel (T : ℕ) : Channel (InputCutoff (α := α) T×μ) (α×μ) :=
  (Channel.traceOutRight (α×μ) (Records (α := α) T)).comp
    (Channel.reindex (queryMemoryFirst T μ))

theorem visibleChannel_apply (T : ℕ) (ρ : CMatrix (InputCutoff (α := α) T×μ)) :
    (visibleChannel T).map ρ=visibleMatrix T ρ := by
  change partialTraceB ((Channel.reindex (queryMemoryFirst T μ)).map ρ)=_
  rw [reindex_apply]
  rfl

theorem visibleChannel_TNI (T : ℕ) :
    MatrixMap.TraceNonincreasingCP (visibleChannel (α := α) (μ := μ) T).map :=
  MatrixMap.traceNonincreasingCP_of_tracePreserving
    (visibleChannel T).completelyPositive (visibleChannel T).tracePreserving

#print axioms rotation_visible
#print axioms rotation_visibleMatrix
#print axioms visibleChannel_TNI
end
end ICO.MHFockRotationErasure

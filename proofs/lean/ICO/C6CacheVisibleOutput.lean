import ICO.C6CacheVisibleGraded

/-! The physical query-choice-memory ordering after literal cache erasure. -/
namespace ICO.C6CacheVisibleOutput
open QIT Matrix ICO.C6GradedCache ICO.C6CacheVisible ICO.C6CacheVisibleGraded
open scoped Matrix
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
universe u
variable {A M N : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

def output (Q : ℕ) : Channel (Graded (A := A) Q (Bool×M)) ((A×Bool)×M) :=
  (ICO.C6ReindexChannel.channel (Equiv.prodAssoc A Bool M)).comp (visible Q)

theorem output_apply (Q : ℕ) (X : CMatrix (Graded (A := A) Q (Bool×M))) :
    (output Q).map X = ((visible Q).map X).submatrix
      (Equiv.prodAssoc A Bool M) (Equiv.prodAssoc A Bool M) := by
  simp only [output, Channel.comp, LinearMap.comp_apply, ICO.C6ReindexChannel.apply]

def grouped (K : Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ) :
    Matrix (A×(Bool×N)) (A×(Bool×M)) ℂ :=
  K.submatrix (Equiv.prodAssoc A Bool N).symm (Equiv.prodAssoc A Bool M).symm

theorem output_known (Q : ℕ) (K : Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ)
    (X : CMatrix (Graded (A := A) Q (Bool×M))) :
    (output Q).map (known Q (grouped K)*X*(known Q (grouped K)).conjTranspose) =
      K*(output Q).map X*K.conjTranspose := by
  rw [output_apply, visible_known, output_apply]
  rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc A Bool M),
    ← Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc A Bool M)]
  simp only [grouped, Matrix.conjTranspose_submatrix, Matrix.submatrix_submatrix,
    Function.comp_def, Equiv.symm_apply_apply]
  rfl

#print axioms output
#print axioms output_known
end
end ICO.C6CacheVisibleOutput

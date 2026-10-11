import ICO.MHDecompressionKnown
import ICO.MHFockDecompressionDefect
import ICO.MHFockRotationSwap

/-! Physical query rotations commute with the actual record decompression. -/
namespace ICO.MHDecompressionRotation
open Matrix QIT ICO.MHDecompressionKnown ICO.MHFockDecompression ICO.MHFockDecompressionDefect
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockKnownOperation ICO.MHFockRotation
  ICO.MHFockRotationSwap ICO.MHTernaryCompression ICO.MHRectangularAction
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A μ : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype μ] [DecidableEq μ]

theorem fockQuery_tensor (C : Matrix.unitaryGroup A ℂ) (T : ℕ) :
    (fockQuery C T : CMatrix (InputCutoff (α := A) T))=
      (Matrix.kronecker (C : CMatrix A) (1 : CMatrix (Records (α := A) T))).submatrix
        (queryRecordEquiv T) (queryRecordEquiv T) := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  by_cases hs : s=s'
  · subst s'
    rw [fockQuery_entry_same]
    simp only [Matrix.submatrix_apply,queryRecordEquiv,records,Equiv.coe_fn_mk,
      Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Sigma.mk.inj_iff,
      heq_eq_eq,Prod.mk.injEq,true_and]
    split_ifs <;> simp_all
  · rw [fockQuery_entry_other C T _ _ hs]
    have hn : (⟨s,(p,q)⟩ : Records (α := A) T)≠⟨s',(p',q')⟩ :=
      fun he => hs (congrArg Sigma.fst he)
    simp [Matrix.submatrix_apply,queryRecordEquiv,records,Matrix.kronecker,
      Matrix.kroneckerMap_apply,Matrix.one_apply,hn]

theorem fockD_query (C : Matrix.unitaryGroup A ℂ) {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    fockD hT*(fockQuery C T : CMatrix (InputCutoff (α := A) T))=
      Matrix.kronecker (C : CMatrix A) (1 : CMatrix (Environment A))*fockD hT := by
  rw [fockD_tensor,fockQuery_tensor]
  change ((Matrix.kronecker (1 : CMatrix A) (recordFockD hT)).submatrix (Equiv.refl _) (queryRecordEquiv T))*
    (Matrix.kronecker (C : CMatrix A) (1 : CMatrix (Records (α := A) T))).submatrix (queryRecordEquiv T) (queryRecordEquiv T)=
    (Matrix.kronecker (C : CMatrix A) (1 : CMatrix (Environment A))).submatrix (Equiv.refl _) (Equiv.refl _)*
      (Matrix.kronecker (1 : CMatrix A) (recordFockD hT)).submatrix (Equiv.refl _) (queryRecordEquiv T)
  simp only [Matrix.submatrix_mul_equiv,Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]

theorem memoryD_query (C : Matrix.unitaryGroup A ℂ) {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    memoryD hT μ*Matrix.kronecker (fockQuery C T : CMatrix (InputCutoff (α := A) T)) (1 : CMatrix μ)=
      Matrix.kronecker (Matrix.kronecker (C : CMatrix A) (1 : CMatrix (Environment A))) (1 : CMatrix μ)*memoryD hT μ := by
  simp only [memoryD,Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.mul_one]
  exact congrArg (fun X => Matrix.kronecker X (1 : CMatrix μ)) (fockD_query C hT)

#print axioms fockD_query
#print axioms memoryD_query
end
end ICO.MHDecompressionRotation
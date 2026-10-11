import ICO.MHDecompressionKnown
import ICO.MHRectangularAction

/-! Decompression is invisible after erasing its private environment, on
the actual bijective-record subspace. -/
namespace ICO.MHDecompressionErasure
open Matrix QIT ICO.MHDecompressionKnown ICO.MHFockDecompression ICO.MHRectangularAction
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockKnownOperation ICO.MHWDomainProjection
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 1800000
variable {H R E : Type*} [Fintype H] [DecidableEq H] [Fintype R] [DecidableEq R]
  [Fintype E] [DecidableEq E]

def fiber (v : H×R→ℂ) (a : H) : EuclideanSpace ℂ R := WithLp.toLp 2 (fun r => v (a,r))

theorem local_mulVec_fiber (D : Matrix E R ℂ) (v : H×R→ℂ) (a : H) :
    fiber (Matrix.kronecker (1 : CMatrix H) D*ᵥv) a=rectAct D (fiber v a) := by
  ext e
  simp [fiber,rectAct,Matrix.toEuclideanLin_apply,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]

theorem partialTrace_fiber (v : H×R→ℂ) (a b : H) :
    partialTraceB (rankOneMatrix v) a b=⟪fiber v b,fiber v a⟫_ℂ := by
  simp [partialTraceB,rankOneMatrix_apply,fiber,PiLp.inner_apply,RCLike.inner_apply,mul_comm]

theorem private_erasure (D : Matrix E R ℂ) (v : H×R→ℂ)
    (hv : Matrix.kronecker (1 : CMatrix H) (D.conjTranspose*D)*ᵥv=v) :
    partialTraceB (rankOneMatrix (Matrix.kronecker (1 : CMatrix H) D*ᵥv))=
      partialTraceB (rankOneMatrix v) := by
  ext a b
  rw [partialTrace_fiber,partialTrace_fiber,local_mulVec_fiber,local_mulVec_fiber,
    rectAct_adjoint_inner,← rectAct_mul]
  have hh := congrArg (fun v => fiber v a) hv
  dsimp only at hh
  rw [local_mulVec_fiber] at hh
  rw [hh]

variable {A μ : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype μ] [DecidableEq μ]

def fockVisible (T : ℕ) (v : InputCutoff (α := A) T×μ→ℂ) : CMatrix (A×μ) :=
  partialTraceB (rankOneMatrix (v ∘ (queryMemoryFirst T μ).symm))

def physicalVisible (v : (A×ICO.MHTernaryCompression.Environment A)×μ→ℂ) : CMatrix (A×μ) :=
  partialTraceB (rankOneMatrix (v ∘ (environmentFirst μ).symm))

theorem memoryD_gram {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    (memoryD hT μ).conjTranspose*memoryD hT μ=Matrix.kronecker (bijProjection T) (1 : CMatrix μ) := by
  simp only [memoryD,Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,fockD_gram,Matrix.mul_one]

theorem memoryD_gram_tensor {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    Matrix.kronecker (bijProjection T) (1 : CMatrix μ)=
      (Matrix.kronecker (1 : CMatrix (A×μ)) ((recordFockD hT).conjTranspose*recordFockD hT)).submatrix
        (queryMemoryFirst T μ) (queryMemoryFirst T μ) := by
  rw [← memoryD_gram hT,memoryD_tensor]
  simp only [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.kronecker,
    Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,← Matrix.mul_kronecker_mul,Matrix.mul_one]

theorem decompression_visible {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (v : InputCutoff (α := A) T×μ→ℂ)
    (hv : Matrix.kronecker (bijProjection T) (1 : CMatrix μ)*ᵥv=v) :
    physicalVisible (memoryD hT μ*ᵥv)=fockVisible T v := by
  have hg : Matrix.kronecker (1 : CMatrix (A×μ)) ((recordFockD hT).conjTranspose*recordFockD hT)*ᵥ
      (v ∘ (queryMemoryFirst T μ).symm)=v ∘ (queryMemoryFirst T μ).symm := by
    rw [memoryD_gram_tensor,Matrix.submatrix_mulVec_equiv] at hv
    have hh := congrArg (fun v => v ∘ (queryMemoryFirst T μ).symm) hv
    simpa only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] using hh
  rw [physicalVisible,memoryD_tensor,Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id]
  exact private_erasure (recordFockD hT) (v ∘ (queryMemoryFirst T μ).symm) hg

#print axioms decompression_visible
end
end ICO.MHDecompressionErasure
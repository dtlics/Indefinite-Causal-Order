import ICO.MHDecompressionErasure
import ICO.MHDecompressionDefect

/-! Actual decompression is a contraction everywhere and an isometry on
bijective-record states, including entangled changing public memory. -/
namespace ICO.MHDecompressionNorm
open Matrix QIT ICO.MHDecompressionKnown ICO.MHFockDecompression ICO.MHDecompressionErasure
  ICO.MHDecompressionDefect ICO.MHRectangularAction ICO.MHWDomainProjection
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockKnownOperation
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 1400000
variable {A μ : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype μ] [DecidableEq μ]

theorem fockD_norm_le {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) : ‖fockD hT‖≤1 := by
  have hh := (bij_projection (α := A) T).norm_le
  rw [← fockD_gram hT,Matrix.l2_opNorm_conjTranspose_mul_self] at hh
  nlinarith [norm_nonneg (fockD hT)]

theorem decompression_norm {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (x : EuclideanSpace ℂ (InputCutoff (α := A) T×μ))
    (hx : rectAct (Matrix.kronecker (bijProjection T) (1 : CMatrix μ)) x=x) :
    ‖rectAct (memoryD hT μ) x‖=‖x‖ := by
  have hh := rectAct_norm_sq (memoryD hT μ) x
  rw [memoryD_gram,hx] at hh
  have hi : (⟪x,x⟫_ℂ).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hi] at hh
  nlinarith [norm_nonneg x,norm_nonneg (rectAct (memoryD hT μ) x)]

#print axioms decompression_norm
end
end ICO.MHDecompressionNorm
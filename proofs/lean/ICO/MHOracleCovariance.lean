import ICO.RecordingOracleAlgebra
import QIT.Core.State

/-! Stable norm algebra for the actual overlap-removing full oracle. -/
namespace ICO.MHOracleCovariance
open Matrix QIT
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
variable {H : Type*} [Fintype H] [DecidableEq H]

def fullOracle (A B : CMatrix H) : CMatrix H :=
  A*(1-B*B.conjTranspose)+(1-A*A.conjTranspose)*B.conjTranspose

theorem image_difference_norm_le (A A' : CMatrix H) (δ : ℝ)
    (hA : ‖A‖ ≤ 1) (hA' : ‖A'‖ ≤ 1) (hδ : ‖A-A'‖ ≤ δ) :
    ‖A*A.conjTranspose-A'*A'.conjTranspose‖ ≤ 2*δ := by
  have he : A*A.conjTranspose-A'*A'.conjTranspose =
      (A-A')*A.conjTranspose+A'*(A.conjTranspose-A'.conjTranspose) := by noncomm_ring
  have hd : ‖A.conjTranspose-A'.conjTranspose‖ = ‖A-A'‖ := by
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  rw [he]
  have hh := (norm_add_le ((A-A')*A.conjTranspose)
    (A'*(A.conjTranspose-A'.conjTranspose))).trans
      (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  rw [Matrix.l2_opNorm_conjTranspose, hd] at hh
  have h1 := mul_le_mul_of_nonneg_left hA (norm_nonneg (A-A'))
  have h2 := mul_le_mul_of_nonneg_right hA' (norm_nonneg (A-A'))
  nlinarith

theorem fullOracle_difference_norm_le (A B A' B' : CMatrix H) (δ : ℝ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hA' : ‖A'‖ ≤ 1) (hB' : ‖B'‖ ≤ 1)
    (hQA : IsStarProjection (A*A.conjTranspose))
    (hQB : IsStarProjection (B*B.conjTranspose))
    (hδA : ‖A-A'‖ ≤ δ) (hδB : ‖B-B'‖ ≤ δ) :
    ‖fullOracle A B-fullOracle A' B'‖ ≤ 6*δ := by
  have hPA := hQA.one_sub.norm_le
  have hPB := hQB.one_sub.norm_le
  have hDQA := image_difference_norm_le A A' δ hA hA' hδA
  have hDQB := image_difference_norm_le B B' δ hB hB' hδB
  have hdB : ‖B.conjTranspose-B'.conjTranspose‖ = ‖B-B'‖ := by
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  have he : fullOracle A B-fullOracle A' B' =
      (A-A')*(1-B*B.conjTranspose)+A'*(B'*B'.conjTranspose-B*B.conjTranspose)+
      (1-A*A.conjTranspose)*(B.conjTranspose-B'.conjTranspose)+
      (A'*A'.conjTranspose-A*A.conjTranspose)*B'.conjTranspose := by
    unfold fullOracle
    noncomm_ring
  have h1 : ‖(A-A')*(1-B*B.conjTranspose)‖ ≤ δ := by
    have hh := norm_mul_le (A-A') (1-B*B.conjTranspose)
    have hp := mul_le_mul_of_nonneg_left hPB (norm_nonneg (A-A'))
    nlinarith
  have h2 : ‖A'*(B'*B'.conjTranspose-B*B.conjTranspose)‖ ≤ 2*δ := by
    have hh := norm_mul_le A' (B'*B'.conjTranspose-B*B.conjTranspose)
    rw [norm_sub_rev (B'*B'.conjTranspose) (B*B.conjTranspose)] at hh
    have hp := mul_le_mul_of_nonneg_right hA'
      (norm_nonneg (B*B.conjTranspose-B'*B'.conjTranspose))
    nlinarith
  have h3 : ‖(1-A*A.conjTranspose)*(B.conjTranspose-B'.conjTranspose)‖ ≤ δ := by
    have hh := norm_mul_le (1-A*A.conjTranspose) (B.conjTranspose-B'.conjTranspose)
    rw [hdB] at hh
    have hp := mul_le_mul_of_nonneg_right hPA (norm_nonneg (B-B'))
    nlinarith
  have h4 : ‖(A'*A'.conjTranspose-A*A.conjTranspose)*B'.conjTranspose‖ ≤ 2*δ := by
    have hh := norm_mul_le (A'*A'.conjTranspose-A*A.conjTranspose) B'.conjTranspose
    rw [norm_sub_rev (A'*A'.conjTranspose) (A*A.conjTranspose),
      Matrix.l2_opNorm_conjTranspose] at hh
    have hp := mul_le_mul_of_nonneg_left hB'
      (norm_nonneg (A*A.conjTranspose-A'*A'.conjTranspose))
    nlinarith
  rw [he]
  exact (norm_add_le _ _).trans (by
    have hh := norm_add_le
      ((A-A')*(1-B*B.conjTranspose)+A'*(B'*B'.conjTranspose-B*B.conjTranspose))
      ((1-A*A.conjTranspose)*(B.conjTranspose-B'.conjTranspose))
    have hg := norm_add_le ((A-A')*(1-B*B.conjTranspose))
      (A'*(B'*B'.conjTranspose-B*B.conjTranspose))
    linarith)

#print axioms fullOracle_difference_norm_le
end
end ICO.MHOracleCovariance

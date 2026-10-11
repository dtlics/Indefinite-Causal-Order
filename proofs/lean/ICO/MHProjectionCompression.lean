import ICO.CausalReverse
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic

/-! Near-commuting projection compression, used in the Ma--Huang relation
projector comparison. This is an actual matrix inequality; a concrete Bell
collision bound must supply the commutator estimate. -/

namespace ICO.MHProjectionCompression
open Matrix QIT ICO.CausalReverse
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 0
local instance matrixNonUnitalCStar (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance matrixCStar (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩
variable {H : Type*} [Fintype H] [DecidableEq H]

theorem projection_sandwich_le (A B : CMatrix H)
    (hA : IsStarProjection A) (hB : IsStarProjection B) : B * A * B ≤ B := by
  have ha := projection_le_one hA.isSelfAdjoint.star_eq hA.isIdempotentElem.eq
  rw [Matrix.le_iff] at ha ⊢
  have hp := ha.mul_mul_conjTranspose_same B
  have hBc : B.conjTranspose = B := hB.isSelfAdjoint.star_eq
  simpa only [hBc, Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_mul, hB.isIdempotentElem.eq] using hp

theorem sandwich_difference_norm_le (A B : CMatrix H)
    (hA : IsStarProjection A) (hB : IsStarProjection B) :
    ‖A * B * A - B * A * B‖ ≤ 2 * ‖A * B - B * A‖ := by
  have he : A * B * A - B * A * B =
      (A * B) * (B * A - A * B) + (A * B - B * A) * (A * B) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc A B B, hB.isIdempotentElem.eq,
      Matrix.mul_assoc B A A, hA.isIdempotentElem.eq]
    noncomm_ring
  have hab : ‖A * B‖ ≤ 1 := (norm_mul_le A B).trans
    (by nlinarith [hA.norm_le, hB.norm_le, norm_nonneg A, norm_nonneg B])
  rw [he]
  have hh := (norm_add_le ((A * B) * (B * A - A * B))
    ((A * B - B * A) * (A * B))).trans
      (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  rw [norm_sub_rev (B * A) (A * B)] at hh
  have h1 := mul_le_mul_of_nonneg_right hab (norm_nonneg (A * B - B * A))
  have h2 := mul_le_mul_of_nonneg_left hab (norm_nonneg (A * B - B * A))
  nlinarith

theorem near_commuting_compression_le (A B : CMatrix H)
    (hA : IsStarProjection A) (hB : IsStarProjection B) :
    A * B * A ≤ B + (2 * ‖A * B - B * A‖ : ℝ) • (1 : CMatrix H) := by
  have hd : IsSelfAdjoint (A * B * A - B * A * B) := by
    show star (A * B * A - B * A * B) = _
    simp only [star_sub, star_mul, hA.isSelfAdjoint.star_eq,
      hB.isSelfAdjoint.star_eq, Matrix.mul_assoc]
  have hh := hd.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one] at hh
  have hs : ‖A * B * A - B * A * B‖ • (1 : CMatrix H) ≤
      (2 * ‖A * B - B * A‖ : ℝ) • (1 : CMatrix H) :=
    smul_le_smul_of_nonneg_right (sandwich_difference_norm_le A B hA hB)
      Matrix.PosSemidef.one.nonneg
  have hb := projection_sandwich_le A B hA hB
  have hx := sub_le_iff_le_add.mp (hh.trans hs)
  simpa only [add_comm] using hx.trans (add_le_add le_rfl hb)

theorem compression_le_of_commutator_le (A B : CMatrix H)
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (δ : ℝ) (hδ : ‖A * B - B * A‖ ≤ δ) :
    A * B * A ≤ B + (2 * δ : ℝ) • (1 : CMatrix H) := by
  apply (near_commuting_compression_le A B hA hB).trans
  apply add_le_add le_rfl
  exact smul_le_smul_of_nonneg_right (by linarith : 2 * ‖A * B - B * A‖ ≤ 2 * δ)
    Matrix.PosSemidef.one.nonneg

#print axioms near_commuting_compression_le
end
end ICO.MHProjectionCompression

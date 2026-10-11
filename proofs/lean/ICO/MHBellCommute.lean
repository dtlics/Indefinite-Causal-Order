import ICO.GramNorm
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-! Bell collision commutators. The nilpotent off-diagonal identity keeps
the exact constant one, rather than losing a factor two by the triangle
inequality. The concrete record projector and Bell columns follow below. -/
namespace ICO.MHBellCommute
open Matrix QIT
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators
noncomputable section
set_option maxHeartbeats 0
local instance bellNonUnitalCStar (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance bellCStar (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩
variable {H : Type*} [Fintype H] [DecidableEq H]

theorem nilpotent_skew_norm (T : CMatrix H) (hT : T * T = 0) :
    ‖T - T.conjTranspose‖ = ‖T‖ := by
  have ha : IsSelfAdjoint (T.conjTranspose * T) := by
    change (T.conjTranspose * T).conjTranspose = _
    simp
  have hb : IsSelfAdjoint (T * T.conjTranspose) := by
    change (T * T.conjTranspose).conjTranspose = _
    simp
  have hab : (T.conjTranspose * T) * (T * T.conjTranspose) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc T T, hT]
    simp
  have hprod : (T - T.conjTranspose).conjTranspose * (T - T.conjTranspose) =
      T.conjTranspose * T + T * T.conjTranspose := by
    have hstar : T.conjTranspose * T.conjTranspose = 0 := by
      simpa using congrArg Matrix.conjTranspose hT
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, hT, hstar]
    abel
  have hh := ha.norm_add_eq_max hb hab
  have hbNorm : ‖T * T.conjTranspose‖ = ‖T‖ * ‖T‖ := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose]
      using Matrix.l2_opNorm_conjTranspose_mul_self T.conjTranspose
  rw [← hprod, Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.l2_opNorm_conjTranspose_mul_self, hbNorm] at hh
  simp only [max_self] at hh
  nlinarith [norm_nonneg (T - T.conjTranspose), norm_nonneg T]

theorem projection_commutator_norm (P B : CMatrix H)
    (hP : IsStarProjection P) (hB : IsSelfAdjoint B) :
    ‖P * B - B * P‖ = ‖(1 - P) * B * P‖ := by
  let T := (1 - P) * B * P
  have hT : T * T = 0 := by
    dsimp [T]
    have hp : P * (1 - P) = 0 := by
      simp [Matrix.mul_sub, hP.isIdempotentElem.eq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P (1 - P), hp]
    simp
  have hPc : P.conjTranspose = P := hP.isSelfAdjoint.star_eq
  have hBc : B.conjTranspose = B := hB.star_eq
  have he : T - T.conjTranspose = B * P - P * B := by
    dsimp [T]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPc, hBc, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    noncomm_ring
  rw [← norm_sub_rev (B * P) (P * B), ← he]
  exact nilpotent_skew_norm T hT

#print axioms projection_commutator_norm
end
end ICO.MHBellCommute

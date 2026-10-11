import ICO.PositiveSupport
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace ICO.PositiveSupport
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
local instance decompositionNonUnitalCStar (I : Type*) [Fintype I] [DecidableEq I] :
    NonUnitalCStarAlgebra (Matrix I I ℂ) := ⟨⟩
local instance decompositionCStar (I : Type*) [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) := ⟨⟩

/-- A positive matrix always has a finite rank-one decomposition. Its index
set is the matrix dimension, independent of any physical environment size. -/
theorem exists_rankOne_decomposition {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℂ) (hC : C.PosSemidef) :
    ∃ v : I → I → ℂ, C = ∑ k, rankOne (v k) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  refine ⟨fun k i => B.conjTranspose i k, ?_⟩
  calc
    C = B.conjTranspose * B := hB
    _ = B.conjTranspose * B.conjTranspose.conjTranspose := by rw [Matrix.conjTranspose_conjTranspose]
    _ = _ := by
      ext i j
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
        rankOne, Matrix.vecMulVec_apply]

theorem sum_rankOne_pos {I K : Type*} [Fintype I] [Fintype K] (v : K → I → ℂ) :
    (∑ k, rankOne (v k)).PosSemidef := by
  let W : Matrix I K ℂ := fun i k => v k i
  have h : (∑ k, rankOne (v k)) = W * Wᴴ := by
    ext i j
    simp [W, rankOne, Matrix.vecMulVec_apply, Matrix.sum_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose W

#print axioms exists_rankOne_decomposition
end
end ICO.PositiveSupport

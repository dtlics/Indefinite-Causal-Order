import ICO.ChoiMass
import ICO.PositiveCoherence

/-! # Actual retained-control coherence and branch mass

The two populations and their coherence are entries of the same physical Choi
matrix. No classical decomposition of that output control is assumed.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.CausalReverse ICO.CircuitOutput ICO.ControlOutcomeReverse

namespace ICO.ControlCoherence

set_option maxHeartbeats 300000
noncomputable section

universe u
variable {A M Z N : Type u}
variable [Fintype A] [Fintype M] [Fintype Z] [Fintype N]
variable [DecidableEq A] [DecidableEq M] [DecidableEq Z] [DecidableEq N]

theorem tracePair_rankOne_eq_quadratic (C : CMatrix N) (v : N → ℂ) :
    tracePair C (rankOneMatrix v) = (star v ⬝ᵥ (C *ᵥ v)).re := by
  unfold tracePair
  apply congrArg Complex.re
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    rankOneMatrix_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, mul_left_comm, mul_comm]

def controlVector (v : N → ℂ) (z : Z) : N × Z → ℂ :=
  fun iz => if iz.2 = z then v iz.1 else 0

theorem controlVector_trace (v : N → ℂ) (z : Z) :
    (rankOneMatrix (controlVector v z)).trace = (rankOneMatrix v).trace := by
  simp [Matrix.trace, Matrix.diag_apply, rankOneMatrix_apply, controlVector,
    Fintype.sum_prod_type]

theorem controlVector_quadratic (C : CMatrix (N × Z)) (v : N → ℂ) (z : Z) :
    star (controlVector v z) ⬝ᵥ (C *ᵥ controlVector v z) =
      star v ⬝ᵥ ((C.submatrix (fun i => (i, z)) (fun i => (i, z))) *ᵥ v) := by
  simp [controlVector, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.mul_sum, Matrix.submatrix, apply_ite, ite_mul, mul_ite]

def groupedChoi (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) :
    CMatrix ((A × A) × Z) :=
  (MatrixMap.choi (fullBranchMap R pre U V)).submatrix
    (fun i => (i.1.1, (i.1.2, i.2))) (fun i => (i.1.1, (i.1.2, i.2)))

theorem groupedChoi_pos (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) :
    (groupedChoi R pre U V).PosSemidef := by
  apply Matrix.PosSemidef.submatrix
  exact fullBranchMap_cp R pre U V

theorem groupedChoi_trace (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) :
    (groupedChoi R pre U V).trace = (pre.conjTranspose * pre).trace := by
  rw [← ICO.ChoiMass.fullBranchChoi_trace R pre U V]
  simp [groupedChoi, Matrix.trace, Matrix.diag_apply, Matrix.submatrix,
    Fintype.sum_prod_type]

theorem groupedChoi_controlBlock
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (z : Z) :
    (groupedChoi R pre U V).submatrix (fun i => (i, z)) (fun i => (i, z)) =
      MatrixMap.choi (selectedMap R pre (U : CMatrix A) (V : CMatrix A) z) := by
  rw [selectedChoi_eq_controlBlock]
  rfl

theorem selectedOverlap_eq_quadratic
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (z : Z)
    (T : CMatrix A) :
    selectedOverlap R pre (U : CMatrix A) (V : CMatrix A) z T =
      ((Fintype.card A : ℝ) ^ 2)⁻¹ *
        (star (controlVector (targetVector T) z) ⬝ᵥ
          (groupedChoi R pre U V *ᵥ controlVector (targetVector T) z)).re := by
  rw [controlVector_quadratic, groupedChoi_controlBlock]
  exact congrArg (((Fintype.card A : ℝ) ^ 2)⁻¹ * ·)
    (tracePair_rankOne_eq_quadratic _ _)

def controlCoherence (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ)
    (z z' : Z) (T S : CMatrix A) : ℂ :=
  ((((Fintype.card A : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) *
    (star (controlVector (targetVector T) z) ⬝ᵥ
      (groupedChoi R pre U V *ᵥ controlVector (targetVector S) z'))

theorem controlCoherence_sq_le
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ)
    (z z' : Z) (T S : CMatrix A) :
    Complex.normSq (controlCoherence R pre U V z z' T S) ≤
      selectedOverlap R pre (U : CMatrix A) (V : CMatrix A) z T *
        selectedOverlap R pre (U : CMatrix A) (V : CMatrix A) z' S := by
  have h := ICO.PositiveCoherence.coherence_sq_le (groupedChoi R pre U V)
    (groupedChoi_pos R pre U V) (controlVector (targetVector T) z)
    (controlVector (targetVector S) z')
  simp only [controlCoherence, Complex.normSq_mul, Complex.normSq_ofReal,
    selectedOverlap_eq_quadratic]
  nlinarith [mul_le_mul_of_nonneg_left h
    (sq_nonneg (((Fintype.card A : ℝ) ^ 2)⁻¹))]

theorem selectedOverlap_nonneg
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (z : Z)
    (T : CMatrix A) :
    0 ≤ selectedOverlap R pre (U : CMatrix A) (V : CMatrix A) z T := by
  rw [selectedOverlap_eq_quadratic]
  apply mul_nonneg (by positivity)
  exact ((groupedChoi_pos R pre U V).dotProduct_mulVec_nonneg _).1

theorem selectedOverlap_le_branchWeight [Nonempty A]
    (R : ICO.OneQueryTree.NormalForm (A × M) (A × M) (A × Z))
    (pre : Matrix (A × M) A ℂ) (U V : Matrix.unitaryGroup A ℂ) (z : Z)
    (T : CMatrix A) (hT : T.conjTranspose * T = 1) :
    selectedOverlap R pre (U : CMatrix A) (V : CMatrix A) z T ≤
      (pre.conjTranspose * pre).trace.re / (Fintype.card A : ℝ) := by
  have h := ICO.ChoiMass.rankOne_score_le_mass (A := A) (groupedChoi R pre U V)
    (groupedChoi_pos R pre U V) (controlVector (targetVector T) z)
    (by rw [controlVector_trace, ICO.ChoiMass.target_rankOne_trace T hT])
  rw [groupedChoi_trace, tracePair_rankOne_eq_quadratic] at h
  rw [selectedOverlap_eq_quadratic]
  exact h

end
end ICO.ControlCoherence

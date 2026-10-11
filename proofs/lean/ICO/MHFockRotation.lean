import ICO.MHSectorCovariance
import ICO.MHFockSpace

/-! Actual unitary record rotations on the common finite Fock register. -/

namespace ICO.MHFockRotation

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHSectorCovariance
  ICO.MHSymmetric ICO.MHCreationCovariance ICO.MHRightCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1500000

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def reindexUnitary (U : Matrix.unitaryGroup a ℂ) (e : b ≃ a) : Matrix.unitaryGroup b ℂ := by
  refine ⟨(U : CMatrix a).submatrix e e, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change ((U : CMatrix a).submatrix e e).conjTranspose *
    (U : CMatrix a).submatrix e e = (1 : CMatrix b)
  have hU : (U : CMatrix a).conjTranspose * (U : CMatrix a) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    hU, Matrix.submatrix_one_equiv]

def blockUnitary {k : Type*} [Fintype k] [DecidableEq k] {m : k → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (U : ∀ i, Matrix.unitaryGroup (m i) ℂ) : Matrix.unitaryGroup (Σ i, m i) ℂ := by
  refine ⟨Matrix.blockDiagonal' (fun i => (U i : CMatrix (m i))), Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change (Matrix.blockDiagonal' (fun i => (U i : CMatrix (m i)))).conjTranspose *
    Matrix.blockDiagonal' (fun i => (U i : CMatrix (m i))) = 1
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  have hU (i : k) : (U i : CMatrix (m i)).conjTranspose * (U i : CMatrix (m i)) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (U i).property
  simp only [hU]
  exact Matrix.blockDiagonal'_one

variable {α : Type*} [Fintype α] [DecidableEq α]

def sectorEquiv (t : ℕ) : InputCutoff (α := α) t ≃
    Σ s : Lengths t, Sector (α := α) s.val.1.val s.val.2.val where
  toFun v := ⟨v.1.1, (v.2, v.1.2)⟩
  invFun v := ⟨⟨v.1, v.2.2⟩, v.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fockQ (C D : Matrix.unitaryGroup α ℂ) (t : ℕ) : Matrix.unitaryGroup (InputCutoff (α := α) t) ℂ :=
  reindexUnitary (blockUnitary (fun s : Lengths t => outputTurn C D s.val.1.val s.val.2.val)) (sectorEquiv t)

def fockQuery (U : Matrix.unitaryGroup α ℂ) (t : ℕ) : Matrix.unitaryGroup (InputCutoff (α := α) t) ℂ :=
  reindexUnitary (blockUnitary (fun s : Lengths t => queryTurn U s.val.1.val s.val.2.val)) (sectorEquiv t)

theorem fockQ_entry_same (C D : Matrix.unitaryGroup α ℂ) (t : ℕ) (s : Lengths t)
    (q q' : TensorPowerProfile (α × α) s.val.2.val)
    (p p' : TensorPowerProfile (α × α) s.val.1.val) (x y : α) :
    (fockQ C D t : CMatrix (InputCutoff (α := α) t)) ⟨⟨s, q⟩, (x, p)⟩ ⟨⟨s, q'⟩, (y, p')⟩ =
      (if x = y then 1 else 0) *
        occupationRotation (leftEdgeUnitary C D) s.val.1.val p p' *
          occupationRotation (rightEdgeUnitary D⁻¹ C⁻¹) s.val.2.val q q' := by
  simp [fockQ, reindexUnitary, blockUnitary, sectorEquiv, Matrix.submatrix_apply,
    Matrix.blockDiagonal'_apply_eq, outputTurn, tensorUnitary, symmetricRotation,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem fockQ_entry_other (C D : Matrix.unitaryGroup α ℂ) (t : ℕ)
    (v w : InputCutoff (α := α) t) (h : v.1.1 ≠ w.1.1) :
    (fockQ C D t : CMatrix (InputCutoff (α := α) t)) v w = 0 := by
  simp [fockQ, reindexUnitary, blockUnitary, sectorEquiv, Matrix.submatrix_apply,
    Matrix.blockDiagonal'_apply, h]

end
end ICO.MHFockRotation

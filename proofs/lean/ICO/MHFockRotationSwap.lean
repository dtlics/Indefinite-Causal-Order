import ICO.MHSymbolTranspose
import ICO.MHFockCovariance
import ICO.MHFockOracle

/-! Record transposition identifies the forward and inverse global record
rotations on the same finite Fock space. -/

namespace ICO.MHFockRotationSwap

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockRotation
  ICO.MHFockTransport ICO.MHFockCovariance ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHProfileTranspose ICO.MHSymbolTranspose ICO.MHSymmetric
  ICO.MHCreationCovariance ICO.MHRightCovariance ICO.MHSectorCovariance
  ICO.RecordingCopyIdentity
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2500000

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem lengthSwap_injective (T : ℕ) : Function.Injective (lengthSwap (t := T)) := by
  intro s r he
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : Lengths T => z.val.2) he)
    (congrArg (fun z : Lengths T => z.val.1) he)

theorem left_right_edge_transpose (C D : Matrix.unitaryGroup α ℂ) (i j : α × α) :
    (leftEdgeUnitary D⁻¹ C⁻¹ : CMatrix (α × α)) i j =
      (rightEdgeUnitary D⁻¹ C⁻¹ : CMatrix (α × α)) i.swap j.swap := by
  simp [leftEdgeUnitary, rightEdgeUnitary, Matrix.kronecker, Matrix.kroneckerMap_apply, mul_comm]

theorem right_left_edge_transpose (C D : Matrix.unitaryGroup α ℂ) (i j : α × α) :
    (rightEdgeUnitary C D : CMatrix (α × α)) i j =
      (leftEdgeUnitary C D : CMatrix (α × α)) i.swap j.swap := by
  simp [leftEdgeUnitary, rightEdgeUnitary, Matrix.kronecker, Matrix.kroneckerMap_apply, mul_comm]

theorem fockQ_swap_entry (C D : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (o i : InputCutoff (α := α) T) :
    (fockQ C D T : CMatrix (InputCutoff (α := α) T)) (recordSwap o) (recordSwap i) =
      (fockQ D⁻¹ C⁻¹ T : CMatrix (InputCutoff (α := α) T)) o i := by
  rcases o with ⟨⟨s,q⟩,x,p⟩
  rcases i with ⟨⟨s',q'⟩,y,p'⟩
  by_cases hs : s = s'
  · subst s'
    rw [show recordSwap ⟨⟨s,q⟩,(x,p)⟩ = ⟨⟨lengthSwap s,profileTranspose _ p⟩,(x,profileTranspose _ q)⟩ from rfl]
    rw [show recordSwap ⟨⟨s,q'⟩,(y,p')⟩ = ⟨⟨lengthSwap s,profileTranspose _ p'⟩,(y,profileTranspose _ q')⟩ from rfl]
    rw [fockQ_entry_same, fockQ_entry_same]
    simp only [inv_inv]
    rw [← occupationRotation_transpose (rightEdgeUnitary D⁻¹ C⁻¹) (leftEdgeUnitary D⁻¹ C⁻¹)
      (left_right_edge_transpose C D)]
    rw [← occupationRotation_transpose (leftEdgeUnitary C D) (rightEdgeUnitary C D)
      (right_left_edge_transpose C D)]
    dsimp only [lengthSwap]
    ring
  · rw [fockQ_entry_other C D T _ _ (fun he => hs (lengthSwap_injective T he)),
      fockQ_entry_other D⁻¹ C⁻¹ T _ _ hs]

theorem swap_fockQ (C D : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    swapMatrix T * (fockQ C D T : CMatrix (InputCutoff (α := α) T)) * swapMatrix T =
      (fockQ D⁻¹ C⁻¹ T : CMatrix (InputCutoff (α := α) T)) := by
  calc
    _ = (basisEmbedding (recordSwapEquiv (α := α) T)).conjTranspose *
        (fockQ C D T : CMatrix (InputCutoff (α := α) T)) * basisEmbedding (recordSwapEquiv (α := α) T) := by
      change swapMatrix T * _ * swapMatrix T = (swapMatrix T).conjTranspose * _ * swapMatrix T
      rw [swapMatrix_selfAdjoint]
    _ = _ := by
      rw [basisEmbedding_compression]
      ext o i
      exact fockQ_swap_entry C D T o i

theorem fockQuery_entry_same (U : Matrix.unitaryGroup α ℂ) (T : ℕ) (s : Lengths T)
    (q q' : TensorPowerProfile (α × α) s.val.2.val)
    (p p' : TensorPowerProfile (α × α) s.val.1.val) (x y : α) :
    (fockQuery U T : CMatrix (InputCutoff (α := α) T)) ⟨⟨s,q⟩,(x,p)⟩ ⟨⟨s,q'⟩,(y,p')⟩ =
      (U : CMatrix α) x y * (if p=p' then 1 else 0) * (if q=q' then 1 else 0) := by
  simp [fockQuery, reindexUnitary, blockUnitary, sectorEquiv,
    queryTurn, tensorUnitary, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem fockQuery_entry_other (U : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (o i : InputCutoff (α := α) T) (h : o.1.1 ≠ i.1.1) :
    (fockQuery U T : CMatrix (InputCutoff (α := α) T)) o i = 0 :=
  inputFamily_other (fun n r => (queryTurn U n r : CMatrix (Sector (α := α) n r))) T o i h

theorem fockQuery_swap_entry (U : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (o i : InputCutoff (α := α) T) :
    (fockQuery U T : CMatrix (InputCutoff (α := α) T)) (recordSwap o) (recordSwap i) =
      (fockQuery U T : CMatrix (InputCutoff (α := α) T)) o i := by
  rcases o with ⟨⟨s,q⟩,x,p⟩
  rcases i with ⟨⟨s',q'⟩,y,p'⟩
  by_cases hs : s = s'
  · subst s'
    change (fockQuery U T : CMatrix (InputCutoff (α := α) T)) ⟨⟨lengthSwap s,profileTranspose _ p⟩,(x,profileTranspose _ q)⟩
      ⟨⟨lengthSwap s,profileTranspose _ p'⟩,(y,profileTranspose _ q')⟩ = _
    rw [fockQuery_entry_same, fockQuery_entry_same]
    change ((U : CMatrix α) x y *
      (if profileTranspose s.val.2.val q = profileTranspose s.val.2.val q' then 1 else 0)) *
      (if profileTranspose s.val.1.val p = profileTranspose s.val.1.val p' then 1 else 0) = _
    simp only [(profileTranspose s.val.1.val).injective.eq_iff,
      (profileTranspose s.val.2.val).injective.eq_iff]
    ring
  · rw [fockQuery_entry_other U T _ _ (fun he => hs (lengthSwap_injective T he)),
      fockQuery_entry_other U T _ _ hs]

theorem swap_fockQuery (U : Matrix.unitaryGroup α ℂ) (T : ℕ) :
    swapMatrix T * (fockQuery U T : CMatrix (InputCutoff (α := α) T)) * swapMatrix T =
      (fockQuery U T : CMatrix (InputCutoff (α := α) T)) := by
  calc
    _ = (basisEmbedding (recordSwapEquiv (α := α) T)).conjTranspose *
        (fockQuery U T : CMatrix (InputCutoff (α := α) T)) * basisEmbedding (recordSwapEquiv (α := α) T) := by
      change swapMatrix T * _ * swapMatrix T = (swapMatrix T).conjTranspose * _ * swapMatrix T
      rw [swapMatrix_selfAdjoint]
    _ = _ := by
      rw [basisEmbedding_compression]
      ext o i
      exact fockQuery_swap_entry U T o i

end
end ICO.MHFockRotationSwap

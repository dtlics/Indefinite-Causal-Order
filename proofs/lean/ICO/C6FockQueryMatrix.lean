import ICO.C6PolarFockCovariance

/-! General query matrices and length masks on the common record space. -/
namespace ICO.C6FockQueryMatrix
open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockRotation
  ICO.MHFockTransport ICO.MHFockCovariance ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHFockRotationSwap ICO.MHProfileTranspose ICO.MHSectorCovariance
  ICO.RecordingCopyIdentity
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
variable {α:Type*} [Fintype α] [DecidableEq α]

def queryFamily (P:CMatrix α) (n r:ℕ) : CMatrix (Sector (α:=α) n r) :=
  Matrix.kronecker (Matrix.kronecker P (1:CMatrix (TensorPowerProfile (α×α) n)))
    (1:CMatrix (TensorPowerProfile (α×α) r))

def queryMatrix (P:CMatrix α) (T:ℕ) : CMatrix (InputCutoff (α:=α) T) :=
  inputFamily (queryFamily P) T

def leftLengthMask (m T:ℕ) : CMatrix (InputCutoff (α:=α) T) :=
  inputFamily (fun n _r => if n≤m then 1 else 0) T

def rightLengthMask (m T:ℕ) : CMatrix (InputCutoff (α:=α) T) :=
  swapMatrix T*leftLengthMask m T*swapMatrix T

theorem queryMatrix_entry_same (P:CMatrix α) (T:ℕ) (s:Lengths T)
    (q q':TensorPowerProfile (α×α) s.val.2.val)
    (p p':TensorPowerProfile (α×α) s.val.1.val) (x y:α) :
    queryMatrix P T ⟨⟨s,q⟩,(x,p)⟩ ⟨⟨s,q'⟩,(y,p')⟩=
      P x y*(if p=p' then 1 else 0)*(if q=q' then 1 else 0) := by
  simp [queryMatrix,inputFamily,sectorEquiv,queryFamily,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]

theorem queryMatrix_entry_other (P:CMatrix α) (T:ℕ)
    (o i:InputCutoff (α:=α) T) (h:o.1.1≠i.1.1) : queryMatrix P T o i=0 :=
  inputFamily_other (queryFamily P) T o i h
theorem queryMatrix_swap_entry (U : CMatrix α) (T : ℕ)
    (o i : InputCutoff (α := α) T) :
    (queryMatrix U T : CMatrix (InputCutoff (α := α) T)) (recordSwap o) (recordSwap i) =
      (queryMatrix U T : CMatrix (InputCutoff (α := α) T)) o i := by
  rcases o with ⟨⟨s,q⟩,x,p⟩
  rcases i with ⟨⟨s',q'⟩,y,p'⟩
  by_cases hs : s = s'
  · subst s'
    change (queryMatrix U T : CMatrix (InputCutoff (α := α) T)) ⟨⟨lengthSwap s,profileTranspose _ p⟩,(x,profileTranspose _ q)⟩
      ⟨⟨lengthSwap s,profileTranspose _ p'⟩,(y,profileTranspose _ q')⟩ = _
    rw [queryMatrix_entry_same, queryMatrix_entry_same]
    change (U x y *
      (if profileTranspose s.val.2.val q = profileTranspose s.val.2.val q' then 1 else 0)) *
      (if profileTranspose s.val.1.val p = profileTranspose s.val.1.val p' then 1 else 0) = _
    simp only [(profileTranspose s.val.1.val).injective.eq_iff,
      (profileTranspose s.val.2.val).injective.eq_iff]
    ring
  · rw [queryMatrix_entry_other U T _ _ (fun he => hs (lengthSwap_injective T he)),
      queryMatrix_entry_other U T _ _ hs]

theorem swap_queryMatrix (U : CMatrix α) (T : ℕ) :
    swapMatrix T * (queryMatrix U T : CMatrix (InputCutoff (α := α) T)) * swapMatrix T =
      (queryMatrix U T : CMatrix (InputCutoff (α := α) T)) := by
  calc
    _ = (basisEmbedding (recordSwapEquiv (α := α) T)).conjTranspose *
        (queryMatrix U T : CMatrix (InputCutoff (α := α) T)) * basisEmbedding (recordSwapEquiv (α := α) T) := by
      change swapMatrix T * _ * swapMatrix T = (swapMatrix T).conjTranspose * _ * swapMatrix T
      rw [swapMatrix_selfAdjoint]
    _ = _ := by
      rw [basisEmbedding_compression]
      ext o i
      exact queryMatrix_swap_entry U T o i

theorem leftLengthMask_diagonal (m T:ℕ) :
    leftLengthMask (α:=α) m T=Matrix.diagonal (fun i:InputCutoff (α:=α) T =>
      if i.1.1.val.1.val≤m then (1:ℂ) else 0) := by
  ext ⟨⟨s,q⟩,p⟩ ⟨⟨s',q'⟩,p'⟩
  by_cases hs:s=s'
  · subst s'
    rw [leftLengthMask,inputFamily_same]
    by_cases hm:s.val.1.val≤m <;>
      simp [hm,Matrix.diagonal_apply,Matrix.one_apply,and_comm]
  · have hi : (⟨⟨s,q⟩,p⟩:InputCutoff (α:=α) T)≠⟨⟨s',q'⟩,p'⟩ := by
      intro he
      exact hs (congrArg (fun v:InputCutoff (α:=α) T => v.1.1) he)
    rw [leftLengthMask,inputFamily_other _ T _ _ hs]
    simp [Matrix.diagonal_apply,hi]

theorem rightLengthMask_diagonal (m T:ℕ) :
    rightLengthMask (α:=α) m T=Matrix.diagonal (fun i:InputCutoff (α:=α) T =>
      if i.1.1.val.2.val≤m then (1:ℂ) else 0) := by
  unfold rightLengthMask
  calc
    _ = (basisEmbedding (recordSwapEquiv (α:=α) T)).conjTranspose*
        leftLengthMask m T*basisEmbedding (recordSwapEquiv (α:=α) T) := by
      change swapMatrix T*_ *swapMatrix T=(swapMatrix T).conjTranspose*_ *swapMatrix T
      rw [swapMatrix_selfAdjoint]
    _ = _ := by
      rw [basisEmbedding_compression,leftLengthMask_diagonal,Matrix.submatrix_diagonal_equiv]
      rfl

#print axioms swap_queryMatrix
#print axioms rightLengthMask_diagonal
end
end ICO.C6FockQueryMatrix

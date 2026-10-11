import ICO.MHFockTransport
import ICO.MHCovarianceNorm

/-! Exact symmetric-insertion covariance and its fresh-insertion estimate
on the actual common finite Fock register. -/

namespace ICO.MHFockCovariance

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockRotation
  ICO.MHFockTransport ICO.MHSectorCovariance ICO.RecordingCopyIdentity
  ICO.MHERecordingApprox ICO.MHCovarianceNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2500000

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem boundedSymmetric_sectors (t : ℕ) : boundedSymmetricInsertion (α := α) t =
    (Matrix.blockDiagonal' (fun s : Lengths t => sectorE (α := α) s.val.1.val s.val.2.val)).submatrix
      (outputSectorEquiv t) (sectorEquiv t) := by
  ext ⟨⟨s,q⟩,p⟩ ⟨⟨s',q'⟩,p'⟩
  by_cases hs : s = s'
  · subst s'
    simp [boundedSymmetricInsertion, outputSectorEquiv, sectorEquiv,
      Matrix.blockDiagonal'_apply, sectorE_block, Matrix.blockDiagonal_apply']
  · have hblock : (⟨s,q⟩ : Block (α := α) t) ≠ ⟨s',q'⟩ := by
      intro he
      exact hs (congrArg Sigma.fst he)
    simp [boundedSymmetricInsertion, outputSectorEquiv, sectorEquiv,
      Matrix.blockDiagonal'_apply, hblock, hs]

theorem inputFamily_adjoint (F : ∀ n r, CMatrix (Sector (α := α) n r)) (t : ℕ) :
    (inputFamily F t).conjTranspose = inputFamily (fun n r => (F n r).conjTranspose) t := by
  simp only [inputFamily, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal'_conjTranspose]

theorem inputFamily_intertwine_adjoint (F : ∀ n r, CMatrix (Sector (α := α) n r))
    {t T : ℕ} (h : t ≤ T) : (basisEmbedding (inputEmbed (α := α) h)).conjTranspose * inputFamily F T =
      inputFamily F t * (basisEmbedding (inputEmbed (α := α) h)).conjTranspose := by
  have he := congrArg Matrix.conjTranspose (inputFamily_intertwine (fun n r => (F n r).conjTranspose) h)
  simpa only [Matrix.conjTranspose_mul, ← inputFamily_adjoint, Matrix.conjTranspose_conjTranspose] using he

theorem boundedSymmetric_covariance (C D : Matrix.unitaryGroup α ℂ) (t : ℕ) :
    outputFamily (fun n r => (queryTurn D n r : CMatrix (Sector (α := α) n r))) t *
      boundedSymmetricInsertion (α := α) t * inputFamily (fun n r => (inputTurn C D n r : CMatrix (Sector (α := α) n r))) t =
    outputFamily (fun n r => (outputTurn C D n r : CMatrix (Sector (α := α) n r))) t * boundedSymmetricInsertion (α := α) t := by
  rw [boundedSymmetric_sectors]
  unfold outputFamily inputFamily
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  congr 1
  funext s
  exact sectorE_covariance C D s.val.1.val s.val.2.val

theorem embedded_covariance {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (Jo : Matrix a b ℂ) (Ji : Matrix a c ℂ) (E : Matrix b c ℂ)
    (D R Q : CMatrix a) (d q : CMatrix b) (r : CMatrix c)
    (hd : D * Jo = Jo * d) (hr : Ji.conjTranspose * R = r * Ji.conjTranspose)
    (hq : Q * Jo = Jo * q) (he : d * E * r = q * E) :
    D * (Jo * E * Ji.conjTranspose) * R = Q * (Jo * E * Ji.conjTranspose) := by
  calc
    _ = (D * Jo) * E * (Ji.conjTranspose * R) := by simp only [Matrix.mul_assoc]
    _ = (Jo * d) * E * (r * Ji.conjTranspose) := by rw [hd, hr]
    _ = Jo * (d * E * r) * Ji.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = Jo * (q * E) * Ji.conjTranspose := by rw [he]
    _ = (Jo * q) * E * Ji.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = (Q * Jo) * E * Ji.conjTranspose := by rw [hq]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem symmetricOnFock_covariance (C D : Matrix.unitaryGroup α ℂ)
    {t T : ℕ} (h : t + 1 ≤ T) :
    inputFamily (fun n r => (queryTurn D n r : CMatrix (Sector (α := α) n r))) T *
      symmetricOnFock h * inputFamily (fun n r => (inputTurn C D n r : CMatrix (Sector (α := α) n r))) T =
    inputFamily (fun n r => (outputTurn C D n r : CMatrix (Sector (α := α) n r))) T * symmetricOnFock h := by
  exact embedded_covariance _ _ _ _ _ _ _ _ _
    (outputFamily_intertwine _ h) (inputFamily_intertwine_adjoint _ _)
    (outputFamily_intertwine _ h) (boundedSymmetric_covariance C D t)

theorem inputFamily_unitary_norm (F : ∀ n r, Matrix.unitaryGroup (Sector (α := α) n r) ℂ) (t : ℕ) :
    ‖inputFamily (fun n r => (F n r : CMatrix (Sector (α := α) n r))) t‖ ≤ 1 :=
  unitary_norm_le (reindexUnitary (blockUnitary (fun s : Lengths t => F s.val.1.val s.val.2.val)) (sectorEquiv t))

theorem leftOnFock_covariance_norm (C D : Matrix.unitaryGroup α ℂ)
    {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    ‖inputFamily (fun n r => (queryTurn D n r : CMatrix (Sector (α := α) n r))) T *
      leftOnFock h * inputFamily (fun n r => (inputTurn C D n r : CMatrix (Sector (α := α) n r))) T -
    inputFamily (fun n r => (outputTurn C D n r : CMatrix (Sector (α := α) n r))) T * leftOnFock h‖ ≤
      2 * Real.sqrt ((2 * (t : ℝ) * (t + 1)) / Fintype.card α) :=
  approximate_intertwine _ _ _ _ _ _ (leftOnFock_difference_norm_le h ht)
    (inputFamily_unitary_norm (queryTurn D) T) (inputFamily_unitary_norm (outputTurn C D) T)
    (inputFamily_unitary_norm (inputTurn C D) T) (symmetricOnFock_covariance C D h)

end
end ICO.MHFockCovariance

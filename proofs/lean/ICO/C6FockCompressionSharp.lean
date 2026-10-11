import ICO.C6FockQueryMatrix
import ICO.C6PolarCompression
import ICO.MHFockKnownOperation

/-! Sharp common-Fock compression keeps the maximum occupied register length. -/
namespace ICO.C6FockCompressionSharp
open QIT ICO.C6PolarFock ICO.C6PolarFockCovariance ICO.C6FockQueryMatrix
  ICO.C6PolarCompression ICO.C6BosonicFreshRotated ICO.MHBoundedRecording
  ICO.MHFockSpace ICO.MHFockTransport ICO.MHFockCovariance ICO.MHFockRotation
  ICO.MHFockSwap ICO.MHFockOracle ICO.MHFockBothCovariance ICO.MHSectorCovariance
  ICO.MHFockKnownOperation ICO.MHBlockNorm ICO.RecordingCopyIdentity ICO.RecordingProcess
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {α:Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def projection (U:Matrix.unitaryGroup α ℂ) (S:Finset α) : CMatrix α :=
  (U:CMatrix α)*coordinateProjection S*(U:CMatrix α).conjTranspose

def compressionBound (k m d:ℕ) : ℝ := Real.sqrt (((k:ℝ)+m)/((d:ℝ)-m))

theorem sector_compression_norm (U:Matrix.unitaryGroup α ℂ) (S:Finset α)
    (n r m:ℕ) (hn:n≤m) (hm:m<Fintype.card α) :
    ‖queryFamily (projection U S) (n+1) r*sectorF (α:=α) n r‖≤
      compressionBound S.card m (Fintype.card α) := by
  have hn' : (n:ℝ)≤m := by exact_mod_cast hn
  have hm' : (m:ℝ)<Fintype.card α := by exact_mod_cast hm
  have hs := rotated_leftPolar_square U S (lt_of_le_of_lt hn hm)
  have hfrac : ((S.card:ℝ)+n)/((Fintype.card α:ℝ)-n)≤
      ((S.card:ℝ)+m)/((Fintype.card α:ℝ)-m) := by
    apply div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)
  have hbase : ‖rotatedQueryProjection U S (n+1)*ICO.C6BosonicPolar.leftPolar (A:=α) n‖≤
      compressionBound S.card m (Fintype.card α) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    exact hs.trans hfrac
  have he : queryFamily (projection U S) (n+1) r*sectorF (α:=α) n r=
      Matrix.kronecker (rotatedQueryProjection U S (n+1)*ICO.C6BosonicPolar.leftPolar (A:=α) n)
        (1:CMatrix (TensorPowerProfile (α×α) r)) := by
    simp only [queryFamily,sectorF,rotatedQueryProjection,projection,Matrix.kronecker]
    rw [←Matrix.mul_kronecker_mul,Matrix.one_mul]
  rw [he]
  exact (tensor_identity_norm_le _).trans hbase

theorem bounded_compression_norm (U:Matrix.unitaryGroup α ℂ) (S:Finset α)
    (t m:ℕ) (hm:m<Fintype.card α) :
    ‖outputFamily (queryFamily (projection U S)) t*boundedPolar (α:=α) t*
      inputFamily (fun n _r => if n≤m then 1 else 0) t‖≤
      compressionBound S.card m (Fintype.card α) := by
  have hmreal : (m:ℝ)<Fintype.card α := by exact_mod_cast hm
  have hden : (0:ℝ)<Fintype.card α-m := sub_pos.mpr hmreal
  rw [boundedPolar_sectors]
  unfold outputFamily inputFamily
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,
    ←Matrix.blockDiagonal'_mul,←Matrix.blockDiagonal'_mul]
  apply (rectangular_reindex_norm_le _ _ _).trans
  apply blockDiagonal'_norm_le _ _ (by positivity)
  intro s
  dsimp only
  by_cases hs:s.val.1.val≤m
  · rw [if_pos hs,Matrix.mul_one]
    exact sector_compression_norm U S _ _ m hs hm
  · rw [if_neg hs,Matrix.mul_zero]
    exact (norm_zero.le).trans (Real.sqrt_nonneg _)

theorem left_compression_norm (U:Matrix.unitaryGroup α ℂ) (S:Finset α)
    {t T:ℕ} (h:t+1≤T) (m:ℕ) (hm:m<Fintype.card α) :
    ‖queryMatrix (projection U S) T*polarLeftOnFock (α:=α) h*leftLengthMask m T‖≤
      compressionBound S.card m (Fintype.card α) := by
  have hO := outputFamily_intertwine (queryFamily (projection U S)) h
  have hI := inputFamily_intertwine_adjoint
    (fun n r => if n≤m then (1:CMatrix (Sector (α:=α) n r)) else 0)
    (Nat.le_trans (Nat.le_succ t) h)
  have he : queryMatrix (projection U S) T*polarLeftOnFock (α:=α) h*leftLengthMask m T=
      basisEmbedding (outputEmbed h)*
        (outputFamily (queryFamily (projection U S)) t*boundedPolar (α:=α) t*
          inputFamily (fun n _r => if n≤m then 1 else 0) t)*
        (basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))).conjTranspose := by
    unfold queryMatrix polarLeftOnFock leftLengthMask
    simp only [←Matrix.mul_assoc]
    rw [hO]
    simp only [Matrix.mul_assoc]
    rw [hI]
  have ho := isometry_matrix_norm_le (basisEmbedding (outputEmbed (α:=α) h)) (outputEmbed_gram h)
  have hi : ‖(basisEmbedding (inputEmbed (α:=α) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose‖≤1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact isometry_matrix_norm_le _ (inputEmbed_gram _)
  rw [he]
  calc
    _ ≤ (‖basisEmbedding (outputEmbed (α:=α) h)‖*
        ‖outputFamily (queryFamily (projection U S)) t*boundedPolar (α:=α) t*
          inputFamily (fun n _r => if n≤m then 1 else 0) t‖)*
        ‖(basisEmbedding (inputEmbed (α:=α) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*compressionBound S.card m (Fintype.card α))*1 :=
      mul_le_mul (mul_le_mul ho (bounded_compression_norm U S t m hm)
        (norm_nonneg _) (by norm_num)) hi (norm_nonneg _) (by unfold compressionBound; positivity)
    _ = _ := by ring

theorem right_compression_norm (U:Matrix.unitaryGroup α ℂ) (S:Finset α)
    {t T:ℕ} (h:t+1≤T) (m:ℕ) (hm:m<Fintype.card α) :
    ‖queryMatrix (projection U S) T*polarRightOnFock (α:=α) h*rightLengthMask m T‖≤
      compressionBound S.card m (Fintype.card α) := by
  have he : queryMatrix (projection U S) T*polarRightOnFock (α:=α) h*rightLengthMask m T=
      swapMatrix T*(queryMatrix (projection U S) T*polarLeftOnFock (α:=α) h*leftLengthMask m T)*swapMatrix T := by
    symm
    simp only [swap_mul,swap_queryMatrix,polarRightOnFock,rightLengthMask,swapMatrix_selfAdjoint]
  rw [he]
  exact (swap_norm_le T _).trans (left_compression_norm U S h m hm)

#print axioms right_compression_norm
end
end ICO.C6FockCompressionSharp

import ICO.C6PolarFockBounds
import ICO.C6FockQueryMatrix
import ICO.C6BosonicFockSupport

/-! The raw-to-polar replacement cost depends on the occupied right length,
not on the larger global query cutoff. -/
namespace ICO.C6BosonicRawRightBound
open QIT ICO.C6PolarFockBounds ICO.C6PolarFock ICO.C6BosonicPolar
  ICO.C6FockQueryMatrix ICO.C6BosonicFockSupport ICO.MHBoundedRecording
  ICO.MHFockSpace ICO.MHFockAlgebra ICO.MHFockSwap ICO.MHFockProjection
  ICO.MHBlockNorm ICO.RecordingCopyIdentity ICO.MHERecordingApprox ICO.RecordingProcess
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2300000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem bounded_masked_difference (m t:ℕ) :
    (boundedSymmetricInsertion (α:=A) t-boundedPolar t)*leftLengthMask m t=
      Matrix.blockDiagonal' (fun k:Block (α:=A) t=>
        if k.1.val.1.val≤m then symmetricInsertion k.1.val.1.val-leftPolar k.1.val.1.val else 0) := by
  rw [boundedPolar_difference,leftLengthMask_diagonal]
  ext ⟨k,o⟩ ⟨j,i⟩
  simp only [Matrix.mul_diagonal,Matrix.blockDiagonal'_apply']
  by_cases hk:k=j
  · subst j
    by_cases hn:k.1.val.1.val≤m <;> simp [hn]
  · simp [hk]

theorem bounded_masked_norm (m t:ℕ) (hm:m<Fintype.card A) :
    ‖(boundedSymmetricInsertion (α:=A) t-boundedPolar t)*leftLengthMask m t‖≤(m:ℝ)/Fintype.card A := by
  rw [bounded_masked_difference]
  have hn : (0:ℝ)≤(m:ℝ)/Fintype.card A := by positivity
  rw [←Real.sqrt_sq hn]
  apply blockDiagonal'_norm_le _ _ (by positivity)
  intro k
  rw [Real.sqrt_sq hn]
  split_ifs with hk
  · exact (leftPolar_distance (lt_of_le_of_lt hk hm)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hk) (Nat.cast_nonneg _))
  · simpa only [norm_zero] using hn

theorem input_adjoint_mask {t T:ℕ} (h:t≤T) (m:ℕ) :
    (basisEmbedding (inputEmbed (α:=A) h)).conjTranspose*leftLengthMask m T=
      leftLengthMask m t*(basisEmbedding (inputEmbed h)).conjTranspose := by
  rw [leftLengthMask_diagonal,leftLengthMask_diagonal]
  exact embedding_adjoint_diagonal _ _

theorem raw_left_masked_norm {t T:ℕ} (h:t+1≤T) (m:ℕ) (hm:m<Fintype.card A) :
    ‖(symmetricOnFock (α:=A) h-polarLeftOnFock h)*leftLengthMask m T‖≤(m:ℝ)/Fintype.card A := by
  let J := basisEmbedding (inputEmbed (α:=A) (Nat.le_trans (Nat.le_succ t) h))
  let K := basisEmbedding (outputEmbed (α:=A) h)
  have hJ : ‖J.conjTranspose‖≤1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact isometry_matrix_norm_le _ (inputEmbed_gram _)
  have hK : ‖K‖≤1 := isometry_matrix_norm_le _ (outputEmbed_gram _)
  have he : (symmetricOnFock (α:=A) h-polarLeftOnFock h)*leftLengthMask m T=
      K*((boundedSymmetricInsertion (α:=A) t-boundedPolar t)*leftLengthMask m t)*J.conjTranspose := by
    rw [symmetricOnFock,polarLeftOnFock,←Matrix.sub_mul,←Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    rw [input_adjoint_mask]
  rw [he]
  calc
    _ ≤ (‖K‖*‖(boundedSymmetricInsertion (α:=A) t-boundedPolar t)*leftLengthMask m t‖)*‖J.conjTranspose‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*((m:ℝ)/Fintype.card A))*1 :=
      mul_le_mul (mul_le_mul hK (bounded_masked_norm m t hm) (norm_nonneg _) (by norm_num))
        hJ (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem raw_right_masked_norm {t T:ℕ} (h:t+1≤T) (m:ℕ) (hm:m<Fintype.card A) :
    ‖(symmetricRightOnFock (α:=A) h-polarRightOnFock h)*rightLengthMask m T‖≤(m:ℝ)/Fintype.card A := by
  let S := swapMatrix (α:=A) T
  have hS : ‖S‖≤1 := swapMatrix_norm_le T
  have hSS : S*S=1 := ICO.MHFockOracle.swapMatrix_sq T
  have he : (symmetricRightOnFock (α:=A) h-polarRightOnFock h)*rightLengthMask m T=
      S*((symmetricOnFock (α:=A) h-polarLeftOnFock h)*leftLengthMask m T)*S := by
    rw [symmetricRightOnFock,polarRightOnFock,rightLengthMask,←Matrix.sub_mul,←Matrix.mul_sub,
      ICO.MHFockOracle.swapMatrix_selfAdjoint]
    change (S*(symmetricOnFock h-polarLeftOnFock h)*S)*(S*leftLengthMask m T*S)=_
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc S S,hSS,Matrix.one_mul]
  rw [he]
  calc
    _ ≤ (‖S‖*‖(symmetricOnFock (α:=A) h-polarLeftOnFock h)*leftLengthMask m T‖)*‖S‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*((m:ℝ)/Fintype.card A))*1 :=
      mul_le_mul (mul_le_mul hS (raw_left_masked_norm h m hm) (norm_nonneg _) (by norm_num))
        hS (norm_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms raw_right_masked_norm
end
end ICO.C6BosonicRawRightBound

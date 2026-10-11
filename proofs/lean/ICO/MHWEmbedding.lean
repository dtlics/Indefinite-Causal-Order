import ICO.MHFockLowInput
import ICO.MHWOverlap

/-! The actual partial oracle W embedded in the unrestricted multiset Fock
space, together with the exact low-record overlap identity. -/

namespace ICO.MHWEmbedding

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockAlgebra
  ICO.MHFockProjection ICO.MHFockNodup ICO.MHFockNodupOracle ICO.MHFockLowInput
  ICO.MHOracleCutoff ICO.RecordingCopyIdentity ICO.RecordingOperatorSupport
  ICO.RecordingOracleAlgebra ICO.MHWPartial ICO.MHWOverlap
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2500000
variable {α : Type*} [Fintype α] [DecidableEq α]

def recordW {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) : CMatrix (InputCutoff (α := α) T) :=
  basisEmbedding (setEmbedding hT) * oracleW * (basisEmbedding (setEmbedding hT)).conjTranspose

theorem recordW_gram {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    (recordW hT).conjTranspose*recordW hT =
      basisEmbedding (setEmbedding hT) * (oracleW.conjTranspose*oracleW) *
        (basisEmbedding (setEmbedding hT)).conjTranspose := by
  unfold recordW
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (basisEmbedding (setEmbedding hT)).conjTranspose (basisEmbedding (setEmbedding hT)),
    basisEmbedding_gram _ (setEmbedding_injective hT),Matrix.one_mul]

theorem adjointEmbedding_cutoff {t T : ℕ} (h : t≤T) (hT : 2*Fintype.card (α×α)≤T) :
    (basisEmbedding (setEmbedding hT)).conjTranspose * sourceProjection (α := α) h =
      oldSourceCutoff (α := α) t * (basisEmbedding (setEmbedding hT)).conjTranspose := by
  rw [sourceProjection_diagonal]
  ext i o
  simp only [oldSourceCutoff,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.conjTranspose_apply,
    basisEmbedding,Matrix.submatrix_apply,id_eq,Matrix.one_apply]
  by_cases he : o=setEmbedding hT i
  · subst o
    rw [setEmbedding_grade]
    simp
  · simp [he]

theorem recordW_overlap_low {t T : ℕ} (h : t+1≤T)
    (hT : 2*Fintype.card (α×α)≤T) (ht : t<Fintype.card α) :
    (recordW hT).conjTranspose * ICO.MHFockOracle.fullOracle h *
        sourceProjection (α := α) (Nat.le_trans (Nat.le_succ t) h) =
      (recordW hT).conjTranspose * recordW hT *
        sourceProjection (α := α) (Nat.le_trans (Nat.le_succ t) h) := by
  let K := basisEmbedding (setEmbedding hT)
  let P := oldSourceCutoff (α := α) t
  let PF := sourceProjection (α := α) (Nat.le_trans (Nat.le_succ t) h)
  let Vt := ICO.MHOracleCovariance.fullOracle (leftInsertion*P) (rightInsertion*P)
  have hKV : K.conjTranspose*ICO.MHFockOracle.fullOracle h=Vt*K.conjTranspose := by
    have hh := congrArg Matrix.conjTranspose (fullOracle_nodup_adjoint h hT ht)
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] using hh
  have hKP : K.conjTranspose*PF=P*K.conjTranspose := adjointEmbedding_cutoff _ hT
  have hWo : (oracleW (A := α)).conjTranspose * Vt * P =
      oracleW.conjTranspose*oracleW*P := by
    rw [Matrix.mul_assoc]
    change oracleW.conjTranspose*(ICO.MHOracleCovariance.fullOracle (leftInsertion*P) (rightInsertion*P)*P)=_
    rw [finite_oracle_cutoff,← Matrix.mul_assoc]
    exact congrArg (fun M => M*P) oracle_overlap_eq_gram
  calc
    _ = K*((oracleW (A := α)).conjTranspose*Vt*P)*K.conjTranspose := by
      change (K*oracleW*K.conjTranspose).conjTranspose*ICO.MHFockOracle.fullOracle h*PF=_
      simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc K.conjTranspose (ICO.MHFockOracle.fullOracle h),hKV]
      simp only [Matrix.mul_assoc]
      rw [hKP]
    _ = K*(oracleW.conjTranspose*oracleW*P)*K.conjTranspose := by rw [hWo]
    _ = _ := by
      rw [recordW_gram]
      change _ = (K*(oracleW.conjTranspose*oracleW)*K.conjTranspose)*PF
      simp only [Matrix.mul_assoc]
      rw [hKP]

end
end ICO.MHWEmbedding

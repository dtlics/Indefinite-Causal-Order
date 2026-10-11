import ICO.MHFockNodupOracle
import ICO.MHOracleCutoff

/-! Actual low-record inputs see exactly the old finite-set recording
oracle under the canonical full-multiset isometry. -/

namespace ICO.MHFockLowInput

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockNodup
  ICO.MHFockNodupOracle ICO.MHFockTransport ICO.MHFockSwap ICO.MHOracleCutoff
  ICO.RecordingCopyIdentity ICO.RecordingOperatorSupport ICO.MHOracleCovariance
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 2000000
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fullOracle_nodup_low {t T : ℕ} (h : t+1≤T)
    (hT : 2*Fintype.card (α×α)≤T) (ht : t<Fintype.card α) :
    ICO.MHFockOracle.fullOracle h * basisEmbedding (setEmbedding hT) * oldSourceCutoff (α := α) t =
      basisEmbedding (setEmbedding hT) * fullOracle (leftInsertion (α := α)) rightInsertion * oldSourceCutoff (α := α) t := by
  rw [fullOracle_nodup_intertwine h hT ht, Matrix.mul_assoc, finite_oracle_cutoff,
    ← Matrix.mul_assoc]

theorem fullOracle_nodup_adjoint {t T : ℕ} (h : t+1≤T)
    (hT : 2*Fintype.card (α×α)≤T) (ht : t<Fintype.card α) :
    (ICO.MHFockOracle.fullOracle h).conjTranspose * basisEmbedding (setEmbedding hT) =
      basisEmbedding (setEmbedding hT) *
        (fullOracle (leftInsertion * oldSourceCutoff (α := α) t) (rightInsertion * oldSourceCutoff (α := α) t)).conjTranspose := by
  change (ICO.MHOracleCovariance.fullOracle (leftOnFock (α := α) h) (rightOnFock (α := α) h)).conjTranspose *
    basisEmbedding (setEmbedding hT) = basisEmbedding (setEmbedding hT) *
      (ICO.MHOracleCovariance.fullOracle (leftInsertion * oldSourceCutoff (α := α) t)
        (rightInsertion * oldSourceCutoff (α := α) t)).conjTranspose
  rw [fullOracle_adjoint,fullOracle_adjoint]
  apply full_intertwine
  · exact rightOnFock_nodup_intertwine h hT ht
  · exact leftOnFock_nodup_intertwine h hT ht
  · exact adjoint_intertwine_of_compression _ _ _ (basisEmbedding_gram _ (setEmbedding_injective hT))
      (rightOnFock_nodup_compression h hT ht) (rightOnFock_commute_nodup h hT)
  · exact adjoint_intertwine_of_compression _ _ _ (basisEmbedding_gram _ (setEmbedding_injective hT))
      (leftOnFock_nodup_compression h hT ht) (leftOnFock_commute_nodup h hT)

theorem fullOracle_nodup_adjoint_low {t T : ℕ} (h : t+1≤T)
    (hT : 2*Fintype.card (α×α)≤T) (ht : t<Fintype.card α) :
    (ICO.MHFockOracle.fullOracle h).conjTranspose * basisEmbedding (setEmbedding hT) * oldSourceCutoff (α := α) t =
      basisEmbedding (setEmbedding hT) * (fullOracle (leftInsertion (α := α)) rightInsertion).conjTranspose * oldSourceCutoff (α := α) t := by
  rw [fullOracle_nodup_adjoint h hT ht, Matrix.mul_assoc, finite_inverse_cutoff,
    ← Matrix.mul_assoc]

end
end ICO.MHFockLowInput

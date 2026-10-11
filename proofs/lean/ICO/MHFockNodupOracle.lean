import ICO.MHFockNodup
import ICO.MHFockRightEntries
import ICO.MHOracleCovariance

/-! The complete multiset oracle restricts exactly to the finite-set oracle
with the same source cutoff, including both adjoint branches. -/

namespace ICO.MHFockNodupOracle

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockLabels
  ICO.MHFockEntries ICO.MHFockRightEntries ICO.MHFockProjection ICO.MHFockTransport
  ICO.MHFockNodup ICO.MHFockSwap ICO.RecordingCopyIdentity ICO.MHEmbeddingProjector
  ICO.RecordingMultisetBridge ICO.RecordingOperatorSupport ICO.MHOccupationSupport
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2500000

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem rightOnFock_nodup_compression {t T : ℕ} (h : t+1 ≤ T)
    (hT : 2 * Fintype.card (α × α) ≤ T) (ht : t < Fintype.card α) :
    (basisEmbedding (setEmbedding hT)).conjTranspose * rightOnFock h * basisEmbedding (setEmbedding hT) =
      rightInsertion * oldSourceCutoff (α := α) t := by
  rw [basisEmbedding_compression]
  ext o i
  change rightOnFock h (setEmbedding hT o) (setEmbedding hT i) = _
  rw [rightOnFock_coefficient, setEmbedding_grade, setEmbedding_label, setEmbedding_label,
    embedded_right_step]
  simp only [oldSourceCutoff, Matrix.mul_diagonal, embed, domainLabels, Finset.val_toFinset]
  by_cases hs : i.2.1.card + i.2.2.card ≤ t
  · have hd := lt_of_le_of_lt hs ht
    simp [rightInsertion, hs, hd, ICO.PathRecordingSupport.leftDomain]
    split_ifs <;> simp_all
  · simp [hs]

theorem rightOnFock_commute_nodup {t T : ℕ} (h : t+1 ≤ T)
    (hT : 2 * Fintype.card (α × α) ≤ T) :
    Commute (rightOnFock h) (basisEmbedding (setEmbedding hT) * (basisEmbedding (setEmbedding hT)).conjTranspose) := by
  rw [basisEmbedding_image _ (setEmbedding_injective hT)]
  change rightOnFock h * Matrix.diagonal _ = Matrix.diagonal _ * rightOnFock h
  ext o i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : rightOnFock h o i = 0
  · simp [hz]
  have hs := (rightOnFock_support h o i hz).2
  have hn : NodupLabel (fockLabel i) ↔ NodupLabel (fockLabel o) :=
    ⟨fun hi => multiset_right_preserves_nodup hi hs,
      fun ho => multiset_right_reverse_preserves_nodup ho hs⟩
  have he : (∃ x, setEmbedding hT x = i) ↔ ∃ x, setEmbedding hT x = o :=
    (setEmbedding_range hT i).trans (hn.trans (setEmbedding_range hT o).symm)
  by_cases hi : ∃ x, setEmbedding hT x = i
  · have ho := he.mp hi
    simp only [if_pos hi, if_pos ho, mul_one, one_mul]
  · have ho := mt he.mpr hi
    simp only [if_neg hi, if_neg ho, mul_zero, zero_mul]

theorem rightOnFock_nodup_intertwine {t T : ℕ} (h : t+1 ≤ T)
    (hT : 2 * Fintype.card (α × α) ≤ T) (ht : t < Fintype.card α) :
    rightOnFock h * basisEmbedding (setEmbedding hT) =
      basisEmbedding (setEmbedding hT) * (rightInsertion * oldSourceCutoff (α := α) t) :=
  intertwine_of_compression _ _ _ (basisEmbedding_gram _ (setEmbedding_injective hT))
    (rightOnFock_nodup_compression h hT ht) (rightOnFock_commute_nodup h hT)

theorem adjoint_intertwine_of_compression {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (J : Matrix b a ℂ) (U : CMatrix b) (V : CMatrix a)
    (hJ : J.conjTranspose*J=1) (hC : J.conjTranspose*U*J=V)
    (hcomm : Commute U (J*J.conjTranspose)) : U.conjTranspose*J=J*V.conjTranspose := by
  apply intertwine_of_compression _ _ _ hJ
  · have he := congrArg Matrix.conjTranspose hC
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using he
  · have he := congrArg Matrix.conjTranspose hcomm.eq
    simpa only [Commute, SemiconjBy, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] using he.symm

theorem mul_intertwine {a b : Type*} [Fintype a] [Fintype b]
    (J : Matrix b a ℂ) (A B : CMatrix b) (a' b' : CMatrix a)
    (hA : A*J=J*a') (hB : B*J=J*b') : (A*B)*J=J*(a'*b') := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

theorem full_intertwine {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (J : Matrix b a ℂ) (A B : CMatrix b) (a' b' : CMatrix a)
    (hA : A*J=J*a') (hB : B*J=J*b')
    (hAa : A.conjTranspose*J=J*a'.conjTranspose)
    (hBa : B.conjTranspose*J=J*b'.conjTranspose) :
    ICO.MHOracleCovariance.fullOracle A B * J = J * ICO.MHOracleCovariance.fullOracle a' b' := by
  have hQA : (1-A*A.conjTranspose)*J=J*(1-a'*a'.conjTranspose) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [mul_intertwine J A A.conjTranspose a' a'.conjTranspose hA hAa]
  have hQB : (1-B*B.conjTranspose)*J=J*(1-b'*b'.conjTranspose) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [mul_intertwine J B B.conjTranspose b' b'.conjTranspose hB hBa]
  unfold ICO.MHOracleCovariance.fullOracle
  rw [Matrix.add_mul, Matrix.mul_add,
    mul_intertwine J A (1-B*B.conjTranspose) a' (1-b'*b'.conjTranspose) hA hQB,
    mul_intertwine J (1-A*A.conjTranspose) B.conjTranspose (1-a'*a'.conjTranspose) b'.conjTranspose hQA hBa]

theorem fullOracle_nodup_intertwine {t T : ℕ} (h : t+1 ≤ T)
    (hT : 2 * Fintype.card (α × α) ≤ T) (ht : t < Fintype.card α) :
    ICO.MHFockOracle.fullOracle h * basisEmbedding (setEmbedding hT) =
      basisEmbedding (setEmbedding hT) * ICO.MHOracleCovariance.fullOracle
        (leftInsertion * oldSourceCutoff (α := α) t) (rightInsertion * oldSourceCutoff (α := α) t) :=
  full_intertwine _ _ _ _ _ (leftOnFock_nodup_intertwine h hT ht) (rightOnFock_nodup_intertwine h hT ht)
    (adjoint_intertwine_of_compression _ _ _ (basisEmbedding_gram _ (setEmbedding_injective hT))
      (leftOnFock_nodup_compression h hT ht) (leftOnFock_commute_nodup h hT))
    (adjoint_intertwine_of_compression _ _ _ (basisEmbedding_gram _ (setEmbedding_injective hT))
      (rightOnFock_nodup_compression h hT ht) (rightOnFock_commute_nodup h hT))

end
end ICO.MHFockNodupOracle

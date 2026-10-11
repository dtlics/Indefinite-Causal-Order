import ICO.MHFockEntries
import ICO.MHFockTransport

/-! The no-repeated-edge subspace is a genuine reducing subspace of the
full multiset insertion. Its compression is the finite-set oracle with the
same explicit source cutoff. -/

namespace ICO.MHFockNodup

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockLabels
  ICO.MHFockEntries ICO.MHFockProjection ICO.MHFockTransport
  ICO.RecordingCopyIdentity ICO.MHEmbeddingProjector ICO.RecordingMultisetBridge
  ICO.RecordingOperatorSupport ICO.MHOccupationSupport
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2500000

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem set_total_bound (i : Basis α) :
    i.2.1.card + i.2.2.card ≤ 2 * Fintype.card (α × α) := by
  have hL := Finset.card_le_univ i.2.1
  have hR := Finset.card_le_univ i.2.2
  omega

def setEmbedding {T : ℕ} (hT : 2 * Fintype.card (α × α) ≤ T) (i : Basis α) : InputCutoff (α := α) T :=
  setFock i ((set_total_bound i).trans hT)

theorem setEmbedding_injective {T : ℕ} (hT : 2 * Fintype.card (α × α) ≤ T) :
    Function.Injective (setEmbedding (α := α) hT) := by
  intro v w he
  exact setFock_injective v w _ _ he

theorem setEmbedding_label {T : ℕ} (hT : 2 * Fintype.card (α × α) ≤ T) (i : Basis α) :
    fockLabel (setEmbedding hT i) = embed i := setFock_label _ _

theorem setEmbedding_grade {T : ℕ} (hT : 2 * Fintype.card (α × α) ≤ T) (i : Basis α) :
    grade (setEmbedding hT i) = i.2.1.card + i.2.2.card := rfl

theorem setEmbedding_usedOutputs {T : ℕ} (hT : 2 * Fintype.card (α × α) ≤ T) (i : Basis α) :
    usedOutputs (setEmbedding hT i).2.2 (setEmbedding hT i).1.2 = (i.2.1 ∪ i.2.2).image Prod.snd :=
  usedOutputs_sets i.2.1 i.2.2

theorem setEmbedding_range {T : ℕ} (hT : 2 * Fintype.card (α × α) ≤ T)
    (v : InputCutoff (α := α) T) :
    (∃ i, setEmbedding hT i = v) ↔ NodupLabel (fockLabel v) := by
  constructor
  · rintro ⟨i,rfl⟩
    rw [setEmbedding_label]
    exact embedded_nodup i
  · intro hv
    obtain ⟨i,hi⟩ := (nodup_iff_embedded (fockLabel v)).mp hv
    refine ⟨i, fockLabel_injective T ?_⟩
    rw [setEmbedding_label,hi]

def oldSourceCutoff (t : ℕ) : CMatrix (Basis α) :=
  Matrix.diagonal (fun i => if i.2.1.card + i.2.2.card ≤ t then 1 else 0)

theorem leftOnFock_nodup_compression {t T : ℕ} (h : t+1 ≤ T)
    (hT : 2 * Fintype.card (α × α) ≤ T) (ht : t < Fintype.card α) :
    (basisEmbedding (setEmbedding hT)).conjTranspose * leftOnFock h * basisEmbedding (setEmbedding hT) =
      leftInsertion * oldSourceCutoff (α := α) t := by
  rw [basisEmbedding_compression]
  ext o i
  change leftOnFock h (setEmbedding hT o) (setEmbedding hT i) = _
  rw [leftOnFock_coefficient, setEmbedding_grade, setEmbedding_label, setEmbedding_label,
    embedded_left_step, setEmbedding_usedOutputs]
  simp only [oldSourceCutoff, Matrix.mul_diagonal]
  by_cases hs : i.2.1.card + i.2.2.card ≤ t
  · have hd := lt_of_le_of_lt hs ht
    simp [leftInsertion, hs, hd]
    split_ifs <;> simp_all
  · simp [hs]

theorem leftOnFock_commute_nodup {t T : ℕ} (h : t+1 ≤ T)
    (hT : 2 * Fintype.card (α × α) ≤ T) :
    Commute (leftOnFock h) (basisEmbedding (setEmbedding hT) * (basisEmbedding (setEmbedding hT)).conjTranspose) := by
  rw [basisEmbedding_image _ (setEmbedding_injective hT)]
  change leftOnFock h * Matrix.diagonal _ = Matrix.diagonal _ * leftOnFock h
  ext o i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : leftOnFock h o i = 0
  · simp [hz]
  have hs := (leftOnFock_support h o i hz).2
  have hn : NodupLabel (fockLabel i) ↔ NodupLabel (fockLabel o) :=
    ⟨fun hi => multiset_left_preserves_nodup hi hs,
      fun ho => multiset_left_reverse_preserves_nodup ho hs⟩
  have he : (∃ x, setEmbedding hT x = i) ↔ ∃ x, setEmbedding hT x = o :=
    (setEmbedding_range hT i).trans (hn.trans (setEmbedding_range hT o).symm)
  by_cases hi : ∃ x, setEmbedding hT x = i
  · have ho := he.mp hi
    simp only [if_pos hi, if_pos ho, mul_one, one_mul]
  · have ho := mt he.mpr hi
    simp only [if_neg hi, if_neg ho, mul_zero, zero_mul]

theorem leftOnFock_nodup_intertwine {t T : ℕ} (h : t+1 ≤ T)
    (hT : 2 * Fintype.card (α × α) ≤ T) (ht : t < Fintype.card α) :
    leftOnFock h * basisEmbedding (setEmbedding hT) =
      basisEmbedding (setEmbedding hT) * (leftInsertion * oldSourceCutoff (α := α) t) :=
  intertwine_of_compression _ _ _ (basisEmbedding_gram _ (setEmbedding_injective hT))
    (leftOnFock_nodup_compression h hT ht) (leftOnFock_commute_nodup h hT)

end
end ICO.MHFockNodup

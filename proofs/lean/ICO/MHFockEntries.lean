import ICO.MHLabelCoefficients
import ICO.MHFockProjection

/-! Entrywise identification of the finite Fock insertion with the source's
arbitrary-multiset recording formula. -/

namespace ICO.MHFockEntries

open QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockLabels
  ICO.MHLabelCoefficients ICO.MHFockProjection ICO.RecordingCopyIdentity
  ICO.MHERecordingApprox ICO.MHFreshInsertion ICO.MHOccupationCounts
  ICO.MHOccupationSupport ICO.RecordingMultisetBridge
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 2500000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem embedding_sandwich_entry {a b c d : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]
    (f : a → c) (g : b → d) (hf : Function.Injective f) (hg : Function.Injective g)
    (M : Matrix a b ℂ) (o : a) (i : b) :
    (basisEmbedding f * M * (basisEmbedding g).conjTranspose) (f o) (g i) = M o i := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, basisEmbedding,
    Matrix.submatrix_apply, Matrix.one_apply, hf.eq_iff, hg.eq_iff]

variable {α : Type*} [Fintype α] [DecidableEq α]

def outputLabel {t : ℕ} (o : OutputCutoff (α := α) t) : MultisetBasis α :=
  fixedLabel o.1.2 o.2

theorem fockLabel_inputEmbed {t T : ℕ} (h : t ≤ T) (i : InputCutoff (α := α) t) :
    fockLabel (inputEmbed h i) = fockLabel i := rfl

theorem fockLabel_outputEmbed {t T : ℕ} (h : t+1 ≤ T) (o : OutputCutoff (α := α) t) :
    fockLabel (outputEmbed h o) = outputLabel o := rfl

def successor {t : ℕ} (y : α) (i : InputCutoff (α := α) t) : OutputCutoff (α := α) t :=
  ⟨i.1, (y, incrementProfile (i.2.1,y) i.2.2)⟩

theorem successor_label {t : ℕ} (y : α) (i : InputCutoff (α := α) t) :
    outputLabel (successor y i) =
      (y, (i.2.1,y) ::ₘ (fockLabel i).2.1, (fockLabel i).2.2) := by
  dsimp only [outputLabel, successor, fixedLabel, fockLabel]
  exact Prod.ext rfl (Prod.ext (incrementProfile_multiset _ _) rfl)

theorem boundedInsertion_support {t : ℕ} (o : OutputCutoff (α := α) t)
    (i : InputCutoff (α := α) t) (hA : boundedInsertion t o i ≠ 0) :
    MultisetLeftStep (fockLabel i) (outputLabel o) := by
  have hk : o.1 = i.1 := by
    by_contra hn
    exact hA (by simp [boundedInsertion, Matrix.blockDiagonal'_apply, hn])
  rcases o with ⟨k,o⟩
  rcases i with ⟨k',i⟩
  dsimp only at hk
  subst k'
  have hF : fullInsertion k.2 o i ≠ 0 := by
    simpa only [boundedInsertion, Matrix.blockDiagonal'_apply_eq] using hA
  have hf : i ∈ freshSupport k.2 o := by
    by_contra hn
    exact hF (by simp [fullInsertion, hn])
  exact (fixed_left_step k.2 o i).mpr hf

theorem leftOnFock_entry_embedded {t T : ℕ} (h : t+1 ≤ T)
    (o : OutputCutoff (α := α) t) (i : InputCutoff (α := α) t) :
    leftOnFock h (outputEmbed h o) (inputEmbed (Nat.le_trans (Nat.le_succ t) h) i) =
      boundedInsertion t o i :=
  embedding_sandwich_entry _ _ (outputEmbed_injective h)
    (inputEmbed_injective _) _ o i

theorem leftOnFock_support {t T : ℕ} (h : t+1 ≤ T)
    (o i : InputCutoff (α := α) T) (hA : leftOnFock h o i ≠ 0) :
    grade i ≤ t ∧ MultisetLeftStep (fockLabel i) (fockLabel o) := by
  obtain ⟨j,hj,hji⟩ := mul_entry_nonzero _ _ o i hA
  obtain ⟨k,hok,hkj⟩ := mul_entry_nonzero _ _ o j hj
  have ho := basisEmbedding_support (outputEmbed h) o k hok
  have hi : i = inputEmbed (Nat.le_trans (Nat.le_succ t) h) j := by
    apply basisEmbedding_support
    intro hz
    apply hji
    simp only [Matrix.conjTranspose_apply, hz, star_zero]
  rw [ho,hi]
  exact ⟨j.1.1.property, boundedInsertion_support k j hkj⟩

theorem step_output_successor {t T : ℕ} (h : t+1 ≤ T)
    (o : InputCutoff (α := α) T) (i : InputCutoff (α := α) t)
    (hs : MultisetLeftStep (fockLabel i) (fockLabel o)) :
    o = outputEmbed h (successor o.2.1 i) := by
  apply fockLabel_injective T
  rw [fockLabel_outputEmbed, successor_label]
  exact Prod.ext rfl (Prod.ext hs.2.2 hs.1)

theorem leftOnFock_coefficient {t T : ℕ} (h : t+1 ≤ T)
    (o i : InputCutoff (α := α) T) :
    leftOnFock h o i = if grade i ≤ t ∧ MultisetLeftStep (fockLabel i) (fockLabel o) then
      (Real.sqrt ((Fintype.card α : ℝ) - (usedOutputs i.2.2 i.1.2).card) : ℂ)⁻¹ else 0 := by
  by_cases hs : grade i ≤ t ∧ MultisetLeftStep (fockLabel i) (fockLabel o)
  · rw [if_pos hs]
    let j : InputCutoff (α := α) t := restrictInput i hs.1
    have hj : inputEmbed (Nat.le_trans (Nat.le_succ t) h) j = i := by
      apply input_ext <;> rfl
    have hstep : MultisetLeftStep (fockLabel j) (fockLabel o) := by
      rw [← hj, fockLabel_inputEmbed] at hs
      exact hs.2
    have ho := step_output_successor h o j hstep
    rw [ho, ← hj, leftOnFock_entry_embedded]
    simp only [boundedInsertion, successor, Matrix.blockDiagonal'_apply_eq]
    erw [Matrix.blockDiagonal'_apply_eq]
    change fullInsertion j.1.2 (o.2.1, incrementProfile (j.2.1,o.2.1) j.2.2) j.2 = _
    have hf : j.2 ∈ freshSupport j.1.2 (o.2.1, incrementProfile (j.2.1,o.2.1) j.2.2) := by
      simp only [freshSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [usedOutputs_multisets]
      exact hstep.2.1
    simp only [fullInsertion, if_pos hf]
    rfl
  · rw [if_neg hs]
    by_contra hne
    exact hs (leftOnFock_support h o i hne)

end
end ICO.MHFockEntries

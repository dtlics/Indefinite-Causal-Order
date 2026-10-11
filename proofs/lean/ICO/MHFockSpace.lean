import ICO.MHBoundedRecording
import ICO.MHInsertionIsometry

/-! Concrete inclusions between finite unrestricted multiset Fock spaces. -/

namespace ICO.MHFockSpace

open QIT ICO.MHBoundedRecording ICO.MHBadInsertion ICO.RecordingCopyIdentity
  ICO.RecordingProcess ICO.MHERecordingApprox ICO.MHInsertionIsometry
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2000000

variable {α : Type*} [Fintype α] [DecidableEq α]

def lengthEmbed {t T : ℕ} (h : t ≤ T) (s : Lengths t) : Lengths T :=
  ⟨(Fin.castLE (Nat.succ_le_succ h) s.val.1, Fin.castLE (Nat.succ_le_succ h) s.val.2),
    le_trans s.property h⟩

def lengthGrow {t T : ℕ} (h : t + 1 ≤ T) (s : Lengths t) : Lengths T :=
  ⟨(⟨s.val.1.val + 1, by have hs := s.val.1.isLt; omega⟩,
      ⟨s.val.2.val, by have hs := s.val.2.isLt; omega⟩), by dsimp only; have hs := s.property; omega⟩

def inputEmbed {t T : ℕ} (h : t ≤ T) (v : InputCutoff (α := α) t) : InputCutoff (α := α) T :=
  ⟨⟨lengthEmbed h v.1.1, v.1.2⟩, v.2⟩

def outputEmbed {t T : ℕ} (h : t + 1 ≤ T) (v : OutputCutoff (α := α) t) : InputCutoff (α := α) T :=
  ⟨⟨lengthGrow h v.1.1, v.1.2⟩, v.2⟩

theorem input_ext {t : ℕ} (v w : InputCutoff (α := α) t)
    (hl : v.1.1.val.1.val = w.1.1.val.1.val)
    (hr : v.1.1.val.2.val = w.1.1.val.2.val)
    (hx : v.2.1 = w.2.1) (hp : v.2.2.val = w.2.2.val) (hq : v.1.2.val = w.1.2.val) : v = w := by
  rcases v with ⟨⟨s, q⟩, x, p⟩
  rcases w with ⟨⟨s', q'⟩, x', p'⟩
  have hs : s = s' := Subtype.ext (Prod.ext (Fin.ext hl) (Fin.ext hr))
  subst s'
  have hpp : p = p' := Subtype.ext hp
  have hqq : q = q' := Subtype.ext hq
  subst p'; subst q'; dsimp only at hx; subst x'
  rfl

theorem output_ext {t : ℕ} (v w : OutputCutoff (α := α) t)
    (hl : v.1.1.val.1.val = w.1.1.val.1.val)
    (hr : v.1.1.val.2.val = w.1.1.val.2.val)
    (hx : v.2.1 = w.2.1) (hp : v.2.2.val = w.2.2.val) (hq : v.1.2.val = w.1.2.val) : v = w := by
  rcases v with ⟨⟨s, q⟩, x, p⟩
  rcases w with ⟨⟨s', q'⟩, x', p'⟩
  have hs : s = s' := Subtype.ext (Prod.ext (Fin.ext hl) (Fin.ext hr))
  subst s'
  have hpp : p = p' := Subtype.ext hp
  have hqq : q = q' := Subtype.ext hq
  subst p'; subst q'; dsimp only at hx; subst x'
  rfl

theorem inputEmbed_injective {t T : ℕ} (h : t ≤ T) : Function.Injective (inputEmbed (α := α) h) := by
  intro v w heq
  apply input_ext v w
  · exact congrArg (fun z : InputCutoff (α := α) T => z.1.1.val.1.val) heq
  · exact congrArg (fun z : InputCutoff (α := α) T => z.1.1.val.2.val) heq
  · exact congrArg (fun z : InputCutoff (α := α) T => z.2.1) heq
  · exact congrArg (fun z : InputCutoff (α := α) T => z.2.2.val) heq
  · exact congrArg (fun z : InputCutoff (α := α) T => z.1.2.val) heq

theorem outputEmbed_injective {t T : ℕ} (h : t + 1 ≤ T) : Function.Injective (outputEmbed (α := α) h) := by
  intro v w heq
  apply output_ext v w
  · have he := congrArg (fun z : InputCutoff (α := α) T => z.1.1.val.1.val) heq
    exact Nat.add_right_cancel he
  · exact congrArg (fun z : InputCutoff (α := α) T => z.1.1.val.2.val) heq
  · exact congrArg (fun z : InputCutoff (α := α) T => z.2.1) heq
  · exact congrArg (fun z : InputCutoff (α := α) T => z.2.2.val) heq
  · exact congrArg (fun z : InputCutoff (α := α) T => z.1.2.val) heq

theorem inputEmbed_gram {t T : ℕ} (h : t ≤ T) :
    (basisEmbedding (inputEmbed (α := α) h)).conjTranspose * basisEmbedding (inputEmbed (α := α) h) =
      (1 : CMatrix (InputCutoff (α := α) t)) :=
  basisEmbedding_gram _ (inputEmbed_injective h)

theorem outputEmbed_gram {t T : ℕ} (h : t + 1 ≤ T) :
    (basisEmbedding (outputEmbed (α := α) h)).conjTranspose * basisEmbedding (outputEmbed (α := α) h) =
      (1 : CMatrix (OutputCutoff (α := α) t)) :=
  basisEmbedding_gram _ (outputEmbed_injective h)

/-- `V^L` as a square matrix on a common finite Fock space, zero on input
sectors outside the chosen cutoff. -/
def leftOnFock {t T : ℕ} (h : t + 1 ≤ T) : CMatrix (InputCutoff (α := α) T) :=
  basisEmbedding (outputEmbed h) * boundedInsertion t *
    (basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))).conjTranspose

def symmetricOnFock {t T : ℕ} (h : t + 1 ≤ T) : CMatrix (InputCutoff (α := α) T) :=
  basisEmbedding (outputEmbed h) * boundedSymmetricInsertion t *
    (basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))).conjTranspose

theorem leftOnFock_difference_norm_le {t T : ℕ} (h : t + 1 ≤ T) (ht : t < Fintype.card α) :
    ‖leftOnFock (α := α) h - symmetricOnFock h‖ ≤
      Real.sqrt ((2 * (t : ℝ) * (t + 1)) / Fintype.card α) := by
  have hOut := isometry_matrix_norm_le (basisEmbedding (outputEmbed (α := α) h)) (outputEmbed_gram h)
  have hIn := isometry_matrix_norm_le (basisEmbedding (inputEmbed (α := α) (Nat.le_trans (Nat.le_succ t) h)))
    (inputEmbed_gram (Nat.le_trans (Nat.le_succ t) h))
  have hAdj : ‖(basisEmbedding (inputEmbed (α := α) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose‖ ≤ 1 := by
    rwa [Matrix.l2_opNorm_conjTranspose]
  rw [leftOnFock, symmetricOnFock, ← Matrix.sub_mul, ← Matrix.mul_sub]
  calc
    _ ≤ (‖basisEmbedding (outputEmbed (α := α) h)‖ *
        ‖boundedInsertion (α := α) t - boundedSymmetricInsertion t‖) *
        ‖(basisEmbedding (inputEmbed (α := α) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ((1 : ℝ) * Real.sqrt ((2 * (t : ℝ) * (t + 1)) / Fintype.card α)) * 1 :=
      mul_le_mul (mul_le_mul hOut (bounded_insertion_difference_norm_le t ht)
        (norm_nonneg _) (by norm_num)) hAdj (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end ICO.MHFockSpace

import ICO.RecordingCopyIdentity
import ICO.RecordingFreshOutput

/-!
# Compressing supported recording vectors to their active basis

This file connects the pointwise support invariant to the explicit finite
input types used by the fresh-output and dephased-Gram channel bounds.
-/

namespace ICO.RecordingSupportCompression

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingCopyIdentity ICO.RecordingFreshOutput
open scoped BigOperators Matrix

noncomputable section

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Extension by the canonical basis embedding recovers any supported vector,
    including vectors with arbitrary coherent and entangled amplitudes. -/
theorem basisEmbedding_recovers_vector (f : a → b) (hf : Function.Injective f)
    (ψ : b → ℂ) (hψ : ∀ i, ψ i ≠ 0 → ∃ j, f j = i) :
    basisEmbedding f *ᵥ (ψ ∘ f) = ψ := by
  funext i
  by_cases hi : ψ i = 0
  · rw [hi, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    simp only [basisEmbedding, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
      Function.comp_apply]
    by_cases hj : i = f j
    · rw [if_pos hj, ← hj, hi, mul_zero]
    · simp [hj]
  · obtain ⟨j, hj⟩ := hψ i hi
    subst i
    simp only [Matrix.mulVec, dotProduct, basisEmbedding, Matrix.submatrix_apply,
      id_eq, Matrix.one_apply, hf.eq_iff, Function.comp_apply]
    simp

variable {α μ : Type*} [Fintype α] [DecidableEq α] [Fintype μ] [DecidableEq μ]

def activeMemoryEmbed (m : ℕ) (u : ActiveSource α m × μ) : Basis α × μ :=
  (u.1.val.val, u.2)

omit [Fintype α] [Fintype μ] [DecidableEq μ] in
theorem activeMemoryEmbed_injective (m : ℕ) :
    Function.Injective (activeMemoryEmbed (α := α) (μ := μ) m) := by
  intro i j h
  have hs := congrArg Prod.fst h
  have hm := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext (Subtype.ext hs)) hm

theorem active_compression_recovers (m : ℕ) (ψ : Basis α × μ → ℂ)
    (hψ : ∀ i, ψ i ≠ 0 → FreshLeft i.1.1 i.1.2.1 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) :
    basisEmbedding (activeMemoryEmbed m) *ᵥ (ψ ∘ activeMemoryEmbed m) = ψ := by
  apply basisEmbedding_recovers_vector _ (activeMemoryEmbed_injective m) ψ
  intro i hi
  obtain ⟨hf, hm⟩ := hψ i hi
  exact ⟨(⟨⟨i.1, hf⟩, hm⟩, i.2), rfl⟩

theorem inverse_active_compression_recovers (m : ℕ) (ψ : Basis α × μ → ℂ)
    (hψ : ∀ i, ψ i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) :
    basisEmbedding (activeMemoryEmbed (m + 1)) *ᵥ
      ((Matrix.kronecker inverseRecording (1 : CMatrix μ) *ᵥ ψ) ∘
        activeMemoryEmbed (m + 1)) =
      Matrix.kronecker inverseRecording (1 : CMatrix μ) *ᵥ ψ := by
  apply active_compression_recovers
  intro i hi
  obtain ⟨_, hf, hm⟩ := inverse_with_memory_support ψ m hψ i hi
  exact ⟨hf, hm⟩

omit [Fintype α] [DecidableEq α] [Fintype μ] [DecidableEq μ] in
theorem boundedMemoryEmbed_injective (m : ℕ) :
    Function.Injective (boundedMemoryEmbed (α := α) (μ := μ) m) := by
  intro i j h
  have hq := congrArg (fun k : Basis α × μ => k.1.1) h
  have hL := congrArg (fun k : Basis α × μ => k.1.2.1) h
  have hR := congrArg (fun k : Basis α × μ => k.1.2.2) h
  have hm := congrArg Prod.snd h
  exact Prod.ext (Prod.ext hq (Subtype.ext (Prod.ext hL hR))) hm

theorem bounded_compression_recovers (m : ℕ) (ψ : Basis α × μ → ℂ)
    (hψ : ∀ i, ψ i ≠ 0 → i.1.2.1.card + i.1.2.2.card ≤ m) :
    basisEmbedding (boundedMemoryEmbed m) *ᵥ (ψ ∘ boundedMemoryEmbed m) = ψ := by
  apply basisEmbedding_recovers_vector _ (boundedMemoryEmbed_injective m) ψ
  intro i hi
  exact ⟨((i.1.1, ⟨(i.1.2.1, i.1.2.2), hψ i hi⟩), i.2), rfl⟩

end
end ICO.RecordingSupportCompression

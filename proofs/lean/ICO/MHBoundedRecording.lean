import ICO.MHERecordingApprox
import ICO.MHBlockNorm
import ICO.MHOccupationCovariance

/-! The unrestricted multiset `V^L−E^L` bound on the entire finite cutoff.
The direct sum permits coherent superpositions of lengths and right records. -/

namespace ICO.MHBoundedRecording

open QIT ICO.MHBadInsertion ICO.MHERecordingApprox ICO.MHBlockNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1500000

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Lengths (t : ℕ) := {s : Fin (t + 1) × Fin (t + 1) // (s.1 : ℕ) + (s.2 : ℕ) ≤ t}

abbrev Block (t : ℕ) := Σ s : Lengths t, TensorPowerProfile (α × α) s.val.2.val

abbrev InputCutoff (t : ℕ) := Σ k : Block (α := α) t, Input (α := α) k.1.val.1.val

abbrev OutputCutoff (t : ℕ) := Σ k : Block (α := α) t, Input (α := α) (k.1.val.1.val + 1)

def boundedInsertion (t : ℕ) : Matrix (OutputCutoff (α := α) t) (InputCutoff (α := α) t) ℂ :=
  Matrix.blockDiagonal' (fun k : Block (α := α) t => fullInsertion (n := k.1.val.1.val) k.2)

def boundedSymmetricInsertion (t : ℕ) : Matrix (OutputCutoff (α := α) t) (InputCutoff (α := α) t) ℂ :=
  Matrix.blockDiagonal' (fun k : Block (α := α) t => symmetricInsertion (α := α) k.1.val.1.val)

theorem bounded_difference (t : ℕ) :
    boundedInsertion (α := α) t - boundedSymmetricInsertion t =
      Matrix.blockDiagonal' (fun k : Block (α := α) t =>
        fullInsertion (n := k.1.val.1.val) k.2 - symmetricInsertion k.1.val.1.val) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  simp only [boundedInsertion, boundedSymmetricInsertion, Matrix.sub_apply,
    Matrix.blockDiagonal'_apply']
  split_ifs <;> simp

/-- The published `sqrt(2t(t+1)/d)` estimate holds on the full finite
unrestricted-multiset register, with coherence across all allowed sectors. -/
theorem bounded_insertion_difference_norm_le (t : ℕ) (ht : t < Fintype.card α) :
    ‖boundedInsertion (α := α) t - boundedSymmetricInsertion t‖ ≤
      Real.sqrt ((2 * (t : ℝ) * (t + 1)) / Fintype.card α) := by
  rw [bounded_difference]
  apply blockDiagonal'_norm_le _ _ (by positivity)
  intro k
  have hnr := k.1.property
  have hs : k.1.val.1.val + k.1.val.2.val < Fintype.card α := lt_of_le_of_lt hnr ht
  refine (insertion_difference_norm_le k.2 hs).trans ?_
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hr : (k.1.val.1.val : ℝ) + k.1.val.2.val ≤ t := by exact_mod_cast hnr
  have hn : 0 ≤ (k.1.val.1.val : ℝ) + k.1.val.2.val := by positivity
  nlinarith

end
end ICO.MHBoundedRecording

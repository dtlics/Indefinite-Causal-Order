import ICO.RecordingFreshOutput
import ICO.RecordingMultisetBridge
import ICO.RecordingOracleChannel

/-!
# The visible one-wrapper bound

We identify the growing insertion's Kraus coefficients after copying the
query, and combine its fresh-output estimate with the exact lost-memory
cost. All states remain subnormalized; no postselection is introduced.
-/

namespace ICO.RecordingWrapperDistance

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingFreshOutput ICO.RecordingDistance
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {α μ : Type*} [Fintype α] [DecidableEq α] [Fintype μ] [DecidableEq μ]

/-- A matrix element of copying the input query, then applying the actual
    left insertion, with the private labels arranged as `(copy, R, L)`. -/
def copiedLeftKraus (m : ℕ) (e : α × Relation α α × Relation α α)
    (y : α) (s : ActiveSource α m) : ℂ :=
  if e.1 = s.val.val.1 then leftInsertion (y, e.2.2, e.2.1) s.val.val else 0

omit [Fintype μ] [DecidableEq μ] in
theorem copiedLeftKraus_eq_recordingKraus (m : ℕ) (hm : m < Fintype.card α) :
    copiedLeftKraus (α := α) m =
      recordingKraus (activeEnvironment m) (freshAmplitude (outputForbidden m)) := by
  funext e y s
  rcases e with ⟨c, r, l⟩
  have hs : s.val.val.2.1.card + s.val.val.2.2.card < Fintype.card α :=
    lt_of_le_of_lt s.property hm
  have hf : FreshRight y (s.val.val.2.1 ∪ s.val.val.2.2) ↔
      y ∉ outputForbidden m s :=
    ICO.RecordingMultisetBridge.freshRight_iff_not_mem_image _ _
  by_cases hy : y ∈ outputForbidden m s
  · have hnf : ¬ FreshRight y (s.val.val.2.1 ∪ s.val.val.2.2) :=
      fun h => (hf.mp h) hy
    simp [copiedLeftKraus, leftInsertion, LeftStep, hnf, recordingKraus,
      freshAmplitude, hy]
  · have hyf := hf.mpr hy
    by_cases hc : c = s.val.val.1 <;>
      by_cases hr : r = s.val.val.2.2 <;>
      by_cases hl : l = insert (s.val.val.1, y) s.val.val.2.1 <;>
      simp [copiedLeftKraus, leftInsertion, LeftStep, hs, hyf, hc, hr, hl,
        recordingKraus, activeEnvironment, environment, freshAmplitude,
        outputForbidden, eq_comm]
    intro x hx
    exact (hyf x (Finset.mem_union.mpr hx)).elim

theorem copiedLeft_fresh_distance (m : ℕ) (hm : m < Fintype.card α)
    (ρ : CMatrix (ActiveSource α m × μ)) (hρ : ρ.PosSemidef) (hmass : ρ.trace.re ≤ 1) :
    normalizedTraceDistance
      (MatrixMap.kron (MatrixMap.ofKraus (copiedLeftKraus m))
        (Channel.idChannel μ).map ρ)
      (memoryOutput (fun _ : α => 1 / (Fintype.card α : ℝ)) (QIT.partialTraceA ρ)) ≤
      (m : ℝ) / (Fintype.card α : ℝ) := by
  rw [copiedLeftKraus_eq_recordingKraus m hm]
  exact active_recording_fresh_distance m hm ρ hρ hmass

def uniformOutput (T : CMatrix μ) : CMatrix (α × μ) :=
  memoryOutput (fun _ : α => 1 / (Fintype.card α : ℝ)) T

omit [Fintype μ] [DecidableEq μ] in
theorem uniformOutput_sub (T S : CMatrix μ) :
    uniformOutput (α := α) (T - S) = uniformOutput T - uniformOutput S := by
  unfold uniformOutput memoryOutput
  simp_rw [smul_sub]
  exact QIT.Classical.blockDiagonal_sub _ _

omit [DecidableEq μ] in
theorem uniformOutput_posSemidef (T : CMatrix μ) (hT : T.PosSemidef) :
    (uniformOutput (α := α) T).PosSemidef := by
  apply QIT.Classical.blockDiagonal_posSemidef
  intro x
  apply hT.smul
  exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / (Fintype.card α : ℝ))

omit [DecidableEq μ] in
theorem uniformOutput_trace (hα : 0 < Fintype.card α) (T : CMatrix μ) :
    (uniformOutput (α := α) T).trace = T.trace := by
  have hd : (Fintype.card α : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hα
  simp only [uniformOutput, memoryOutput, QIT.Classical.blockDiagonal_trace,
    Matrix.trace_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  field_simp

/-- Replacing a positive lost-memory block by uniform output costs precisely
    one half of its lost trace, including subnormalized inputs. -/
theorem uniformOutput_loss_distance (hα : 0 < Fintype.card α)
    (before after : CMatrix μ) (hloss : (before - after).PosSemidef) :
    normalizedTraceDistance (uniformOutput (α := α) after) (uniformOutput before) =
      (before.trace.re - after.trace.re) / 2 := by
  have hp : (uniformOutput (α := α) before - uniformOutput after).PosSemidef := by
    rw [← uniformOutput_sub]
    exact uniformOutput_posSemidef _ hloss
  rw [distance_of_positive_loss _ _ hp, uniformOutput_trace hα, uniformOutput_trace hα]

/-- The finite growing wrapper obeys the advertised local estimate once the
    actual inverse operation's positive lost-memory marginal is supplied.
    `inverseRecording_lost_memory` establishes that positivity for V†. -/
theorem copiedLeft_with_lost_memory (m : ℕ) (hm : m < Fintype.card α)
    (ρ : CMatrix (ActiveSource α m × μ)) (hρ : ρ.PosSemidef) (hmass : ρ.trace.re ≤ 1)
    (before : CMatrix μ) (hloss : (before - QIT.partialTraceA ρ).PosSemidef) :
    normalizedTraceDistance
      (MatrixMap.kron (MatrixMap.ofKraus (copiedLeftKraus m))
        (Channel.idChannel μ).map ρ) (uniformOutput before) ≤
      (m : ℝ) / (Fintype.card α : ℝ) + (before.trace.re - ρ.trace.re) / 2 := by
  have htri := normalizedTraceDistance_triangle
    (MatrixMap.kron (MatrixMap.ofKraus (copiedLeftKraus m))
      (Channel.idChannel μ).map ρ)
    (uniformOutput (QIT.partialTraceA ρ)) (uniformOutput before)
  have hf := copiedLeft_fresh_distance m hm ρ hρ hmass
  have hl := uniformOutput_loss_distance (α := α) (lt_of_le_of_lt (Nat.zero_le m) hm)
    before (QIT.partialTraceA ρ) hloss
  rw [QIT.partialTraceA_trace] at hl
  rw [hl] at htri
  exact le_trans htri (add_le_add hf (le_refl _))

end
end ICO.RecordingWrapperDistance

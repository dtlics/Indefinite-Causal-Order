import ICO.PureHybrid
import ICO.RecordingDistance

/-! Final comparison of the Haar, recording, modified-recording, and
depolarizing states. The Haar-to-recording bound remains an explicit premise
until the separate analytic theorem is proved. -/

namespace ICO.RecordingCombination

open Matrix QIT
open scoped ComplexOrder MatrixOrder

noncomputable section

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem trace_difference_le_distance (H M : CMatrix a) :
    |H.trace.re - M.trace.re| ≤ 2 * normalizedTraceDistance H M := by
  have h := (Complex.abs_re_le_norm (H - M).trace).trans
    (QIT.trace_abs_le_traceNorm (H - M))
  simpa [Matrix.trace_sub, normalizedTraceDistance, traceNormDistance] using h

theorem lost_mass_from_distance (H M : CMatrix a) (hH : H.trace.re = 1)
    (δ : ℝ) (hδ : normalizedTraceDistance H M ≤ δ) :
    1 - M.trace.re ≤ 2 * δ := by
  have h := trace_difference_le_distance H M
  rw [hH] at h
  have habs := le_abs_self (1 - M.trace.re)
  linarith

theorem haar_recording_modified_comparison (H V M D : CMatrix a)
    (hH : H.trace.re = 1) (ε η q d : ℝ)
    (hHV : normalizedTraceDistance H V ≤ ε)
    (hVM : normalizedTraceDistance V M ≤ η)
    (hMD : normalizedTraceDistance M D ≤ q ^ 2 / d + (1 - M.trace.re) / 2) :
    normalizedTraceDistance H D ≤ 2 * ε + 2 * η + q ^ 2 / d := by
  have hHM : normalizedTraceDistance H M ≤ ε + η :=
    (normalizedTraceDistance_triangle H V M).trans (add_le_add hHV hVM)
  have hloss := lost_mass_from_distance H M hH (ε + η) hHM
  have htri := normalizedTraceDistance_triangle H M D
  linarith

#print axioms haar_recording_modified_comparison

end
end ICO.RecordingCombination

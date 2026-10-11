import ICO.HaarLink

/-!+# The causal reverse-composition test

This module combines the Haar-frame estimate, the explicit positive link,
and the causal trace constraint. `reverseTest` is constructed from the two
independent frames by the Bell contraction and the Choi factor `1/d²`.
The separate operational bridge must still identify a circuit's average
entanglement fidelity with this matrix trace pairing.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.CausalReverse ICO.HaarFrame ICO.HaarLink

namespace ICO.ReverseFidelity

set_option maxHeartbeats 1500000

noncomputable section

universe u
variable {A : Type u} [Fintype A] [DecidableEq A]

theorem tracePair_add_right {N : Type*} [Fintype N] (C X Y : CMatrix N) :
    tracePair C (X + Y) = tracePair C X + tracePair C Y := by
  simp [tracePair, Matrix.mul_add, Matrix.trace_add]

theorem tracePair_real_smul_right {N : Type*} [Fintype N]
    (C X : CMatrix N) (r : ℝ) :
    tracePair C ((r : ℂ) • X) = r * tracePair C X := by
  simp only [tracePair, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem tracePair_identity {N : Type*} [Fintype N] [DecidableEq N] (C : CMatrix N) :
    tracePair C 1 = C.trace.re := by simp [tracePair]

/-- Linked independent Haar frames with normalized input/target Choi states. -/
def reverseTest [Nonempty A] : CMatrix (SixWires A) :=
  ((((Fintype.card A : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) •
    link (Matrix.kronecker (haarFrame (A := A)) (haarFrame (A := A)))

/-- The explicit four-term positive upper envelope from linking the frame bounds. -/
def reverseEnvelope [Nontrivial A] : CMatrix (SixWires A) :=
  ((((Fintype.card A : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
    (tripleBell + (frameBeta A : ℂ) • singleBellBF +
      (frameBeta A : ℂ) • singleBellPC +
        (((Fintype.card A : ℝ) ^ 2 * frameBeta A ^ 2 : ℝ) : ℂ) • 1)

theorem reverseTest_pos [Nontrivial A] : (reverseTest (A := A)).PosSemidef := by
  have hs : (0 : ℂ) ≤ ((((Fintype.card A : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast (by positivity : 0 ≤ ((Fintype.card A : ℝ) ^ 2)⁻¹)
  exact (link_pos ((haarFrame_pos (A := A)).kronecker (haarFrame_pos (A := A)))).smul hs

theorem frameUpper_tensor_expansion [Nontrivial A] :
    Matrix.kronecker (frameUpper (A := A)) (frameUpper (A := A)) =
      Matrix.kronecker (frameMain (A := A)) (frameMain (A := A)) +
        (frameBeta A : ℂ) • Matrix.kronecker (frameMain (A := A)) (1 : CMatrix (FrameWires A)) +
        (frameBeta A : ℂ) • Matrix.kronecker (1 : CMatrix (FrameWires A)) (frameMain (A := A)) +
        (frameBeta A : ℂ) ^ 2 • Matrix.kronecker (1 : CMatrix (FrameWires A)) (1 : CMatrix (FrameWires A)) := by
  ext i j
  simp only [frameUpper, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Linking the two upper frames gives precisely the four terms of the envelope. -/
theorem linked_upper_eq_envelope [Nontrivial A] :
    ((((Fintype.card A : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) •
      link (Matrix.kronecker (frameUpper (A := A)) (frameUpper (A := A))) =
        reverseEnvelope (A := A) := by
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [frameUpper_tensor_expansion]
  simp only [link_add, link_smul,
    link_main_main, link_main_identity, link_identity_main, link_identity_identity]
  ext i j
  simp [reverseEnvelope, Matrix.smul_apply, smul_eq_mul]
  field_simp [hd]
  <;> ring

/-- Actual operator comparison before any trace or comb hypothesis is imposed. -/
theorem reverseTest_le_envelope [Nontrivial A] :
    reverseTest (A := A) ≤ reverseEnvelope := by
  have h := cMatrix_ofReal_smul_le_smul
    (by positivity : 0 ≤ ((Fintype.card A : ℝ) ^ 2)⁻¹)
    (link_mono (two_frames_le_upper (A := A)))
  rw [linked_upper_eq_envelope] at h
  exact h

/-- Matrix form of the reverse-fidelity bound for a positive ordered
component. The trace of the completed parent fixes its mass. -/
theorem causal_reverse_test_bound [Nontrivial A]
    (C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    tracePair C reverseTest ≤
      (C.trace.re / (Fintype.card A : ℝ) ^ 3) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  have hlead := causal_tripleBell_bound_trace C C₂ hC hC₂ hcausal
  have hbf : tracePair C (singleBellBF (A := A)) ≤ C.trace.re := by
    simpa [tracePair] using tracePair_mono_right hC (singleBellBF_le_one (A := A))
  have hpc : tracePair C (singleBellPC (A := A)) ≤ C.trace.re := by
    simpa [tracePair] using tracePair_mono_right hC (singleBellPC_le_one (A := A))
  have hβ := frameBeta_nonneg (A := A)
  have hdpos : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd := ne_of_gt hdpos
  have hden : (Fintype.card A : ℝ) ^ 2 - 1 ≠ 0 := by
    have hdgt : 1 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := A)
    nlinarith
  calc
    tracePair C reverseTest ≤ tracePair C reverseEnvelope :=
      tracePair_mono_right hC (reverseTest_le_envelope (A := A))
    _ = ((Fintype.card A : ℝ) ^ 3)⁻¹ *
        (tracePair C tripleBell + frameBeta A * tracePair C singleBellBF +
          frameBeta A * tracePair C singleBellPC +
            ((Fintype.card A : ℝ) ^ 2 * frameBeta A ^ 2) * C.trace.re) := by
      simp only [reverseEnvelope, tracePair_real_smul_right, tracePair_add_right,
        tracePair_identity]
    _ ≤ ((Fintype.card A : ℝ) ^ 3)⁻¹ *
        (C.trace.re / (Fintype.card A : ℝ) ^ 2 + frameBeta A * C.trace.re +
          frameBeta A * C.trace.re +
            ((Fintype.card A : ℝ) ^ 2 * frameBeta A ^ 2) * C.trace.re) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (add_le_add (add_le_add hlead (mul_le_mul_of_nonneg_left hbf hβ))
          (mul_le_mul_of_nonneg_left hpc hβ)) le_rfl
    _ = _ := by
      unfold frameBeta
      field_simp [hd, hden]
      <;> ring

/-- A selected final outcome inherits the bound from its completed parent,
without treating the selected outcome as a causally normalized comb. -/
theorem outcome_reverse_test_bound [Nontrivial A]
    (Cout C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hparent : Cout ≤ C) (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    tracePair Cout reverseTest ≤
      (C.trace.re / (Fintype.card A : ℝ) ^ 3) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  exact (outcome_test_le_parent (reverseTest_pos (A := A)) hparent).trans
    (causal_reverse_test_bound C C₂ hC hC₂ hcausal)

end

end ICO.ReverseFidelity

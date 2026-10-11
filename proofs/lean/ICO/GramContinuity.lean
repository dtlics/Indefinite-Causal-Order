import ICO.GramAverage

namespace ICO.GramWitness
open Matrix QIT
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 600000
variable {H I Ω : Type} [Fintype H] [DecidableEq H] [Nonempty H]
  [Fintype I] [DecidableEq I] [Nonempty I] [TopologicalSpace Ω]

theorem switchColumns_continuous (X Y : Ω → Matrix H I ℂ)
    (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun ω => switchColumns (X ω) (Y ω)) := by
  apply continuous_pi
  intro hb
  apply continuous_pi
  intro i
  cases h : hb.2 <;> simp only [switchColumns, h, Bool.false_eq_true, ↓reduceIte]
  · exact Continuous.const_mul (hX.matrix_elem hb.1 i) _
  · exact Continuous.const_mul (hY.matrix_elem hb.1 i) _

theorem frame_continuous (Z : Ω → Matrix H I ℂ) (hZ : Continuous Z) :
    Continuous (fun ω => frame (Z ω)) := hZ.matrix_mul hZ.matrix_conjTranspose

theorem effect_continuous (Z : Ω → Matrix H I ℂ) (hZ : Continuous Z) :
    Continuous (fun ω => effect (Z ω)) := by
  have hF := frame_continuous Z hZ
  have hs : Continuous (fun ω => scale (Z ω)) := continuous_const.max hF.norm
  have hi := hs.inv₀ (fun ω => ne_of_gt (scale_pos (Z ω)))
  exact (Complex.continuous_ofReal.comp hi).smul hF

theorem ideal_matrix_continuous (Z : Ω → Matrix H I ℂ) (hZ : Continuous Z)
    (hdiag : ∀ ω i, gram (Z ω) i i = 1) :
    Continuous (fun ω => (idealState (Z ω) (hdiag ω)).matrix) :=
  (frame_continuous Z hZ).const_smul _

theorem witness_acceptance_continuous (Z : Ω → Matrix H I ℂ) (ρ : Ω → State H)
    (hZ : Continuous Z) (hρ : Continuous (fun ω => (ρ ω).matrix)) :
    Continuous (fun ω => ((witnessTest (Z ω)).acceptProb (ρ ω) : ℝ)) := by
  simp only [BinaryHypothesisTest.acceptProb_eq_trace_re, BinaryHypothesisTest.acceptRhoEffect,
    witnessTest, Bool.cond_true]
  exact Complex.continuous_re.comp ((hρ.matrix_mul (effect_continuous Z hZ)).matrix_trace)

end
end ICO.GramWitness

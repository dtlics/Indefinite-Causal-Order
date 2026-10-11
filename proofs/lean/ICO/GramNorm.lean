import ICO.GramWitness
import QIT.States.TraceNorm.Spectral

namespace ICO.GramWitness
open Matrix QIT ICO.CausalReverse MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 0
local instance normMatrixNonUnitalCStar (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance normMatrixCStar (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩
variable {H I : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
  [Fintype I] [DecidableEq I] [Nonempty I]

theorem effect_le_frame (Z : Matrix H I ℂ) : effect Z ≤ frame Z := by
  have hs := scale_pos Z
  have hdiv : 1 / scale Z ≤ 1 := (div_le_one hs).2 (le_max_left _ _)
  have hnonneg : 0 ≤ 1 - (scale Z)⁻¹ := by simpa only [one_div] using sub_nonneg.mpr hdiv
  rw [Matrix.le_iff]
  have hh := (frame_pos Z).smul (show (0 : ℂ) ≤ ((1 - (scale Z)⁻¹ : ℝ) : ℂ) by
    exact_mod_cast hnonneg)
  convert hh using 1
  ext i j
  simp only [effect, Matrix.sub_apply, Matrix.smul_apply, Complex.ofReal_sub,
    Complex.ofReal_one, smul_eq_mul, sub_mul, one_mul]

theorem positive_pair_le_norm_trace (G ρ : CMatrix H)
    (hG : G.PosSemidef) (hρ : ρ.PosSemidef) :
    tracePair ρ G ≤ ‖G‖ * ρ.trace.re := by
  have hle := (CStarAlgebra.norm_le_iff_le_algebraMap G (norm_nonneg G) hG.nonneg).mp
    (le_refl ‖G‖)
  have hh := tracePair_mono_right hρ hle
  simpa [tracePair, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
    Matrix.trace_smul] using hh

theorem norm_sq_le_hilbertSchmidtSq (G : CMatrix I) : ‖G‖ ^ 2 ≤ hilbertSchmidtSq G := by
  have hh := QIT.State.norm_le_trace_re_mul_norm_one_of_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self G)
  simpa only [Matrix.l2_opNorm_conjTranspose_mul_self, norm_one, mul_one,
    pow_two, hilbertSchmidtSq] using hh

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem mean_ideal_acceptance_ge_one_sub_defect (Z : Ω → Matrix H I ℂ)
    (hdiag : ∀ ω i, gram (Z ω) i i = 1)
    (haccept : Integrable (fun ω =>
      ((witnessTest (Z ω)).acceptProb (idealState (Z ω) (hdiag ω)) : ℝ)) μ)
    (hdefect : Integrable (fun ω => ‖gram (Z ω) - 1‖) μ) :
    1 - (∫ ω, ‖gram (Z ω) - 1‖ ∂μ) ≤
      ∫ ω, ((witnessTest (Z ω)).acceptProb (idealState (Z ω) (hdiag ω)) : ℝ) ∂μ := by
  have hh := integral_mono ((integrable_const (1 : ℝ)).sub hdefect) haccept
    (fun ω => ideal_acceptance_ge_one_sub_defect (Z ω) (hdiag ω))
  simpa [integral_sub (integrable_const (1 : ℝ)) hdefect] using hh

#print axioms effect_le_frame
#print axioms positive_pair_le_norm_trace
#print axioms norm_sq_le_hilbertSchmidtSq
#print axioms mean_ideal_acceptance_ge_one_sub_defect
end
end ICO.GramWitness

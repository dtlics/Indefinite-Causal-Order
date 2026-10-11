import ICO.MHControlledMixture
import ICO.MHOutputMixture

/-! The actual uniform phase-permutation purification erases to the Haar
output mixture after the two external Haar rotations. -/
namespace ICO.MHHaarPurifiedMixture
open Matrix QIT MeasureTheory ICO.PureHybrid ICO.MHPhasePermutation
  ICO.MHControlledMixture ICO.MHOutputMixture ICO.MHHaarAbsorption
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
variable {A H O : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]

local instance cmContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

def purifiedResponse (f : Matrix.unitaryGroup A ℂ → EuclideanSpace ℂ H)
    (C D : Matrix.unitaryGroup A ℂ) : EuclideanSpace ℂ (H × ICO.MHTernaryCompression.Environment A) :=
  WithLp.toLp 2 (fun o => uniformAmplitude (A := A) * f (D*phaseOracleUnitary o.2*C) o.1)

theorem erased_response (f : Matrix.unitaryGroup A ℂ → EuclideanSpace ℂ H)
    (C D : Matrix.unitaryGroup A ℂ) :
    partialTraceB (outer (purifiedResponse f C D) (purifiedResponse f C D)) =
      (Fintype.card (ICO.MHTernaryCompression.Environment A) : ℂ)⁻¹ •
        ∑ e, outer (f (D*phaseOracleUnitary e*C)) (f (D*phaseOracleUnitary e*C)) := by
  simpa only [purifiedResponse,uniformAmplitude_square,WithLp.toLp_ofLp] using
    erase_uniform_fibers (fun e h => f (D*phaseOracleUnitary e*C) h) (uniformAmplitude (A := A))

theorem erased_haar_one (Φ : MatrixMap H O)
    (f : Matrix.unitaryGroup A ℂ → EuclideanSpace ℂ H) (hf : Continuous f)
    (D : Matrix.unitaryGroup A ℂ) :
    (∫ C, Φ (partialTraceB (outer (purifiedResponse f C D) (purifiedResponse f C D)))
      ∂unitaryHaarMeasure (a := A)) =
      ∫ U, Φ (outer (f U) (f U)) ∂unitaryHaarMeasure (a := A) := by
  have hF : Continuous (fun U => Φ (outer (f U) (f U))) :=
    Φ.continuous_of_finiteDimensional.comp (outer_continuous f hf)
  have hint (e : ICO.MHTernaryCompression.Environment A) :
      Integrable (fun C : Matrix.unitaryGroup A ℂ =>
        Φ (outer (f (D*phaseOracleUnitary e*C)) (f (D*phaseOracleUnitary e*C))))
        (unitaryHaarMeasure (a := A)) :=
    (hF.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [erased_response,map_smul,map_sum]
  rw [integral_smul,integral_finset_sum _ (fun e _ => hint e)]
  have he (e : ICO.MHTernaryCompression.Environment A) :
      (∫ C, Φ (outer (f (D*phaseOracleUnitary e*C)) (f (D*phaseOracleUnitary e*C)))
        ∂unitaryHaarMeasure (a := A)) =
        ∫ U, Φ (outer (f U) (f U)) ∂unitaryHaarMeasure (a := A) :=
    fixed_absorption D (phaseOracleUnitary e) (fun U => Φ (outer (f U) (f U)))
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := ICO.MHTernaryCompression.Environment A)),one_smul]

theorem erased_haar_two (Φ : MatrixMap H O)
    (f : Matrix.unitaryGroup A ℂ → EuclideanSpace ℂ H) (hf : Continuous f) :
    (∫ D, ∫ C, Φ (partialTraceB (outer (purifiedResponse f C D) (purifiedResponse f C D)))
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) =
      ∫ U, Φ (outer (f U) (f U)) ∂unitaryHaarMeasure (a := A) := by
  simp_rw [erased_haar_one Φ f hf]
  simp

#print axioms erased_response
#print axioms erased_haar_two
end
end ICO.MHHaarPurifiedMixture


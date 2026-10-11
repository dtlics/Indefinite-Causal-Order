import ICO.MHHaarAbsorption
import ICO.MHProfileTwirl
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Exact double-Haar inversion/swap and fixed-unitary conjugation transport. -/
namespace ICO.MHHaarInverseTransport
open Matrix QIT MeasureTheory ICO.MHProfileTwirl
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1400000
variable {A H : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype H] [DecidableEq H]

local instance cmContinuousENorm {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

local instance haar_isHaar : (unitaryHaarMeasure (a := A)).IsHaarMeasure := by
  dsimp [unitaryHaarMeasure]
  infer_instance

theorem probability_left_unique (ν : Measure (Matrix.unitaryGroup A ℂ))
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] : ν=unitaryHaarMeasure (a := A) := by
  have h := Measure.isMulLeftInvariant_eq_smul ν (unitaryHaarMeasure (a := A))
  have hc := congrArg (fun μ : Measure (Matrix.unitaryGroup A ℂ) => μ Set.univ) h
  have hs : Measure.haarScalarFactor ν (unitaryHaarMeasure (a := A))=1 := by
    simpa using hc.symm
  simpa [hs] using h

instance haar_isMulRightInvariant : (unitaryHaarMeasure (a := A)).IsMulRightInvariant := by
  constructor
  intro U
  haveI : IsProbabilityMeasure ((unitaryHaarMeasure (a := A)).map (fun x => x*U)) :=
    ⟨by rw [Measure.map_apply (measurable_mul_const U) MeasurableSet.univ]; simp⟩
  apply probability_left_unique

instance haar_isInvInvariant : (unitaryHaarMeasure (a := A)).IsInvInvariant := by
  constructor
  haveI : IsProbabilityMeasure (unitaryHaarMeasure (a := A)).inv := ⟨by simp⟩
  apply probability_left_unique

theorem haar_integral_inverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Matrix.unitaryGroup A ℂ → E) :
    (∫ U, f U⁻¹ ∂unitaryHaarMeasure (a := A))=∫ U, f U ∂unitaryHaarMeasure (a := A) :=
  integral_inv_eq_self f (unitaryHaarMeasure (a := A))

theorem double_inverse_swap (F : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ → CMatrix H)
    (hF : Continuous F) :
    (∫ D, ∫ C, F (D⁻¹,C⁻¹) ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) =
      ∫ D, ∫ C, F (C,D) ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A) := by
  have he (D : Matrix.unitaryGroup A ℂ) :
      (∫ C, F (D⁻¹,C⁻¹) ∂unitaryHaarMeasure (a := A)) =
        ∫ C, F (D⁻¹,C) ∂unitaryHaarMeasure (a := A) :=
    haar_integral_inverse (fun C => F (D⁻¹,C))
  simp_rw [he]
  rw [haar_integral_inverse (fun D => ∫ C, F (D,C) ∂unitaryHaarMeasure (a := A))]
  exact integral_integral_swap (hF.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := (unitaryHaarMeasure (a := A)).prod (unitaryHaarMeasure (a := A))))

theorem double_compression (S : CMatrix H)
    (F : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ → CMatrix H) (hF : Continuous F) :
    (∫ D, ∫ C, S.conjTranspose*F (C,D)*S
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) =
      S.conjTranspose*(∫ D, ∫ C, F (C,D)
        ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A))*S := by
  have hc (D : Matrix.unitaryGroup A ℂ) : Continuous (fun C => F (C,D)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have he (D : Matrix.unitaryGroup A ℂ) :
      (∫ C, S.conjTranspose*F (C,D)*S ∂unitaryHaarMeasure (a := A)) =
        S.conjTranspose*(∫ C, F (C,D) ∂unitaryHaarMeasure (a := A))*S :=
    (compressionCLM S).integral_comp_comm ((hc D).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := unitaryHaarMeasure (a := A)))
  simp_rw [he]
  have hinner : Continuous (fun D => ∫ C, F (C,D) ∂unitaryHaarMeasure (a := A)) := by
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous (μ := unitaryHaarMeasure (a := A))
        (f := fun D C => F (C,D)) (hF.comp (continuous_snd.prodMk continuous_fst)) isCompact_univ
  exact (compressionCLM S).integral_comp_comm (hinner.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := unitaryHaarMeasure (a := A)))

theorem inverse_swap_compression (S : CMatrix H)
    (F : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ → CMatrix H) (hF : Continuous F) :
    (∫ D, ∫ C, S.conjTranspose*F (D⁻¹,C⁻¹)*S
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) =
      S.conjTranspose*(∫ D, ∫ C, F (C,D)
        ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A))*S := by
  have hc : Continuous (fun p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ => F (p.2⁻¹,p.1⁻¹)) :=
    hF.comp (continuous_snd.inv.prodMk continuous_fst.inv)
  rw [double_compression S _ hc]
  rw [double_inverse_swap F hF]

#print axioms inverse_swap_compression
end
end ICO.MHHaarInverseTransport


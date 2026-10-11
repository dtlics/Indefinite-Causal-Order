import ICO.QuantumDecision
import ICO.MHTraceIntegral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Actual averaged quantum states and Born acceptance probabilities. -/
namespace ICO.BornAverage
open Matrix QIT MeasureTheory ICO.MHTraceIntegral ICO.QuantumDecision
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {H Ω : Type*} [Fintype H] [DecidableEq H]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
local instance matrixNonUnitalCStar : NonUnitalCStarAlgebra (CMatrix H) := ⟨⟩
local instance cmContinuousENorm : ContinuousENorm (CMatrix H) := SeminormedAddGroup.toContinuousENorm

def averageState (F : Ω→State H) (hF : Integrable (fun ω => (F ω).matrix) μ) : State H where
  matrix := ∫ω,(F ω).matrix ∂μ
  pos := Matrix.nonneg_iff_posSemidef.mp (integral_nonneg (fun ω => (F ω).pos.nonneg))
  trace_eq_one := by
    have ht := (traceMulCLM (1 : CMatrix H)).integral_comp_comm hF
    change (∫ω,((F ω).matrix*1).trace ∂μ)=((∫ω,(F ω).matrix ∂μ)*1).trace at ht
    simp only [Matrix.mul_one] at ht
    rw [←ht]
    simp only [State.trace_eq_one,integral_const,probReal_univ,one_smul]

def acceptCLM (T : BinaryHypothesisTest H) : CMatrix H→L[ℝ]ℝ :=
  Complex.reCLM.comp ((traceMulCLM T.acceptRhoEffect).restrictScalars ℝ)

theorem accept_eq (T : BinaryHypothesisTest H) (ρ : State H) :
    acceptCLM T ρ.matrix=(T.acceptProb ρ : ℝ) := (T.acceptProb_eq_trace_re ρ).symm

theorem accept_average (T : BinaryHypothesisTest H) (F : Ω→State H)
    (hF : Integrable (fun ω => (F ω).matrix) μ) :
    (T.acceptProb (averageState F hF) : ℝ)=∫ω,(T.acceptProb (F ω):ℝ) ∂μ := by
  rw [←accept_eq]
  exact ((acceptCLM T).integral_comp_comm hF).symm.trans
    (integral_congr_ae (Filter.Eventually.of_forall (fun ω => accept_eq T (F ω))))

theorem accept_integrable (T : BinaryHypothesisTest H) (F : Ω→State H)
    (hF : Integrable (fun ω => (F ω).matrix) μ) :
    Integrable (fun ω => (T.acceptProb (F ω):ℝ)) μ := by
  exact ((acceptCLM T).integrable_comp hF).congr
    (Filter.Eventually.of_forall (fun ω => accept_eq T (F ω)))

theorem mean_accept_gap_le (T : BinaryHypothesisTest H) (F : Ω→State H) (σ : State H)
    (hF : Integrable (fun ω => (F ω).matrix) μ) :
    (∫ω,(T.acceptProb (F ω):ℝ) ∂μ)-(T.acceptProb σ:ℝ)≤
      QIT.normalizedTraceDistance (∫ω,(F ω).matrix ∂μ) σ.matrix := by
  rw [←accept_average T F hF]
  exact accept_gap_le_traceDistance T (averageState F hF) σ

theorem abs_mean_accept_gap_le (T : BinaryHypothesisTest H) (F : Ω→State H) (σ : State H)
    (hF : Integrable (fun ω => (F ω).matrix) μ) :
    |(∫ω,(T.acceptProb (F ω):ℝ) ∂μ)-(T.acceptProb σ:ℝ)|≤
      QIT.normalizedTraceDistance (∫ω,(F ω).matrix ∂μ) σ.matrix := by
  have hf := mean_accept_gap_le T F σ hF
  have hr := accept_gap_le_traceDistance T σ (averageState F hF)
  rw [State.normalizedTraceDistance_comm,accept_average] at hr
  change (T.acceptProb σ:ℝ)-(∫ω,(T.acceptProb (F ω):ℝ) ∂μ)≤
    QIT.normalizedTraceDistance (∫ω,(F ω).matrix ∂μ) σ.matrix at hr
  exact abs_le.mpr ⟨by linarith, hf⟩

theorem mean_decision_impossible (T : BinaryHypothesisTest H) (F : Ω→State H) (σ : State H)
    (hF : Integrable (fun ω => (F ω).matrix) μ)
    (hhigh : ∀ω,(2/3:ℝ)≤(T.acceptProb (F ω):ℝ))
    (hlow : (T.acceptProb σ:ℝ)≤1/3) (δ : ℝ)
    (hδ : QIT.normalizedTraceDistance (∫ω,(F ω).matrix ∂μ) σ.matrix≤δ)
    (hsmall : δ<1/3) : False := by
  have hg := mean_accept_gap_le T F σ hF
  have hi := integral_mono (integrable_const (2/3:ℝ)) (accept_integrable T F hF) hhigh
  simp only [integral_const,probReal_univ,one_smul] at hi
  linarith

#print axioms mean_decision_impossible
end
end ICO.BornAverage

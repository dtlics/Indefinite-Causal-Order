import ICO.HaarSecondMoment
import Mathlib.MeasureTheory.Integral.Pi

/-! # Conditional integration of a finite independent Haar family -/

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory

namespace ICO.HaarFamily

set_option maxHeartbeats 400000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

abbrev Unitary := Matrix.unitaryGroup A ℂ

def familyMeasure (n : ℕ) : Measure (Fin n → Unitary (A := A)) :=
  Measure.pi (fun _ => unitaryHaarMeasure (a := A))

instance familyMeasure_probability (n : ℕ) : IsProbabilityMeasure (familyMeasure (A := A) n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => unitaryHaarMeasure (a := A))))

theorem integral_insertNth {n : ℕ} (i : Fin (n + 1))
    (f : (Fin (n + 1) → Unitary (A := A)) → ℝ) (hf : Continuous f) :
    (∫ W, f W ∂familyMeasure (A := A) (n + 1)) =
      ∫ rest : Fin n → Unitary (A := A),
        ∫ U : Unitary (A := A), f (i.insertNth U rest) ∂unitaryHaarMeasure (a := A)
        ∂familyMeasure (A := A) n := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Unitary (A := A)) i
  have hpres := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => unitaryHaarMeasure (a := A)) i).symm
  have hc : Continuous (fun p : Unitary (A := A) × (Fin n → Unitary (A := A)) =>
      f (i.insertNth p.1 p.2)) := hf.comp
        (Continuous.finInsertNth (A := fun _ => Unitary (A := A)) i continuous_fst continuous_snd)
  have hint := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (unitaryHaarMeasure (a := A)).prod (familyMeasure (A := A) n))
  calc
    _ = ∫ p : Unitary (A := A) × (Fin n → Unitary (A := A)),
        f (i.insertNth p.1 p.2)
        ∂(unitaryHaarMeasure (a := A)).prod (familyMeasure (A := A) n) := by
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, familyMeasure] using (hpres.integral_comp' f).symm
    _ = _ := integral_prod_symm _ hint

theorem integral_of_coordinate_average {n : ℕ} (i : Fin (n + 1))
    (f : (Fin (n + 1) → Unitary (A := A)) → ℝ) (hf : Continuous f)
    (c : ℝ) (hc : ∀ rest : Fin n → Unitary (A := A),
      (∫ U : Unitary (A := A), f (i.insertNth U rest) ∂unitaryHaarMeasure (a := A)) = c) :
    (∫ W, f W ∂familyMeasure (A := A) (n + 1)) = c := by
  rw [integral_insertNth i f hf]
  simp_rw [hc]
  simp

theorem normSq_trace_adjoint (X : CMatrix A) :
    Complex.normSq X.conjTranspose.trace = Complex.normSq X.trace := by
  rw [Matrix.trace_conjTranspose]
  exact Complex.normSq_conj _

theorem adjoint_trace_average (V : Unitary (A := A)) :
    (∫ U : Unitary (A := A),
      Complex.normSq ((U : CMatrix A).conjTranspose * (V : CMatrix A)).trace
      ∂unitaryHaarMeasure (a := A)) = 1 := by
  have hp (U : Unitary (A := A)) :
      Complex.normSq ((U : CMatrix A).conjTranspose * (V : CMatrix A)).trace =
        Complex.normSq (((V⁻¹ * U : Unitary (A := A)) : CMatrix A)).trace := by
    have h := normSq_trace_adjoint ((U : CMatrix A).conjTranspose * (V : CMatrix A))
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
      Matrix.star_eq_conjTranspose] using h.symm
  simp_rw [hp]
  exact ICO.HaarSecondMoment.translated_trace_normSq_average V⁻¹

end
end ICO.HaarFamily


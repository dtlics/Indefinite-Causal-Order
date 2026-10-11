import ICO.C6LabelSymmetry
import ICO.MHSpectatorTwirl
import ICO.MHTraceIntegral
import QIT.Util.SDP.HermitianPSDTraceDuality

/-! The equality-event bound for two labels in a commonly invariant state.
Spectators can rotate with the same unitary and contain arbitrary reference
systems. The Haar bound is imported as an actual matrix integral. -/

namespace ICO.C6InvariantTwirl
open QIT Matrix MeasureTheory ICO.EqualityTwirl ICO.MHSpectatorTwirl
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
universe u
variable {A Γ : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype Γ] [DecidableEq Γ]

local instance cmContinuousENorm {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

theorem invariant_trace_conjugation {H : Type u} [Fintype H] [DecidableEq H]
    (ω P R : CMatrix H) (hR : R * R.conjTranspose = 1) (hc : R * ω = ω * R) :
    (ω * (R.conjTranspose * P * R)).trace = (ω * P).trace := by
  have hconj : R * ω * R.conjTranspose = ω := by
    rw [hc, Matrix.mul_assoc, hR, Matrix.mul_one]
  calc
    _ = ((ω * R.conjTranspose * P) * R).trace := by congr 1; noncomm_ring
    _ = (R * (ω * R.conjTranspose * P)).trace := Matrix.trace_mul_comm _ _
    _ = ((R * ω * R.conjTranspose) * P).trace := by congr 1; noncomm_ring
    _ = _ := by rw [hconj]

def traceLeftCLM {H : Type u} [Fintype H] [DecidableEq H] (ω : CMatrix H) :
    CMatrix H →L[ℂ] ℂ :=
  ({ toFun := fun M => (ω * M).trace
     map_add' := by intros; simp [Matrix.mul_add, Matrix.trace_add]
     map_smul' := by intros; simp [Matrix.mul_smul, Matrix.trace_smul] } :
    CMatrix H →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem invariant_equality_trace_le (ω : CMatrix (Γ × (A × A)))
    (hpos : ω.PosSemidef)
    (S : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Γ ℂ)
    (hinv : ∀ U : Matrix.unitaryGroup A ℂ,
      Matrix.kronecker (S U : CMatrix Γ) (sameTensor U) * ω =
        ω * Matrix.kronecker (S U : CMatrix Γ) (sameTensor U)) :
    (ω * lift (Γ := Γ) (equalityProjector (A := A))).trace.re ≤
      (2 / ((Fintype.card A : ℝ) + 1)) * ω.trace.re := by
  let P := lift (Γ := Γ) (equalityProjector (A := A))
  let R (U : Matrix.unitaryGroup A ℂ) := Matrix.kronecker (S U : CMatrix Γ) (sameTensor U)
  have hRR (U : Matrix.unitaryGroup A ℂ) : R U * (R U).conjTranspose = 1 := by
    apply Matrix.mem_unitaryGroup_iff.mp
    exact Matrix.kronecker_mem_unitary (S U).property
      (Matrix.kronecker_mem_unitary U.property U.property)
  have ht (U : Matrix.unitaryGroup A ℂ) :
      (ω * ((R U).conjTranspose * P * R U)).trace = (ω * P).trace :=
    invariant_trace_conjugation ω P (R U) (hRR U) (hinv U)
  have hi : Integrable (fun U : Matrix.unitaryGroup A ℂ => (R U).conjTranspose * P * R U)
      (unitaryHaarMeasure (a := A)) := by
    simp only [R, P, spectator_cancel]
    exact (lift_continuous.comp ((sameTensor_continuous.matrix_conjTranspose.matrix_mul
      continuous_const).matrix_mul sameTensor_continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmean : (ω * (∫ U : Matrix.unitaryGroup A ℂ,
      (R U).conjTranspose * P * R U ∂unitaryHaarMeasure (a := A))).trace = (ω * P).trace := by
    have he := (traceLeftCLM ω).integral_comp_comm hi
    change (∫ U : Matrix.unitaryGroup A ℂ,
      (ω * ((R U).conjTranspose * P * R U)).trace ∂unitaryHaarMeasure (a := A)) =
      (ω * (∫ U : Matrix.unitaryGroup A ℂ,
        (R U).conjTranspose * P * R U ∂unitaryHaarMeasure (a := A))).trace at he
    rw [← he]
    simp_rw [ht]
    simp
  have hle := cMatrix_trace_mul_le_of_le_posSemidef_left hpos
    (ICO.MHSpectatorTwirl.same_equality_twirl_le S)
  change (ω * (∫ U : Matrix.unitaryGroup A ℂ,
    (R U).conjTranspose * P * R U ∂unitaryHaarMeasure (a := A))).trace.re ≤ _ at hle
  rw [hmean] at hle
  simpa only [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hle

#print axioms invariant_equality_trace_le
end
end ICO.C6InvariantTwirl

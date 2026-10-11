import ICO.MHSpectatorTwirl
import ICO.MHWordRotation
import ICO.MHBellEntries

/-! Haar losses for the actual finite recording-word rotation. -/
namespace ICO.MHWordTwirl
open Matrix QIT MeasureTheory ICO.MHWordDistinct ICO.MHWordRotation
  ICO.EqualityTwirl ICO.MHSpectatorTwirl ICO.CausalReverse ICO.HaarFrame
  ICO.MHBellProjectors ICO.MHBellEntries ICO.HaarMoments
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A J : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype J] [DecidableEq J]

local instance cmContinuousENorm {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

def submatrixCLM {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Y → X) : CMatrix X →L[ℝ] CMatrix Y :=
  ({ toFun := fun M => M.submatrix e e
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : CMatrix X →ₗ[ℝ] CMatrix Y).toContinuousLinearMap

theorem integral_submatrix {X Y Ω : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → CMatrix X) (hF : Integrable F μ) (e : Y → X) :
    (∫ ω, (F ω).submatrix e e ∂μ) = (∫ ω, F ω ∂μ).submatrix e e :=
  (submatrixCLM e).integral_comp_comm hF

theorem reindex_mono {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {B C : CMatrix X} (h : B ≤ C) (e : Y → X) : B.submatrix e e ≤ C.submatrix e e := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.submatrix_sub] using (Matrix.le_iff.mp h).submatrix e

theorem equality_lift {Γ : Type} [Fintype Γ] [DecidableEq Γ] :
    equalityProjection (A := A) (Γ := Γ) = lift (Γ := Γ) (equalityProjector (A := A)) := by
  ext p q
  simp only [equalityProjection,equalityProjector,lift,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.diagonal_apply,Matrix.one_apply]
  by_cases hp : p=q
  · subst q; simp
  · by_cases h1 : p.1=q.1
    · have h2 : p.2≠q.2 := by intro h; exact hp (Prod.ext h1 h)
      simp [hp,h1,h2]
    · simp [hp,h1]

theorem bell_lift {Γ : Type} [Fintype Γ] [DecidableEq Γ] :
    bellProjection (A := A) (Γ := Γ) = lift (Γ := Γ) (bellMatrix A) := by
  ext p q
  simp only [bellProjection_apply,lift,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,bell_entry_delta,delta]
  by_cases h1 : p.1=q.1 <;> by_cases h2 : p.2.1=p.2.2 <;>
    by_cases h3 : q.2.1=q.2.2 <;> simp [h1,h2,h3,HaarMoments.delta]

theorem reindexed_same_twirl_le {Γ H : Type} [Fintype Γ] [DecidableEq Γ]
    [Fintype H] [DecidableEq H] (e : H ≃ Γ × (A × A))
    (S : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Γ ℂ) :
    (∫ U, ((Matrix.kronecker (S U : CMatrix Γ) (sameTensor U)).submatrix e e).conjTranspose *
      (lift (Γ := Γ) (equalityProjector (A := A))).submatrix e e *
      (Matrix.kronecker (S U : CMatrix Γ) (sameTensor U)).submatrix e e
        ∂unitaryHaarMeasure (a := A)) ≤
      (2 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix H) := by
  simp_rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  have hcont : Continuous (fun U : Matrix.unitaryGroup A ℂ => lift (Γ := Γ)
      ((sameTensor U).conjTranspose * equalityProjector (A := A) * sameTensor U)) :=
    lift_continuous.comp ((sameTensor_continuous.matrix_conjTranspose.matrix_mul
      continuous_const).matrix_mul sameTensor_continuous)
  have hi : Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      (Matrix.kronecker (S U : CMatrix Γ) (sameTensor U)).conjTranspose *
        lift (Γ := Γ) (equalityProjector (A := A)) *
        Matrix.kronecker (S U : CMatrix Γ) (sameTensor U)) (unitaryHaarMeasure (a := A)) := by
    simp_rw [spectator_cancel]
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_submatrix _ _ hi]
  have hh := reindex_mono (MHSpectatorTwirl.same_equality_twirl_le S) e
  simpa only [Matrix.submatrix_smul,Pi.smul_apply,Matrix.submatrix_one_equiv] using hh

theorem reindexed_conjugate_twirl_le {Γ H : Type} [Fintype Γ] [DecidableEq Γ]
    [Fintype H] [DecidableEq H] (e : H ≃ Γ × (A × A))
    (S : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Γ ℂ) :
    (∫ U, ((Matrix.kronecker (S U : CMatrix Γ) (conjugateTensor U)).submatrix e e).conjTranspose *
      (lift (Γ := Γ) (equalityProjector (A := A)-bellMatrix A)).submatrix e e *
      (Matrix.kronecker (S U : CMatrix Γ) (conjugateTensor U)).submatrix e e
        ∂unitaryHaarMeasure (a := A)) ≤
      (1 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix H) := by
  simp_rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  have hcont : Continuous (fun U : Matrix.unitaryGroup A ℂ => lift (Γ := Γ)
      ((conjugateTensor U).conjTranspose * (equalityProjector (A := A)-bellMatrix A) * conjugateTensor U)) :=
    lift_continuous.comp ((conjugateTensor_continuous.matrix_conjTranspose.matrix_mul
      continuous_const).matrix_mul conjugateTensor_continuous)
  have hi : Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      (Matrix.kronecker (S U : CMatrix Γ) (conjugateTensor U)).conjTranspose *
        lift (Γ := Γ) (equalityProjector (A := A)-bellMatrix A) *
        Matrix.kronecker (S U : CMatrix Γ) (conjugateTensor U)) (unitaryHaarMeasure (a := A)) := by
    simp_rw [spectator_cancel]
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_submatrix _ _ hi]
  have hh := reindex_mono (MHSpectatorTwirl.conjugate_complement_twirl_le S) e
  simpa only [Matrix.submatrix_smul,Pi.smul_apply,Matrix.submatrix_one_equiv] using hh

theorem left_slot_mean_le (R : Finset J) (D : Matrix.unitaryGroup A ℂ) (i : J) (hi : i ∉ R) :
    (∫ C, (turn R C D : CMatrix (WordBasis A J)).conjTranspose * slotEquality i *
      (turn R C D : CMatrix (WordBasis A J)) ∂unitaryHaarMeasure (a := A)) ≤
      (2 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix (WordBasis A J)) := by
  simp_rw [turn_left_split R _ D i hi,slotEquality,equality_lift]
  exact reindexed_same_twirl_le (slotEquiv i) _

theorem right_slot_mean_le (R : Finset J) (D : Matrix.unitaryGroup A ℂ) (i : J) (hi : i ∈ R) :
    (∫ C, (turn R C D : CMatrix (WordBasis A J)).conjTranspose * (slotEquality i-slotBell i) *
      (turn R C D : CMatrix (WordBasis A J)) ∂unitaryHaarMeasure (a := A)) ≤
      (1 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix (WordBasis A J)) := by
  have he : slotEquality (A := A) i-slotBell i =
      (lift (Γ := Spectator A i) (equalityProjector (A := A)-bellMatrix A)).submatrix
        (slotEquiv i) (slotEquiv i) := by
    rw [slotEquality,slotBell,equality_lift,bell_lift]
    ext p q
    simp [lift,Matrix.kronecker,Matrix.kroneckerMap_apply,mul_sub,Matrix.submatrix_apply]
  simp_rw [turn_right_split R _ D i hi,he]
  exact reindexed_conjugate_twirl_le (slotEquiv i) _

#print axioms left_slot_mean_le
#print axioms right_slot_mean_le
end
end ICO.MHWordTwirl


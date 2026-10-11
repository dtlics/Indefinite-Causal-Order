import ICO.EqualityTwirlNorm

/-! Local Haar twirls with arbitrary unitary spectator registers. The spectator
may depend on the same Haar unitary; its cancellation is pointwise. -/
namespace ICO.MHSpectatorTwirl
open Matrix QIT MeasureTheory ICO.EqualityTwirl ICO.HaarMoments ICO.HaarFrame ICO.CausalReverse
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
universe u
variable {A Γ H : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype Γ] [DecidableEq Γ] [Fintype H] [DecidableEq H]

local instance cmContinuousENorm {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm
local instance matrixNonUnitalCStar (n : Type u) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance matrixCStar (n : Type u) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩

def lift (B : CMatrix H) : CMatrix (Γ × H) := Matrix.kronecker 1 B

theorem spectator_cancel (S : Matrix.unitaryGroup Γ ℂ) (T B : CMatrix H) :
    (Matrix.kronecker (S : CMatrix Γ) T).conjTranspose * lift (Γ := Γ) B *
      Matrix.kronecker (S : CMatrix Γ) T = lift (Γ := Γ) (T.conjTranspose * B * T) := by
  simp only [lift, Matrix.conjTranspose_kronecker, Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one]
  have hs : (S : CMatrix Γ).conjTranspose * (S : CMatrix Γ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp S.property
  rw [hs]

theorem lift_continuous : Continuous (lift (Γ := Γ) (H := H)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_const.mul (continuous_apply j.2 |>.comp (continuous_apply i.2))

theorem matrix_integral_entry (F : Matrix.unitaryGroup A ℂ → CMatrix H)
    (hF : Continuous F) (i j : H) :
    (∫ U, F U ∂unitaryHaarMeasure (a := A)) i j =
      ∫ U, F U i j ∂unitaryHaarMeasure (a := A) := by
  have hint := hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := unitaryHaarMeasure (a := A))
  simpa [cMatrixEntryCLM] using ((cMatrixEntryCLM i j).integral_comp_comm hint).symm

theorem integral_lift (F : Matrix.unitaryGroup A ℂ → CMatrix H) (hF : Continuous F) :
    (∫ U, lift (Γ := Γ) (F U) ∂unitaryHaarMeasure (a := A)) =
      lift (Γ := Γ) (∫ U, F U ∂unitaryHaarMeasure (a := A)) := by
  ext i j
  have hc : Continuous (fun U => lift (Γ := Γ) (F U)) := lift_continuous.comp hF
  rw [matrix_integral_entry _ hc]
  simp only [lift, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [integral_const_mul, matrix_integral_entry F hF]

theorem same_equality_twirl (S : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Γ ℂ) :
    (∫ U, (Matrix.kronecker (S U : CMatrix Γ) (sameTensor U)).conjTranspose *
      lift (Γ := Γ) (equalityProjector (A := A)) *
      Matrix.kronecker (S U : CMatrix Γ) (sameTensor U) ∂unitaryHaarMeasure (a := A)) =
    lift (Γ := Γ) (((Fintype.card A : ℂ)+1)⁻¹ • (1 + swapMatrix (A := A))) := by
  simp_rw [spectator_cancel]
  rw [integral_lift _ (((sameTensor_continuous (A := A)).matrix_conjTranspose.matrix_mul
    continuous_const).matrix_mul sameTensor_continuous), ICO.EqualityTwirl.same_equality_twirl]

theorem conjugate_complement_twirl
    (S : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Γ ℂ) :
    (∫ U, (Matrix.kronecker (S U : CMatrix Γ) (conjugateTensor U)).conjTranspose *
      lift (Γ := Γ) (equalityProjector (A := A) - bellMatrix A) *
      Matrix.kronecker (S U : CMatrix Γ) (conjugateTensor U) ∂unitaryHaarMeasure (a := A)) =
    lift (Γ := Γ) (((Fintype.card A : ℂ)+1)⁻¹ • (1 - bellMatrix A)) := by
  simp_rw [spectator_cancel]
  rw [integral_lift _ (((conjugateTensor_continuous (A := A)).matrix_conjTranspose.matrix_mul
    continuous_const).matrix_mul conjugateTensor_continuous), conjugate_complement_equality_twirl]

theorem lift_mono {B C : CMatrix H} (h : B ≤ C) : lift (Γ := Γ) B ≤ lift C := by
  apply Matrix.le_iff.mpr
  have hp := (Matrix.PosSemidef.one (n := Γ) (R := ℂ)).kronecker (Matrix.le_iff.mp h)
  have he : Matrix.kronecker (1 : CMatrix Γ) (C-B) = lift (Γ := Γ) C - lift B := by
    ext i j
    simp [lift,Matrix.kronecker,Matrix.kroneckerMap_apply,mul_sub]
  change (Matrix.kronecker (1 : CMatrix Γ) (C-B)).PosSemidef at hp
  rwa [he] at hp

theorem lift_scalar (c : ℝ) : lift (Γ := Γ) (c • (1 : CMatrix H)) =
    c • (1 : CMatrix (Γ × H)) := by
  simp [lift, Matrix.kronecker_smul, Matrix.one_kronecker_one]

theorem hermitian_le_norm (B : CMatrix H) (hB : B.IsHermitian) : B ≤ ‖B‖ • (1 : CMatrix H) := by
  have hs : IsSelfAdjoint B := hB
  simpa only [Algebra.algebraMap_eq_smul_one] using hs.le_algebraMap_norm_self

theorem same_local_le :
    ((Fintype.card A : ℂ)+1)⁻¹ • (1 + swapMatrix (A := A)) ≤
      (2 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix (A × A)) := by
  have hh : (((Fintype.card A : ℂ)+1)⁻¹ • (1 + swapMatrix (A := A))).IsHermitian := by
    change _ = _
    simp [Matrix.conjTranspose_smul, swapMatrix_hermitian]
  apply (hermitian_le_norm _ hh).trans
  apply smul_le_smul_of_nonneg_right _ zero_le_one
  rw [← ICO.EqualityTwirl.same_equality_twirl]
  exact same_equality_twirl_norm_le

theorem conjugate_local_le :
    ((Fintype.card A : ℂ)+1)⁻¹ • (1 - bellMatrix A) ≤
      (1 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix (A × A)) := by
  have hh : (((Fintype.card A : ℂ)+1)⁻¹ • (1 - bellMatrix A)).IsHermitian := by
    change _ = _
    have hb : (bellMatrix A).conjTranspose = bellMatrix A := (bellMatrix_pos (A := A)).isHermitian
    simp [Matrix.conjTranspose_smul,hb]
  apply (hermitian_le_norm _ hh).trans
  apply smul_le_smul_of_nonneg_right _ zero_le_one
  rw [← conjugate_complement_equality_twirl]
  exact conjugate_complement_twirl_norm_le

theorem same_equality_twirl_le (S : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Γ ℂ) :
    (∫ U, (Matrix.kronecker (S U : CMatrix Γ) (sameTensor U)).conjTranspose *
      lift (Γ := Γ) (equalityProjector (A := A)) *
      Matrix.kronecker (S U : CMatrix Γ) (sameTensor U) ∂unitaryHaarMeasure (a := A)) ≤
    (2 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix (Γ × (A × A))) := by
  rw [same_equality_twirl, ← lift_scalar]
  exact lift_mono same_local_le

theorem conjugate_complement_twirl_le
    (S : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Γ ℂ) :
    (∫ U, (Matrix.kronecker (S U : CMatrix Γ) (conjugateTensor U)).conjTranspose *
      lift (Γ := Γ) (equalityProjector (A := A) - bellMatrix A) *
      Matrix.kronecker (S U : CMatrix Γ) (conjugateTensor U) ∂unitaryHaarMeasure (a := A)) ≤
    (1 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix (Γ × (A × A))) := by
  rw [conjugate_complement_twirl, ← lift_scalar]
  exact lift_mono conjugate_local_le

#print axioms same_equality_twirl_le
#print axioms conjugate_complement_twirl_le
end
end ICO.MHSpectatorTwirl




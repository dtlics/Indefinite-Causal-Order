import ICO.C6MemoryNatural
import ICO.C6CacheDecode

/-! The invariant-label information bound for every actual known basis. -/
namespace ICO.C6BasisInvariant
open QIT Matrix ICO.C6MemoryNatural ICO.C6DephaseChannel ICO.C6BasisDephase
  ICO.C6MatrixCovariance ICO.MHWordRotation ICO.C6LabelSymmetry
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1200000
universe u
variable {A M Z : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype Z] [DecidableEq Z]

theorem depolarizing_unitary_conjugate (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup M ℂ) (X : CMatrix (A × M)) :
    (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map
      ((Matrix.kronecker (U : CMatrix A) (V : CMatrix M)).conjTranspose * X *
        Matrix.kronecker (U : CMatrix A) (V : CMatrix M)) =
    (Matrix.kronecker (U : CMatrix A) (V : CMatrix M)).conjTranspose *
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X *
        Matrix.kronecker (U : CMatrix A) (V : CMatrix M) := by
  have hp := partialTraceA_local_unitary_conj X U V
  simp only [Matrix.star_eq_conjTranspose] at hp
  rw [ICO.RecordingDepolarizing.withMemory_apply, hp,
    ICO.RecordingDepolarizing.withMemory_apply, uniformOutput_eq_kronecker,
    uniformOutput_eq_kronecker]
  have hu : (U : CMatrix A).conjTranspose * (U : CMatrix A) = 1 := U.property.1
  simp only [Matrix.kronecker, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, hu]

theorem invariant_depolarizing_conjugate (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup M ℂ) (X : CMatrix (A × M))
    (hX : Matrix.kronecker (U : CMatrix A) (V : CMatrix M) * X =
      X * Matrix.kronecker (U : CMatrix A) (V : CMatrix M)) :
    Matrix.kronecker (U : CMatrix A) (V : CMatrix M) *
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X *
      (Matrix.kronecker (U : CMatrix A) (V : CMatrix M)).conjTranspose =
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X := by
  let R := tensorUnitary U V
  have hr : (R : CMatrix (A × M)).conjTranspose * (R : CMatrix (A × M)) = 1 := R.property.1
  have hs : (R : CMatrix (A × M)) * (R : CMatrix (A × M)).conjTranspose = 1 := R.property.2
  have hx : (R : CMatrix (A × M)) * X = X * (R : CMatrix (A × M)) := hX
  have he : (R : CMatrix (A × M)).conjTranspose * X * (R : CMatrix (A × M)) = X := by
    rw [Matrix.mul_assoc, ← hx, ← Matrix.mul_assoc, hr, Matrix.one_mul]
  have hp := depolarizing_unitary_conjugate U V X
  change (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map
      ((R : CMatrix (A × M)).conjTranspose * X * (R : CMatrix (A × M))) =
    (R : CMatrix (A × M)).conjTranspose *
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X *
      (R : CMatrix (A × M)) at hp
  rw [he] at hp
  have hh := congrArg (fun Y => (R : CMatrix (A × M)) * Y *
    (R : CMatrix (A × M)).conjTranspose) hp
  simpa only [Matrix.mul_assoc,
    ← Matrix.mul_assoc (R : CMatrix (A × M)) (R : CMatrix (A × M)).conjTranspose,
    hs, Matrix.one_mul, Matrix.mul_one] using hh

theorem invariant_basis_norm (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup M ℂ) (X : CMatrix (A × M))
    (hX : Matrix.kronecker (U : CMatrix A) (V : CMatrix M) * X =
      X * Matrix.kronecker (U : CMatrix A) (V : CMatrix M)) :
    traceNorm (basisMap U X - (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X) =
    traceNorm (pinchingMap X - (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X) := by
  rw [invariant_basis_apply U V X hX]
  conv_lhs =>
    arg 1
    arg 2
    rw [← invariant_depolarizing_conjugate U V X hX]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  exact traceNorm_unitary_conjugate (tensorUnitary U V) _

theorem depolarizing_invariant (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup M ℂ) (X : CMatrix (A × M))
    (hX : Matrix.kronecker (U : CMatrix A) (V : CMatrix M) * X =
      X * Matrix.kronecker (U : CMatrix A) (V : CMatrix M)) :
    Matrix.kronecker (U : CMatrix A) (V : CMatrix M) *
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X =
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X *
        Matrix.kronecker (U : CMatrix A) (V : CMatrix M) := by
  let R := tensorUnitary U V
  have hr : (R : CMatrix (A × M)).conjTranspose * (R : CMatrix (A × M)) = 1 := R.property.1
  have hc := invariant_depolarizing_conjugate U V X hX
  change (R : CMatrix (A × M)) *
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X *
      (R : CMatrix (A × M)).conjTranspose =
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X at hc
  have hh := congrArg (fun Y => Y * (R : CMatrix (A × M))) hc
  change (R : CMatrix (A × M)) * _ = _
  simpa only [Matrix.mul_assoc, hr, Matrix.mul_one] using hh

theorem depolarizing_head_invariant (U : Matrix.unitaryGroup A ℂ)
    (X : CMatrix (A × M)) :
    (headRotation (M := M) U : CMatrix (A × M)) *
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X =
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X *
        (headRotation (M := M) U : CMatrix (A × M)) := by
  rw [ICO.RecordingDepolarizing.withMemory_apply, uniformOutput_eq_kronecker]
  simp only [headRotation, tensorUnitary, Matrix.kronecker, Matrix.mul_smul,
    Matrix.smul_mul]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

theorem depolarizing_makes_head_invariant (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup M ℂ) (X : CMatrix (A × M))
    (hX : (sideRotation (A := A) V : CMatrix (A × M)) * X =
      X * (sideRotation (A := A) V : CMatrix (A × M))) :
    Matrix.kronecker (U : CMatrix A) (V : CMatrix M) *
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X =
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X *
        Matrix.kronecker (U : CMatrix A) (V : CMatrix M) := by
  have hs := depolarizing_invariant (1 : Matrix.unitaryGroup A ℂ) V X hX
  have hh := depolarizing_head_invariant U X
  change (sideRotation (A := A) V : CMatrix (A × M)) * _ =
    _ * (sideRotation (A := A) V : CMatrix (A × M)) at hs
  rw [← head_side_factor U V]
  rw [Matrix.mul_assoc, hs, ← Matrix.mul_assoc, hh, Matrix.mul_assoc]

theorem common_head_factor (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (commonRotation (Z := Z) U (n + 1)).submatrix
      (Equiv.prodAssoc A (TensorPower A n) Z).symm
      (Equiv.prodAssoc A (TensorPower A n) Z).symm =
    Matrix.kronecker (U : CMatrix A)
      (commonRotation (Z := Z) U n) := by
  ext x y
  change ((U : CMatrix A) x.1 y.1 *
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n)) x.2.1 y.2.1) *
      (1 : CMatrix Z) x.2.2 y.2.2 =
    (U : CMatrix A) x.1 y.1 *
      ((unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n)) x.2.1 y.2.1 *
        (1 : CMatrix Z) x.2.2 y.2.2)
  ring

theorem invariant_basis_bound (U : Matrix.unitaryGroup A ℂ) (n : ℕ)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) (hpos : ω.PosSemidef)
    (hω : CommonInvariant (n + 1) ω) :
    traceNorm (basisMap U (headMatrix n ω) -
      (ICO.RecordingDepolarizing.withMemory (α := A) (μ := TensorPower A n × Z)).map
        (headMatrix n ω)) ≤ 6 * (n : ℝ) * ω.trace.re / (Fintype.card A : ℝ) := by
  let V := tensorUnitary (unitaryTensorPowerMatrix U n) (1 : Matrix.unitaryGroup Z ℂ)
  have hi : Matrix.kronecker (U : CMatrix A) (V : CMatrix (TensorPower A n × Z)) *
      headMatrix n ω = headMatrix n ω *
      Matrix.kronecker (U : CMatrix A) (V : CMatrix (TensorPower A n × Z)) := by
    have hh := congrArg (fun B => B.submatrix
      (Equiv.prodAssoc A (TensorPower A n) Z).symm
      (Equiv.prodAssoc A (TensorPower A n) Z).symm) (hω U)
    dsimp only at hh
    rw [← Matrix.submatrix_mul_equiv (commonRotation (Z := Z) U (n + 1)) ω
      (Equiv.prodAssoc A (TensorPower A n) Z).symm
      (Equiv.prodAssoc A (TensorPower A n) Z).symm
      (Equiv.prodAssoc A (TensorPower A n) Z).symm,
      ← Matrix.submatrix_mul_equiv ω (commonRotation (Z := Z) U (n + 1))
      (Equiv.prodAssoc A (TensorPower A n) Z).symm
      (Equiv.prodAssoc A (TensorPower A n) Z).symm
      (Equiv.prodAssoc A (TensorPower A n) Z).symm,
      ] at hh
    erw [common_head_factor (Z := Z) U n] at hh
    exact hh
  rw [invariant_basis_norm U V _ hi]
  exact invariant_pinching_bound n ω hpos hω

#print axioms invariant_basis_bound
end
end ICO.C6BasisInvariant

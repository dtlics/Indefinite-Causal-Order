import ICO.C6PolarFock
import ICO.MHFockBothCovariance

/-! Exact global record covariance of the actual polar creators. -/
namespace ICO.C6PolarFockCovariance
open QIT ICO.C6PolarFock ICO.MHBoundedRecording ICO.MHFockSpace
  ICO.MHFockRotation ICO.MHFockTransport ICO.MHFockCovariance ICO.MHSectorCovariance
  ICO.MHSymmetric ICO.MHCreationCovariance ICO.MHRightCovariance
  ICO.MHFockSwap ICO.MHFockOracle ICO.MHFockBothCovariance ICO.MHFockRotationSwap
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
set_option Elab.async false
variable {α:Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem normalized_polar_covariance (C D:Matrix.unitaryGroup α ℂ) {n:ℕ} (hn:n<Fintype.card α) :
    Matrix.kronecker (D:CMatrix α) (1:CMatrix (TensorPowerProfile (α×α) (n+1)))*
      ICO.C6BosonicPolar.leftPolar (A:=α) n*Matrix.kronecker (C:CMatrix α)
        (occupationRotation (leftEdgeUnitary C D) n)=
    Matrix.kronecker (1:CMatrix α) (occupationRotation (leftEdgeUnitary C D) (n+1))*
      ICO.C6BosonicPolar.leftPolar (A:=α) n := by
  have h := ICO.C6BosonicPolar.leftPolar_covariance C D hn
  have hD : (D:CMatrix α)*((D⁻¹:Matrix.unitaryGroup α ℂ):CMatrix α)=1 := D.property.2
  have hd : Matrix.kronecker (D:CMatrix α) (1:CMatrix (TensorPowerProfile (α×α) (n+1)))*
      (ICO.C6BosonicPolar.outputRotation C D (n+1):CMatrix (ICO.C6BosonicPolar.Sector (A:=α) (n+1)))=
      Matrix.kronecker (1:CMatrix α) (occupationRotation (leftEdgeUnitary C D) (n+1)) := by
    change Matrix.kronecker _ _ * Matrix.kronecker _ _ = _
    simp only [Matrix.kronecker]
    rw [←Matrix.mul_kronecker_mul,hD,Matrix.one_mul]
    rfl
  have hh := congrArg (fun M => Matrix.kronecker (D:CMatrix α)
    (1:CMatrix (TensorPowerProfile (α×α) (n+1)))*M) h
  dsimp only at hh
  rw [←Matrix.mul_assoc,hd] at hh
  simpa only [Matrix.mul_assoc,ICO.C6BosonicPolar.inputRotation,tensorUnitary,symmetricRotation] using hh.symm

def sectorF (n r:ℕ) : Matrix (Sector (α:=α) (n+1) r) (Sector (α:=α) n r) ℂ :=
  Matrix.kronecker (ICO.C6BosonicPolar.leftPolar (A:=α) n)
    (1:CMatrix (TensorPowerProfile (α×α) r))

theorem sectorF_block (n r:ℕ) : sectorF (α:=α) n r=
    Matrix.blockDiagonal (fun _q:TensorPowerProfile (α×α) r => ICO.C6BosonicPolar.leftPolar (A:=α) n) := by
  ext ⟨o,q⟩ ⟨i,p⟩
  simp [sectorF,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.blockDiagonal_apply']
theorem sectorF_covariance (C D : Matrix.unitaryGroup α ℂ) (n r : ℕ) (hn:n<Fintype.card α) :
    (queryTurn D (n + 1) r : CMatrix (Sector (α := α) (n + 1) r)) * sectorF (α := α) n r *
      (inputTurn C D n r : CMatrix (Sector (α := α) n r)) =
    (outputTurn C D (n + 1) r : CMatrix (Sector (α := α) (n + 1) r)) * sectorF (α := α) n r := by
  change Matrix.kronecker (Matrix.kronecker (D : CMatrix α) 1) 1 *
      Matrix.kronecker (ICO.C6BosonicPolar.leftPolar (A:=α) n) 1 *
      Matrix.kronecker (Matrix.kronecker (C : CMatrix α) (occupationRotation (leftEdgeUnitary C D) n))
        (occupationRotation (rightEdgeUnitary D⁻¹ C⁻¹) r) =
    Matrix.kronecker (Matrix.kronecker (1 : CMatrix α) (occupationRotation (leftEdgeUnitary C D) (n + 1)))
      (occupationRotation (rightEdgeUnitary D⁻¹ C⁻¹) r) *
      Matrix.kronecker (ICO.C6BosonicPolar.leftPolar (A:=α) n) 1
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  erw [normalized_polar_covariance C D hn]
  rfl

theorem boundedPolar_sectors (t : ℕ) : boundedPolar (α := α) t =
    (Matrix.blockDiagonal' (fun s : Lengths t => sectorF (α := α) s.val.1.val s.val.2.val)).submatrix
      (outputSectorEquiv t) (sectorEquiv t) := by
  ext ⟨⟨s,q⟩,p⟩ ⟨⟨s',q'⟩,p'⟩
  by_cases hs : s = s'
  · subst s'
    simp [boundedPolar, outputSectorEquiv, sectorEquiv,
      Matrix.blockDiagonal'_apply, sectorF_block, Matrix.blockDiagonal_apply']
  · have hblock : (⟨s,q⟩ : Block (α := α) t) ≠ ⟨s',q'⟩ := by
      intro he
      exact hs (congrArg Sigma.fst he)
    simp [boundedPolar, outputSectorEquiv, sectorEquiv,
      Matrix.blockDiagonal'_apply, hblock, hs]

theorem boundedPolar_covariance (C D : Matrix.unitaryGroup α ℂ) (t : ℕ) (ht:t<Fintype.card α) :
    outputFamily (fun n r => (queryTurn D n r : CMatrix (Sector (α := α) n r))) t *
      boundedPolar (α := α) t * inputFamily (fun n r => (inputTurn C D n r : CMatrix (Sector (α := α) n r))) t =
    outputFamily (fun n r => (outputTurn C D n r : CMatrix (Sector (α := α) n r))) t * boundedPolar (α := α) t := by
  rw [boundedPolar_sectors]
  unfold outputFamily inputFamily
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  congr 1
  funext s
  exact sectorF_covariance C D s.val.1.val s.val.2.val (by have hs:=s.property; omega)

theorem polarLeftOnFock_covariance (C D : Matrix.unitaryGroup α ℂ)
    {t T : ℕ} (h : t + 1 ≤ T) (ht:t<Fintype.card α) :
    inputFamily (fun n r => (queryTurn D n r : CMatrix (Sector (α := α) n r))) T *
      polarLeftOnFock h * inputFamily (fun n r => (inputTurn C D n r : CMatrix (Sector (α := α) n r))) T =
    inputFamily (fun n r => (outputTurn C D n r : CMatrix (Sector (α := α) n r))) T * polarLeftOnFock h := by
  exact embedded_covariance _ _ _ _ _ _ _ _ _
    (outputFamily_intertwine _ h) (inputFamily_intertwine_adjoint _ _)
    (outputFamily_intertwine _ h) (boundedPolar_covariance C D t ht)


theorem left_covariance (C D:Matrix.unitaryGroup α ℂ) {t T:ℕ}
    (h:t+1≤T) (ht:t<Fintype.card α) :
    (fockQuery D T:CMatrix (InputCutoff (α:=α) T))*polarLeftOnFock h*
      ((fockQuery C T:CMatrix (InputCutoff (α:=α) T))*(fockQ C D T:CMatrix (InputCutoff (α:=α) T)))=
      (fockQ C D T:CMatrix (InputCutoff (α:=α) T))*polarLeftOnFock h := by
  rw [fockQuery_fockQ]
  exact polarLeftOnFock_covariance C D h ht

theorem right_covariance (C D:Matrix.unitaryGroup α ℂ) {t T:ℕ}
    (h:t+1≤T) (ht:t<Fintype.card α) :
    (fockQuery C⁻¹ T:CMatrix (InputCutoff (α:=α) T))*polarRightOnFock h*
      ((fockQuery D⁻¹ T:CMatrix (InputCutoff (α:=α) T))*(fockQ C D T:CMatrix (InputCutoff (α:=α) T)))=
      (fockQ C D T:CMatrix (InputCutoff (α:=α) T))*polarRightOnFock h := by
  have hh := congrArg (fun M => swapMatrix (α:=α) T*M*swapMatrix T)
    (left_covariance D⁻¹ C⁻¹ h ht)
  simpa only [swap_mul,swap_fockQuery,swap_fockQ,inv_inv,
    polarRightOnFock,swapMatrix_selfAdjoint] using hh

#print axioms left_covariance
#print axioms right_covariance
end
end ICO.C6PolarFockCovariance

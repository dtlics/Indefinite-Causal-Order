import ICO.C6BasisDephase

/-! Actual channel transport through isometries of unrestricted side memory. -/
namespace ICO.C6MemoryNatural
open QIT Matrix ICO.C6DephaseChannel ICO.C6BasisDephase
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1100000
universe u
variable {A M N J : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N] [Fintype J]

def queryEmbedding (D : Matrix N M ℂ) : Matrix (A × N) (A × M) ℂ :=
  Matrix.kronecker (1 : CMatrix A) D

theorem reference_apply_eq (V : ReferenceIsometry M N) (X : CMatrix (A × M)) :
    V.applyMatrixRight X = queryEmbedding (A := A) V.matrix * X *
      (queryEmbedding (A := A) V.matrix).conjTranspose := by
  ext i j
  simp [ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock, queryEmbedding,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, apply_ite]

theorem queryEmbedding_gram (D : Matrix N M ℂ) (hD : D.conjTranspose * D = 1) :
    (queryEmbedding (A := A) D).conjTranspose * queryEmbedding (A := A) D = 1 := by
  simp only [queryEmbedding, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, hD]
  simp only [Matrix.one_mul, Matrix.one_kronecker_one]

theorem kraus_intertwine (D : Matrix N M ℂ) (K : CMatrix A) :
    Matrix.kronecker K (1 : CMatrix N) * queryEmbedding (A := A) D =
      queryEmbedding (A := A) D * Matrix.kronecker K (1 : CMatrix M) := by
  simp only [queryEmbedding, Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]

theorem oracle_natural (D : Matrix N M ℂ) (K : J → CMatrix A)
    (X : CMatrix (A × M)) :
    ICO.AllChannelDilation.oracleMap (M := N) K
        (queryEmbedding (A := A) D * X * (queryEmbedding (A := A) D).conjTranspose) =
      queryEmbedding (A := A) D * ICO.AllChannelDilation.oracleMap (M := M) K X *
        (queryEmbedding (A := A) D).conjTranspose := by
  change (∑ j : J, Matrix.kronecker (K j) (1 : CMatrix N) *
      (queryEmbedding (A := A) D * X * (queryEmbedding (A := A) D).conjTranspose) *
      (Matrix.kronecker (K j) (1 : CMatrix N)).conjTranspose) =
    queryEmbedding (A := A) D *
      (∑ j : J, Matrix.kronecker (K j) (1 : CMatrix M) * X *
        (Matrix.kronecker (K j) (1 : CMatrix M)).conjTranspose) *
        (queryEmbedding (A := A) D).conjTranspose
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have h := kraus_intertwine (A := A) D (K j)
  have ha := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_mul] at ha
  calc
    Matrix.kronecker (K j) (1 : CMatrix N) *
      (queryEmbedding (A := A) D * X * (queryEmbedding (A := A) D).conjTranspose) *
      (Matrix.kronecker (K j) (1 : CMatrix N)).conjTranspose =
      (Matrix.kronecker (K j) (1 : CMatrix N) * queryEmbedding (A := A) D) * X *
      ((queryEmbedding (A := A) D).conjTranspose *
        (Matrix.kronecker (K j) (1 : CMatrix N)).conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = (queryEmbedding (A := A) D * Matrix.kronecker (K j) (1 : CMatrix M)) * X *
      ((Matrix.kronecker (K j) (1 : CMatrix M)).conjTranspose *
        (queryEmbedding (A := A) D).conjTranspose) := by rw [h, ha]
    _ = queryEmbedding (A := A) D *
      (Matrix.kronecker (K j) (1 : CMatrix M) * X *
        (Matrix.kronecker (K j) (1 : CMatrix M)).conjTranspose) *
        (queryEmbedding (A := A) D).conjTranspose := by simp only [Matrix.mul_assoc]

theorem basis_natural (D : Matrix N M ℂ) (U : Matrix.unitaryGroup A ℂ)
    (X : CMatrix (A × M)) :
    basisMap (M := N) U (queryEmbedding (A := A) D * X * (queryEmbedding (A := A) D).conjTranspose) =
      queryEmbedding (A := A) D * basisMap (M := M) U X * (queryEmbedding (A := A) D).conjTranspose :=
  oracle_natural D _ X

theorem uniformOutput_eq_kronecker (T : CMatrix M) :
    ICO.RecordingWrapperDistance.uniformOutput (α := A) T =
      ((1 / (Fintype.card A : ℝ) : ℝ) : ℂ) • Matrix.kronecker (1 : CMatrix A) T := by
  unfold ICO.RecordingWrapperDistance.uniformOutput ICO.RecordingDistance.memoryOutput
  rw [QIT.Classical.blockDiagonal_smul, ← QIT.Classical.identityTensor_eq_blockDiagonal]

theorem depolarizing_natural (D : Matrix N M ℂ) (hD : D.conjTranspose * D = 1)
    (X : CMatrix (A × M)) :
    (ICO.RecordingDepolarizing.withMemory (α := A) (μ := N)).map
        (queryEmbedding (A := A) D * X * (queryEmbedding (A := A) D).conjTranspose) =
      queryEmbedding (A := A) D * (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X *
        (queryEmbedding (A := A) D).conjTranspose := by
  let V : ReferenceIsometry M N := ⟨D, hD⟩
  have hp := V.partialTraceA_applyMatrixRight X
  rw [reference_apply_eq] at hp
  change partialTraceA (queryEmbedding (A := A) D * X * (queryEmbedding (A := A) D).conjTranspose) =
    D * partialTraceA X * D.conjTranspose at hp
  rw [ICO.RecordingDepolarizing.withMemory_apply, hp,
    ICO.RecordingDepolarizing.withMemory_apply, uniformOutput_eq_kronecker,
    uniformOutput_eq_kronecker]
  simp only [queryEmbedding, Matrix.kronecker, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul]

#print axioms basis_natural
#print axioms depolarizing_natural
end
end ICO.C6MemoryNatural

import ICO.MHTernaryFourier

/-! Exact Fourier conjugacy between recording shifts and controlled random phases. -/
namespace ICO.MHPurifiedFourier
open Matrix QIT ICO.MHTernaryCompression ICO.MHTernaryFourier ICO.MHPurifiedOracle
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [DecidableEq A]

def environmentFourier : CMatrix (Environment A) :=
  Matrix.kronecker (1 : CMatrix (Equiv.Perm A)) (fourierMatrix (A := A))

def queryFourier : CMatrix (A × Environment A) :=
  Matrix.kronecker (1 : CMatrix A) (environmentFourier (A := A))

def environmentFourierUnitary : Matrix.unitaryGroup (Environment A) ℂ :=
  ⟨environmentFourier, Matrix.kronecker_mem_unitary (1 : Matrix.unitaryGroup (Equiv.Perm A) ℂ).property
    (fourierUnitary (A := A)).property⟩

def queryFourierUnitary : Matrix.unitaryGroup (A × Environment A) ℂ :=
  ⟨queryFourier, Matrix.kronecker_mem_unitary (1 : Matrix.unitaryGroup A ℂ).property
    (environmentFourierUnitary (A := A)).property⟩

theorem queryFourier_entry (o i : A × Environment A) :
    queryFourier o i = (if o.1=i.1 then (1:ℂ) else 0) *
      (if o.2.1=i.2.1 then (1:ℂ) else 0) * coefficient (A := A) * character o.2.2 i.2.2 := by
  simp [queryFourier,environmentFourier,Matrix.kronecker,Matrix.one_apply,fourierMatrix,mul_assoc]

def phaseEquiv : A × Environment A ≃ A × Environment A where
  toFun i := (i.2.1 i.1,i.2)
  invFun o := (o.2.1.symm o.1,o.2)
  left_inv i := by rcases i with ⟨x,π,f⟩; simp
  right_inv o := by rcases o with ⟨y,π,f⟩; simp

def phasePermutation : CMatrix (A × Environment A) :=
  ICO.MemoryEmbedding.embedding ⟨phaseEquiv,phaseEquiv.injective⟩

def phaseQuery : CMatrix (A × Environment A) :=
  phasePermutation * Matrix.diagonal (fun i : A × Environment A => ZMod.stdAddChar (i.2.2 i.1))

theorem phaseQuery_entry (o i : A × Environment A) :
    phaseQuery o i = if o=phaseEquiv i then ZMod.stdAddChar (i.2.2 i.1) else 0 := by
  simp [phaseQuery,Matrix.mul_diagonal,phasePermutation,ICO.MemoryEmbedding.embedding]

theorem mul_query_entry (K : CMatrix (A × Environment A)) (o i : A × Environment A) :
    (K * queryMatrix (A := A)) o i = K o (queryEquiv i) := by
  simp [Matrix.mul_apply,queryMatrix_entry]

theorem phasePermutation_mul_entry (K : CMatrix (A × Environment A)) (o i : A × Environment A) :
    (phasePermutation (A := A)*K) o i = K (phaseEquiv.symm o) i := by
  rw [Matrix.mul_apply,Finset.sum_eq_single (phaseEquiv.symm o)]
  · simp [phasePermutation,ICO.MemoryEmbedding.embedding]
  · intro j hj hjo
    have hne : o ≠ phaseEquiv j := by
      intro h
      apply hjo
      apply phaseEquiv.injective
      simpa using h.symm
    simp [phasePermutation,ICO.MemoryEmbedding.embedding,hne]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem phaseQuery_mul_entry (K : CMatrix (A × Environment A)) (o i : A × Environment A) :
    (phaseQuery (A := A)*K) o i = ZMod.stdAddChar (o.2.2 (o.2.1.symm o.1))*K (phaseEquiv.symm o) i := by
  rw [phaseQuery,Matrix.mul_assoc,phasePermutation_mul_entry,Matrix.diagonal_mul]
  rfl

theorem fourier_shift_entry (o i : A × Environment A) :
    queryFourier o (queryEquiv i) =
      ZMod.stdAddChar (o.2.2 (o.2.1.symm o.1))*queryFourier (phaseEquiv.symm o) i := by
  rcases o with ⟨y,π,f⟩
  rcases i with ⟨x,σ,z⟩
  by_cases hπ : π=σ
  · subst σ
    by_cases hy : y=π x
    · subst y
      simp only [queryFourier_entry,queryEquiv,phaseEquiv,Equiv.coe_fn_mk,
        Equiv.symm_mk,Equiv.apply_symm_apply,Equiv.symm_apply_apply,ite_true,one_mul]
      rw [character_shift]
      ring
    · have hx : π.symm y ≠ x := by
        intro h
        apply hy
        exact (π.apply_symm_apply y).symm.trans (congrArg π h)
      simp [queryFourier_entry,queryEquiv,phaseEquiv,hy,hx]
  · simp [queryFourier_entry,queryEquiv,phaseEquiv,hπ]

/-- One actual frequency-shift oracle call is a controlled phase-permutation
call after a unitary Fourier change of the private environment basis. -/
theorem fourier_intertwining :
    queryFourier (A := A) * queryMatrix = phaseQuery * queryFourier (A := A) := by
  ext o i
  rw [mul_query_entry,phaseQuery_mul_entry,fourier_shift_entry]

theorem phase_conjugation : phaseQuery (A := A) =
    queryFourier * queryMatrix * (queryFourier (A := A)).conjTranspose := by
  rw [fourier_intertwining,Matrix.mul_assoc]
  have h := Matrix.mem_unitaryGroup_iff.mp (queryFourierUnitary (A := A)).property
  change queryFourier * (queryFourier (A := A)).conjTranspose = 1 at h
  rw [h,Matrix.mul_one]

def phaseQueryUnitary : Matrix.unitaryGroup (A × Environment A) ℂ :=
  queryFourierUnitary * queryUnitary * queryFourierUnitary⁻¹

theorem phaseQueryUnitary_matrix : (phaseQueryUnitary (A := A) : CMatrix (A × Environment A)) =
    phaseQuery := by
  exact phase_conjugation.symm

theorem fourier_inverse_intertwining :
    queryFourier (A := A) * (queryMatrix (A := A)).conjTranspose =
      (phaseQuery (A := A)).conjTranspose * queryFourier := by
  rw [phase_conjugation]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  have h := Matrix.mem_unitaryGroup_iff'.mp (queryFourierUnitary (A := A)).property
  change (queryFourier (A := A)).conjTranspose * queryFourier = 1 at h
  rw [h,Matrix.mul_one]

theorem known_operation_commutes {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (W : Matrix K H ℂ) :
    Matrix.kronecker W (1 : CMatrix (Environment A)) *
      Matrix.kronecker (1 : CMatrix H) (environmentFourier (A := A)) =
    Matrix.kronecker (1 : CMatrix K) (environmentFourier (A := A)) *
      Matrix.kronecker W (1 : CMatrix (Environment A)) := by
  calc
    _ = Matrix.kronecker (W*1) ((1 : CMatrix (Environment A))*environmentFourier) :=
      (Matrix.mul_kronecker_mul W 1 (1 : CMatrix (Environment A)) (environmentFourier (A := A))).symm
    _ = Matrix.kronecker ((1 : CMatrix K)*W) ((environmentFourier (A := A))*1) := by simp
    _ = _ := Matrix.mul_kronecker_mul (1 : CMatrix K) W (environmentFourier (A := A)) 1

#print axioms fourier_intertwining
#print axioms phase_conjugation
#print axioms fourier_inverse_intertwining
end
end ICO.MHPurifiedFourier

import ICO.MHFockReachability
import ICO.MHBlockNorm

/-! Known isometries act on the accessible query and memory only. Their
literal lift preserves the private occupation records, even with changing
finite memory spaces. -/
namespace ICO.MHFockKnownOperation
open QIT ICO.MHBoundedRecording ICO.MHFockLabels ICO.MHFockSpace ICO.MHFockProjection
  ICO.MHBijectionProfiles ICO.MHOccupationCounts ICO.RecordingProcess ICO.MHBlockNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 512
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Records (T : ℕ) := Σ s : Lengths T,
  TensorPowerProfile (α×α) s.val.1.val × TensorPowerProfile (α×α) s.val.2.val

def records {T : ℕ} (i : InputCutoff (α := α) T) : Records (α := α) T :=
  ⟨i.1.1,(i.2.2,i.1.2)⟩

def queryMemoryFirst (T : ℕ) (μ : Type*) :
    (InputCutoff (α := α) T × μ) ≃ (α×μ)×Records (α := α) T where
  toFun i := ((i.1.2.1,i.2),records i.1)
  invFun i := (⟨⟨i.2.1,i.2.2.2⟩,(i.1.1,i.2.2.1)⟩,i.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable {μ ν : Type*} [fμ : Fintype μ] [dμ : DecidableEq μ] [fν : Fintype ν] [dν : DecidableEq ν]

def known (T : ℕ) (K : Matrix (α×ν) (α×μ) ℂ) :
    Matrix (InputCutoff (α := α) T×ν) (InputCutoff (α := α) T×μ) ℂ :=
  (Matrix.kronecker K (1 : CMatrix (Records (α := α) T))).submatrix
    (queryMemoryFirst T ν) (queryMemoryFirst T μ)

theorem known_coefficient (T : ℕ) (K : Matrix (α×ν) (α×μ) ℂ)
    (o : InputCutoff (α := α) T×ν) (i : InputCutoff (α := α) T×μ) :
    known T K o i=K (o.1.2.1,o.2) (i.1.2.1,i.2)*(if records o.1=records i.1 then 1 else 0) := rfl

theorem known_isometry (T : ℕ) (K : Matrix (α×ν) (α×μ) ℂ) (hK : K.conjTranspose*K=1) :
    (known T K).conjTranspose*known T K=1 := by
  simp only [known,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
    Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul,hK,Matrix.mul_one,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]

theorem known_norm_le (T : ℕ) (K : Matrix (α×ν) (α×μ) ℂ) (hK : K.conjTranspose*K=1) :
    ‖known (α := α) (μ := μ) (ν := ν) T K‖≤1 :=
  isometry_matrix_norm_le _ (known_isometry T K hK)

theorem known_records (T : ℕ) (K : Matrix (α×ν) (α×μ) ℂ)
    (o : InputCutoff (α := α) T×ν) (i : InputCutoff (α := α) T×μ)
    (h : known T K o i≠0) : records o.1=records i.1 := by
  by_contra hn
  exact h (by simp [known_coefficient,hn])

theorem known_grade (T : ℕ) (K : Matrix (α×ν) (α×μ) ℂ)
    (o : InputCutoff (α := α) T×ν) (i : InputCutoff (α := α) T×μ)
    (h : known T K o i≠0) : grade o.1=grade i.1 :=
  congrArg (fun R : Records (α := α) T => R.1.val.1.val+R.1.val.2.val) (known_records T K o i h)

theorem known_bij (T : ℕ) (K : Matrix (α×ν) (α×μ) ℂ)
    (o : InputCutoff (α := α) T×ν) (i : InputCutoff (α := α) T×μ)
    (h : known T K o i≠0) :
    BijMultiset (fockLabel o.1).2.1 (fockLabel o.1).2.2 ↔
      BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2 := by
  have he := congrArg (fun R : Records (α := α) T => BijProfile R.2.1 R.2.2)
    (known_records T K o i h)
  exact Iff.of_eq he

theorem tensor_identity_norm_le {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (M : Matrix b a ℂ) :
    ‖Matrix.kronecker M (1 : CMatrix μ)‖≤‖M‖ := by
  have he : Matrix.kronecker M (1 : CMatrix μ)=Matrix.blockDiagonal (fun _ : μ => M) := by
    ext o i
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
      Matrix.blockDiagonal_apply,mul_ite,mul_one,mul_zero]
  rw [he]
  have hs : Real.sqrt (‖M‖^2)=‖M‖ := by rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg M)]
  rw [← hs]
  apply blockDiagonal_norm_le _ _ (sq_nonneg ‖M‖)
  intro j
  rw [hs]

end
end ICO.MHFockKnownOperation

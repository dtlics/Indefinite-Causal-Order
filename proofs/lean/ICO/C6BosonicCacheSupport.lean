import ICO.C6BosonicFockRotated

/-! The fresh inverse preserves the actual occupied left-label support. -/
namespace ICO.C6BosonicCacheSupport
open QIT ICO.C6BosonicFockSupport ICO.C6BosonicFreshContraction
  ICO.C6PolarFock ICO.MHFockSwap ICO.MHFockBothCovariance ICO.MHBoundedRecording
  ICO.MHFockSpace ICO.MHFockOracle ICO.MHProfileTranspose ICO.C6BosonicLabelSupport ICO.RecordingCopyIdentity
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2300000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def rightDiagonal (f : ∀ n, TensorPowerProfile (A×A) n → ℂ) (T : ℕ) :
    CMatrix (InputCutoff (α:=A) T) := Matrix.diagonal (fun i => f _ i.1.2)

def rightOutputDiagonal (f : ∀ n, TensorPowerProfile (A×A) n → ℂ) (t : ℕ) :
    CMatrix (OutputCutoff (α:=A) t) := Matrix.diagonal (fun i => f _ i.1.2)

theorem bounded_rightDiagonal (f : ∀ n, TensorPowerProfile (A×A) n → ℂ) (t : ℕ) :
    rightOutputDiagonal f t * boundedPolar t=boundedPolar t*rightDiagonal f t := by
  ext ⟨k,o⟩ ⟨l,i⟩
  simp only [rightOutputDiagonal,rightDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases h : k=l
  · subst l
    exact mul_comm _ _
  · simp [boundedPolar,Matrix.blockDiagonal'_apply,h]

theorem fock_rightDiagonal (f : ∀ n, TensorPowerProfile (A×A) n → ℂ)
    {t T : ℕ} (h : t+1≤T) :
    rightDiagonal f T*polarLeftOnFock h=polarLeftOnFock h*rightDiagonal f T := by
  have hO : rightDiagonal f T*basisEmbedding (outputEmbed (α:=A) h)=
      basisEmbedding (outputEmbed h)*rightOutputDiagonal f t := diagonal_embedding _ _
  have hI : (basisEmbedding (inputEmbed (α:=A) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose*
      rightDiagonal f T=rightDiagonal f t*
        (basisEmbedding (inputEmbed (α:=A) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose :=
    embedding_adjoint_diagonal _ _
  unfold polarLeftOnFock
  calc
    _ = (rightDiagonal f T*basisEmbedding (outputEmbed h))*boundedPolar t*
        (basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hO]
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc (rightOutputDiagonal f t) (boundedPolar t),bounded_rightDiagonal]
      simp only [Matrix.mul_assoc,←hI]

def transposedRightSupport (S : Finset A) (T : ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  rightDiagonal (fun n q => if LabelsIn S (profileTranspose n q) then 1 else 0) T

theorem record_swap (S : Finset A) (T : ℕ) :
    fockRecord S T*swapMatrix T=swapMatrix T*transposedRightSupport S T :=
  diagonal_embedding _ _

theorem swap_record (S : Finset A) (T : ℕ) :
    swapMatrix T*fockRecord S T=transposedRightSupport S T*swapMatrix T := by
  have h := congrArg (fun M => swapMatrix T*M*swapMatrix T) (record_swap S T)
  simp only [Matrix.mul_assoc] at h
  rw [←Matrix.mul_assoc (swapMatrix (α:=A) T) (swapMatrix T),swapMatrix_sq,
    Matrix.one_mul,Matrix.mul_one] at h
  exact h

theorem right_preserves_left (S : Finset A) {t T : ℕ} (h : t+1≤T) :
    fockRecord S T*polarRightOnFock h=polarRightOnFock h*fockRecord S T := by
  have hr : transposedRightSupport S T*polarLeftOnFock h=
      polarLeftOnFock h*transposedRightSupport S T := fock_rightDiagonal _ h
  unfold polarRightOnFock
  rw [swapMatrix_selfAdjoint]
  calc
    _ = (fockRecord S T*swapMatrix T)*polarLeftOnFock h*swapMatrix T := by
      simp only [Matrix.mul_assoc]
    _ = swapMatrix T*(transposedRightSupport S T*polarLeftOnFock h)*swapMatrix T := by
      rw [record_swap]; simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hr]
      simp only [Matrix.mul_assoc]
      rw [←swap_record]

theorem record_input (S : Finset A) (T : ℕ) :
    fockRecord S T*fockInput S T=fockInput S T := by
  rw [fockRecord,fockInput,Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  by_cases h : LabelsIn S i.2.2 <;> simp [h]

theorem retrieval_preserves_left (S : Finset A) {t T : ℕ} (h : t+1≤T)
    (ht : t<Fintype.card A) :
    fockRecord S T*(polarLeftOnFock h).conjTranspose*fockRecord S T=
      (polarLeftOnFock h).conjTranspose*fockRecord S T := by
  rw [Matrix.mul_assoc,←fock_polar_adjoint_support S h ht,←Matrix.mul_assoc,
    record_input,fock_polar_adjoint_support S h ht]

theorem left_image_support (S : Finset A) {t T : ℕ} (h : t+1≤T)
    (ht : t<Fintype.card A) :
    fockRecord S T*(polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)=
      (polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)*fockRecord S T := by
  rw [←Matrix.mul_assoc,fock_polar_support S h ht,Matrix.mul_assoc,
    fock_polar_adjoint_support S h ht,←Matrix.mul_assoc]

theorem fresh_query_support (S : Finset A) (T : ℕ) :
    fockRecord S T*queryFresh S T=queryFresh S T*fockRecord S T := by
  rw [fockRecord,queryFresh,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  exact mul_comm _ _

theorem freshInverse_preserves_left (S : Finset A) {t T : ℕ} (h : t+1≤T)
    (ht : t<Fintype.card A) :
    fockRecord S T*freshInverse (polarLeftOnFock h) (polarRightOnFock h) (queryFresh S T)*
      fockRecord S T=
      freshInverse (polarLeftOnFock h) (polarRightOnFock h) (queryFresh S T)*fockRecord S T := by
  have hB : fockRecord S T*fockRecord S T=fockRecord S T :=
    (fockRecord_projection S T).isIdempotentElem.eq
  have hc : fockRecord S T*(1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)=
      (1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)*fockRecord S T := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,left_image_support S h ht]
  unfold freshInverse
  simp only [Matrix.mul_add,Matrix.add_mul]
  rw [retrieval_preserves_left S h ht]
  congr 1
  calc
    _ = ((fockRecord S T*queryFresh S T)*polarRightOnFock h)*
        (1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)*fockRecord S T := by
      simp only [Matrix.mul_assoc]
    _ = (queryFresh S T*polarRightOnFock h)*
        ((1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose)*(fockRecord S T*fockRecord S T)) := by
      rw [fresh_query_support]
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc (fockRecord S T) (polarRightOnFock h),right_preserves_left S h]
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc (fockRecord S T) (1-polarLeftOnFock h*(polarLeftOnFock h).conjTranspose),hc]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hB]; simp only [Matrix.mul_assoc]

#print axioms right_preserves_left
#print axioms freshInverse_preserves_left
end
end ICO.C6BosonicCacheSupport

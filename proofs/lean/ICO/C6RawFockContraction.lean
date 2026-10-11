import ICO.C6RawFreshContraction
import ICO.C6BosonicRawRightBound
import ICO.C6FockNumber
import ICO.C6RotatedNumber
import ICO.C6PolarCompression

/-! The genuine raw right insertion, restricted to unoccupied outgoing modes,
is contractive on the entire finite Fock space. -/
namespace ICO.C6RawFockContraction
open QIT ICO.C6BosonicCompression ICO.C6RawFreshContraction ICO.C6BosonicFresh ICO.C6BosonicSupport
  ICO.C6PolarCompression ICO.C6BosonicRight ICO.C6BosonicPolar ICO.C6BosonicFockSupport
  ICO.C6BosonicCacheSupport ICO.C6FockNumber ICO.C6FockQueryMatrix
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHFockBothCovariance ICO.MHProfileTranspose ICO.MHERecordingApprox
  ICO.MHBlockNorm ICO.RecordingCopyIdentity ICO.RecordingProcess
  ICO.MHFockRotation ICO.MHFockRotationSwap ICO.MHFockCovariance
  ICO.MHSectorCovariance ICO.C6BosonicFockRotated ICO.C6NumberRotationAlgebra
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def imageZero (S:Finset A) (n:ℕ) : CMatrix (ICO.C6BosonicPolar.Sector (A:=A) n) :=
  Matrix.diagonal (fun i=>if labelNumber S (profileTranspose n i.2)=0 then 1 else 0)

theorem left_raw_fresh_norm (S:Finset A) (n:ℕ) :
    ‖queryProjection S (n+1)*symmetricInsertion (α:=A) n*imageZero S n‖≤1 := by
  have he : queryProjection S (n+1)*symmetricInsertion (α:=A) n*imageZero S n=
      ((queryProjection S (n+1)*ICO.C6BosonicRight.rightInsertion (A:=A) n*targetNumberProjection S n 0) : Matrix (ICO.C6BosonicPolar.Sector (A:=A) (n+1)) (ICO.C6BosonicPolar.Sector (A:=A) n) ℂ).submatrix
        (sectorTranspose (n+1)) (sectorTranspose n) := by
    rw [rightInsertion_transpose]
    ext ⟨x,p⟩ ⟨y,q⟩
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,queryProjection,imageZero,
      targetNumberProjection,Matrix.submatrix_apply,sectorTranspose,Equiv.prodCongr_apply,
      Equiv.refl_apply,Prod.map_fst,Prod.map_snd,Prod.map_apply,profileTranspose_involutive]
  rw [he]
  exact (rectangular_reindex_norm_le _ _ _).trans (raw_fresh_norm S n)

def queryIn (S:Finset A) (T:ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  Matrix.diagonal (fun i=>if i.2.1∈S then 1 else 0)

def outputQueryIn (S:Finset A) (t:ℕ) : CMatrix (OutputCutoff (α:=A) t) :=
  Matrix.diagonal (fun i=>if i.2.1∈S then 1 else 0)

def leftImageZero (S:Finset A) (T:ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  Matrix.diagonal (fun i=>if labelNumber S (profileTranspose _ i.2.2)=0 then 1 else 0)

theorem bounded_raw_fresh (S:Finset A) (t:ℕ) :
    outputQueryIn S t*boundedSymmetricInsertion (α:=A) t*leftImageZero S t=
      Matrix.blockDiagonal' (fun k:Block (α:=A) t=>
        queryProjection S (k.1.val.1.val+1)*symmetricInsertion k.1.val.1.val*
          imageZero S k.1.val.1.val) := by
  ext ⟨k,o⟩ ⟨j,i⟩
  simp only [outputQueryIn,leftImageZero,Matrix.diagonal_mul,Matrix.mul_diagonal,
    boundedSymmetricInsertion,Matrix.blockDiagonal'_apply']
  by_cases hk:k=j
  · subst j
    simp only [dite_true,cast_eq,queryProjection,imageZero,Matrix.diagonal_mul,Matrix.mul_diagonal]
  · simp [hk]

theorem bounded_raw_fresh_norm (S:Finset A) (t:ℕ) :
    ‖outputQueryIn S t*boundedSymmetricInsertion (α:=A) t*leftImageZero S t‖≤1 := by
  rw [bounded_raw_fresh]
  rw [show (1:ℝ)=Real.sqrt 1 from Real.sqrt_one.symm]
  apply blockDiagonal'_norm_le _ 1 (by norm_num)
  intro k
  rw [Real.sqrt_one]
  exact left_raw_fresh_norm (A:=A) S k.1.val.1.val
theorem left_raw_fock_norm (S:Finset A) {t T:ℕ} (h:t+1≤T) :
    ‖queryIn S T*symmetricOnFock (α:=A) h*leftImageZero S T‖≤1 := by
  let J:=basisEmbedding (inputEmbed (α:=A) (Nat.le_trans (Nat.le_succ t) h))
  let K:=basisEmbedding (outputEmbed (α:=A) h)
  have hO:queryIn S T*K=K*outputQueryIn S t:=diagonal_embedding _ _
  have hI:J.conjTranspose*leftImageZero S T=leftImageZero S t*J.conjTranspose:=
    embedding_adjoint_diagonal _ _
  have he:queryIn S T*symmetricOnFock (α:=A) h*leftImageZero S T=
      K*(outputQueryIn S t*boundedSymmetricInsertion (α:=A) t*leftImageZero S t)*J.conjTranspose := by
    change queryIn S T*(K*boundedSymmetricInsertion t*J.conjTranspose)*leftImageZero S T=_
    simp only [←Matrix.mul_assoc]
    rw [hO]
    simp only [Matrix.mul_assoc]
    rw [hI]
  have hJ:‖J.conjTranspose‖≤1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact isometry_matrix_norm_le _ (inputEmbed_gram _)
  have hK:‖K‖≤1:=isometry_matrix_norm_le _ (outputEmbed_gram _)
  rw [he]
  calc
    _ ≤ (‖K‖*‖outputQueryIn S t*boundedSymmetricInsertion (α:=A) t*leftImageZero S t‖)*‖J.conjTranspose‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*1)*1:=mul_le_mul (mul_le_mul hK (bounded_raw_fresh_norm S t)
      (norm_nonneg _) (by norm_num)) hJ (norm_nonneg _) (by norm_num)
    _ = 1:=by norm_num

theorem swap_queryIn (S:Finset A) (T:ℕ) :
    swapMatrix T*queryIn S T*swapMatrix T=queryIn S T := by
  calc
    _ = (basisEmbedding (recordSwapEquiv (α:=A) T)).conjTranspose*queryIn S T*
        basisEmbedding (recordSwapEquiv (α:=A) T) := by rw [←swapMatrix,swapMatrix_selfAdjoint]
    _ = _ := by
      rw [basisEmbedding_compression,queryIn,Matrix.submatrix_diagonal_equiv]
      rfl

theorem swap_leftImageZero (S:Finset A) (T:ℕ) :
    swapMatrix T*leftImageZero S T*swapMatrix T=rightNumber S 0 T := by
  calc
    _ = (basisEmbedding (recordSwapEquiv (α:=A) T)).conjTranspose*leftImageZero S T*
        basisEmbedding (recordSwapEquiv (α:=A) T) := by rw [←swapMatrix,swapMatrix_selfAdjoint]
    _ = _ := by
      rw [basisEmbedding_compression,leftImageZero,Matrix.submatrix_diagonal_equiv]
      ext i j
      simp only [rightNumber,rightDiagonal,Matrix.diagonal_apply]
      change (if i=j then (if labelNumber S (profileTranspose _ (profileTranspose _ i.1.2))=0 then (1:ℂ) else 0) else 0)=_
      rw [profileTranspose_involutive]

theorem right_raw_fock_norm (S:Finset A) {t T:ℕ} (h:t+1≤T) :
    ‖queryIn S T*symmetricRightOnFock (α:=A) h*rightNumber S 0 T‖≤1 := by
  have he:queryIn S T*symmetricRightOnFock (α:=A) h*rightNumber S 0 T=
      swapMatrix T*(queryIn S T*symmetricOnFock h*leftImageZero S T)*swapMatrix T := by
    symm
    simp only [swap_mul,swap_queryIn,swap_leftImageZero,symmetricRightOnFock,swapMatrix_selfAdjoint]
  rw [he]
  exact (swap_norm_le T _).trans (left_raw_fock_norm S h)

theorem raw_left_covariance (C D:Matrix.unitaryGroup A ℂ) {t T:ℕ} (h:t+1≤T) :
    (fockQuery D T:CMatrix (InputCutoff (α:=A) T))*symmetricOnFock h*
      ((fockQuery C T:CMatrix (InputCutoff (α:=A) T))*(fockQ C D T:CMatrix (InputCutoff (α:=A) T)))=
      (fockQ C D T:CMatrix (InputCutoff (α:=A) T))*symmetricOnFock h := by
  rw [fockQuery_fockQ]
  exact symmetricOnFock_covariance C D h

theorem raw_right_covariance (C D:Matrix.unitaryGroup A ℂ) {t T:ℕ} (h:t+1≤T) :
    (fockQuery C⁻¹ T:CMatrix (InputCutoff (α:=A) T))*symmetricRightOnFock h*
      ((fockQuery D⁻¹ T:CMatrix (InputCutoff (α:=A) T))*(fockQ C D T:CMatrix (InputCutoff (α:=A) T)))=
      (fockQ C D T:CMatrix (InputCutoff (α:=A) T))*symmetricRightOnFock h := by
  have hh:=congrArg (fun M=>swapMatrix (α:=A) T*M*swapMatrix T)
    (raw_left_covariance D⁻¹ C⁻¹ h)
  simpa only [swap_mul,swap_fockQuery,swap_fockQ,inv_inv,
    symmetricRightOnFock,swapMatrix_selfAdjoint] using hh

theorem raw_fresh_covariance (U:Matrix.unitaryGroup A ℂ) (B:Finset A)
    {t T:ℕ} (h:t+1≤T) :
    (rotatedFresh U B T*symmetricRightOnFock h)*(fockQ U 1 T:CMatrix (InputCutoff (α:=A) T))=
      ((fockQuery U T:CMatrix (InputCutoff (α:=A) T))*(fockQ U 1 T:CMatrix (InputCutoff (α:=A) T)))*
        (queryFresh B T*symmetricRightOnFock h) := by
  let C:CMatrix (InputCutoff (α:=A) T):=fockQuery U T
  let R:CMatrix (InputCutoff (α:=A) T):=fockQ U 1 T
  have hg:=raw_right_covariance U 1 h
  simp only [inv_one,query_one,Matrix.one_mul,fockQuery_inverse] at hg
  change C.conjTranspose*symmetricRightOnFock h*R=R*symmetricRightOnFock h at hg
  change (C*queryFresh B T*C.conjTranspose)*symmetricRightOnFock h*R=(C*R)*(queryFresh B T*symmetricRightOnFock h)
  calc
    _ = C*queryFresh B T*(C.conjTranspose*symmetricRightOnFock h*R) := by simp only [Matrix.mul_assoc]
    _ = C*queryFresh B T*(R*symmetricRightOnFock h) := by rw [hg]
    _ = _ := by
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc (queryFresh B T) R,queryFresh_commutes]
      simp only [Matrix.mul_assoc]
      rfl

theorem raw_rotated_fresh_norm (U:Matrix.unitaryGroup A ℂ) (B:Finset A)
    {t T:ℕ} (h:t+1≤T) :
    ‖rotatedFresh U B T*symmetricRightOnFock h*rotatedNumber U Bᶜ 0 T‖≤1 := by
  let C:CMatrix (InputCutoff (α:=A) T):=fockQuery U T
  let R:CMatrix (InputCutoff (α:=A) T):=fockQ U 1 T
  have hC:‖C‖≤1:=unitary_norm_le (fockQuery U T)
  have hR:‖R‖≤1:=unitary_norm_le (fockQ U 1 T)
  have hRa:‖R.conjTranspose‖≤1:=by rwa [Matrix.l2_opNorm_conjTranspose]
  have hq:queryFresh B T=queryIn Bᶜ T:=by ext i j; simp [queryFresh,queryIn]
  have hN:‖queryFresh B T*symmetricRightOnFock h*rightNumber Bᶜ 0 T‖≤1:=by
    rw [hq]; exact right_raw_fock_norm Bᶜ h
  have he:rotatedFresh U B T*symmetricRightOnFock h*rotatedNumber U Bᶜ 0 T=
      (C*R)*(queryFresh B T*symmetricRightOnFock h*rightNumber Bᶜ 0 T)*R.conjTranspose := by
    unfold rotatedNumber
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,raw_fresh_covariance]
    simp only [Matrix.mul_assoc]
    rfl
  rw [he]
  have hCR:‖C*R‖≤1:=(norm_mul_le _ _).trans (by nlinarith [norm_nonneg C,norm_nonneg R])
  exact (norm_mul_le _ _).trans (by
    have hh:‖(C*R)*(queryFresh B T*symmetricRightOnFock h*rightNumber Bᶜ 0 T)‖≤1:=
      (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (C*R),norm_nonneg (queryFresh B T*symmetricRightOnFock h*rightNumber Bᶜ 0 T)])
    nlinarith [norm_nonneg ((C*R)*(queryFresh B T*symmetricRightOnFock h*rightNumber Bᶜ 0 T)),norm_nonneg R.conjTranspose])

#print axioms right_raw_fock_norm
#print axioms raw_rotated_fresh_norm
end
end ICO.C6RawFockContraction






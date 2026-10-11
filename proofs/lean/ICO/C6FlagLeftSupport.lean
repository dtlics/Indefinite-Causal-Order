import ICO.C6RawStageError
import ICO.C6BosonicStageSupport
import ICO.C6BosonicVacuum

namespace ICO.C6FlagLeftSupport
open Matrix QIT ICO.C6RawFlags ICO.C6RawFockContraction ICO.C6RawInverseError
  ICO.C6BosonicCacheSupport ICO.C6BosonicFockSupport ICO.C6BosonicHistoryClosure
  ICO.C6BosonicHistorySupport ICO.C6BosonicGeometricCreation ICO.C6BosonicQueryAlgebra
  ICO.C6BosonicFockRotated ICO.C6BosonicFreshContraction ICO.C6NumberRotationAlgebra
  ICO.C6BosonicStageSupport ICO.C6BosonicVacuum ICO.C6BosonicBlocks
  ICO.C6RetainedHistory ICO.C6BirthFlags ICO.C6PolarFock
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHFockRotation ICO.RecordingCopyIdentity ICO.C6CacheSpanProjection
  ICO.MHRectangularAction ICO.C6RotatedNumber ICO.C6PairedTrajectory
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem raw_bounded_rightDiagonal (f : ∀ n, TensorPowerProfile (A×A) n → ℂ) (t : ℕ) :
    rightOutputDiagonal f t * boundedSymmetricInsertion t=boundedSymmetricInsertion t*rightDiagonal f t := by
  ext ⟨k,o⟩ ⟨l,i⟩
  simp only [rightOutputDiagonal,rightDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases h : k=l
  · subst l
    exact mul_comm _ _
  · simp [boundedSymmetricInsertion,Matrix.blockDiagonal'_apply,h]

theorem raw_fock_rightDiagonal (f : ∀ n, TensorPowerProfile (A×A) n → ℂ)
    {t T : ℕ} (h : t+1≤T) :
    rightDiagonal f T*symmetricOnFock h=symmetricOnFock h*rightDiagonal f T := by
  have hO : rightDiagonal f T*basisEmbedding (outputEmbed (α:=A) h)=
      basisEmbedding (outputEmbed h)*rightOutputDiagonal f t := diagonal_embedding _ _
  have hI : (basisEmbedding (inputEmbed (α:=A) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose*
      rightDiagonal f T=rightDiagonal f t*
        (basisEmbedding (inputEmbed (α:=A) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose :=
    embedding_adjoint_diagonal _ _
  unfold symmetricOnFock
  calc
    _ = (rightDiagonal f T*basisEmbedding (outputEmbed h))*boundedSymmetricInsertion t*
        (basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hO]
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc (rightOutputDiagonal f t) (boundedSymmetricInsertion t),raw_bounded_rightDiagonal]
      simp only [Matrix.mul_assoc,←hI]

theorem raw_right_preserves_left (S : Finset A) {t T : ℕ} (h : t+1≤T) :
    fockRecord S T*symmetricRightOnFock h=symmetricRightOnFock h*fockRecord S T := by
  have hr : transposedRightSupport S T*symmetricOnFock h=
      symmetricOnFock h*transposedRightSupport S T := raw_fock_rightDiagonal _ h
  unfold symmetricRightOnFock
  rw [swapMatrix_selfAdjoint]
  calc
    _ = (fockRecord S T*swapMatrix T)*symmetricOnFock h*swapMatrix T := by
      simp only [Matrix.mul_assoc]
    _ = swapMatrix T*(transposedRightSupport S T*symmetricOnFock h)*swapMatrix T := by
      rw [record_swap]; simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hr]
      simp only [Matrix.mul_assoc]
      rw [←swap_record]

theorem raw_geometric_birth_support (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    {t T : ℕ} (h : t+1≤T) (ht : t<Fintype.card A) :
    fockSupport (spanProjection U S) T*(rotatedFresh U S T*symmetricRightOnFock h)=
      (rotatedFresh U S T*symmetricRightOnFock h)*fockSupport (spanProjection U S) T := by
  have hb : fockRecord S T*(queryFresh S T*symmetricRightOnFock h)=
      (queryFresh S T*symmetricRightOnFock h)*fockRecord S T := by
    rw [←Matrix.mul_assoc,fresh_query_support,Matrix.mul_assoc,raw_right_preserves_left]
    simp only [Matrix.mul_assoc]
  have hh := transported_intertwining (rotatedFresh U S T*symmetricRightOnFock h)
    (queryFresh S T*symmetricRightOnFock h) (fockRecord S T) (fockRecord S T)
    (fockQ U 1 T) (fockQuery U T*fockQ U 1 T) (raw_fresh_covariance U S h) hb
  rw [commuting_conjugate _ _ _ (query_record_rotation U U T) (query_record U S T)] at hh
  simpa only [fockSupport_rotated,rotatedRecord] using hh



theorem selected_support {X:Type} [Fintype X] [DecidableEq X]
    (B R D C:CMatrix X) (hB:B*B=B) (hR:B*R*B=R*B)
    (hD:B*D=D*B) (hC:B*C=C*B) (b:Bool) :
    B*(if b then D*C else R)*B=(if b then D*C else R)*B := by
  cases b
  · simpa using hR
  · simp only [Bool.true_eq,if_true]
    calc
      _ = D*(B*C)*B := by rw [←Matrix.mul_assoc B D,hD]; simp only [Matrix.mul_assoc]
      _ = D*C*(B*B) := by rw [hC]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hB]

theorem selected_zero_support {X:Type} [Fintype X] [DecidableEq X]
    (B M N:CMatrix X) (hM:B*M*B=M*B) (hN:B*N=N*B) :
    B*(M*N*B)=M*N*B := by
  calc
    _ = B*M*B*N := by simp only [Matrix.mul_assoc]; rw [←hN]
    _ = M*B*N := by rw [hM]
    _ = M*N*B := by simp only [Matrix.mul_assoc]; rw [hN]

theorem history_selected_support {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (η:ICO.RecordingPurifiedProtocol.History (A×Bool) i)
    (b:Bool) : historySupport (vectors H i η) T*flagInverse h H i η b=flagInverse h H i η b := by
  let U:=historyUnitary (vectors H i η)
  let S:=historyIndices (vectors H i η)
  let B:=historySupport (vectors H i η) T
  have hc:B*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)=
      (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*B := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
    have he:B*(polarLeftOnFock h*(polarLeftOnFock h)ᴴ)=(polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*B := geometric_image_support U S h ht
    rw [he]
  simpa only [flagInverse,Matrix.mul_assoc] using selected_support B
    (polarLeftOnFock h)ᴴ (rotatedFresh U S T*polarRightOnFock h)
    (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)
    (historySupport_projection _ T).isIdempotentElem.eq
    (geometric_retrieval_support U S h ht) (geometric_birth_support U S h ht) hc b

theorem history_raw_support {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (η:ICO.RecordingPurifiedProtocol.History (A×Bool) i)
    (b:Bool) : historySupport (vectors H i η) T*rawFlagInverse h H i η b=rawFlagInverse h H i η b := by
  let U:=historyUnitary (vectors H i η)
  let S:=historyIndices (vectors H i η)
  let B:=historySupport (vectors H i η) T
  have hc:B*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)=
      (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*B := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
    have he:B*(polarLeftOnFock h*(polarLeftOnFock h)ᴴ)=(polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*B := geometric_image_support U S h ht
    rw [he]
  apply selected_zero_support
  · exact selected_support B (polarLeftOnFock h)ᴴ (rotatedFresh U S T*symmetricRightOnFock h)
      (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)
      (historySupport_projection _ T).isIdempotentElem.eq
      (geometric_retrieval_support U S h ht) (raw_geometric_birth_support U S h ht) hc b
  · exact (zero_left_commute H i T η).symm

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem stage_support {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (J:CMatrix (InputCutoff (α:=A) T×Public (A:=A) μ i))
    (hj:publicSupport (μ:=μ) H i T*J=J) :
    publicSupport H (i+1) T*(publicStage T K i*reencodingStage (μ:=μ) h H i*J)=
      publicStage T K i*reencodingStage (μ:=μ) h H i*J := by
  let A0:=publicSupport (μ:=μ) H i T
  let A1:=middleSupport (μ:=μ) H i T
  let A2:=publicSupport (μ:=μ) H (i+1) T
  let L:Matrix (InputCutoff (α:=A) T×Middle (A:=A) μ i)
      (InputCutoff (α:=A) T×Public (A:=A) μ i) ℂ:=reencodingStage h H i
  let P:=publicStage T K i
  have hl:A1*L*A0=L*A0:=reencoding_history_support (μ:=μ) h ht H i
  have hp:A2*P=P*A1:=public_history_support T H K i
  have he:A2*(P*L*J)=P*L*J := by
    calc
      _ = (A2*P)*L*(A0*J) := by rw [hj]; simp only [Matrix.mul_assoc]
      _ = P*(A1*L*A0)*J := by rw [hp]; simp only [Matrix.mul_assoc]
      _ = P*(L*A0)*J := by rw [hl]
      _ = _ := by simp only [Matrix.mul_assoc]; rw [hj]
  exact he

theorem flagStage_support {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) (b:Bool) :
    publicSupport H (i+1) T*flagStage h H K i b=flagStage h H K i b := by
  have hh:publicSupport (μ:=μ) H i T*controlled (M:=μ i) (fun η=>flagInverse h H i η b)=
      controlled (M:=μ i) (fun η=>flagInverse h H i η b) := by
    rw [publicSupport,ICO.C6HistoryControlled.controlled_mul]
    exact congrArg (controlled (M:=μ i)) (funext (fun η=>history_selected_support h ht H i η b))
  simpa only [flagStage,reencodingStage,Matrix.mul_assoc] using stage_support h ht H K i _ hh

theorem rawFlagStage_support {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) (b:Bool) :
    publicSupport H (i+1) T*rawFlagStage h H K i b=rawFlagStage h H K i b := by
  have hh:publicSupport (μ:=μ) H i T*controlled (M:=μ i) (fun η=>rawFlagInverse h H i η b)=
      controlled (M:=μ i) (fun η=>rawFlagInverse h H i η b) := by
    rw [publicSupport,ICO.C6HistoryControlled.controlled_mul]
    exact congrArg (controlled (M:=μ i)) (funext (fun η=>history_raw_support h ht H i η b))
  simpa only [rawFlagStage,reencodingStage,Matrix.mul_assoc] using stage_support h ht H K i _ hh


theorem publicSupport_initial (H:Matrix.unitaryGroup A ℂ) (T:ℕ)
    (z:A×Public (A:=A) μ 0→ℂ) :
    rectAct (publicSupport (μ:=μ) H 0 T)
      (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z))=
      WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z) := by
  change WithLp.toLp 2 (_*ᵥ(ICO.MHFockTrajectory.initial T z))=_
  rw [publicSupport,controlled_family,ICO.MHFockTrajectory.initial,Matrix.mulVec_mulVec]
  have hh:=family_initial (fun p:Public (A:=A) μ 0=>historySupport (vectors H 0 p.2.1) T)
    (fun m o x=>support_empty (spanProjection (historyUnitary (vectors H 0 m.2.1))
      (historyIndices (vectors H 0 m.2.1))) T o x)
  rw [hh]

theorem flagRun_history {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (i:ℕ) (κ:ICO.RecordingPurifiedProtocol.History Bool i) :
    rectAct (publicSupport (μ:=μ) H i T)
      (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ)=
      flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ := by
  cases i with
  | zero=>exact publicSupport_initial H T z
  | succ i=>
    change rectAct _ (rectAct (flagStage h H K i κ.1) _)=rectAct (flagStage h H K i κ.1) _
    rw [←rectAct_mul,flagStage_support h ht H K i κ.1]

theorem rawFlagRun_history {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (i:ℕ) (κ:ICO.RecordingPurifiedProtocol.History Bool i) :
    rectAct (publicSupport (μ:=μ) H i T)
      (rawFlagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ)=
      rawFlagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ := by
  cases i with
  | zero=>exact publicSupport_initial H T z
  | succ i=>
    change rectAct _ (rectAct (rawFlagStage h H K i κ.1) _)=rectAct (rawFlagStage h H K i κ.1) _
    rw [←rectAct_mul,rawFlagStage_support h ht H K i κ.1]

theorem rawFlagRun_history_slice {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (i:ℕ) (κ:ICO.RecordingPurifiedProtocol.History Bool i)
    (η:ICO.RecordingPurifiedProtocol.History (A×Bool) i) :
    rectAct (Matrix.kronecker (historySupport (vectors H i η) T) (1:CMatrix (Bool×μ i)))
      (ICO.C6FlagSlices.slice η (rawFlagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ))=
      ICO.C6FlagSlices.slice η (rawFlagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ) := by
  have hh:=congrArg (ICO.C6FlagSlices.slice (A:=A) (μ:=μ) (T:=T) (i:=i) η)
    (rawFlagRun_history h ht H K z i κ)
  rw [publicSupport,ICO.C6RawStageError.slice_controlled] at hh
  exact hh

theorem flagRun_history_slice {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (i:ℕ) (κ:ICO.RecordingPurifiedProtocol.History Bool i)
    (η:ICO.RecordingPurifiedProtocol.History (A×Bool) i) :
    rectAct (Matrix.kronecker (historySupport (vectors H i η) T) (1:CMatrix (Bool×μ i)))
      (ICO.C6FlagSlices.slice η (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ))=
      ICO.C6FlagSlices.slice η (flagRun h H K (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i κ) := by
  have hh:=congrArg (ICO.C6FlagSlices.slice (A:=A) (μ:=μ) (T:=T) (i:=i) η)
    (flagRun_history h ht H K z i κ)
  rw [publicSupport,ICO.C6RawStageError.slice_controlled] at hh
  exact hh

#print axioms rawFlagRun_history_slice
#print axioms flagRun_history_slice
end
end ICO.C6FlagLeftSupport

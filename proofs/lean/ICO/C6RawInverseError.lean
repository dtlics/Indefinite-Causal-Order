import ICO.C6RawFlagContraction
import ICO.C6RawLocalAlgebra
import ICO.C6BosonicRawRightBound

namespace ICO.C6RawInverseError
open Matrix QIT ICO.C6RawFlagContraction ICO.C6RawLocalAlgebra ICO.C6RawFlags
  ICO.C6FlagStack ICO.C6BirthFlags ICO.C6RetainedHistory ICO.C6HistoryControlled
  ICO.C6PairedTrajectory ICO.C6PolarFock ICO.C6BosonicFockRotated
  ICO.C6BosonicHistorySupport ICO.C6CacheSpanProjection ICO.C6NumberRotationAlgebra
  ICO.C6RightHistorySupport ICO.C6BosonicLengthMasks ICO.C6FockQueryMatrix
  ICO.C6BosonicQueryAlgebra ICO.C6BosonicRawRightBound ICO.MHFockSwap
  ICO.MHBoundedRecording ICO.MHRectangularAction ICO.RecordingPurifiedProtocol
  ICO.C6PolarCompression ICO.MHBlockNorm ICO.MHFockKnownOperation
  ICO.MHFockBothCovariance ICO.MHSectorCovariance
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem right_left_support_commute (P Q:CMatrix A) (T:ℕ) :
    rightFockSupport P T*fockSupport Q T=fockSupport Q T*rightFockSupport P T := by
  unfold rightFockSupport fockSupport
  rw [inputFamily_mul,inputFamily_mul]
  congr 1
  funext n r
  simp only [rightSupportSector,supportSector,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul,Matrix.mul_one]

theorem zero_left_commute (H:Matrix.unitaryGroup A ℂ) (i T:ℕ) (η:History (A×Bool) i) :
    historyZero H i T η*historySupport (vectors H i η) T=
      historySupport (vectors H i η) T*historyZero H i T η := by
  rw [historyZero,zero_number_geometric]
  exact right_left_support_commute _ _ _

theorem zero_mask_commute (H:Matrix.unitaryGroup A ℂ) (i m T:ℕ) (η:History (A×Bool) i) :
    historyZero H i T η*rightLengthMask m T=rightLengthMask m T*historyZero H i T η := by
  rw [historyZero,zero_number_geometric]
  exact (mask_family _ _ _).symm

theorem complement_mask {t T:ℕ} (h:t+1≤T) (m:ℕ) :
    (1-polarLeftOnFock (α:=A) h*(polarLeftOnFock h)ᴴ)*rightLengthMask m T=
      rightLengthMask m T*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ) := by
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_one]
  rw [←Matrix.mul_assoc (rightLengthMask m T),left_mask]
  simp only [Matrix.mul_assoc]
  rw [left_adjoint_mask]

theorem inverse_difference_stack {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i m:ℕ) (hm:m<Fintype.card A) (η:History (A×Bool) i) :
    ‖stack (fun b=>(flagInverse h H i η b-rawFlagInverse h H i η b)*
      historyZero H i T η*rightLengthMask m T)‖≤(m:ℝ)/Fintype.card A := by
  let F:=polarLeftOnFock (α:=A) h
  let G:=polarRightOnFock (α:=A) h
  let E:=symmetricRightOnFock (α:=A) h
  let Q:=rotatedFresh (historyUnitary (vectors H i η)) (historyIndices (vectors H i η)) T
  let N:=historyZero H i T η
  let B:=historySupport (vectors H i η) T
  let R:=rightLengthMask (α:=A) m T
  have hN:N*N=N:=(historyZero_projection H i T η).isIdempotentElem.eq
  have hBN:B*N=N*B:=(zero_left_commute H i T η).symm
  have hNR:N*R=R*N:=zero_mask_commute H i m T η
  have hBR:B*R=R*B:=(mask_family _ m T).symm
  have hCR:(1-F*Fᴴ)*R=R*(1-F*Fᴴ):=complement_mask h m
  have he:(fun b=>(flagInverse h H i η b-rawFlagInverse h H i η b)*N*R)=
      (fun b:Bool=>if b then Q*((G-E)*R)*(1-F*Fᴴ)*B*N else 0) := by
    funext b
    exact masked_branch_difference F G E Q N B R hN hBN hNR hBR hCR b
  change ‖stack (fun b=>(flagInverse h H i η b-rawFlagInverse h H i η b)*N*R)‖≤_
  rw [he]
  apply one_birth_stack_bound _ _ (by positivity)
  apply sandwich_bound _ _ _ _ _ _ (by positivity)
  · exact IsStarProjection.norm_le _ (unitary_projection _ _
      (ICO.C6BosonicFockSupport.queryFresh_projection _ _))
  · have hD:=raw_right_masked_norm h m hm
    have hd:(G-E)*R= -((E-G)*R):=by rw [←Matrix.neg_mul,neg_sub]
    rw [hd,norm_neg]
    exact hD
  · exact IsStarProjection.norm_le _ (ICO.RecordingOracleAlgebra.image_projection _ _
      (polarLeftOnFock_gram h ht) (polarLeftOnFock_domain h)).one_sub
  · exact IsStarProjection.norm_le _ (historySupport_projection _ _)
  · exact IsStarProjection.norm_le _ (historyZero_projection H i T η)

theorem controlled_stack_bound {T i:ℕ} {M:Type} [Fintype M] [DecidableEq M]
    (F:History (A×Bool) i→Bool→CMatrix (InputCutoff (α:=A) T))
    (ε:ℝ) (hε:0≤ε) (hF:∀η,‖stack (F η)‖≤ε) :
    ‖stack (fun b=>controlled (M:=M) (fun η=>F η b))‖≤ε := by
  rw [controlled_stack]
  apply (rectangular_reindex_norm_le _ _ _).trans
  have hs:Real.sqrt (ε^2)=ε:=Real.sqrt_sq hε
  have hh:=blockDiagonal_norm_le (fun η=>Matrix.kronecker (stack (F η)) (1:CMatrix (Bool×M)))
    (ε^2) (sq_nonneg _) (fun η=>by rw [hs]; exact (tensor_identity_norm_le _).trans (hF η))
  simpa only [hs] using hh

def comparisonMask (H:Matrix.unitaryGroup A ℂ) (i m T:ℕ) (η:History (A×Bool) i) :
    CMatrix (InputCutoff (α:=A) T) := historyZero H i T η*rightLengthMask m T

theorem controlled_difference_stack {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i m:ℕ) (hm:m<Fintype.card A)
    (M:Type) [Fintype M] [DecidableEq M] :
    ‖stack (fun b=>(controlled (M:=M) (fun η=>flagInverse h H i η b)-
      controlled (M:=M) (fun η=>rawFlagInverse h H i η b))*
        controlled (M:=M) (comparisonMask H i m T))‖≤(m:ℝ)/Fintype.card A := by
  simp only [←controlled_sub,controlled_mul]
  apply controlled_stack_bound _ _ (by positivity)
  intro η
  simpa only [comparisonMask,←Matrix.mul_assoc] using inverse_difference_stack h ht H i m hm η

#print axioms inverse_difference_stack
#print axioms controlled_difference_stack
end
end ICO.C6RawInverseError


import ICO.C6RawFlags
import ICO.C6RawFockContraction
import ICO.C6FlagStack

/-! The raw trajectory is a globally contractive flagged quantum operation,
after its explicit causal right-vacuum compression. -/
namespace ICO.C6RawFlagContraction
open Matrix QIT ICO.C6RawFlags ICO.C6RawFockContraction ICO.C6FlagStack
  ICO.C6BirthFlags ICO.C6RetainedHistory ICO.C6HistoryControlled
  ICO.C6PairedTrajectory ICO.C6PolarFock ICO.C6BosonicFockRotated
  ICO.C6BosonicHistorySupport ICO.C6CacheSpanProjection ICO.C6NumberRotationAlgebra
  ICO.C6FockNumber ICO.C6BosonicCacheSupport ICO.C6BosonicSupport
  ICO.C6RotatedNumber ICO.C6RightHistorySupport ICO.MHFockKnownOperation
  ICO.MHBoundedRecording ICO.MHRectangularAction ICO.RecordingPurifiedProtocol
  ICO.C6PolarCompression ICO.MHBlockNorm ICO.MHFockRotation
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem number_projection (S:Finset A) (k T:ℕ) : IsStarProjection (rightNumber S k T) := by
  constructor
  · change rightNumber S k T*rightNumber S k T=rightNumber S k T
    ext i j
    simp only [rightNumber,rightDiagonal,Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply]
    split_ifs <;> simp
  · exact rightNumber_adjoint S k T

theorem historyZero_projection (H:Matrix.unitaryGroup A ℂ) (i T:ℕ) (η:History (A×Bool) i) :
    IsStarProjection (historyZero H i T η) :=
  unitary_projection _ _ (number_projection _ _ _)

theorem historyZero_left (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (η:History (A×Bool) i)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    historyZero H i T η*polarLeftOnFock h=polarLeftOnFock h*historyZero H i T η :=
  left_preserves_rotated_number _ _ _ h ht

theorem historyZero_complement (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (η:History (A×Bool) i)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    historyZero H i T η*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)=
      (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*historyZero H i T η := by
  let N:=historyZero H i T η
  have hN:Nᴴ=N:=(historyZero_projection H i T η).isSelfAdjoint.star_eq
  have hf:N*polarLeftOnFock h=polarLeftOnFock h*N:=historyZero_left H i η h ht
  have ha:N*(polarLeftOnFock h)ᴴ=(polarLeftOnFock h)ᴴ*N := by
    have hh:=congrArg Matrix.conjTranspose hf
    simpa only [Matrix.conjTranspose_mul,hN] using hh.symm
  change N*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)=_
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
  rw [←Matrix.mul_assoc,hf,Matrix.mul_assoc,ha]
  simp only [Matrix.mul_assoc]
  rfl

theorem raw_inverse_stack_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (η:History (A×Bool) i) :
    ‖stack (rawFlagInverse h H i η)‖≤1 := by
  apply split_compressed_norm
  · exact ICO.RecordingOracleAlgebra.image_projection _ _
      (polarLeftOnFock_gram h ht) (polarLeftOnFock_domain h)
  · exact historyZero_projection H i T η
  · exact historyZero_complement H i η h ht
  · exact raw_rotated_fresh_norm _ _ h
  · exact IsStarProjection.norm_le _ (historySupport_projection _ _)
def flaggedHistoryFirst (T i:ℕ) (M:Type) :
    (Bool×(InputCutoff (α:=A) T×(Bool×(History (A×Bool) i×M))))≃
      (((Bool×InputCutoff (α:=A) T)×(Bool×M))×History (A×Bool) i) where
  toFun x:=(((x.1,x.2.1),(x.2.2.1,x.2.2.2.2)),x.2.2.2.1)
  invFun x:=(x.1.1.1,(x.1.1.2,(x.1.2.1,(x.2,x.1.2.2))))
  left_inv _:=rfl
  right_inv _:=rfl

theorem controlled_stack {T i:ℕ} {M:Type} [Fintype M] [DecidableEq M]
    (F:History (A×Bool) i→Bool→CMatrix (InputCutoff (α:=A) T)) :
    stack (fun b=>controlled (M:=M) (fun η=>F η b))=
      (Matrix.blockDiagonal (fun η=>Matrix.kronecker (stack (F η)) (1:CMatrix (Bool×M)))).submatrix
        (flaggedHistoryFirst T i M) (historyFirst T i M) := by
  ext ⟨b,o,c,η,m⟩ ⟨p,d,η',n⟩
  simp only [stack,controlled_entry,Matrix.submatrix_apply,flaggedHistoryFirst,historyFirst,
    Equiv.coe_fn_mk,Matrix.blockDiagonal_apply',Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  by_cases hh:η=η' <;> by_cases hc:c=d <;> by_cases hm:m=n <;> simp_all [Prod.mk.injEq]

theorem controlled_stack_norm {T i:ℕ} {M:Type} [Fintype M] [DecidableEq M]
    (F:History (A×Bool) i→Bool→CMatrix (InputCutoff (α:=A) T))
    (hF:∀η,‖stack (F η)‖≤1) :
    ‖stack (fun b=>controlled (M:=M) (fun η=>F η b))‖≤1 := by
  rw [controlled_stack]
  apply (rectangular_reindex_norm_le _ _ _).trans
  have hh:=blockDiagonal_norm_le (fun η=>Matrix.kronecker (stack (F η)) (1:CMatrix (Bool×M)))
    1 (by norm_num) (fun η=>by
      rw [Real.sqrt_one]
      exact (tensor_identity_norm_le _).trans (hF η))
  simpa only [Real.sqrt_one] using hh

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem raw_stage_stack_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1) (i:ℕ) :
    ‖stack (rawFlagStage h H K i)‖≤1 := by
  apply stack_common_norm
  · apply ICO.C6FockPairs.mul_norm_le_one
    · apply ICO.C6FockPairs.mul_norm_le_one
      · exact publicStage_norm T K hK i
      · exact (tensor_identity_norm_le _).trans (polarLeftOnFock_norm_le h ht)
    · exact middleStage_norm T H i
  · exact controlled_stack_norm _ (raw_inverse_stack_norm h ht H i)

#print axioms raw_inverse_stack_norm
#print axioms raw_stage_stack_norm
end
end ICO.C6RawFlagContraction


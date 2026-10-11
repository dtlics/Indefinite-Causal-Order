import ICO.C6RetainedHistory
import ICO.C6BosonicLocalInverse

namespace ICO.C6HistoryControlled
open Matrix QIT ICO.C6RetainedHistory ICO.C6BosonicLocalInverse
  ICO.C6BosonicHistorySupport ICO.C6BosonicLengthMasks ICO.C6BosonicFreshContraction
  ICO.C6BosonicFockRotated ICO.C6CacheSpanProjection ICO.C6FockQueryMatrix
  ICO.C6PolarFock ICO.C6FockCompressionSharp ICO.MHBoundedRecording
  ICO.MHProfileBlocks ICO.MHBlockNorm ICO.MHFockKnownOperation ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2300000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {T i:ℕ} {M:Type} [Fintype M] [DecidableEq M]

theorem controlled_const (F:CMatrix (InputCutoff (α:=A) T)) :
    controlled (i:=i) (M:=M) (fun _=>F)=
      Matrix.kronecker F (1:CMatrix (Bool×(History (A×Bool) i×M))) := by
  ext o j
  rw [controlled_entry]
  simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  split_ifs <;> simp

theorem controlled_sub (F G:History (A×Bool) i→CMatrix (InputCutoff (α:=A) T)) :
    controlled (M:=M) (fun η=>F η-G η)=controlled F-controlled G := by
  ext o j
  simp only [controlled_entry,Matrix.sub_apply]
  split_ifs <;> simp

theorem controlled_mul (F G:History (A×Bool) i→CMatrix (InputCutoff (α:=A) T)) :
    controlled (M:=M) F*controlled G=controlled (fun η=>F η*G η) := by
  simp only [controlled,Matrix.submatrix_mul_equiv]
  rw [←Matrix.blockDiagonal_mul]
  congr 2
  funext η
  simp only [Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,Matrix.one_mul]

theorem controlled_bound (F:History (A×Bool) i→CMatrix (InputCutoff (α:=A) T))
    (ε:ℝ) (hε:0≤ε) (hF:∀η,‖F η‖≤ε) : ‖controlled (M:=M) F‖≤ε := by
  apply (reindex_norm_le _ _).trans
  have hs:Real.sqrt (ε^2)=ε := by rw [Real.sqrt_sq_eq_abs,abs_of_nonneg hε]
  have hb:=blockDiagonal_norm_le (fun η=>Matrix.kronecker (F η) (1:CMatrix (Bool×M)))
    (ε^2) (sq_nonneg ε) (fun η=>by rw [hs]; exact (tensor_identity_norm_le _).trans (hF η))
  simpa only [hs] using hb

def prefixMask (H:Matrix.unitaryGroup A ℂ) (i T:ℕ) (η:History (A×Bool) i) :
    CMatrix (InputCutoff (α:=A) T) :=
  historySupport (vectors H i η) T*rightLengthMask i T

def freshCost (d:ℕ) : ℕ→ℝ
  | 0=>0
  | i+1=>compressionBound (i+1) i d+compressionBound (i+1) (i+1) d

theorem freshCost_nonneg (d i:ℕ) : 0≤freshCost d i := by
  cases i <;> simp only [freshCost]
  · exact le_refl 0
  · exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem inverseBlock_error {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (hi:i<Fintype.card A) (η:History (A×Bool) i) :
    ‖((polarOracle h)ᴴ-inverseBlock h H i η)*prefixMask H i T η‖≤freshCost (Fintype.card A) i := by
  let B:=historySupport (vectors H i η) T
  let J:=freshInverse (polarLeftOnFock h) (polarRightOnFock h)
    (rotatedFresh (historyUnitary (vectors H i η)) (historyIndices (vectors H i η)) T)
  have hB:B*B=B:=(historySupport_projection _ _).isIdempotentElem.eq
  have he:((polarOracle h)ᴴ-J*B)*(B*rightLengthMask i T)=
      ((polarOracle h)ᴴ-J)*B*rightLengthMask i T := by
    simp only [Matrix.sub_mul,Matrix.mul_assoc]
    rw [←Matrix.mul_assoc B B,hB]
  change ‖((polarOracle h)ᴴ-J*B)*(B*rightLengthMask i T)‖≤_
  rw [he]
  cases i with
  | zero =>
    have hh:=local_inverse_zero (historyUnitary (vectors H 0 η))
      (historyIndices (vectors H 0 η)) h ht
    have hc:(historyIndices (vectors H 0 η)).card=0 := Nat.eq_zero_of_le_zero (history_realization _).2
    simpa only [B,J,historySupport,historyProjection,hc,compressionBound,freshCost,
      Nat.cast_zero,zero_add,zero_div,Real.sqrt_zero] using hh
  | succ i =>
    exact history_inverse_succ (vectors H (i+1) η) h ht hi

#print axioms controlled_mul
#print axioms inverseBlock_error
end
end ICO.C6HistoryControlled

import ICO.MHDecompressionKnown
import ICO.MHFockTrajectory

/-! The empty actual Fock record decompresses to the physical uniform
permutation, zero-frequency initial environment. -/
namespace ICO.MHDecompressionInitial
open Matrix QIT ICO.MHDecompressionKnown ICO.MHFockDecompression ICO.MHFockTrajectory
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockLabels ICO.MHFockNodup
  ICO.MHTernaryCompression ICO.MHPurifiedOracle ICO.MHRecordDecompression
  ICO.RecordingCopyIdentity ICO.RecordingMultisetBridge ICO.PathRecordingSupport
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A μ : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype μ] [DecidableEq μ]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem fockD_set_entry {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (o : A×Environment A) (i : ICO.RecordingOperatorSupport.Basis A) :
    fockD hT o (setEmbedding hT i)=ICO.MHRecordDecompression.D o i := by
  have he : fockD hT*basisEmbedding (setEmbedding hT)=ICO.MHRecordDecompression.D := by
    rw [fockD,Matrix.mul_assoc,basisEmbedding_gram _ (setEmbedding_injective hT),Matrix.mul_one]
  change fockD hT*(1 : CMatrix (InputCutoff (α := A) T)).submatrix (Equiv.refl _) (setEmbedding hT)=_ at he
  rw [Matrix.mul_submatrix_one] at he
  exact congrArg (fun M => M o i) he

theorem emptyFock_set {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (x : A) :
    emptyFock T x=setEmbedding hT (x,∅,∅) := by
  apply fockLabel_injective T
  rw [empty_label,setEmbedding_label]
  rfl

theorem fockD_empty {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (o : A×Environment A) (x : A) :
    fockD hT o (emptyFock T x)=if o.1=x then initialVector o.2 else 0 := by
  rw [emptyFock_set hT,fockD_set_entry]
  have hv : Valid ((∅ : Relation A A),∅) := emptyRecord.property
  simp only [ICO.MHRecordDecompression.D,recordMap,dif_pos hv,initialVector,emptyRecord]

def frequencyInitial (v : A×μ→ℂ) : (A×Environment A)×μ→ℂ :=
  fun o => initialVector o.1.2*v (o.1.1,o.2)

theorem decompression_initial {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (v : A×μ→ℂ) :
    memoryD hT μ*ᵥinitial T v=frequencyInitial v := by
  rw [initial,Matrix.mulVec_mulVec]
  change ((memoryD hT μ)*(1 : CMatrix (InputCutoff (α := A) T×μ)).submatrix (Equiv.refl _) (initialEmbed T))*ᵥv=_
  rw [Matrix.mul_submatrix_one]
  funext o
  simp only [Matrix.mulVec,dotProduct,Matrix.submatrix_apply,id_eq,memoryD,Matrix.kronecker,
    Matrix.kroneckerMap_apply,initialEmbed,fockD_empty,Matrix.one_apply,ite_mul,mul_ite,mul_one,mul_zero]
  simp [Fintype.sum_prod_type,ICO.MHFockTrajectory.initialEmbed,fockD_empty,frequencyInitial]

#print axioms decompression_initial
end
end ICO.MHDecompressionInitial
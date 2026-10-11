import ICO.MHFockDecompression
import ICO.MHFockKnownOperation

/-! Decompression acts only on private records, so it commutes with every
rectangular accessible-memory operation, including fresh private copies. -/
namespace ICO.MHDecompressionKnown
open Matrix QIT ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockLabels ICO.MHFockNodup
  ICO.MHFockDecompression ICO.MHFockKnownOperation ICO.RecordingCopyIdentity
  ICO.MHTernaryCompression ICO.MHRecordDecompression ICO.RecordingOperatorSupport ICO.PathRecordingSupport
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A μ ν : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def recordSetEmbed {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (r : Relation A A×Relation A A) : Records (α := A) T :=
  records (setEmbedding hT (Classical.arbitrary A,r))

def queryRecordEquiv (T : ℕ) : InputCutoff (α := A) T≃A×Records (α := A) T where
  toFun i := (i.2.1,records i)
  invFun i := ⟨⟨i.2.1,i.2.2.2⟩,(i.1,i.2.2.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem setEmbedding_queryRecord {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (x : A)
    (r : Relation A A×Relation A A) :
    queryRecordEquiv T (setEmbedding hT (x,r))=(x,recordSetEmbed hT r) := rfl

def recordFockD {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    Matrix (Environment A) (Records (α := A) T) ℂ :=
  recordMap*(basisEmbedding (recordSetEmbed hT)).conjTranspose

theorem fockD_tensor {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) :
    fockD hT=(Matrix.kronecker (1 : CMatrix A) (recordFockD hT)).submatrix id (queryRecordEquiv T) := by
  ext o i
  simp only [fockD,Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  simp only [recordFockD,Matrix.mul_apply,Matrix.conjTranspose_apply,
    ICO.MHRecordDecompression.D,basisEmbedding,Matrix.submatrix_apply,
    id_eq,Matrix.one_apply,apply_ite,star_one,star_zero,Matrix.kronecker,Matrix.kroneckerMap_apply]
  have he (x : A) (r : Relation A A×Relation A A) :
      i=setEmbedding hT (x,r) ↔ i.2.1=x ∧ records i=recordSetEmbed hT r := by
    rw [← (queryRecordEquiv T).injective.eq_iff,setEmbedding_queryRecord]
    simp only [queryRecordEquiv,Equiv.coe_fn_mk,Prod.mk.injEq]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    queryRecordEquiv,Equiv.coe_fn_mk]
  by_cases hi : o.1=i.2.1
  · simp [hi,ite_and]
  · simp [hi,Ne.symm hi,ite_and]
/-- Move environment past public memory. -/
def environmentFirst (μ : Type*) : ((A×Environment A)×μ)≃(A×μ)×Environment A where
  toFun i := ((i.1.1,i.2),i.1.2)
  invFun i := ((i.1.1,i.2),i.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def physicalKnown (K : Matrix (A×ν) (A×μ) ℂ) :
    Matrix ((A×Environment A)×ν) ((A×Environment A)×μ) ℂ :=
  (Matrix.kronecker K (1 : CMatrix (Environment A))).submatrix (environmentFirst ν) (environmentFirst μ)

def memoryD {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (μ : Type*) [Fintype μ] [DecidableEq μ] :
    Matrix ((A×Environment A)×μ) (InputCutoff (α := A) T×μ) ℂ :=
  Matrix.kronecker (fockD hT) (1 : CMatrix μ)

theorem memoryD_tensor {T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (μ : Type*) [Fintype μ] [DecidableEq μ] :
    memoryD hT μ=(Matrix.kronecker (1 : CMatrix (A×μ)) (recordFockD hT)).submatrix
      (environmentFirst μ) (queryMemoryFirst T μ) := by
  rw [memoryD,fockD_tensor]
  ext o i
  simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.submatrix_apply,queryRecordEquiv,
    environmentFirst,queryMemoryFirst,Equiv.coe_fn_mk,Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

theorem memoryD_known {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : Matrix (A×ν) (A×μ) ℂ) :
    physicalKnown K*memoryD hT μ=memoryD hT ν*known T K := by
  simp only [physicalKnown,memoryD_tensor,known,Matrix.submatrix_mul_equiv]
  simp only [Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul]

#print axioms memoryD_known
end
end ICO.MHDecompressionKnown
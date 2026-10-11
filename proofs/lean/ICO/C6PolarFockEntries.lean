import ICO.C6PolarReindex
import ICO.C6PolarFock

/-! Exact sector embeddings for the actual common-space polar creators. -/
namespace ICO.C6PolarFockEntries
open QIT ICO.C6PolarFock ICO.C6BosonicPolar ICO.C6BosonicRight ICO.C6PolarReindex
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHProfileTranspose ICO.RecordingCopyIdentity
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false

section Rectangular
variable {a b c:Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c]
theorem embedding_compression (f:a→c) (g:b→c) (M:CMatrix c) :
    (basisEmbedding f).conjTranspose*M*basisEmbedding g=M.submatrix f g := by
  simp only [basisEmbedding,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_one]
  change (1:CMatrix c).submatrix f (Equiv.refl c)*M*
    (1:CMatrix c).submatrix (Equiv.refl c) g=_
  rw [Matrix.one_submatrix_mul f (Equiv.refl c),Matrix.mul_submatrix_one (Equiv.refl c) g]
  rfl
end Rectangular

variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem left_compression {t T:ℕ} (h:t+1≤T) :
    (polarLeftOnFock (α:=A) h).submatrix (outputEmbed h)
      (inputEmbed (Nat.le_trans (Nat.le_succ t) h))=boundedPolar (α:=A) t := by
  rw [←embedding_compression,polarLeftOnFock]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (basisEmbedding (outputEmbed (α:=A) h)).conjTranspose
    (basisEmbedding (outputEmbed (α:=A) h)),outputEmbed_gram,Matrix.one_mul]
  rw [inputEmbed_gram,Matrix.mul_one]

theorem right_swap_entry {t T:ℕ} (h:t+1≤T) (o i:InputCutoff (α:=A) T) :
    polarRightOnFock h (recordSwap o) (recordSwap i)=polarLeftOnFock h o i := by
  have he : swapMatrix T*polarRightOnFock (α:=A) h*swapMatrix T=polarLeftOnFock h := by
    rw [polarRightOnFock,swapMatrix_selfAdjoint]
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc (swapMatrix (α:=A) T) (swapMatrix (α:=A) T),swapMatrix_sq,
      Matrix.one_mul,Matrix.mul_one]
  have hs : swapMatrix T*polarRightOnFock (α:=A) h*swapMatrix T=
      (polarRightOnFock h).submatrix (recordSwapEquiv T) (recordSwapEquiv T) := by
    rw [←basisEmbedding_compression]
    change swapMatrix T*_ *swapMatrix T=(swapMatrix T).conjTranspose*_ *swapMatrix T
    rw [swapMatrix_selfAdjoint]
  rw [hs] at he
  exact congrFun (congrFun he o) i

def rightInput {t T:ℕ} (h:t≤T) (s:Lengths t)
    (L:TensorPowerProfile (A×A) s.val.2.val) (v:Sector (A:=A) s.val.1.val) :
    InputCutoff (α:=A) T :=
  recordSwap (inputEmbed h ⟨⟨s,profileTranspose _ L⟩,(v.1,profileTranspose _ v.2)⟩)

def rightOutput {t T:ℕ} (h:t+1≤T) (s:Lengths t)
    (L:TensorPowerProfile (A×A) s.val.2.val) (v:Sector (A:=A) (s.val.1.val+1)) :
    InputCutoff (α:=A) T :=
  recordSwap (outputEmbed h ⟨⟨s,profileTranspose _ L⟩,(v.1,profileTranspose _ v.2)⟩)

theorem right_sector_entry {t T:ℕ} (h:t+1≤T) (s:Lengths t)
    (L:TensorPowerProfile (A×A) s.val.2.val)
    (o:Sector (A:=A) (s.val.1.val+1)) (i:Sector (A:=A) s.val.1.val) :
    polarRightOnFock h (rightOutput h s L o)
      (rightInput (Nat.le_trans (Nat.le_succ t) h) s L i)=rightPolar (A:=A) s.val.1.val o i := by
  rw [rightOutput,rightInput,right_swap_entry]
  have he := congrFun (congrFun (left_compression (A:=A) h)
    ⟨⟨s,profileTranspose _ L⟩,(o.1,profileTranspose _ o.2)⟩)
    ⟨⟨s,profileTranspose _ L⟩,(i.1,profileTranspose _ i.2)⟩
  change polarLeftOnFock h _ _=_ at he
  rw [he]
  simp only [boundedPolar,Matrix.blockDiagonal'_apply_eq]
  rw [rightPolar_transpose]
  rfl

#print axioms right_sector_entry
end
end ICO.C6PolarFockEntries

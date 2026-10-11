import ICO.C6PolarFock
import ICO.C6BosonicLabelSupport
import ICO.C6BosonicFreshContraction

/-! Literal allowed-label support on the common finite Fock space. -/
namespace ICO.C6BosonicFockSupport
open QIT ICO.C6PolarFock ICO.C6BosonicLabelSupport ICO.MHBoundedRecording
  ICO.MHFockSpace ICO.RecordingCopyIdentity ICO.C6BosonicFreshContraction
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000

section Embeddings
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem diagonal_embedding (e : a→b) (f : b→ℂ) :
    Matrix.diagonal f * basisEmbedding e = basisEmbedding e * Matrix.diagonal (f∘e) := by
  ext i j
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,basisEmbedding,Function.comp_apply]
  by_cases h : i=e j <;> simp [h,mul_comm]

theorem embedding_adjoint_diagonal (e : a→b) (f : b→ℂ) :
    (basisEmbedding e).conjTranspose * Matrix.diagonal f =
      Matrix.diagonal (f∘e) * (basisEmbedding e).conjTranspose := by
  ext i j
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.conjTranspose_apply,
    basisEmbedding,Function.comp_apply]
  by_cases h : j=e i <;> simp [h,mul_comm]
end Embeddings

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def fockRecord (S : Finset A) (T : ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  Matrix.diagonal (fun i => if LabelsIn S i.2.2 then 1 else 0)

def fockInput (S : Finset A) (T : ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  Matrix.diagonal (fun i => if i.2.1∈S ∧ LabelsIn S i.2.2 then 1 else 0)

def boundedOutputRecord (S : Finset A) (t : ℕ) : CMatrix (OutputCutoff (α:=A) t) :=
  Matrix.diagonal (fun i => if LabelsIn S i.2.2 then 1 else 0)

theorem bounded_polar_support (S : Finset A) (t : ℕ) (ht : t<Fintype.card A) :
    boundedOutputRecord S t * boundedPolar t = boundedPolar t * fockInput S t := by
  ext ⟨k,o⟩ ⟨l,i⟩
  simp only [boundedOutputRecord,fockInput,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases h : k=l
  · subst l
    have hn : k.1.val.1.val<Fintype.card A := by have hh:=k.1.property; omega
    have he := congrFun (congrFun (leftPolar_support S hn) o) i
    simpa only [recordSupport,inputSupport,Matrix.diagonal_mul,Matrix.mul_diagonal,
      boundedPolar,Matrix.blockDiagonal'_apply_eq] using he
  · simp [boundedPolar,Matrix.blockDiagonal'_apply,h]

theorem fock_polar_support (S : Finset A) {t T : ℕ} (h : t+1≤T)
    (ht : t<Fintype.card A) :
    fockRecord S T * polarLeftOnFock h = polarLeftOnFock h * fockInput S T := by
  have hO : fockRecord S T * basisEmbedding (outputEmbed (α:=A) h)=
      basisEmbedding (outputEmbed h) * boundedOutputRecord S t :=
    diagonal_embedding _ _
  have hI : (basisEmbedding (inputEmbed (α:=A) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose *
      fockInput S T = fockInput S t *
        (basisEmbedding (inputEmbed (α:=A) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose :=
    embedding_adjoint_diagonal _ _
  unfold polarLeftOnFock
  calc
    _ = (fockRecord S T*basisEmbedding (outputEmbed h))*boundedPolar t*
        (basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hO]
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc (boundedOutputRecord S t) (boundedPolar t),bounded_polar_support S t ht]
      simp only [Matrix.mul_assoc,←hI]

theorem fockRecord_adjoint (S : Finset A) (T : ℕ) :
    (fockRecord S T).conjTranspose=fockRecord S T := by
  rw [fockRecord,Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  simp only [Function.comp_apply,Pi.star_apply]
  split_ifs <;> simp

theorem fockInput_adjoint (S : Finset A) (T : ℕ) :
    (fockInput S T).conjTranspose=fockInput S T := by
  rw [fockInput,Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  simp only [Function.comp_apply,Pi.star_apply]
  split_ifs <;> simp

theorem fock_polar_adjoint_support (S : Finset A) {t T : ℕ} (h : t+1≤T)
    (ht : t<Fintype.card A) :
    fockInput S T * (polarLeftOnFock h).conjTranspose=
      (polarLeftOnFock h).conjTranspose * fockRecord S T := by
  have he := congrArg Matrix.conjTranspose (fock_polar_support S h ht)
  simpa only [Matrix.conjTranspose_mul,fockRecord_adjoint,fockInput_adjoint] using he.symm

def queryFresh (S : Finset A) (T : ℕ) : CMatrix (InputCutoff (α:=A) T) :=
  Matrix.diagonal (fun i => if i.2.1∉S then 1 else 0)

theorem fockRecord_projection (S : Finset A) (T : ℕ) : IsStarProjection (fockRecord S T) := by
  constructor
  · change fockRecord S T*fockRecord S T=fockRecord S T
    rw [fockRecord,Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  · exact fockRecord_adjoint S T

theorem queryFresh_projection (S : Finset A) (T : ℕ) : IsStarProjection (queryFresh S T) := by
  constructor
  · change queryFresh S T*queryFresh S T=queryFresh S T
    rw [queryFresh,Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  · change (queryFresh S T).conjTranspose=queryFresh S T
    rw [queryFresh,Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp only [Function.comp_apply,Pi.star_apply]
    split_ifs <;> simp

theorem queryFresh_fockInput_zero (S : Finset A) (T : ℕ) :
    queryFresh S T*fockInput S T=0 := by
  rw [queryFresh,fockInput,Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply,Pi.mul_apply,Matrix.zero_apply]
  by_cases h : i=j
  · subst j
    by_cases hi : i.2.1∈S <;> simp [hi]
  · simp [h]

theorem actual_freshInverse_contraction (S : Finset A) {t T : ℕ} (h : t+1≤T)
    (ht : t<Fintype.card A) :
    ‖freshInverse (polarLeftOnFock h) (polarRightOnFock h) (queryFresh S T) *
        fockRecord S T‖≤1 := by
  apply freshInverse_supported_norm
  · exact ICO.RecordingOracleAlgebra.image_projection _ _
      (polarLeftOnFock_gram h ht) (polarLeftOnFock_domain h)
  · exact polarRightOnFock_norm_le h ht
  · exact queryFresh_projection S T
  · exact fockRecord_projection S T
  · rw [Matrix.mul_assoc,←fock_polar_adjoint_support S h ht,
      ←Matrix.mul_assoc,queryFresh_fockInput_zero,Matrix.zero_mul]

#print axioms fock_polar_support
#print axioms fock_polar_adjoint_support
#print axioms actual_freshInverse_contraction
end
end ICO.C6BosonicFockSupport

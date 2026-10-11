import ICO.C6ProjectedInsertion
import ICO.MHFockKnownOperation
import ICO.MHFockEntries

/-! The query compression estimate on the common finite Fock space, with
coherence between all record-length sectors preserved. -/
namespace ICO.C6FockCompression
open Matrix QIT ICO.C6ProjectedInsertion ICO.MHBoundedRecording ICO.MHFockSpace
open ICO.MHFockKnownOperation ICO.MHBlockNorm ICO.MHERecordingApprox
open ICO.MHFockProjection ICO.RecordingCopyIdentity ICO.RecordingProcess
open ICO.MHEmbeddingProjector ICO.MHFockEntries
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
set_option Elab.async false
set_option synthInstance.maxSize 512
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev CreatedRecords (t : ℕ) := Σ k : Block (α:=A) t,
  TensorPowerProfile (A×A) (k.1.val.1.val+1)

def forgetQuery {t : ℕ} (o : OutputCutoff (α:=A) t) : CreatedRecords (A:=A) t :=
  ⟨o.1,o.2.2⟩

def blockQuery (t : ℕ) (ψ : A→ℂ) :
    Matrix (OutputCutoff (α:=A) t) (CreatedRecords (A:=A) t) ℂ :=
  Matrix.blockDiagonal' (fun k : Block (α:=A) t =>
    queryEmbedding (n:=k.1.val.1.val+1) ψ)

theorem blockQuery_entry {t : ℕ} (ψ : A→ℂ)
    (o : OutputCutoff (α:=A) t) (c : CreatedRecords (A:=A) t) :
    blockQuery t ψ o c = if forgetQuery o=c then ψ o.2.1 else 0 := by
  rcases o with ⟨k,o⟩
  rcases c with ⟨l,c⟩
  by_cases h : k=l
  · subst l
    simp [blockQuery, Matrix.blockDiagonal'_apply_eq, queryEmbedding,forgetQuery]
  · have he : (⟨k,o.2⟩ : CreatedRecords (A:=A) t)≠⟨l,c⟩ := by
      intro he
      exact h (congrArg Sigma.fst he)
    simp [blockQuery,Matrix.blockDiagonal'_apply',h,he,forgetQuery]

theorem bounded_compression {t : ℕ} (ψ : A→ℂ) (hψ : ∑ y,‖ψ y‖^2≤1)
    (ht : t<Fintype.card A) :
    ‖(boundedInsertion (α:=A) t).conjTranspose*blockQuery t ψ‖≤
      Real.sqrt ((t+1:ℝ)/((Fintype.card A:ℝ)-t)) := by
  rw [boundedInsertion,blockQuery,Matrix.blockDiagonal'_conjTranspose,
    ←Matrix.blockDiagonal'_mul]
  have hd : (0:ℝ)<Fintype.card A-t := by
    have hh : (t:ℝ)<Fintype.card A := by exact_mod_cast ht
    linarith
  apply blockDiagonal'_norm_le _ _ (by positivity)
  intro k
  have hsize : k.1.val.1.val+k.1.val.2.val<Fintype.card A := lt_of_le_of_lt k.1.property ht
  refine (actual_compressed_norm k.2 ψ hψ hsize).trans ?_
  apply Real.sqrt_le_sqrt
  have hlen : (k.1.val.1.val:ℝ)+k.1.val.2.val≤t := by exact_mod_cast k.1.property
  have hn : (0:ℝ)≤k.1.val.1.val := Nat.cast_nonneg _
  have hr : (0:ℝ)≤k.1.val.2.val := Nat.cast_nonneg _
  have hden : (Fintype.card A:ℝ)-t≤Fintype.card A-k.1.val.1.val-k.1.val.2.val := by linarith
  exact div_le_div₀ (by positivity) (by linarith) hd hden

def fockQuery (T : ℕ) (ψ : A→ℂ) :
    Matrix (InputCutoff (α:=A) T) (Records (α:=A) T) ℂ :=
  fun i R => if records i=R then ψ i.2.1 else 0

def createdEmbed {t T : ℕ} (h : t+1≤T) (c : CreatedRecords (A:=A) t) : Records (α:=A) T :=
  ⟨lengthGrow h c.1.1,(c.2,c.1.2)⟩

theorem createdEmbed_injective {t T : ℕ} (h : t+1≤T) :
    Function.Injective (createdEmbed (A:=A) h) := by
  intro c e he
  rcases c with ⟨⟨s,q⟩,p⟩
  rcases e with ⟨⟨s',q'⟩,p'⟩
  have hs0 := congrArg (fun R:Records (α:=A) T => R.1.val.1.val) he
  have hs1 := congrArg (fun R:Records (α:=A) T => R.1.val.2.val) he
  have hs : s=s' := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact Nat.add_right_cancel hs0
    · exact hs1
  subst s'
  have hq := congrArg (fun R:Records (α:=A) T => R.2.2.val) he
  have hq' : q=q' := Subtype.ext hq
  subst q'
  have hp := congrArg (fun R:Records (α:=A) T => R.2.1.val) he
  have hp' : p=p' := Subtype.ext hp
  subst p'
  rfl

theorem output_records {t T : ℕ} (h : t+1≤T) (o : OutputCutoff (α:=A) t) :
    records (outputEmbed h o)=createdEmbed h (forgetQuery o) := rfl

theorem output_query_intertwine {t T : ℕ} (h : t+1≤T) (ψ : A→ℂ) :
    (basisEmbedding (outputEmbed (α:=A) h)).conjTranspose*fockQuery T ψ =
      blockQuery t ψ*(basisEmbedding (createdEmbed h)).conjTranspose := by
  ext o R
  have hl : ((basisEmbedding (outputEmbed (α:=A) h)).conjTranspose*fockQuery T ψ) o R=
      fockQuery T ψ (outputEmbed h o) R :=
    congrFun (basisEmbedding_adjoint_mulVec (outputEmbed h) (fun i => fockQuery T ψ i R)) o
  rw [hl,Matrix.mul_apply]
  simp only [blockQuery_entry,ite_mul,zero_mul]
  simp [fockQuery,output_records,Matrix.conjTranspose_apply,basisEmbedding,
    Matrix.submatrix_apply,Matrix.one_apply,eq_comm]
  rfl

theorem left_fock_compression {t T : ℕ} (h : t+1≤T) (ψ : A→ℂ)
    (hψ : ∑ y,‖ψ y‖^2≤1) (ht : t<Fintype.card A) :
    ‖(leftOnFock (α:=A) h).conjTranspose*fockQuery T ψ‖≤
      Real.sqrt ((t+1:ℝ)/((Fintype.card A:ℝ)-t)) := by
  have hi := isometry_matrix_norm_le (basisEmbedding (inputEmbed (α:=A) (Nat.le_trans (Nat.le_succ t) h)))
    (inputEmbed_gram (Nat.le_trans (Nat.le_succ t) h))
  have hr := isometry_matrix_norm_le (basisEmbedding (createdEmbed (A:=A) h))
    (basisEmbedding_gram _ (createdEmbed_injective h))
  have hr' : ‖(basisEmbedding (createdEmbed (A:=A) h)).conjTranspose‖≤1 := by
    rwa [Matrix.l2_opNorm_conjTranspose]
  have he : (leftOnFock (α:=A) h).conjTranspose*fockQuery T ψ =
      basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))*
      ((boundedInsertion t).conjTranspose*blockQuery t ψ)*
      (basisEmbedding (createdEmbed h)).conjTranspose := by
    rw [leftOnFock,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [output_query_intertwine]
  rw [he]
  calc
    _ ≤ (‖basisEmbedding (inputEmbed (Nat.le_trans (Nat.le_succ t) h))‖*
      ‖(boundedInsertion (α:=A) t).conjTranspose*blockQuery t ψ‖)*
      ‖(basisEmbedding (createdEmbed h)).conjTranspose‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*Real.sqrt ((t+1:ℝ)/((Fintype.card A:ℝ)-t)))*1 :=
      mul_le_mul (mul_le_mul hi (bounded_compression ψ hψ ht) (norm_nonneg _) (by norm_num))
        hr' (norm_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms left_fock_compression
end
end ICO.C6FockCompression

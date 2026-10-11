import ICO.MHFockTrajectory
import ICO.MHFockLowInput

/-! Exact transport of accessible operations from finite-set records to the
full occupation register. The no-repeat subspace is preserved literally. -/
namespace ICO.MHFockFiniteKnown
open QIT ICO.MHFockTrajectory ICO.MHFockKnownOperation ICO.MHFockLabels ICO.MHFockNodup
  ICO.MHBoundedRecording ICO.MHOccupationCounts ICO.RecordingOperatorSupport
  ICO.RecordingMultisetBridge ICO.RecordingCopyIdentity ICO.MHFockSpace
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 512
variable {α : Type*} [Fintype α] [DecidableEq α]

def recordLabels (T : ℕ) (R : Records (α := α) T) : Multiset (α×α) × Multiset (α×α) :=
  (occupationMultiset _ R.2.1,occupationMultiset _ R.2.2)

theorem records_labels {T : ℕ} (v : InputCutoff (α := α) T) :
    recordLabels T (records v)=(fockLabel v).2 := rfl

theorem set_records_eq {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (o i : Basis α) :
    records (setEmbedding hT o)=records (setEmbedding hT i) ↔ o.2=i.2 := by
  constructor
  · intro he
    have hh := congrArg (recordLabels T) he
    simp only [records_labels,setEmbedding_label,embed] at hh
    apply Prod.ext
    · exact Finset.val_injective (congrArg Prod.fst hh)
    · exact Finset.val_injective (congrArg Prod.snd hh)
  · rcases o with ⟨x,L,R⟩
    rcases i with ⟨y,L',R'⟩
    intro he
    have heL := congrArg Prod.fst he
    have heR := congrArg Prod.snd he
    dsimp only at heL heR
    subst L'
    subst R'
    rfl

def setMemory {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) {μ : Type*}
    (i : Basis α×μ) : InputCutoff (α := α) T×μ := (setEmbedding hT i.1,i.2)

theorem setMemory_injective {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (μ : Type*) :
    Function.Injective (setMemory hT (μ := μ)) := by
  intro i j he
  apply Prod.ext
  · exact setEmbedding_injective hT (congrArg (fun i : InputCutoff (α := α) T×μ => i.1) he)
  · exact congrArg (fun i : InputCutoff (α := α) T×μ => i.2) he

theorem setMemory_matrix {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    {μ : Type*} [Fintype μ] [DecidableEq μ] :
    basisEmbedding (setMemory hT (μ := μ))=
      Matrix.kronecker (basisEmbedding (setEmbedding hT)) (1 : CMatrix μ) := by
  ext o i
  simp only [basisEmbedding,Matrix.submatrix_apply,id_eq,Matrix.one_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,setMemory,Prod.ext_iff]
  split_ifs <;> simp_all

theorem embedding_intertwining {a b c d : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (f : a→b) (g : c→d) (hg : Function.Injective g) (M : Matrix d b ℂ) (N : Matrix c a ℂ)
    (hentry : ∀o i,M (g o) (f i)=N o i)
    (hsupport : ∀o i,M o (f i)≠0→∃j,g j=o) :
    M*basisEmbedding f=basisEmbedding g*N := by
  have hm : M*basisEmbedding f=M.submatrix id f := by
    change M*(1 : CMatrix b).submatrix (Equiv.refl b) f=_
    rw [Matrix.mul_submatrix_one]
    rfl
  rw [hm]
  ext o i
  change M o (f i)=(basisEmbedding g*N) o i
  by_cases ho : ∃j,g j=o
  · obtain ⟨j,rfl⟩ := ho
    rw [hentry]
    simp [Matrix.mul_apply,basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,hg.eq_iff]
  · have hz : M o (f i)=0 := by by_contra hn; exact ho (hsupport o i hn)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hn : o≠g j := fun he => ho ⟨j,he.symm⟩
    simp [basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,hn]

theorem known_set_intertwining {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    {μ ν : Type*} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (K : Matrix (α×ν) (α×μ) ℂ) :
    known T K*basisEmbedding (setMemory hT (μ := μ))=
      basisEmbedding (setMemory hT (μ := ν))*knownOperation K := by
  apply embedding_intertwining _ _ (setMemory_injective hT ν)
  · intro o i
    simp only [known_coefficient,setMemory,set_records_eq]
    change K (o.1.1,o.2) (i.1.1,i.2)*(if o.1.2=i.1.2 then 1 else 0)=_
    simp only [knownOperation]
    split_ifs <;> simp_all
  · intro o i hi
    have he := congrArg (recordLabels T) (known_records T K o (setMemory hT i) hi)
    simp only [records_labels,setMemory,setEmbedding_label,embed] at he
    have hn : NodupLabel (fockLabel o.1) := by
      change (fockLabel o.1).2.1.Nodup ∧ (fockLabel o.1).2.2.Nodup
      rw [congrArg Prod.fst he,congrArg Prod.snd he]
      exact ⟨i.1.2.1.nodup,i.1.2.2.nodup⟩
    obtain ⟨j,hj⟩ := (setEmbedding_range hT o.1).mpr hn
    exact ⟨(j,o.2),Prod.ext hj rfl⟩

#print axioms known_set_intertwining
end
end ICO.MHFockFiniteKnown

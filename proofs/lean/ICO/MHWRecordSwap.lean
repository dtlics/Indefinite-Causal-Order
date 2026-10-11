import ICO.MHWRecordEntries
import ICO.MHWDomainProjection
import ICO.MHFockRightEntries
import ICO.MHFockBothCovariance

/-! The actual partial recording oracle has the forward/inverse record symmetry. -/
namespace ICO.MHWRecordSwap
open Matrix QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.MHWPartial ICO.MHBijectionProfiles ICO.MHBoundedRecording
  ICO.MHFockSpace ICO.MHFockLabels ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHFockRightEntries ICO.MHWEmbedding ICO.MHWDomainProjection
  ICO.RecordingMultisetBridge ICO.MHFockNodup ICO.RecordingCopyIdentity
  ICO.MHFockEntries
  ICO.MHFockBothCovariance ICO.MHFockProjection ICO.MHFockAlgebra
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def relSwap (L : Relation α α) : Relation α α :=
  L.map (Equiv.prodComm α α).toEmbedding

@[simp] theorem mem_relSwap (L : Relation α α) (x y : α) :
    (x,y)∈relSwap L ↔ (y,x)∈L := by
  simp only [relSwap,Finset.mem_map_equiv,Equiv.prodComm_symm,Equiv.prodComm_apply,
    Prod.swap_prod_mk]

@[simp] theorem relSwap_twice (L : Relation α α) : relSwap (relSwap L)=L := by
  ext z
  rcases z with ⟨x,y⟩
  simp

@[simp] theorem relSwap_card (L : Relation α α) : (relSwap L).card=L.card :=
  Finset.card_map _

@[simp] theorem relSwap_val (L : Relation α α) : (relSwap L).val=L.val.map Prod.swap := rfl

theorem relSwap_union (L R : Relation α α) : relSwap (L∪R)=relSwap L∪relSwap R := by
  exact Finset.map_union _ _

theorem relSwap_insert (L : Relation α α) (x y : α) :
    relSwap (insert (x,y) L)=insert (y,x) (relSwap L) := by
  exact Finset.map_insert _ _ _

def setSwap (i : Basis α) : Basis α := (i.1,relSwap i.2.2,relSwap i.2.1)

@[simp] theorem setSwap_twice (i : Basis α) : setSwap (setSwap i)=i := by
  rcases i with ⟨x,L,R⟩
  simp [setSwap]

def setSwapEquiv : Basis α ≃ Basis α :=
  ⟨setSwap,setSwap,setSwap_twice,setSwap_twice⟩

theorem bijMultiset_swap (L R : Multiset (α×α)) :
    BijMultiset (R.map Prod.swap) (L.map Prod.swap) ↔ BijMultiset L R := by
  simp only [BijMultiset,←Multiset.map_add,Multiset.map_map,Function.comp_def,
    Prod.fst_swap,Prod.snd_swap]
  rw [Multiset.add_comm R L]
  exact and_comm

theorem bijRecord_swap (L R : Relation α α) :
    BijRecord (relSwap R) (relSwap L) ↔ BijRecord L R := by
  rw [←bijMultiset_sets,relSwap_val,relSwap_val,bijMultiset_swap,bijMultiset_sets]

theorem freshLeft_swap (x : α) (L R : Relation α α) :
    FreshLeft x (relSwap R∪relSwap L) ↔ FreshRight x (L∪R) := by
  simp only [FreshLeft,FreshRight,Finset.mem_union,mem_relSwap]
  simp only [or_comm]

theorem freshRight_swap (x : α) (L R : Relation α α) :
    FreshRight x (relSwap R∪relSwap L) ↔ FreshLeft x (L∪R) := by
  simp only [FreshLeft,FreshRight,Finset.mem_union,mem_relSwap]
  simp only [or_comm]

theorem leftPredicate_swap (i : Basis α) : leftPredicate (setSwap i) ↔ rightPredicate i := by
  simp only [leftPredicate,rightPredicate,setSwap,bijRecord_swap,freshLeft_swap,relSwap_card]
  rw [Nat.add_comm i.2.2.card i.2.1.card]

theorem leftStep_swap (i o : Basis α) : LeftStep (setSwap i) (setSwap o) ↔ RightStep i o := by
  simp only [LeftStep,RightStep,setSwap,freshRight_swap]
  have hi : Function.Injective (relSwap (α:=α)) :=
    Function.LeftInverse.injective relSwap_twice
  rw [hi.eq_iff,←relSwap_insert,hi.eq_iff]

theorem image_swap (L R : Relation α α) :
    ((relSwap R∪relSwap L).image Prod.snd)=leftDomain (L∪R) := by
  ext x
  simp only [Finset.mem_image,Finset.mem_union,leftDomain]
  constructor
  · rintro ⟨⟨a,b⟩,h,rfl⟩
    exact ⟨(b,a),by simpa only [mem_relSwap,or_comm] using h,rfl⟩
  · rintro ⟨⟨a,b⟩,h,rfl⟩
    exact ⟨(b,a),by simpa only [mem_relSwap,or_comm] using h,rfl⟩

theorem leftInsertion_swap (o i : Basis α) :
    leftInsertion (setSwap o) (setSwap i)=rightInsertion o i := by
  simp only [leftInsertion,rightInsertion,setSwap,relSwap_card]
  change (if i.2.2.card+i.2.1.card<Fintype.card α ∧
      LeftStep (setSwap i) (setSwap o) then _ else 0)=_
  rw [leftStep_swap,image_swap,Nat.add_comm i.2.2.card i.2.1.card]

theorem leftW_swap (o i : Basis α) : leftW (setSwap o) (setSwap i)=rightW o i := by
  simp only [leftW,rightW,leftProjection,rightProjection,predicateProjection,Matrix.mul_diagonal]
  rw [leftInsertion_swap]
  simp only [leftPredicate_swap]

theorem oracleW_swap (o i : Basis α) :
    oracleW (setSwap o) (setSwap i)=oracleW.conjTranspose o i := by
  have hr : rightW (setSwap i) (setSwap o)=leftW i o := by
    simpa only [setSwap_twice] using (leftW_swap (setSwap i) (setSwap o)).symm
  simp only [oracleW,Matrix.add_apply,Matrix.conjTranspose_apply,leftW_swap,hr,star_add,
    star_star]
  exact add_comm _ _

theorem recordSwap_setEmbedding {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (i : Basis α) :
    recordSwap (setEmbedding hT i)=setEmbedding hT (setSwap i) := by
  apply fockLabel_injective T
  rw [fockLabel_recordSwap,setEmbedding_label,setEmbedding_label]
  simp only [embed,swapLabel,setSwap,relSwap_val]

theorem recordW_entry_swap {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (o i : InputCutoff (α:=α) T) :
    recordW hT (recordSwap o) (recordSwap i)=(recordW hT).conjTranspose o i := by
  by_cases ho : ∃ x, setEmbedding hT x=o
  · obtain ⟨o,rfl⟩ := ho
    by_cases hi : ∃ x, setEmbedding hT x=i
    · obtain ⟨i,rfl⟩ := hi
      rw [recordSwap_setEmbedding,recordSwap_setEmbedding,recordW,
        embedding_sandwich_entry _ _ (setEmbedding_injective hT) (setEmbedding_injective hT),
        Matrix.conjTranspose_apply,embedding_sandwich_entry _ _
          (setEmbedding_injective hT) (setEmbedding_injective hT)]
      exact oracleW_swap o i
    · have hsi : ¬∃ x, setEmbedding hT x=recordSwap i := by
        rintro ⟨x,hx⟩
        apply hi
        refine ⟨setSwap x,?_⟩
        have hh := congrArg recordSwap hx
        simpa only [recordSwap_setEmbedding,recordSwap_involutive] using hh
      simp only [recordW,Matrix.conjTranspose_apply]
      rw [ICO.MHWRecordEntries.embedding_sandwich_zero_col _ _ _ _ hsi,
        ICO.MHWRecordEntries.embedding_sandwich_zero_row _ _ _ _ hi,star_zero]
  · have hso : ¬∃ x, setEmbedding hT x=recordSwap o := by
      rintro ⟨x,hx⟩
      apply ho
      refine ⟨setSwap x,?_⟩
      have hh := congrArg recordSwap hx
      simpa only [recordSwap_setEmbedding,recordSwap_involutive] using hh
    simp only [recordW,Matrix.conjTranspose_apply]
    rw [ICO.MHWRecordEntries.embedding_sandwich_zero_row _ _ _ _ hso,
      ICO.MHWRecordEntries.embedding_sandwich_zero_col _ _ _ _ ho,star_zero]

theorem recordW_swap {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    swapMatrix T*recordW hT*swapMatrix T=(recordW hT).conjTranspose := by
  nth_rw 1 [←swapMatrix_selfAdjoint]
  change (basisEmbedding (recordSwapEquiv T)).conjTranspose*recordW hT*
    basisEmbedding (recordSwapEquiv T)=_
  rw [basisEmbedding_compression]
  ext o i
  exact recordW_entry_swap hT o i

theorem bijProjection_swap (T : ℕ) :
    swapMatrix (α:=α) T*bijProjection T*swapMatrix T=bijProjection T := by
  nth_rw 1 [←swapMatrix_selfAdjoint]
  change (basisEmbedding (recordSwapEquiv (α:=α) T)).conjTranspose*bijProjection T*
    basisEmbedding (recordSwapEquiv (α:=α) T)=_
  rw [basisEmbedding_compression]
  ext o i
  by_cases he : o=i
  · subst i
    simp only [bijProjection,Matrix.submatrix_apply,Matrix.diagonal_apply_eq,
      recordSwapEquiv,Equiv.coe_fn_mk,fockLabel_recordSwap,swapLabel,bijMultiset_swap]
  · have hs : recordSwapEquiv T o≠recordSwapEquiv T i :=
      fun h => he ((recordSwapEquiv T).injective h)
    simp only [bijProjection,Matrix.submatrix_apply,Matrix.diagonal_apply_ne _ he,
      Matrix.diagonal_apply_ne _ hs]

theorem involution_sandwich_mul {H : Type*} [Fintype H] [DecidableEq H]
    (S A B : CMatrix H) (hS : S*S=1) :
    S*(A*B)*S=(S*A*S)*(S*B*S) := by
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc S S,hS,Matrix.one_mul]

theorem recordW_adjoint_swap {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    swapMatrix T*(recordW hT).conjTranspose*swapMatrix T=recordW hT := by
  rw [←recordW_swap hT]
  simp only [←Matrix.mul_assoc,swapMatrix_sq,Matrix.one_mul]
  rw [Matrix.mul_assoc,swapMatrix_sq,Matrix.mul_one]

theorem recordGram_swap {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    swapMatrix T*((recordW hT).conjTranspose*recordW hT)*swapMatrix T=
      recordW hT*(recordW hT).conjTranspose := by
  rw [involution_sandwich_mul _ _ _ (swapMatrix_sq T),recordW_adjoint_swap,recordW_swap]

theorem missingInverse_swap {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) :
    swapMatrix T*(bijProjection T-(recordW hT).conjTranspose*recordW hT)*swapMatrix T=
      bijProjection T-recordW hT*(recordW hT).conjTranspose := by
  rw [Matrix.mul_sub,Matrix.sub_mul,bijProjection_swap,recordGram_swap]

theorem involution_sandwich_adjoint {H : Type*} [Fintype H] [DecidableEq H]
    (S A : CMatrix H) (hS : S.conjTranspose=S) :
    S*A.conjTranspose*S=(S*A*S).conjTranspose := by
  simp only [Matrix.conjTranspose_mul,hS,Matrix.mul_assoc]

theorem fullOracle_swap {t T : ℕ} (h : t+1≤T) :
    swapMatrix (α:=α) T*ICO.MHFockOracle.fullOracle h*swapMatrix T=
      (ICO.MHFockOracle.fullOracle h).conjTranspose := by
  have hl : swapMatrix (α:=α) T*leftOnFock h*swapMatrix T=rightOnFock h := by
    simp only [rightOnFock,swapMatrix_selfAdjoint]
  have hr : swapMatrix (α:=α) T*rightOnFock h*swapMatrix T=leftOnFock h := by
    simp only [rightOnFock,swapMatrix_selfAdjoint,←Matrix.mul_assoc,swapMatrix_sq,Matrix.one_mul]
    rw [Matrix.mul_assoc,swapMatrix_sq,Matrix.mul_one]
  have hsone : swapMatrix (α:=α) T*(1 : CMatrix (InputCutoff (α:=α) T))*swapMatrix T=1 := by
    rw [Matrix.mul_one,swapMatrix_sq]
  simp only [ICO.MHFockOracle.fullOracle,Matrix.mul_add,Matrix.add_mul]
  simp only [swap_mul,swap_sub,involution_sandwich_adjoint _ _ (swapMatrix_selfAdjoint T),
    hl,hr,hsone]
  simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_mul,Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  exact add_comm _ _

theorem source_swap {t T : ℕ} (ht : t≤T) :
    swapMatrix (α:=α) T*sourceProjection ht*swapMatrix T=sourceProjection ht := by
  rw [←(source_commute_swap ht).eq,Matrix.mul_assoc,swapMatrix_sq,Matrix.mul_one]

theorem recordW_inverse_overlap_low {t T : ℕ} (h : t+1≤T)
    (hT : 2*Fintype.card (α×α)≤T) (ht : t<Fintype.card α) :
    recordW hT*(ICO.MHFockOracle.fullOracle h).conjTranspose*
        sourceProjection (Nat.le_trans (Nat.le_succ t) h)=
      recordW hT*(recordW hT).conjTranspose*
        sourceProjection (Nat.le_trans (Nat.le_succ t) h) := by
  have hh := congrArg (fun M : CMatrix (InputCutoff (α:=α) T) => swapMatrix T*M*swapMatrix T)
    (recordW_overlap_low h hT ht)
  simpa only [swap_mul,recordW_adjoint_swap,recordW_swap,fullOracle_swap,source_swap]
    using hh

#print axioms recordW_swap
#print axioms bijProjection_swap
#print axioms recordW_inverse_overlap_low
end
end ICO.MHWRecordSwap

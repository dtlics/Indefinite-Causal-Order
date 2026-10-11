import ICO.C6RightImageErasure
import ICO.C6RightHistorySupport
import ICO.C6ActualAcceptedModes
import ICO.C6RawSelectedSector
import ICO.C6ModeFockEncoding
import ICO.C6RawFlags

/-! A literal orthogonal-mode encoding lies in the occupation support of
any projection fixing its supplied label vectors. -/
namespace ICO.C6EncodingSupport
open Matrix QIT ICO.C6RightImageErasure ICO.C6ModeEncoding ICO.C6ModeBirthProduct
  ICO.C6OrthogonalModeBirth ICO.C6OrthogonalFrame ICO.C6BosonicLabelSupport
  ICO.C6BosonicWordSupport ICO.C6BosonicGeometricSupport ICO.C6CacheSpanProjection
  ICO.MHSymmetric ICO.MHCreationCovariance ICO.MHOccupationCovariance ICO.RecordingCopyIdentity
  ICO.MHProtocolOverlap ICO.C6CacheHistorySpan ICO.C6AcceptedModes
  ICO.C6ResidualModes ICO.C6HistoryConjugation ICO.C6ActualAcceptedModes
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem profile_allowed_range {n:ℕ} (labels images:Fin n→A) (S:Finset A)
    (h:∀i,labels i∈S) : LabelsIn S (profile labels images) := by
  intro a ha
  change Fintype.card {j:Fin n // tensorPowerEquiv n
    ((tensorPowerEquiv n).symm (fun i=>(labels i,images i))) j=a}=0
  have he:IsEmpty {j:Fin n // tensorPowerEquiv n
    ((tensorPowerEquiv n).symm (fun i=>(labels i,images i))) j=a} := by
    constructor
    intro j
    have hj:labels j.val=a.1:=by
      simpa only [Equiv.apply_symm_apply] using congrArg Prod.fst j.property
    exact ha (hj ▸ h j.val)
  exact Fintype.card_eq_zero

theorem encode_support {n:ℕ} (labels:Fin n→A) (S:Finset A)
    (h:∀i,labels i∈S) : profileSupport S n*encode labels=encode labels := by
  ext p images
  rw [profileSupport,Matrix.diagonal_mul]
  by_cases hp:p=profile labels images
  · subst p
    rw [if_pos (profile_allowed_range labels images S h),one_mul]
  · simp only [encode,basisEmbedding,Matrix.submatrix_apply,id_eq,Matrix.one_apply,if_neg hp,mul_zero]

theorem rotated_encoding_support (U:Matrix.unitaryGroup A ℂ) {n:ℕ}
    (labels:Fin n→A) (S:Finset A) (h:∀i,labels i∈S) :
    occupationSupport (spanProjection U S) n*rotatedEncode U labels=rotatedEncode U labels := by
  rw [occupationSupport_rotated,rotatedEncode]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (occupationRotation (leftEdgeUnitary U 1) n)ᴴ,
    occupationRotation_gram,Matrix.one_mul,encode_support labels S h]

theorem fixed_projection {n:ℕ} (P:CMatrix A) (U:Matrix.unitaryGroup A ℂ)
    (labels:Fin n→A) (h:∀i,act P (column U (labels i))=column U (labels i)) :
    P*spanProjection U (Finset.univ.image labels)=spanProjection U (Finset.univ.image labels) := by
  apply (Matrix.toEuclideanCLM (n:=A) (𝕜:=ℂ)).injective
  apply ContinuousLinearMap.ext
  intro x
  change act (P*spanProjection U (Finset.univ.image labels)) x=_
  rw [act_mul]
  have hm:=projection_mem U (Finset.univ.image labels) x
  apply Submodule.span_induction (p:=fun y _=>act P y=y) _ _ _ _ hm
  · rintro _ ⟨a,rfl⟩
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp a.property
    simpa only [hi] using h i
  · exact map_zero _
  · intro a b _ _ ha hb;rw [map_add,ha,hb]
  · intro c y _ hy;rw [map_smul,hy]

theorem directEncoding_support {n:ℕ} (P:CMatrix A) (v:Fin n→EuclideanSpace ℂ A)
    (hv:Orthonormal ℂ v) (hP:∀i,act P (v i)=v i) :
    occupationSupport P n*directEncoding v=directEncoding v := by
  obtain ⟨U,labels,hl,he⟩:=unitary_extension v hv
  have hvcol:∀i,column U (labels i)=v i := by intro i;ext x;exact he i x
  have hd:directEncoding v=rotatedEncode U labels := by
    ext p images
    change directProduct n v images p=rotatedEncode U labels p images
    rw [directProduct_eq U n labels v he images,birthProduct_eq U n labels images hl]
  have hs:occupationSupport (spanProjection U (Finset.univ.image labels)) n*directEncoding v=
      directEncoding v := by
    rw [hd]
    exact rotated_encoding_support U labels _ (fun i=>Finset.mem_image_of_mem labels (Finset.mem_univ i))
  calc
    _ = occupationSupport P n*(occupationSupport (spanProjection U (Finset.univ.image labels)) n*directEncoding v) := by rw [hs]
    _ = _ := by
      rw [←Matrix.mul_assoc,occupationSupport_absorption U _ P
        (fixed_projection P U labels (fun i=>by rw [hvcol,hP])),hs]

theorem mode_mem_history {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (i:Fin n) :
    C6ResidualModes.mode v i∈historySpan v := by
  have hp:historySpan (prior v i)≤historySpan v := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Submodule.subset_span ⟨⟨j.val,lt_trans j.isLt i.isLt⟩,rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (historySpan_contains v i)
    (hp (projection_mem_prior v i)))

theorem accepted_projection {n:ℕ} (v:Fin n→EuclideanSpace ℂ A)
    (κ:ICO.RecordingPurifiedProtocol.History Bool n) (i:Fin (ICO.C6FlagCount.flagCount n κ)) :
    act (historyProjection v) (modes v κ i)=modes v κ i := by
  apply projection_fixes
  rw [(history_realization v).1]
  exact mode_mem_history v _

theorem accepted_encoding_support {n:ℕ} (v:Fin n→EuclideanSpace ℂ A)
    (κ:ICO.RecordingPurifiedProtocol.History Bool n) (hv:Valid v κ) :
    occupationSupport (historyProjection v) (ICO.C6FlagCount.flagCount n κ)*directEncoding (modes v κ)=
      directEncoding (modes v κ) :=
  directEncoding_support _ _ (modes_orthonormal v κ hv) (accepted_projection v κ)



theorem creation_zero (n:ℕ) : creationOccupation (a:=A×A) n 0=0 := by
  rw [ICO.MHOccupationCovariance.creationOccupation_expansion]
  simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero]

theorem directProduct_zero {n:ℕ} (v:Fin n→EuclideanSpace ℂ A)
    (i:Fin n) (hi:v i=0) (images:Fin n→A) : directProduct n v images=0 := by
  induction n with
  | zero=>exact i.elim0
  | succ n ih=>
    cases i using Fin.cases with
    | zero=>
      have hm:C6RightImageErasure.mode (v 0) (images 0)=0 := by
        rw [hi];funext z;simp [C6RightImageErasure.mode]
      rw [directProduct,hm,creation_zero,Matrix.zero_mulVec]
    | succ i=>
      rw [directProduct,ih (Fin.tail v) i hi (Fin.tail images),Matrix.mulVec_zero]

theorem directEncoding_zero {n:ℕ} (v:Fin n→EuclideanSpace ℂ A)
    (i:Fin n) (hi:v i=0) : directEncoding v=0 := by
  ext p images
  exact congrFun (directProduct_zero v i hi images) p

theorem invalid_encoding_zero {n:ℕ} (v:Fin n→EuclideanSpace ℂ A)
    (κ:ICO.RecordingPurifiedProtocol.History Bool n) (hv:¬Valid v κ) :
    directEncoding (modes v κ)=0 := by
  simp only [Valid,not_forall,Classical.not_imp,not_not] at hv
  obtain ⟨i,hi,hzero⟩:=hv
  obtain ⟨j,hj⟩:=ICO.C6AcceptedIndices.selected_range n κ i hi
  apply directEncoding_zero _ j
  simp only [modes,hj,C6ResidualModes.mode,hzero,smul_zero]

theorem accepted_encoding_support_all {n:ℕ} (v:Fin n→EuclideanSpace ℂ A)
    (κ:ICO.RecordingPurifiedProtocol.History Bool n) :
    occupationSupport (historyProjection v) (ICO.C6FlagCount.flagCount n κ)*directEncoding (modes v κ)=
      directEncoding (modes v κ) := by
  by_cases hv:Valid v κ
  · exact accepted_encoding_support v κ hv
  · rw [invalid_encoding_zero v κ hv,Matrix.mul_zero]

theorem act_conjugate (P:CMatrix A) (x:EuclideanSpace ℂ A) :
    act (P.map star) (bar x)=bar (act P x) := by
  ext a
  change (∑b,star (P a b)*star (x b))=star (∑b,P a b*x b)
  simp only [star_sum,star_mul,mul_comm]

theorem historyProjection_conjugate {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) :
    (historyProjection v).map star=historyProjection (fun i=>bar (v i)) := by
  apply (Matrix.toEuclideanCLM (n:=A) (𝕜:=ℂ)).injective
  apply ContinuousLinearMap.ext
  intro x
  change act ((historyProjection v).map star) x=act (historyProjection (fun i=>bar (v i))) x
  have h1:=act_conjugate (historyProjection v) (bar x)
  have h2:=projection_bar v (bar x)
  simp only [bar_bar] at h1 h2
  exact h1.trans h2.symm

open ICO.C6RightHistorySupport ICO.C6TwoFockSector ICO.C6TwoFockMemory
  ICO.C6TwoFockVisible ICO.C6CacheDecode ICO.C6CacheKnownOperation
  ICO.C6ModeFockEncoding ICO.C6RawSelectedSector ICO.MHFockTransport
  ICO.C6RawFlags ICO.C6RetainedHistory ICO.MHBoundedRecording

variable {M:Type} [Fintype M] [DecidableEq M]

theorem right_memory_factor (l r:ℕ) (D:CMatrix (TensorPowerProfile (A×A) r)) :
    Matrix.kronecker (1:CMatrix (Cache (A:=A) (M:=M) l)) D=
      (Matrix.kronecker (Matrix.kronecker (1:CMatrix (A×TensorPowerProfile (A×A) l)) D) (1:CMatrix M)).submatrix
        (sectorMemoryFirst (A:=A) (M:=M) l r) (sectorMemoryFirst (A:=A) (M:=M) l r) := by
  ext ⟨⟨s,m⟩,R⟩ ⟨⟨v,n⟩,S⟩
  simp [sectorMemoryFirst,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
    mul_assoc,mul_comm,mul_left_comm,ite_and]

#print axioms accepted_encoding_support

theorem right_memory_support (P:CMatrix A) (T l r:ℕ) (h:l+r≤T) :
    Matrix.kronecker (rightFockSupport P T) (1:CMatrix M)*memoryJ T l r h=
      memoryJ (A:=A) (M:=M) T l r h*
        Matrix.kronecker (1:CMatrix (Cache (A:=A) (M:=M) l)) (occupationSupport (P.map star) r) := by
  rw [memoryJ_factor,right_memory_factor]
  rw [mul_submatrix_id,Matrix.submatrix_mul_equiv _ _ _
    (sectorMemoryFirst (A:=A) (M:=M) l r)]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
  rw [show rightFockSupport P T*J T l r h=J T l r h*rightSupportSector P l r from
    family_sector (rightSupportSector P) T l r h]
  rfl

theorem encoding_support (P:CMatrix A) (T l r:ℕ) (h:l+r≤T)
    (v:Fin r→EuclideanSpace ℂ A)
    (hv:occupationSupport (P.map star) r*directEncoding v=directEncoding v) :
    Matrix.kronecker (rightFockSupport P T) (1:CMatrix M)*encoding T l r h v=
      encoding (M:=M) T l r h v := by
  rw [encoding,←Matrix.mul_assoc,right_memory_support,Matrix.mul_assoc]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.one_mul,hv]

theorem historyZero_encoding (H:Matrix.unitaryGroup A ℂ) (n T l:ℕ)
    (η:ICO.RecordingPurifiedProtocol.History (A×Bool) n)
    (κ:ICO.RecordingPurifiedProtocol.History Bool n) (h:l+ICO.C6FlagCount.flagCount n κ≤T) :
    Matrix.kronecker (historyZero H n T η) (1:CMatrix M)*
      encoding T l (ICO.C6FlagCount.flagCount n κ) h (modes (rightVectors H n η) κ)=
      encoding (M:=M) T l (ICO.C6FlagCount.flagCount n κ) h (modes (rightVectors H n η) κ) := by
  rw [historyZero,zero_number_geometric]
  apply encoding_support
  change occupationSupport ((historyProjection (vectors H n η)).map star)
    (ICO.C6FlagCount.flagCount n κ)*directEncoding (modes (rightVectors H n η) κ)=
      directEncoding (modes (rightVectors H n η) κ)
  rw [historyProjection_conjugate]
  exact accepted_encoding_support_all (rightVectors H n η) κ

#print axioms accepted_encoding_support_all
#print axioms historyProjection_conjugate
#print axioms historyZero_encoding
end
end ICO.C6EncodingSupport


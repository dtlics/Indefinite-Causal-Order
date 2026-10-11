import ICO.C6BosonicBlocks
import ICO.MHFockEmptyRotation

/-! The actual empty recording state satisfies the geometric history and
right-record support projections. -/
namespace ICO.C6BosonicVacuum
open QIT ICO.C6BosonicBlocks ICO.C6BosonicHistorySupport ICO.C6BosonicGeometricSupport
  ICO.C6BosonicWordSupport ICO.C6WordPower ICO.C6RetainedHistory ICO.C6HistoryControlled
  ICO.C6FockQueryMatrix ICO.C6CacheSpanProjection ICO.MHFockTrajectory ICO.MHFockLabels
  ICO.MHFockTransport ICO.MHFockSpace ICO.MHBoundedRecording ICO.MHSymmetric
  ICO.RecordingCopyIdentity ICO.MHRectangularAction
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem occupationSupport_zero (P:CMatrix A) : occupationSupport P 0=1 := by
  rw [occupationSupport,wordPower,Matrix.mul_one,occupationEmbedding_gram]

theorem support_empty (P:CMatrix A) (T:ℕ) (o:InputCutoff (α:=A) T) (x:A) :
    fockSupport P T o (emptyFock T x)=if o=emptyFock T x then 1 else 0 := by
  rcases o with ⟨⟨s,q⟩,y,p⟩
  by_cases hs:s=(emptyFock T x).1.1
  · subst s
    simp only [emptyFock,labelFock,Multiset.card_zero,fockSupport,inputFamily,
      ICO.MHFockRotation.sectorEquiv,Matrix.submatrix_apply,supportSector,occupationSupport_zero,
      Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.blockDiagonal'_apply_eq]
    split_ifs <;> simp_all [occupationSupport_zero,Matrix.one_apply]
    all_goals erw [Matrix.one_apply]
    all_goals simp_all
    all_goals aesop
  · have hz := inputFamily_other (supportSector P) T ⟨⟨s,q⟩,(y,p)⟩ (emptyFock T x) hs
    have hn : (⟨⟨s,q⟩,(y,p)⟩:InputCutoff (α:=A) T)≠emptyFock T x := by
      intro he
      exact hs (congrArg (fun i:InputCutoff (α:=A) T=>i.1.1) he)
    rw [show fockSupport P T ⟨⟨s,q⟩,(y,p)⟩ (emptyFock T x)=0 from hz,if_neg hn]

theorem prefix_empty (H:Matrix.unitaryGroup A ℂ) (T:ℕ)
    (η:ICO.RecordingPurifiedProtocol.History (A×Bool) 0) (o:InputCutoff (α:=A) T) (x:A) :
    prefixMask H 0 T η o (emptyFock T x)=if o=emptyFock T x then 1 else 0 := by
  rw [prefixMask,rightLengthMask_diagonal,Matrix.mul_diagonal]
  have he : (emptyFock (α:=A) T x).1.1.val.2.val=0 := rfl
  simp only [he,le_refl,ite_true,mul_one,historySupport]
  exact support_empty _ T o x

theorem family_initial {T:ℕ} {M:Type} [Fintype M] [DecidableEq M]
    (F:M→CMatrix (InputCutoff (α:=A) T))
    (hF:∀m o x,F m o (emptyFock T x)=if o=emptyFock T x then 1 else 0) :
    diagonalFamily F*basisEmbedding (initialEmbed (α:=A) (μ:=M) T)=
      basisEmbedding (initialEmbed T) := by
  unfold basisEmbedding
  change _*(1:CMatrix (InputCutoff (α:=A) T×M)).submatrix (Equiv.refl _) _=_
  rw [Matrix.mul_submatrix_one]
  ext o i
  change (if o.2=i.2 then F o.2 o.1 (emptyFock T i.1) else 0)=
    (if o=(emptyFock T i.1,i.2) then 1 else 0)
  rw [hF]
  by_cases ho:o.1=emptyFock T i.1 <;> by_cases hm:o.2=i.2 <;> simp [ho,hm,Prod.ext_iff]

theorem prefix_initial (H:Matrix.unitaryGroup A ℂ) (T:ℕ)
    {M:Type} [Fintype M] [DecidableEq M]
    (z:A×(Bool×(ICO.RecordingPurifiedProtocol.History (A×Bool) 0×M))→ℂ) :
    rectAct (controlled (M:=M) (prefixMask H 0 T)) (WithLp.toLp 2 (initial T z))=
      WithLp.toLp 2 (initial T z) := by
  change WithLp.toLp 2 (_*ᵥ(initial T z))=_
  rw [controlled_family,initial,Matrix.mulVec_mulVec,family_initial _ (fun m o x=>prefix_empty H T m.2.1 o x)]

#print axioms prefix_initial
end
end ICO.C6BosonicVacuum

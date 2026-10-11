import ICO.C6DecodedCoreErasure
import ICO.C6DecodedTags
import ICO.C6GradedTransport

namespace ICO.C6DecodedChoiceErasure
open Matrix QIT ICO.C6DecodedHistory ICO.C6DecodedTags ICO.C6DecodedCoreErasure
  ICO.C6CacheMemoryTags ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6GradedCacheReference ICO.C6GradedTransport ICO.C6RetainedGradeSupport
  ICO.C6RetainedSectorOperations ICO.C6RetainedChoice ICO.C6ChoiceCache
open scoped Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem core_choice (U:Matrix.unitaryGroup A ℂ) (j:A) (c:ℂ) (r:ℕ) (f b:Bool) :
    core (M:=Bool×M) U j c r f*choiceImages r b=
      imageTag (r+if f then 1 else 0) b*core (M:=M) U j c r f*(imageTag r b)ᴴ := by
  rw [choiceImages_eq,←Matrix.mul_assoc,core_tag]

theorem imageTag_erasure (r:ℕ) (b:Bool)
    (X:CMatrix (ImageCache (A:=A) r M)) :
    partialTraceB (conjugate (imageTag r b) X)=
      conjugate (tag r b) (partialTraceB X) :=
  partialTraceB_known (tag (A:=A) (M:=M) r b) X

theorem imageTag_adjoint_erasure (r:ℕ) (b:Bool)
    (X:CMatrix (ImageCache (A:=A) r (Bool×M))) :
    partialTraceB (conjugate (imageTag (M:=M) r b)ᴴ X)=
      conjugate (tag (M:=M) r b)ᴴ (partialTraceB X) := by
  have he:(imageTag (A:=A) (M:=M) r b)ᴴ=
      Matrix.kronecker (tag (A:=A) (M:=M) r b)ᴴ (1:CMatrix (Fin r→A)) := by
    simp only [imageTag,Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [he]
  exact partialTraceB_known (tag (A:=A) (M:=M) r b)ᴴ X

theorem selected_core_erasure (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ) (w:Bool→A→ℝ) (r:Fin (Q+1)) (hr:r.val<Q)
    (j:A) (b f:Bool) (c:ℂ) (hc:c*star c=((w b j/(Fintype.card A:ℝ):ℝ):ℂ))
    (X:CMatrix (ImageCache (A:=A) r.val (Bool×M))) :
    conjugate (embed Q (nextGrade Q r hr f))
      (partialTraceB (conjugate (core (U b) j c r.val f*choiceImages r.val b) X))=
      branch Q hpos hQ U w (j,b) f (conjugate (embed Q r) (partialTraceB X)) := by
  have he:=congrArg (fun D:Matrix (ImageCache (A:=A) (r.val+if f then 1 else 0) (Bool×M))
      (ImageCache (A:=A) r.val (Bool×M)) ℂ=>
        conjugate (embed Q (nextGrade Q r hr f)) (partialTraceB (conjugate D X)))
    (core_choice (M:=M) (U b) j c r.val f b)
  refine he.trans ?_
  dsimp only
  rw [←conjugate_comp_apply,←conjugate_comp_apply]
  have ht:=congrArg (conjugate (embed (A:=A) (M:=Bool×M) Q (nextGrade Q r hr f)))
    (imageTag_erasure (M:=M) (r.val+if f then 1 else 0) b
      (conjugate (core (M:=M) (U b) j c r.val f)
        (conjugate (imageTag (A:=A) (M:=M) r.val b)ᴴ X)))
  refine ht.trans ?_
  rw [tag_external]
  refine (choice_included (M:=M) Q (nextGrade Q r hr f) b _).symm.trans ?_
  have hi:=congrArg (conjugate (choiceEmbed (A:=A) (M:=M) Q b))
    (included_core_erasure (M:=M) Q hpos hQ (U b) (w b) r hr j c hc f
      (conjugate (imageTag (A:=A) (M:=M) r.val b)ᴴ X))
  refine hi.trans ?_
  have hx:=imageTag_adjoint_erasure (M:=M) r.val b X
  rw [tag_external] at hx
  have hadj:(ICO.C6CacheKnownOperation.externalLift r.val
      (ICO.RecordingCopyIdentity.basisEmbedding (tagInjection (A:=A) (M:=M) b)))ᴴ=
      ICO.C6CacheKnownOperation.externalLift r.val
        (ICO.RecordingCopyIdentity.basisEmbedding (tagInjection (A:=A) (M:=M) b))ᴴ := by
    simp only [ICO.C6CacheKnownOperation.externalLift,Matrix.conjTranspose_submatrix,
      Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [hadj] at hx
  have hy:=congrArg (fun Y=>conjugate (choiceEmbed (A:=A) (M:=M) Q b)
      (ICO.C6RetainedGraded.localBranch Q hpos hQ (U b) (w b) r j f Y)) hx
  have hb:=branch_included (M:=M) Q hpos hQ U w r j b f (partialTraceB X)
  have hfinal:=hy.trans hb.symm
  exact hfinal

#print axioms selected_core_erasure
end
end ICO.C6DecodedChoiceErasure

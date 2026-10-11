import ICO.C6GradedSupport
import ICO.C6CacheVisibleGraded
import ICO.C6RetainedChoice

namespace ICO.C6GradedTransport
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6GradedSupport ICO.C6CacheKnownOperation ICO.C6CacheVisibleGraded
  ICO.C6GradedCacheReference ICO.C6SectorChannel ICO.C6CacheVisible
  ICO.C6ChoiceCache ICO.C6RetainedGraded ICO.C6RetainedChoice
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 1024
set_option Elab.async false
universe u
variable {A M N:Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem known_included (Q:ℕ) (r:Fin (Q+1)) (K:Matrix (A×N) (A×M) ℂ)
    (X:CMatrix (Cache (A:=A) (M:=M) r.val)) :
    conjugate (known Q K) (conjugate (embed Q r) X)=
      conjugate (embed Q r) (conjugate (externalLift r.val K) X) := by
  rw [conjugate_comp_apply,known_embed,←conjugate_comp_apply]

theorem supported_known (Q:ℕ) (r:Fin (Q+1)) (K:Matrix (A×N) (A×M) ℂ)
    (X:CMatrix (Graded (A:=A) Q M)) (hX:Supported Q r X) :
    Supported Q r (conjugate (known Q K) X) := by
  obtain ⟨Y,rfl⟩:=hX
  exact ⟨conjugate (externalLift r.val K) Y,known_included Q r K Y⟩

theorem visible_included (Q:ℕ) (r:Fin (Q+1))
    (X:CMatrix (Cache (A:=A) (M:=M) r.val)) :
    (visible Q).map (conjugate (embed Q r) X)=(sectorVisible r.val).map X := by
  rw [visible_apply,Finset.sum_eq_single r]
  · have hc:=compress_self (H:=fun t:Fin (Q+1)=>Cache (A:=A) (M:=M) t.val) r X
    simp only [conjugate_apply,Matrix.conjTranspose_conjTranspose] at hc
    simpa only [embed,conjugate_apply,hc]
  · intro s _ hsr
    have hc:=compress_included (H:=fun t:Fin (Q+1)=>Cache (A:=A) (M:=M) t.val) s r X hsr
    simp only [conjugate_apply,Matrix.conjTranspose_conjTranspose] at hc
    simpa only [embed,conjugate_apply,hc,map_zero]
  · intro hr
    exact (hr (Finset.mem_univ _)).elim

theorem choice_included (Q:ℕ) (r:Fin (Q+1)) (b:Bool)
    (X:CMatrix (Cache (A:=A) (M:=M) r.val)) :
    conjugate (choiceEmbed Q b) (conjugate (embed Q r) X)=
      conjugate (embed Q r) (conjugate (externalLift r.val
        (ICO.RecordingCopyIdentity.basisEmbedding (tagInjection (A:=A) (M:=M) b))) X) := by
  rw [choiceEmbed_known,known_included]

theorem choice_compress_included (Q:ℕ) (r:Fin (Q+1)) (b:Bool)
    (X:CMatrix (Cache (A:=A) (M:=Bool×M) r.val)) :
    conjugate (choiceEmbed (A:=A) (M:=M) Q b).conjTranspose (conjugate (embed Q r) X)=
      conjugate (embed Q r) (conjugate (externalLift r.val
        (ICO.RecordingCopyIdentity.basisEmbedding (tagInjection (A:=A) (M:=M) b)).conjTranspose) X) := by
  rw [choiceEmbed_known,known_conjTranspose,known_included]

theorem branch_included (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ) (w:Bool→A→ℝ) (r:Fin (Q+1))
    (j:A) (b f:Bool) (X:CMatrix (Cache (A:=A) (M:=Bool×M) r.val)) :
    branch Q hpos hQ U w (j,b) f (conjugate (embed Q r) X)=
      conjugate (choiceEmbed Q b) (localBranch Q hpos hQ (U b) (w b) r j f
        (conjugate (externalLift r.val
          (ICO.RecordingCopyIdentity.basisEmbedding (tagInjection (A:=A) (M:=M) b)).conjTranspose) X)) := by
  simp only [branch,LinearMap.comp_apply]
  rw [choice_compress_included,queryBranch_included]

#print axioms branch_included
#print axioms visible_included
end
end ICO.C6GradedTransport

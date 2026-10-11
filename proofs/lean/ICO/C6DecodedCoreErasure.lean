import ICO.C6DecodedHistory
import ICO.C6RetainedGraded
import ICO.C6RetainedGradeSupport

/-! Exact erasure of old and newly appended private images gives the
outcome-resolved weighted cache branch, for every input matrix. -/
namespace ICO.C6DecodedCoreErasure
open Matrix QIT ICO.C6DecodedHistory ICO.C6RetainedGraded ICO.C6RetainedCacheLocal
  ICO.C6PrivateImageAppend ICO.C6RetainedSectorOperations ICO.C6CacheDecode
  ICO.C6CacheMap ICO.C6CacheQueryBound ICO.C6GradedCache ICO.C6GradedCacheReference
  ICO.C6ModeFockRetrieval ICO.C6FlagCount ICO.C6RetainedGradeSupport
open scoped Matrix
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem conjugate_smul {a b:Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (c:ℂ) (F:Matrix b a ℂ) (X:CMatrix a) :
    conjugate (c •F) X=(c*star c) •conjugate F X := by
  simp only [conjugate_apply,Matrix.conjTranspose_smul,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul]
  rw [mul_comm (star c) c]

theorem core_true_erasure (U:Matrix.unitaryGroup A ℂ) (j:A) (c:ℂ) (r:ℕ)
    (X:CMatrix (ImageCache (A:=A) r M)) :
    partialTraceB (conjugate (core U j c r true) X)=
      (c*star c) •conjugate (memoryPolar r)
        ((preparation U r j).map (conjugate (missing r) (partialTraceB X))) := by
  have he:=congrArg partialTraceB
    (conjugate_smul c (appendPrivate r (birthMatrix (M:=M) U r j)) X)
  refine he.trans ?_
  rw [partialTraceB_smul,append_erasure]
  simp only [birthMatrix,←conjugate_comp_apply,partialTraceB_known,preparation_erasure]

theorem core_false_erasure (U:Matrix.unitaryGroup A ℂ) (j:A) (c:ℂ) (r:ℕ)
    (X:CMatrix (ImageCache (A:=A) r M)) :
    partialTraceB (conjugate (core U j c r false) X)=
      conjugate (retrieved U j r) (partialTraceB X) := by
  exact partialTraceB_known (retrieved (M:=M) U j r) X

theorem included_core_erasure (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (r:Fin (Q+1)) (hr:r.val<Q)
    (j:A) (c:ℂ) (hc:c*star c=((w j/(Fintype.card A:ℝ):ℝ):ℂ)) (f:Bool)
    (X:CMatrix (ImageCache (A:=A) r.val M)) :
    conjugate (embed Q (nextGrade Q r hr f))
      (partialTraceB (conjugate (core U j c r.val f) X))=
      localBranch Q hpos hQ U w r j f (partialTraceB X) := by
  rcases r with ⟨r,hr'⟩
  cases r with
  | zero=>
    cases f with
    | false=>
      have he:=congrArg (conjugate (embed (A:=A) (M:=M) Q (nextGrade Q ⟨0,hr'⟩ hr false)))
        (core_false_erasure (M:=M) U j c 0 X)
      refine he.trans ?_
      simp [retrieved,localBranch,conjugate_apply,partialTraceB]
      exact map_zero _
    | true=>
      have he:=congrArg (conjugate (embed (A:=A) (M:=M) Q (nextGrade Q ⟨0,hr'⟩ hr true)))
        (core_true_erasure (M:=M) U j c 0 X)
      refine he.trans ?_
      rw [hc]
      simp only [missing,conjugate_apply,Matrix.one_mul,Matrix.conjTranspose_one,
        Matrix.mul_one,localBranch,if_true,LinearMap.smul_apply,LinearMap.comp_apply,
        vacuumBranch,map_smul,nextGrade]
      rw [smul_smul]
      have hs:((w j/(Fintype.card A:ℝ):ℝ):ℂ)=
          (w j:ℂ)*((1/(Fintype.card A:ℝ):ℝ):ℂ) := by
        simp only [Complex.ofReal_div,Complex.ofReal_one];ring
      rw [hs]
      have hm:=map_smul (conjugate (embed (A:=A) (M:=M) Q ⟨1,by omega⟩))
        ((w j:ℂ)*((1/(Fintype.card A:ℝ):ℝ):ℂ))
        (memoryPolar (A:=A) (M:=M) 0*(preparation (M:=M) U 0 j).map (partialTraceB X)*
          (memoryPolar (A:=A) (M:=M) 0)ᴴ)
      refine hm.trans ?_
      exact congrArg (fun D:CMatrix (Graded (A:=A) Q M)=>
        ((w j:ℂ)*((1/(Fintype.card A:ℝ):ℝ):ℂ)) •D)
        (conjugate_apply (embed (A:=A) (M:=M) Q ⟨1,by omega⟩) _)
  | succ r=>
    have hlt:r+1<Q:=hr
    cases f with
    | false=>
      have he:=congrArg (conjugate (embed (A:=A) (M:=M) Q (nextGrade Q ⟨r+1,hr'⟩ hr false)))
        (core_false_erasure (M:=M) U j c (r+1) X)
      refine he.trans ?_
      simp only [localBranch,dif_pos hlt,Bool.false_eq_true,if_false,
        LinearMap.comp_apply,retrieved,nextGrade,Nat.add_zero]
      rw [retrieve_projection]
      rfl
    | true=>
      have he:=congrArg (conjugate (embed (A:=A) (M:=M) Q (nextGrade Q ⟨r+1,hr'⟩ hr true)))
        (core_true_erasure (M:=M) U j c (r+1) X)
      refine he.trans ?_
      rw [hc]
      simp only [localBranch,dif_pos hlt,if_true,LinearMap.smul_apply,LinearMap.comp_apply,
        ICO.C6RetainedCacheLocal.birth,missing,map_smul,nextGrade]
      rw [smul_smul]
      have hs:((w j/(Fintype.card A:ℝ):ℝ):ℂ)=
          (w j:ℂ)*((1/(Fintype.card A:ℝ):ℝ):ℂ) := by
        simp only [Complex.ofReal_div,Complex.ofReal_one];ring
      rw [hs]
      exact map_smul (conjugate (embed (A:=A) (M:=M) Q ⟨r+2,by omega⟩)) _ _

#print axioms included_core_erasure
end
end ICO.C6DecodedCoreErasure

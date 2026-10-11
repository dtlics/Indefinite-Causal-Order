import ICO.C6GradedTransport

namespace ICO.C6RetainedGradeSupport
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6GradedSupport ICO.C6GradedTransport ICO.C6CacheKnownOperation
  ICO.C6ChoiceCache ICO.C6RetainedGraded ICO.C6RetainedChoice
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 1024
set_option Elab.async false
universe u
variable {A M:Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def nextGrade (Q:ℕ) (r:Fin (Q+1)) (hr:r.val<Q) (f:Bool) : Fin (Q+1) :=
  ⟨r.val+(if f then 1 else 0),by cases f <;> simp <;> omega⟩

theorem localBranch_supported (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (r:Fin (Q+1)) (hr:r.val<Q)
    (j:A) (f:Bool) (X:CMatrix (Cache (A:=A) (M:=M) r.val)) :
    Supported Q (nextGrade Q r hr f) (localBranch Q hpos hQ U w r j f X) := by
  rcases r with ⟨r,hr'⟩
  cases r with
  | zero=>
    cases f
    · simpa only [localBranch,Bool.false_eq_true,↓reduceIte,LinearMap.zero_apply] using
        supported_zero (A:=A) (M:=M) Q (nextGrade Q ⟨0,hr'⟩ hr false)
    · refine ⟨(w j:ℂ) •vacuumBranch U j X,?_⟩
      exact (map_smul (conjugate (embed (A:=A) (M:=M) Q ⟨1,by omega⟩))
        (w j:ℂ) (vacuumBranch U j X)).symm
  | succ n=>
    have hn:n+1<Q:=hr
    cases f
    · refine ⟨ICO.C6RetainedCacheLocal.retrieve U n j X,?_⟩
      simp only [localBranch,dif_pos hn,Bool.false_eq_true,↓reduceIte,
        LinearMap.comp_apply,nextGrade,Nat.add_zero]
      rfl
    · refine ⟨(w j:ℂ) •ICO.C6RetainedCacheLocal.birth U n j X,?_⟩
      simp only [localBranch,dif_pos hn,↓reduceIte,LinearMap.smul_apply,LinearMap.comp_apply]
      exact (map_smul (conjugate (embed (A:=A) (M:=M) Q ⟨n+2,by omega⟩))
        (w j:ℂ) (ICO.C6RetainedCacheLocal.birth U n j X)).symm

theorem queryBranch_supported (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (r:Fin (Q+1)) (hr:r.val<Q)
    (j:A) (f:Bool) (X:CMatrix (Graded (A:=A) Q M)) (hX:Supported Q r X) :
    Supported Q (nextGrade Q r hr f) (queryBranch Q hpos hQ U w j f X) := by
  obtain ⟨Y,rfl⟩:=hX
  rw [queryBranch_included]
  exact localBranch_supported Q hpos hQ U w r hr j f Y

theorem choice_supported (Q:ℕ) (r:Fin (Q+1)) (b:Bool)
    (X:CMatrix (Graded (A:=A) Q M)) (hX:Supported Q r X) :
    Supported Q r (conjugate (choiceEmbed Q b) X) := by
  rw [choiceEmbed_known]
  exact supported_known Q r _ X hX

theorem choice_compress_supported (Q:ℕ) (r:Fin (Q+1)) (b:Bool)
    (X:CMatrix (Graded (A:=A) Q (Bool×M))) (hX:Supported Q r X) :
    Supported Q r (conjugate (choiceEmbed (A:=A) (M:=M) Q b).conjTranspose X) := by
  rw [choiceEmbed_known,ICO.C6CacheVisibleGraded.known_conjTranspose]
  exact supported_known Q r _ X hX

theorem branch_supported (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ) (w:Bool→A→ℝ) (r:Fin (Q+1)) (hr:r.val<Q)
    (o:A×Bool) (f:Bool) (X:CMatrix (Graded (A:=A) Q (Bool×M))) (hX:Supported Q r X) :
    Supported Q (nextGrade Q r hr f) (branch Q hpos hQ U w o f X) := by
  simp only [branch,LinearMap.comp_apply]
  apply choice_supported
  apply queryBranch_supported Q hpos hQ _ _ r hr
  exact choice_compress_supported Q r o.2 X hX

#print axioms branch_supported
end
end ICO.C6RetainedGradeSupport

import ICO.C6RetainedCacheLocal

namespace ICO.C6RetainedCacheCP
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheReference ICO.C6CacheMap
  ICO.C6CachePreparation ICO.C6CacheWeighted ICO.C6MatrixCovariance
  ICO.C6CacheQueryBound ICO.C6RetainedCacheLocal
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
universe u v w
variable {a : Type u} {b : Type v} {c : Type w}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c]

theorem cp_zero : MatrixMap.IsCompletelyPositive (0:MatrixMap a b) := by
  change (MatrixMap.choi (0:MatrixMap a b)).PosSemidef
  have h:MatrixMap.choi (0:MatrixMap a b)=0 := by ext i j; rfl
  rw [h]
  exact Matrix.PosSemidef.zero

theorem sum_post {I:Type*} [Fintype I] (Φ:MatrixMap b c) (Ψ:I→MatrixMap a b) :
    (∑j,Φ.comp (Ψ j))=Φ.comp (∑j,Ψ j) := by
  ext X i j
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,map_sum,Matrix.sum_apply]

theorem sum_pre {I:Type*} [Fintype I] (Φ:I→MatrixMap b c) (Ψ:MatrixMap a b) :
    (∑j,(Φ j).comp Ψ)=(∑j,Φ j).comp Ψ := by
  ext X i j
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,Matrix.sum_apply]

theorem post_smul (Φ:MatrixMap b c) (Ψ:MatrixMap a b) (z:ℂ) :
    Φ.comp (z • Ψ)=z • Φ.comp Ψ := by
  ext X i j
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,map_smul]

variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem retrieve_cp (U:Matrix.unitaryGroup A ℂ) (n:ℕ) (j:A) :
    MatrixMap.IsCompletelyPositive (retrieve (M:=M) U n j) :=
  MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
    (MatrixMap.isCompletelyPositive_comp _ _ (basisBranch_cp U n j) (conjugate_cp _))

theorem birth_cp (U:Matrix.unitaryGroup A ℂ) (n:ℕ) (j:A) :
    MatrixMap.IsCompletelyPositive (C6RetainedCacheLocal.birth (M:=M) U n j) := by
  apply cp_real_smul
  · exact MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
      (MatrixMap.isCompletelyPositive_comp _ _ (preparation U (n+1) j).completelyPositive
        (conjugate_cp _))
  · positivity

theorem birth_trace (U:Matrix.unitaryGroup A ℂ) (n:ℕ)
    (hn:n<Fintype.card A) (hs:n+1<Fintype.card A) (j:A)
    (X:CMatrix (Cache (A:=A) (M:=M) (n+1))) :
    (C6RetainedCacheLocal.birth U n j X).trace=
      ((1/(Fintype.card A:ℝ):ℝ):ℂ)*((1-image (memoryPolar n))*X).trace := by
  simp only [C6RetainedCacheLocal.birth,LinearMap.smul_apply,
    LinearMap.comp_apply,Matrix.trace_smul,smul_eq_mul]
  rw [conjugate_trace_of_isometry _ (memoryPolar_gram hs),
    (preparation U (n+1) j).tracePreserving,
    ICO.C6CacheExtension.complement_trace _ (memoryPolar_gram hn)]

theorem complement_mass (n:ℕ) (hn:n<Fintype.card A)
    (X:CMatrix (Cache (A:=A) (M:=M) (n+1))) (hX:X.PosSemidef) :
    0≤((1-image (memoryPolar n))*X).trace.re ∧
      ((1-image (memoryPolar n))*X).trace.re≤X.trace.re := by
  let F:=memoryPolar (A:=A) (M:=M) n
  have hf:F.conjTranspose*F=1:=memoryPolar_gram hn
  have hp:=MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp (1-image F)) X hX
  have hr:=MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp F.conjTranspose) X hX
  have hpt:0≤((1-image F)*X).trace.re := by
    rw [←ICO.C6CacheExtension.complement_trace F hf]
    exact (Complex.nonneg_iff.mp hp.trace_nonneg).1
  have hrt:0≤(image F*X).trace.re := by
    have hh:= (Complex.nonneg_iff.mp hr.trace_nonneg).1
    rw [conjugate_trace,Matrix.conjTranspose_conjTranspose] at hh
    exact hh
  have ht:((1-image F)*X).trace.re+(image F*X).trace.re=X.trace.re := by
    rw [←Complex.add_re,←Matrix.trace_add,←Matrix.add_mul,sub_add_cancel,Matrix.one_mul]
  exact ⟨hpt,by linarith⟩

#print axioms birth_trace
#print axioms complement_mass
end
end ICO.C6RetainedCacheCP

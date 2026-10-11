import ICO.C6RetainedGraded
import ICO.C6SectorCovariance

namespace ICO.C6RetainedGradedDeficit
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6CachePreparation
  ICO.C6CacheQueryBound ICO.C6RetainedCacheLocal ICO.C6RetainedCacheCP
  ICO.C6RetainedGraded ICO.C6GradedCache ICO.C6CacheWeighted
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
universe u
variable {A M:Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem local_difference (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (r:Fin (Q+1)) (j:A) (flag:Bool) :
    localBranch (M:=M) Q hpos hQ U (fun _=>1) r j flag-localBranch Q hpos hQ U w r j flag=
      ((if flag then 1-w j else 0:ℝ):ℂ) •
        localBranch Q hpos hQ U (fun _=>1) r j flag := by
  rcases r with ⟨r,hr⟩
  cases r with
  | zero=>
    cases flag <;> simp only [localBranch,Bool.false_eq_true,↓reduceIte,
      Complex.ofReal_one,Complex.ofReal_zero,zero_smul,sub_self]
    ext X a b
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  | succ n=>
    by_cases hn:n+1<Q
    · cases flag <;> simp only [localBranch,dif_pos hn,Bool.false_eq_true,↓reduceIte,
        Complex.ofReal_one,Complex.ofReal_zero,zero_smul,sub_self]
      ext X a b
      simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.comp_apply,
        Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_one]
      ring
    · cases flag <;> simp [localBranch,hn]

theorem local_deficit_cp (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (hw:∀j,w j≤1)
    (r:Fin (Q+1)) (j:A) (flag:Bool) :
    MatrixMap.IsCompletelyPositive (localBranch (M:=M) Q hpos hQ U (fun _=>1) r j flag-
      localBranch Q hpos hQ U w r j flag) := by
  rw [local_difference]
  apply cp_real_smul _ (localBranch_cp Q hpos hQ U _ (fun _=>by norm_num) r j flag)
  cases flag <;> simp only [Bool.false_eq_true,↓reduceIte]
  · exact le_rfl
  · exact sub_nonneg.mpr (hw j)

theorem local_birth_mass (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (r:Fin (Q+1))
    (X:CMatrix (Cache (A:=A) (M:=M) r.val)) (hX:X.PosSemidef) :
    ∃m:ℝ,0≤m ∧ m≤X.trace.re ∧ ∀j:A,
      (localBranch (M:=M) Q hpos hQ U (fun _=>1) r j true X).trace.re=m/(Fintype.card A:ℝ) := by
  rcases r with ⟨r,hr⟩
  cases r with
  | zero=>
    refine ⟨X.trace.re,(Complex.nonneg_iff.mp hX.trace_nonneg).1,le_rfl,?_⟩
    intro j
    simp only [localBranch,↓reduceIte,Complex.ofReal_one,one_smul,LinearMap.comp_apply]
    rw [conjugate_trace_of_isometry _ (embed_gram Q _)]
    simp only [vacuumBranch,LinearMap.smul_apply,LinearMap.comp_apply,
      Matrix.trace_smul,smul_eq_mul]
    rw [conjugate_trace_of_isometry _ (memoryPolar_gram (by omega)),
      (preparation U 0 j).tracePreserving]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  | succ n=>
    by_cases hn:n+1<Q
    · obtain ⟨hm0,hmle⟩:=complement_mass n (by omega) X hX
      refine ⟨((1-image (memoryPolar n))*X).trace.re,hm0,hmle,?_⟩
      intro j
      simp only [localBranch,dif_pos hn,↓reduceIte,Complex.ofReal_one,one_smul,
        LinearMap.comp_apply]
      rw [conjugate_trace_of_isometry _ (embed_gram Q _),
        C6RetainedCacheCP.birth_trace U n (by omega) (by omega)]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      ring
    · refine ⟨0,le_rfl,(Complex.nonneg_iff.mp hX.trace_nonneg).1,?_⟩
      intro j
      simp [localBranch,hn]

theorem local_deficit_bound (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (hw:∀j,w j≤1) (r:Fin (Q+1))
    (X:CMatrix (Cache (A:=A) (M:=M) r.val)) (hX:X.PosSemidef) :
    (∑j:A,∑flag:Bool,((localBranch (M:=M) Q hpos hQ U (fun _=>1) r j flag-
      localBranch (M:=M) Q hpos hQ U w r j flag :
        MatrixMap (Cache (A:=A) (M:=M) r.val) (Graded (A:=A) Q M)) X).trace.re)≤
        ((∑j:A,(1-w j))/(Fintype.card A:ℝ))*X.trace.re := by
  obtain ⟨m,hm0,hmle,hm⟩:=local_birth_mass Q hpos hQ U r X hX
  simp_rw [local_difference]
  simp only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,
    Complex.ofReal_zero,zero_smul,LinearMap.zero_apply,Matrix.trace_zero,Complex.zero_re,
    add_zero,LinearMap.smul_apply,Matrix.trace_smul,smul_eq_mul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp_rw [hm]
  rw [←Finset.sum_mul]
  have hc:0≤(∑j:A,(1-w j))/(Fintype.card A:ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun j _=>sub_nonneg.mpr (hw j))) (Nat.cast_nonneg _)
  calc
    _ = ((∑j:A,(1-w j))/(Fintype.card A:ℝ))*m := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmle hc

theorem query_difference (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (j:A) (flag:Bool) :
    queryBranch (M:=M) Q hpos hQ U (fun _=>1) j flag-queryBranch Q hpos hQ U w j flag=
      ∑r:Fin (Q+1),(localBranch Q hpos hQ U (fun _=>1) r j flag-
        localBranch Q hpos hQ U w r j flag).comp
          (conjugate (embed (A:=A) (M:=M) Q r).conjTranspose) := by
  ext X a b
  simp only [queryBranch,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.comp_apply,
    Matrix.sum_apply,Matrix.sub_apply,Finset.sum_sub_distrib]

theorem query_deficit_cp (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (hw:∀j,w j≤1) (j:A) (flag:Bool) :
    MatrixMap.IsCompletelyPositive (queryBranch (M:=M) Q hpos hQ U (fun _=>1) j flag-
      queryBranch Q hpos hQ U w j flag) := by
  rw [query_difference]
  apply ICO.C6CacheWeighted.cp_sum
  intro r
  exact MatrixMap.isCompletelyPositive_comp _ _
    (local_deficit_cp Q hpos hQ U w hw r j flag) (conjugate_cp _)

#print axioms local_deficit_bound
#print axioms query_deficit_cp
end
end ICO.C6RetainedGradedDeficit

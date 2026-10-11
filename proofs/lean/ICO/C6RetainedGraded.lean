import ICO.C6RetainedCacheCP
import ICO.C6GradedCacheReference

/-! Outcome and birth-flag resolved maps on the same ambient graded cache as
the uniform reference channel. All maps are defined on every sector. -/
namespace ICO.C6RetainedGraded
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheReference ICO.C6CacheMap
  ICO.C6CachePreparation ICO.C6CacheWeighted ICO.C6MatrixCovariance
  ICO.C6CacheQueryBound ICO.C6RetainedCacheLocal ICO.C6RetainedCacheCP
  ICO.C6GradedCache ICO.C6SectorChannel ICO.C6GradedCacheReference
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def vacuumBranch (U:Matrix.unitaryGroup A ℂ) (j:A) :
    MatrixMap (Cache (A:=A) (M:=M) 0) (Cache (A:=A) (M:=M) 1) :=
  ((1/(Fintype.card A:ℝ):ℝ):ℂ) •
    (conjugate (memoryPolar 0)).comp (preparation U 0 j).map

theorem vacuumBranch_sum (U:Matrix.unitaryGroup A ℂ) (hd:0<Fintype.card A) :
    (∑j,vacuumBranch (M:=M) U j)=(vacuumStep (M:=M) hd).map := by
  simp only [vacuumBranch,←post_smul,sum_post,preparation_average]
  rfl

def localBranch (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (r:Fin (Q+1)) (j:A) (flag:Bool) :
    MatrixMap (Cache (A:=A) (M:=M) r.val) (Graded (A:=A) Q M) := by
  exact match r with
  | ⟨0,hr⟩ => if flag then (w j:ℂ) •
      (conjugate (embed Q ⟨1,by omega⟩)).comp (vacuumBranch U j) else 0
  | ⟨n+1,hr⟩ => if hn:n+1<Q then
      (if flag then (w j:ℂ) •
        (conjugate (embed Q ⟨n+2,by omega⟩)).comp (C6RetainedCacheLocal.birth U n j)
      else (conjugate (embed Q ⟨n+1,hr⟩)).comp (retrieve U n j))
    else (if flag then 0 else ((1/(Fintype.card A:ℝ):ℝ):ℂ) •
        conjugate (embed Q ⟨n+1,hr⟩))

def queryBranch (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (j:A) (flag:Bool) :
    MatrixMap (Graded (A:=A) Q M) (Graded (A:=A) Q M) :=
  ∑r:Fin (Q+1),(localBranch Q hpos hQ U w r j flag).comp
    (conjugate (embed (A:=A) (M:=M) Q r).conjTranspose)

theorem localBranch_cp (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (hw:∀j,0≤w j)
    (r:Fin (Q+1)) (j:A) (flag:Bool) :
    MatrixMap.IsCompletelyPositive (localBranch (M:=M) Q hpos hQ U w r j flag) := by
  rcases r with ⟨r,hr⟩
  cases r with
  | zero=>
    cases flag
    · exact cp_zero
    · apply cp_real_smul _ _ _ (hw j)
      apply MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
      apply cp_real_smul
      · exact MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
          (preparation U 0 j).completelyPositive
      · positivity
  | succ n=>
    by_cases hn:n+1<Q
    · cases flag
      · simpa only [localBranch,dif_pos hn,Bool.false_eq_true,↓reduceIte] using
          MatrixMap.isCompletelyPositive_comp _ _
            (conjugate_cp (embed (A:=A) (M:=M) Q ⟨n+1,hr⟩)) (retrieve_cp U n j)
      · simp only [localBranch,dif_pos hn,↓reduceIte]
        apply cp_real_smul _ _ _ (hw j)
        exact MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
          (C6RetainedCacheCP.birth_cp U n j)
    · cases flag
      · simp only [localBranch,dif_neg hn,Bool.false_eq_true,↓reduceIte]
        exact cp_real_smul _ (conjugate_cp _) _ (by positivity)
      · simpa only [localBranch,dif_neg hn,↓reduceIte] using
          (cp_zero (a:=Cache (A:=A) (M:=M) (n+1)) (b:=Graded (A:=A) Q M))

theorem queryBranch_cp (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (hw:∀j,0≤w j) (j:A) (flag:Bool) :
    MatrixMap.IsCompletelyPositive (queryBranch (M:=M) Q hpos hQ U w j flag) := by
  apply ICO.C6CacheWeighted.cp_sum
  intro r
  exact MatrixMap.isCompletelyPositive_comp _ _
    (localBranch_cp Q hpos hQ U w hw r j flag) (conjugate_cp _)

theorem localBranch_sum (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (r:Fin (Q+1)) :
    (∑j:A,∑flag:Bool,localBranch (M:=M) Q hpos hQ U (fun _=>1) r j flag)=
      (localQuery (M:=M) Q hpos hQ (some U) r).map := by
  rcases r with ⟨r,hr⟩
  cases r with
  | zero=>
    change (∑j:A,∑flag:Bool,if flag then (1:ℂ) •
      (conjugate (embed (A:=A) (M:=M) Q ⟨1,by omega⟩)).comp (vacuumBranch U j) else 0)=
        (conjugate (embed Q ⟨1,by omega⟩)).comp (vacuumStep (by omega)).map
    simp only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,
      one_smul,add_zero,sum_post]
    rw [vacuumBranch_sum U (by omega)]
  | succ n=>
    by_cases hn:n+1<Q
    · simp only [localBranch,dif_pos hn,Fintype.sum_bool,Bool.false_eq_true,
        ↓reduceIte,Complex.ofReal_one,one_smul,Finset.sum_add_distrib,sum_post,
        birth_sum,retrieve_sum]
      ext X a b
      simp only [localQuery,dif_pos hn,Channel.comp,LinearMap.comp_apply,
        ICO.C6MatrixCovariance.isometryChannel,cacheStep,cacheChannel,LinearMap.add_apply]
      rw [sum_cache_apply]
      simp only [Matrix.add_apply,add_comm]
    · ext X a b
      have hd:(Fintype.card A:ℂ)≠0:=by exact_mod_cast Fintype.card_ne_zero
      simp [localBranch,localQuery,dif_neg hn,hn,Fintype.sum_bool,
        ICO.C6MatrixCovariance.isometryChannel,LinearMap.sum_apply,LinearMap.smul_apply,
        Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
        Complex.ofReal_div,Complex.ofReal_natCast,hd,mul_assoc]

theorem queryBranch_sum (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) :
    (∑j:A,∑flag:Bool,queryBranch (M:=M) Q hpos hQ U (fun _=>1) j flag)=
      (ICO.C6GradedCache.query (M:=M) Q hpos hQ (some U)).map := by
  simp only [queryBranch]
  calc
    _ = ∑r : Fin (Q+1),∑j:A,∑flag:Bool,
        (localBranch (M:=M) Q hpos hQ U (fun _=>1) r j flag).comp
          (conjugate (embed (A:=A) (M:=M) Q r).conjTranspose) := by
      calc
        _ = ∑j:A,∑r : Fin (Q+1),∑flag:Bool,
            (localBranch (M:=M) Q hpos hQ U (fun _=>1) r j flag).comp
              (conjugate (embed (A:=A) (M:=M) Q r).conjTranspose) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ = ∑r : Fin (Q+1),(localQuery (M:=M) Q hpos hQ (some U) r).map.comp
        (conjugate (embed (A:=A) (M:=M) Q r).conjTranspose) := by
      apply Finset.sum_congr rfl
      intro r _
      simp_rw [sum_pre]
      rw [localBranch_sum]
    _ = _ := rfl

#print axioms queryBranch_cp
#print axioms queryBranch_sum
end
end ICO.C6RetainedGraded

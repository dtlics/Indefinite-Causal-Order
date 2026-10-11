import ICO.C6RetainedGradedDeficit
import ICO.C6RetainedChoice
import ICO.C6ChoiceCacheBound

namespace ICO.C6RetainedQueryDeficit
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6RetainedCacheCP ICO.C6RetainedGraded ICO.C6RetainedGradedDeficit
  ICO.C6RetainedChoice ICO.C6ChoiceCache
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
universe u
variable {A M:Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem query_deficit_bound (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (hw:∀j,w j≤1)
    (X:CMatrix (Graded (A:=A) Q M)) (hX:X.PosSemidef) :
    (∑j:A,∑flag:Bool,((queryBranch (M:=M) Q hpos hQ U (fun _=>1) j flag-
      queryBranch Q hpos hQ U w j flag : MatrixMap (Graded (A:=A) Q M) (Graded (A:=A) Q M)) X).trace.re)≤
        ((∑j:A,(1-w j))/(Fintype.card A:ℝ))*X.trace.re := by
  simp_rw [query_difference]
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,Matrix.trace_sum,Complex.re_sum]
  calc
    _ = ∑r:Fin (Q+1),∑j:A,∑flag:Bool,
        ((localBranch Q hpos hQ U (fun _=>1) r j flag-localBranch Q hpos hQ U w r j flag :
          MatrixMap (Cache (A:=A) (M:=M) r.val) (Graded (A:=A) Q M))
          (conjugate (embed (A:=A) (M:=M) Q r).conjTranspose X)).trace.re := by
      calc
        _ = ∑j:A,∑r:Fin (Q+1),∑flag:Bool,
            ((localBranch Q hpos hQ U (fun _=>1) r j flag-localBranch Q hpos hQ U w r j flag :
              MatrixMap (Cache (A:=A) (M:=M) r.val) (Graded (A:=A) Q M))
              (conjugate (embed (A:=A) (M:=M) Q r).conjTranspose X)).trace.re := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ ≤ ∑r:Fin (Q+1),((∑j:A,(1-w j))/(Fintype.card A:ℝ))*
        (conjugate (embed (A:=A) (M:=M) Q r).conjTranspose X).trace.re := by
      apply Finset.sum_le_sum
      intro r _
      exact local_deficit_bound Q hpos hQ U w hw r _
        (MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) X hX)
    _ = _ := by
      rw [←Finset.mul_sum]
      have hm:=congrArg Complex.re (ICO.C6SectorCovariance.block_mass X)
      simp only [Complex.re_sum] at hm
      change (∑r:Fin (Q+1),((embed Q r).conjTranspose*X*embed Q r).trace.re)=X.trace.re at hm
      simpa only [conjugate_apply,Matrix.conjTranspose_conjTranspose,hm]

theorem branch_difference (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ) (w:Bool→A→ℝ) (outcome:A×Bool) (flag:Bool) :
    branch (M:=M) Q hpos hQ U (fun _ _=>1) outcome flag-branch Q hpos hQ U w outcome flag=
      (conjugate (choiceEmbed Q outcome.2)).comp
        ((queryBranch Q hpos hQ (U outcome.2) (fun _=>1) outcome.1 flag-
          queryBranch Q hpos hQ (U outcome.2) (w outcome.2) outcome.1 flag).comp
            (conjugate (choiceEmbed (A:=A) (M:=M) Q outcome.2).conjTranspose)) := by
  ext X a b
  simp only [branch,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,Matrix.sub_apply]

theorem branch_deficit_cp (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ) (w:Bool→A→ℝ) (hw:∀b j,w b j≤1)
    (outcome:A×Bool) (flag:Bool) :
    MatrixMap.IsCompletelyPositive (branch (M:=M) Q hpos hQ U (fun _ _=>1) outcome flag-
      branch Q hpos hQ U w outcome flag) := by
  rw [branch_difference]
  exact MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
    (MatrixMap.isCompletelyPositive_comp _ _
      (query_deficit_cp Q hpos hQ (U outcome.2) (w outcome.2) (hw outcome.2) outcome.1 flag)
      (conjugate_cp _))

theorem choice_deficit_bound (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ) (w:Bool→A→ℝ) (hw:∀b j,w b j≤1)
    (i:ℕ) (hi:∀b,(∑j:A,(1-w b j)) ≤ (i:ℝ))
    (X:CMatrix (Graded (A:=A) Q (Bool×M))) (hX:X.PosSemidef) :
    (∑outcome:A×Bool,∑flag:Bool,
      ((branch (M:=M) Q hpos hQ U (fun _ _=>1) outcome flag-branch Q hpos hQ U w outcome flag :
        MatrixMap (Graded (A:=A) Q (Bool×M)) (Graded (A:=A) Q (Bool×M))) X).trace.re)≤
        ((i:ℝ)/(Fintype.card A:ℝ))*X.trace.re := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [branch_difference]
  simp only [LinearMap.comp_apply,conjugate_trace_of_isometry _ (choiceEmbed_gram Q _)]
  have hp (b:Bool): (conjugate (choiceEmbed (A:=A) (M:=M) Q b).conjTranspose X).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) X hX
  calc
    _ ≤ ∑b:Bool,((i:ℝ)/(Fintype.card A:ℝ))*
        (conjugate (choiceEmbed (A:=A) (M:=M) Q b).conjTranspose X).trace.re := by
      apply Finset.sum_le_sum
      intro b _
      apply (query_deficit_bound Q hpos hQ (U b) (w b) (hw b) _ (hp b)).trans
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hi b) (Nat.cast_nonneg _))
        (Complex.nonneg_iff.mp (hp b).trace_nonneg).1
    _ = _ := by
      rw [←Finset.mul_sum]
      have hm:=congrArg Complex.re (ICO.C6ChoiceCacheBound.choice_block_mass Q X)
      simp only [choiceBlock_eq,Complex.re_sum] at hm
      simpa only [conjugate_apply,Matrix.conjTranspose_conjTranspose,hm]

#print axioms choice_deficit_bound
#print axioms branch_deficit_cp
end
end ICO.C6RetainedQueryDeficit

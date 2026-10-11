import ICO.C6RetainedGraded
import ICO.C6ChoiceCache

/-! The actual selected-box cache instrument. The outcome is (j,b), where b
is privately copied as well as retained in the public selector. -/
namespace ICO.C6RetainedChoice
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6RetainedCacheCP ICO.C6RetainedGraded ICO.C6ChoiceCache
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def branch (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ) (w:Bool→A→ℝ) (outcome:A×Bool) (flag:Bool) :
    MatrixMap (Graded (A:=A) Q (Bool×M)) (Graded (A:=A) Q (Bool×M)) :=
  (conjugate (choiceEmbed Q outcome.2)).comp
    ((queryBranch Q hpos hQ (U outcome.2) (w outcome.2) outcome.1 flag).comp
      (conjugate (choiceEmbed (A:=A) (M:=M) Q outcome.2).conjTranspose))

theorem branch_cp (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ) (w:Bool→A→ℝ) (hw:∀b j,0≤w b j)
    (outcome:A×Bool) (flag:Bool) :
    MatrixMap.IsCompletelyPositive (branch (M:=M) Q hpos hQ U w outcome flag) :=
  MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
    (MatrixMap.isCompletelyPositive_comp _ _
      (queryBranch_cp Q hpos hQ (U outcome.2) (w outcome.2) (hw outcome.2) outcome.1 flag)
      (conjugate_cp _))

theorem branch_sum (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ) :
    (∑outcome:A×Bool,∑flag:Bool,branch (M:=M) Q hpos hQ U (fun _ _=>1) outcome flag)=
      (ICO.C6ChoiceCache.query (M:=M) Q hpos hQ (fun b=>some (U b))).map := by
  simp only [Fintype.sum_prod_type,branch]
  rw [Finset.sum_comm]
  simp_rw [sum_post,sum_pre]
  simp_rw [queryBranch_sum]
  ext X a b
  rw [ICO.C6ChoiceCache.query_apply]
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,conjugate_apply,
    Matrix.conjTranspose_conjTranspose,Matrix.sum_apply,choiceBlock_eq]

#print axioms branch_sum
end
end ICO.C6RetainedChoice

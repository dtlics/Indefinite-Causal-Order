import ICO.MHCompressedQuery
import ICO.MHWPartial

namespace ICO.MHRecordDecompression
open Matrix QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport ICO.MHWPartial
  ICO.MHPermutationExtensions ICO.MHTernaryProfile ICO.MHTernaryCompression
  ICO.MHRecordExtension ICO.MHPurifiedOracle ICO.MHCompressedQuery
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 1000000

def recordMap : Matrix (Environment A) (Relation A A × Relation A A) ℂ :=
  fun e r => if h : Valid r then state ⟨r,h⟩ e else 0

def D : Matrix (A × Environment A) (Basis A) ℂ :=
  fun o i => if o.1=i.1 then recordMap o.2 i.2 else 0

def bijProjection : CMatrix (Basis A) :=
  predicateProjection (fun i => BijRecord i.2.1 i.2.2)

theorem recordMap_gram (r s : Relation A A × Relation A A) :
    (∑ e : Environment A,star (recordMap e r)*recordMap e s)=
      if r=s ∧ Valid r then 1 else 0 := by
  by_cases hr : Valid r
  · by_cases hs : Valid s
    · simp only [recordMap,dif_pos hr,dif_pos hs]
      rw [state_orthonormal]
      simp only [Subtype.mk.injEq,hr,and_true]
    · have hn : r≠s := by intro he; subst s; exact hs hr
      simp [recordMap,hs,hn]
  · simp [recordMap,hr]

theorem decompression_gram : (D (A:=A)).conjTranspose*D=bijProjection := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [D]
  have hs (a : A) : (∑ e : Environment A,
      star (if a=i.1 then recordMap e i.2 else 0)*
      (if a=j.1 then recordMap e j.2 else 0)) =
      if a=i.1 ∧ a=j.1 then (if i.2=j.2 ∧ Valid i.2 then 1 else 0) else 0 := by
    by_cases hi : a=i.1
    · by_cases hj : a=j.1
      · simp only [if_pos hi,if_pos hj,if_pos (And.intro hi hj)]
        exact recordMap_gram i.2 j.2
      · simp only [if_neg hj,mul_zero,Finset.sum_const_zero,
          if_neg (show ¬(a=i.1 ∧ a=j.1) by tauto)]
    · simp only [if_neg hi,star_zero,zero_mul,Finset.sum_const_zero,
        if_neg (show ¬(a=i.1 ∧ a=j.1) by tauto)]
  simp_rw [hs]
  by_cases he : i=j
  · subst j
    simp [bijProjection,predicateProjection,Matrix.diagonal_apply,Valid,BijRecord]
  · have hn : ¬(i.1=j.1 ∧ i.2=j.2) := by rintro ⟨h1,h2⟩; exact he (Prod.ext h1 h2)
    have hz (a : A) :
      (if a=i.1 ∧ a=j.1 then (if i.2=j.2 ∧ Valid i.2 then (1:ℂ) else 0) else 0)=0 := by
      by_cases h : a=i.1 ∧ a=j.1
      · have hr : i.2≠j.2 := by intro hr; exact hn ⟨h.1.symm.trans h.2,hr⟩
        simp [h,hr]
      · simp [h]
    simp_rw [hz]
    simp [bijProjection,predicateProjection,Matrix.diagonal_apply,he,Ne.symm he]

theorem D_column (i : Basis A) (hi : Valid i.2) :
    (fun o => D o i) = queryState i.1 ⟨i.2,hi⟩ := by
  funext o
  simp [D,recordMap,queryState,hi]

#print axioms decompression_gram
end
end ICO.MHRecordDecompression

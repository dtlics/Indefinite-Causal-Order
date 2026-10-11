import ICO.MHRecordDecompression
import ICO.MHRecordCard

namespace ICO.MHCompressionFreshInverse
open Matrix QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport ICO.MHWPartial
  ICO.MHPermutationExtensions ICO.MHTernaryProfile ICO.MHTernaryCompression
  ICO.MHRecordExtension ICO.MHPurifiedOracle ICO.MHCompressedQuery
  ICO.MHRecordDecompression ICO.MHRecordCard
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 1200000

theorem D_rightW_entry (i : Basis A) (h : rightPredicate i) (y : A) (e : Environment A) :
    ((D (A:=A))*(rightW (A:=A))) (y,e) i =
      if hy : FreshLeft y (i.2.1∪i.2.2) then
        stepCoefficient ⟨i.2,h.1⟩ * state (rightExtend ⟨i.2,h.1⟩ y i.1 hy h.2.1) e else 0 := by
  by_cases hy : FreshLeft y (i.2.1∪i.2.2)
  · rw [dif_pos hy,Matrix.mul_apply]
    let k : Basis A := (y,i.2.1,insert (y,i.1) i.2.2)
    rw [Finset.sum_eq_single k]
    · have hs : RightStep i k := ⟨rfl,hy,rfl⟩
      have hw : (rightW (A:=A)) k i=stepCoefficient ⟨i.2,h.1⟩ := by
        rw [coefficient_leftDomain]
        simp only [rightW,Matrix.mul_diagonal,rightProjection,predicateProjection,if_pos h,mul_one]
        exact if_pos ⟨h.2.2,hs⟩
      have hd : (D (A:=A)) (y,e) k = state (rightExtend ⟨i.2,h.1⟩ y i.1 hy h.2.1) e := by
        have hv : Valid k.2 := (rightExtend ⟨i.2,h.1⟩ y i.1 hy h.2.1).property
        simp only [D,k,if_pos rfl,recordMap,dif_pos hv]
        rfl
      rw [hw,hd,mul_comm]
    · intro j hj hjk
      by_cases hjy : j.1=y
      · by_cases hw : (rightW (A:=A)) j i=0
        · simp [hw]
        · have hs := (rightW_support hw).2
          have he : j=k := by
            apply Prod.ext hjy
            exact Prod.ext hs.1 (by simpa [hjy,k] using hs.2.2)
          exact (hjk he).elim
      · have hd : D (y,e) j=0 := by simp [D,Ne.symm hjy]
        simp [hd]
    · intro hk
      exact (hk (Finset.mem_univ _)).elim
  · rw [dif_neg hy,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjy : j.1=y
    · have hw : (rightW (A:=A)) j i=0 := by
        by_contra hn
        have hs := (rightW_support hn).2.2.1
        exact hy (by simpa [hjy] using hs)
      simp [hw]
    · have hd : D (y,e) j=0 := by simp [D,Ne.symm hjy]
      simp [hd]

/-- Concrete exact intertwining on the fresh inverse-query domain. -/
theorem inverse_fresh_intertwine :
    (queryMatrix (A:=A)).conjTranspose * (D (A:=A)) * (rightProjection (A:=A)) = ((D (A:=A)) * rightW (A:=A)) := by
  ext o i
  have hc : ((queryMatrix (A:=A)).conjTranspose * (D (A:=A)) * (rightProjection (A:=A))) o i =
      ((queryMatrix (A:=A)).conjTranspose * (D (A:=A))) o i * (if rightPredicate i then 1 else 0) := by
    simp [rightProjection,predicateProjection,Matrix.mul_diagonal]
  rw [hc]
  by_cases hi : rightPredicate i
  · rw [if_pos hi,mul_one]
    have hcol : ((queryMatrix (A:=A)).conjTranspose * (D (A:=A))) o i =
        ((queryMatrix (A:=A)).conjTranspose *ᵥ queryState i.1 ⟨i.2,hi.1⟩) o := by
      change ((queryMatrix (A:=A)).conjTranspose *ᵥ (fun k => D k i)) o = _
      rw [D_column i hi.1]
    rw [hcol]
    rcases o with ⟨y,e⟩
    rw [inverse_query_fresh_entry _ _ hi.2.1,D_rightW_entry i hi y e]
  · rw [if_neg hi,mul_zero]
    symm
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hw : (rightW (A:=A)) j i=0 := by
      simp [rightW,rightProjection,predicateProjection,Matrix.mul_diagonal,hi]
    simp [hw]

#print axioms inverse_fresh_intertwine
end
end ICO.MHCompressionFreshInverse

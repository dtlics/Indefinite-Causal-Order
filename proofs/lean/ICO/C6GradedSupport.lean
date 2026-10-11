import ICO.C6RetainedGraded
import ICO.MHEmbeddingProjector

namespace ICO.C6GradedSupport
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6SectorChannel ICO.RecordingCopyIdentity
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
universe u v

variable {I:Type v} [Fintype I] [DecidableEq I]
  {H:I→Type u} [∀i,Fintype (H i)] [∀i,DecidableEq (H i)]

theorem inclusion_cross (i j:I) (hij:i≠j) :
    (inclusion (H:=H) i).conjTranspose*inclusion (H:=H) j=0 := by
  ext x y
  have hn:(⟨i,x⟩:Σk,H k)≠⟨j,y⟩ := by
    intro h
    exact hij (congrArg Sigma.fst h)
  simp only [inclusion,basisEmbedding,Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_one]
  change ((1:CMatrix (Σk,H k)).submatrix (Sigma.mk i) (Equiv.refl _)*
    (1:CMatrix (Σk,H k)).submatrix (Equiv.refl _) (Sigma.mk j)) x y=0
  rw [Matrix.one_submatrix_mul]
  simp [Matrix.submatrix_apply,Matrix.one_apply,hn]

theorem compress_included (i j:I) (X:CMatrix (H j)) (hij:i≠j) :
    conjugate (inclusion (H:=H) i).conjTranspose (conjugate (inclusion j) X)=0 := by
  simp only [conjugate_apply,Matrix.conjTranspose_conjTranspose]
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,inclusion_cross i j hij,
    Matrix.zero_mul,Matrix.zero_mul,Matrix.zero_mul]

theorem compress_self (i:I) (X:CMatrix (H i)) :
    conjugate (inclusion (H:=H) i).conjTranspose (conjugate (inclusion i) X)=X := by
  simp only [conjugate_apply,Matrix.conjTranspose_conjTranspose]
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,inclusion_gram,Matrix.one_mul,
    Matrix.mul_assoc,inclusion_gram,Matrix.mul_one]

variable {A M:Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def Supported (Q:ℕ) (r:Fin (Q+1)) (X:CMatrix (Graded (A:=A) Q M)) : Prop :=
  ∃Y:CMatrix (Cache (A:=A) (M:=M) r.val),X=conjugate (embed Q r) Y

theorem supported_zero (Q:ℕ) (r:Fin (Q+1)) : Supported (A:=A) (M:=M) Q r 0 := by
  exact ⟨0,(map_zero _).symm⟩

theorem queryBranch_included (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Matrix.unitaryGroup A ℂ) (w:A→ℝ) (r:Fin (Q+1)) (j:A) (f:Bool)
    (X:CMatrix (Cache (A:=A) (M:=M) r.val)) :
    ICO.C6RetainedGraded.queryBranch Q hpos hQ U w j f (conjugate (embed Q r) X)=
      ICO.C6RetainedGraded.localBranch Q hpos hQ U w r j f X := by
  simp only [ICO.C6RetainedGraded.queryBranch,LinearMap.sum_apply,LinearMap.comp_apply]
  rw [Finset.sum_eq_single r]
  · rw [show embed (A:=A) (M:=M) Q r=inclusion r from rfl,compress_self]
  · intro s _ hsr
    rw [show embed (A:=A) (M:=M) Q s=inclusion s from rfl,
      show embed (A:=A) (M:=M) Q r=inclusion r from rfl,
      compress_included (H:=fun r:Fin (Q+1)=>Cache (A:=A) (M:=M) r.val) s r X hsr,map_zero]
  · intro hr
    exact (hr (Finset.mem_univ _)).elim

#print axioms queryBranch_included
end
end ICO.C6GradedSupport

import ICO.C6FockNumber
import ICO.C6FockFlagErasure

namespace ICO.C6FockNumberContinuation
open Matrix QIT ICO.C6FockNumber ICO.C6PolarFock ICO.C6BosonicCacheSupport
  ICO.C6BosonicFockSupport ICO.C6BosonicFreshContraction ICO.C6BosonicSupport
  ICO.MHBoundedRecording ICO.MHFockKnownOperation
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem fresh_birth_preserves_old_number (S B:Finset A) (hSB:S⊆B) (k:ℕ)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rightNumber S k T*(queryFresh B T*polarRightOnFock h)=
      (queryFresh B T*polarRightOnFock h)*rightNumber S k T := by
  ext o i
  simp only [rightNumber,rightDiagonal,queryFresh,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hq:o.2.1∈B
  · simp [hq]
  · have hnS:o.2.1∉S := fun hs=>hq (hSB hs)
    by_cases hg:polarRightOnFock h o i=0
    · simp [hg]
    · have hn:=right_number_step S h ht o i hg
      simp only [if_neg hnS,add_zero] at hn
      simp only [if_neg hq,one_mul,hn]
      exact mul_comm _ _

theorem freshInverse_preserves_number (S B:Finset A) (hSB:S⊆B) (k:ℕ)
    {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A) :
    rightNumber S k T*freshInverse (polarLeftOnFock h) (polarRightOnFock h) (queryFresh B T)=
      freshInverse (polarLeftOnFock h) (polarRightOnFock h) (queryFresh B T)*rightNumber S k T := by
  have hc:rightNumber S k T*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)=
      (1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)*rightNumber S k T := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul]
    rw [←Matrix.mul_assoc,left_preserves_number,Matrix.mul_assoc,retrieval_preserves_number]
    simp only [Matrix.mul_assoc]
  unfold freshInverse
  rw [Matrix.mul_add,Matrix.add_mul,retrieval_preserves_number]
  congr 1
  rw [←Matrix.mul_assoc, fresh_birth_preserves_old_number S B hSB k h ht,Matrix.mul_assoc,hc]
  simp only [Matrix.mul_assoc]

theorem known_preserves_number {M N:Type*} [Fintype M] [DecidableEq M]
    [Fintype N] [DecidableEq N] (S:Finset A) (k T:ℕ) (K:Matrix (A×N) (A×M) ℂ) :
    Matrix.kronecker (rightNumber S k T) (1:CMatrix N)*known T K=
      known T K*Matrix.kronecker (rightNumber S k T) (1:CMatrix M) := by
  have hn : Matrix.kronecker (rightNumber S k T) (1:CMatrix N)=
      Matrix.diagonal (fun i:InputCutoff (α:=A) T×N=>if labelNumber S i.1.1.2=k then 1 else 0) := by
    rw [rightNumber,rightDiagonal]
    change Matrix.kronecker (Matrix.diagonal _) (Matrix.diagonal (fun _:N=>(1:ℂ)))=_
    rw [Matrix.kronecker,Matrix.diagonal_kronecker_diagonal]
    simp only [mul_one]
  have hm : Matrix.kronecker (rightNumber S k T) (1:CMatrix M)=
      Matrix.diagonal (fun i:InputCutoff (α:=A) T×M=>if labelNumber S i.1.1.2=k then 1 else 0) := by
    rw [rightNumber,rightDiagonal]
    change Matrix.kronecker (Matrix.diagonal _) (Matrix.diagonal (fun _:M=>(1:ℂ)))=_
    rw [Matrix.kronecker,Matrix.diagonal_kronecker_diagonal]
    simp only [mul_one]
  rw [hn,hm]
  ext o i
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases he:records o.1=records i.1
  · have hc:labelNumber S o.1.1.2=labelNumber S i.1.1.2 := by
      have hh:=congrArg (fun R:Records (α:=A) T=>labelNumber S R.2.2) he
      exact hh
    rw [hc]
    exact mul_comm _ _
  · have hz:known T K o i=0 := by
      by_contra hh
      exact he (known_records T K o i hh)
    simp [hz]

#print axioms freshInverse_preserves_number
#print axioms known_preserves_number
end
end ICO.C6FockNumberContinuation

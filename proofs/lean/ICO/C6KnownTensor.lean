import ICO.C6BosonicQueryAlgebra
import ICO.MHFockKnownOperation

namespace ICO.C6KnownTensor
open Matrix QIT ICO.C6FockQueryMatrix ICO.C6BosonicQueryAlgebra
  ICO.MHFockKnownOperation ICO.MHBoundedRecording
open scoped Matrix
noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {A M N:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem known_tensor (T:ℕ) (P:CMatrix A) (D:Matrix N M ℂ) :
    known T (Matrix.kronecker P D)=Matrix.kronecker (queryMatrix P T) D := by
  ext ⟨⟨⟨s,R⟩,a,L⟩,m⟩ ⟨⟨⟨s',R'⟩,b,L'⟩,n⟩
  rw [known_coefficient]
  simp only [Matrix.kronecker,Matrix.kroneckerMap_apply]
  by_cases hs:s=s'
  · subst s'
    rw [queryMatrix_entry_same]
    simp [records,Sigma.mk.inj_iff,heq_eq_eq,Prod.mk.injEq,
      ite_and,mul_ite,ite_mul,mul_assoc,mul_left_comm,mul_comm]
    split_ifs <;> simp_all
  · have hr:records (⟨⟨s,R⟩,(a,L)⟩:InputCutoff (α:=A) T)≠
        records (⟨⟨s',R'⟩,(b,L')⟩:InputCutoff (α:=A) T) := by
      intro he
      exact hs (congrArg Sigma.fst he)
    rw [queryMatrix_entry_other _ _ _ _ hs]
    simp [hr]

theorem known_memory (T:ℕ) (D:Matrix N M ℂ) :
    known T (Matrix.kronecker (1:CMatrix A) D)=
      Matrix.kronecker (1:CMatrix (InputCutoff (α:=A) T)) D := by
  rw [known_tensor,ICO.C6BosonicQueryAlgebra.query_one]

#print axioms known_tensor
end
end ICO.C6KnownTensor

import ICO.C6BosonicReencoding
import ICO.C6HistoryControlled

/-! Explicit accessible-memory blocks of the literal finite-Fock maps. -/
namespace ICO.C6BosonicBlocks
open QIT ICO.C6BosonicReencoding ICO.C6BosonicQueryAlgebra ICO.C6FockQueryMatrix
  ICO.C6RetainedHistory ICO.C6HistoryControlled ICO.MHBoundedRecording
  ICO.MHFockKnownOperation ICO.C6FockChoiceMeasurement
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
variable {X M N L : Type*} [Fintype X] [DecidableEq X]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N] [Fintype L] [DecidableEq L]

def block (K : Matrix (X×N) (X×M) ℂ) (o:N) (i:M) : CMatrix X :=
  fun x y=>K (x,o) (y,i)

theorem block_mul (K : Matrix (X×L) (X×N) ℂ) (J : Matrix (X×N) (X×M) ℂ)
    (o:L) (i:M) : block (K*J) o i=∑n:N,block K o n*block J n i := by
  ext x y
  simp only [block,Matrix.sum_apply,Matrix.mul_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem block_tensor (F:CMatrix X) (o i:M) :
    block (Matrix.kronecker F (1:CMatrix M)) o i=if o=i then F else 0 := by
  ext x y
  simp only [block,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  split_ifs <;> simp

def diagonalFamily (F:M→CMatrix X) : CMatrix (X×M) :=
  fun o i=>if o.2=i.2 then F o.2 o.1 i.1 else 0

theorem block_diagonalFamily (F:M→CMatrix X) (o i:M) :
    block (diagonalFamily F) o i=if o=i then F o else 0 := by
  ext x y
  simp only [block,diagonalFamily]
  split_ifs <;> rfl

theorem block_left_family (F:N→CMatrix X) (K:Matrix (X×N) (X×M) ℂ) (o:N) (i:M) :
    block (diagonalFamily F*K) o i=F o*block K o i := by
  rw [block_mul]
  simp only [block_diagonalFamily,ite_mul,Matrix.zero_mul]
  simp

theorem block_right_family (F:M→CMatrix X) (K:Matrix (X×N) (X×M) ℂ) (o:N) (i:M) :
    block (K*diagonalFamily F) o i=block K o i*F i := by
  rw [block_mul]
  simp only [block_diagonalFamily,mul_ite,Matrix.mul_zero]
  simp

theorem block_left_tensor (F:CMatrix X) (K:Matrix (X×N) (X×M) ℂ) (o:N) (i:M) :
    block (Matrix.kronecker F (1:CMatrix N)*K) o i=F*block K o i := by
  rw [block_mul]
  simp only [block_tensor,ite_mul,Matrix.zero_mul]
  simp

theorem family_absorption (F:N→CMatrix X) (G:M→CMatrix X)
    (K:Matrix (X×N) (X×M) ℂ)
    (h:∀o i,F o*block K o i*G i=block K o i*G i) :
    diagonalFamily F*K*diagonalFamily G=K*diagonalFamily G := by
  ext ⟨x,o⟩ ⟨y,i⟩
  have he : block (diagonalFamily F*K*diagonalFamily G) o i=block (K*diagonalFamily G) o i := by
    rw [block_right_family,block_left_family,block_right_family]
    exact h o i
  exact congrFun (congrFun he x) y

variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem known_block (T:ℕ) (K:Matrix (A×N) (A×M) ℂ) (o:N) (i:M) :
    block (known T K) o i=queryMatrix (fun a b=>K (a,o) (b,i)) T := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  simp only [block,known_coefficient]
  by_cases hs:s=s'
  · subst s'
    rw [queryMatrix_entry_same]
    simp only [records,Sigma.mk.inj_iff,heq_eq_eq,Prod.mk.injEq,true_and]
    by_cases hp:p=p' <;> by_cases hq:q=q' <;> simp [hp,hq]
  · rw [queryMatrix_entry_other _ T _ _ hs]
    simp [records,Sigma.mk.inj_iff,hs]

theorem controlled_family {T i:ℕ} {M:Type} [Fintype M] [DecidableEq M]
    (F:ICO.RecordingPurifiedProtocol.History (A×Bool) i→CMatrix (InputCutoff (α:=A) T)) :
    controlled (M:=M) F=diagonalFamily (fun p=>F p.2.1) := by
  ext o j
  exact controlled_entry F o j

#print axioms known_block
#print axioms family_absorption
end
end ICO.C6BosonicBlocks

import ICO.C6SharedSchedule

/-! Reassociate the oracle-choice bit into memory. The unknown unitary in
this schedule always acts on A, independently of the adaptive choice. -/
namespace ICO.C6SharedQuerySchedule
open Matrix QIT ICO.C6SharedBasis ICO.C6SharedStages ICO.C6SharedSchedule
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable (μ : ℕ→Type) [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

abbrev QueryMemory (k n:ℕ) := Bool×Memory (A:=A) μ k n

variable {μ}
def known (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ) (k n:ℕ) :
    Matrix (A×QueryMemory (A:=A) μ k (n+1)) (A×QueryMemory (A:=A) μ k n) ℂ :=
  (knownTagged H K k n).submatrix (regroup (Memory (A:=A) μ k (n+1))).symm
    (regroup (Memory (A:=A) μ k n)).symm

theorem known_isometry (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (hK:∀t,(K t)ᴴ*K t=1) (k n:ℕ) :
    (known H K k n)ᴴ*known H K k n=1 := by
  simp only [known,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
    knownTagged_isometry H K hK,Matrix.submatrix_one_equiv]

theorem oracle_regroup (U : Matrix.unitaryGroup A ℂ) (k n:ℕ) :
    (lift (M:=Memory (A:=A) μ k n) (taggedOracle U n)).submatrix
      (regroup (Memory (A:=A) μ k n)).symm (regroup (Memory (A:=A) μ k n)).symm =
      Matrix.kronecker (ICO.DoubleQuerySchedule.oracle (U:CMatrix A) n)
        (1:CMatrix (QueryMemory (A:=A) μ k n)) := by
  unfold taggedOracle ICO.DoubleQuerySchedule.oracle
  split_ifs
  · rw [←lift_star,←Matrix.conjTranspose_submatrix,shared_regroup]
    simpa [Matrix.kronecker] using
      Matrix.conjTranspose_kronecker (U:CMatrix A) (1:CMatrix (QueryMemory (A:=A) μ k n))
  · exact shared_regroup U

def run (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (U : Matrix.unitaryGroup A ℂ) (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) (n:ℕ) :
    A×QueryMemory (A:=A) μ k n→ℂ :=
  taggedRun H K U k v n ∘ (regroup (Memory (A:=A) μ k n)).symm

theorem run_zero (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (U : Matrix.unitaryGroup A ℂ) (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) :
    run H K U k v 0=v ∘ (regroup (Memory (A:=A) μ k 0)).symm := rfl

theorem run_succ (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (U : Matrix.unitaryGroup A ℂ) (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) (n:ℕ) :
    run H K U k v (n+1)=known H K k n*ᵥ
      (Matrix.kronecker (ICO.DoubleQuerySchedule.oracle (U:CMatrix A) n)
        (1:CMatrix (QueryMemory (A:=A) μ k n))*ᵥrun H K U k v n) := by
  rw [←oracle_regroup (μ:=μ) U k n]
  simp only [run,known,Matrix.submatrix_mulVec_equiv,Function.comp_assoc,
    Equiv.symm_comp_self,Function.comp_id]
  rfl

#print axioms known_isometry
#print axioms run_succ
end
end ICO.C6SharedQuerySchedule

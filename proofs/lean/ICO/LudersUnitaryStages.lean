import ICO.PrivateQueryStep

namespace ICO.LudersUnitaryStages
open Matrix QIT ICO.SequentialIsometry ICO.RecordingPublicHistory ICO.RecordingPublicStep
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 2400000
variable {A M N H : Type u} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
  [Fintype H] [DecidableEq H]

/-- Copy only the query basis index. The existing memory, including previous
private copied outcomes, is untouched. -/
def copyQuery : Matrix (A×(A×M)) (A×M) ℂ := fun o i =>
  if o.1=i.1 ∧ o.2.1=i.1 ∧ o.2.2=i.2 then 1 else 0

theorem copyQuery_isometry : (copyQuery (A:=A) (M:=M)).conjTranspose*copyQuery (A:=A) (M:=M)=(1 : CMatrix (A×M)) := by
  ext i j
  rcases i with ⟨a,m⟩
  rcases j with ⟨b,n⟩
  simp [copyQuery,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Matrix.one_apply,Prod.mk.injEq,ite_and,apply_ite,ite_mul,mul_ite]
  aesop

/-- Two actual unitary calls per Lüders query: first U†, then a private copy,
then U, then the oracle-independent public computation. -/
def step (U : CMatrix A) (K : Matrix (A×N) (A×M) ℂ) :
    Matrix (A×((A×H)×N)) (A×(H×M)) ℂ :=
  publicStep (h:=H) K * Matrix.kronecker U (1 : CMatrix (A×(H×M))) *
    copyQuery * Matrix.kronecker U.conjTranspose (1 : CMatrix (H×M))

theorem step_eq_luders (U : CMatrix A) (K : Matrix (A×N) (A×M) ℂ) :
    step (H:=H) U K=ICO.PrivateQueryStep.luders U K := by
  rw [ICO.PrivateQueryStep.luders_eq_step]
  ext o i
  rcases o with ⟨a,⟨⟨j,e⟩,n⟩⟩
  rcases i with ⟨b,⟨f,m⟩⟩
  by_cases hef : e=f
  all_goals
    simp [step,ICO.PrivateQueryStep.step,publicStep,historyKnown,regroupInput,copyQuery,
      ICO.SwitchObservable.basisProjection,Matrix.mul_apply,Matrix.submatrix_apply,
      Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.kronecker,
      Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.single,Prod.mk.injEq,ite_and,
      apply_ite,ite_mul,mul_ite,hef,Finset.sum_mul,Finset.mul_sum,mul_assoc]

#print axioms copyQuery_isometry
#print axioms step_eq_luders
end
end ICO.LudersUnitaryStages

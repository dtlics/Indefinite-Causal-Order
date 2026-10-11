import ICO.C6SharedStages

/-! The fixed middle isometry exposes orthogonal private branches with a
rank-one query vector. Both the box choice and the outcome remain private. -/
namespace ICO.C6ChoiceMeasurement
open Matrix QIT ICO.C6SharedBasis ICO.C6SharedStages ICO.FullSwitchChannel
open ICO.LudersUnitaryStages
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def queryVector (H : Matrix.unitaryGroup A ℂ) (p:Bool×A) : A→ℂ :=
  fun a => if p.1 then (H:CMatrix A) a p.2 else (1:CMatrix A) a p.2

theorem queryVector_normalized (H : Matrix.unitaryGroup A ℂ) (p:Bool×A) :
    ∑a,‖queryVector H p a‖^2=1 := by
  rcases p with ⟨b,j⟩
  cases b
  · simp [queryVector,Matrix.one_apply,apply_ite]
  · have hH : (H:CMatrix A)ᴴ*(H:CMatrix A)=1 := H.property.1
    have hh := congrArg Complex.re (congrFun (congrFun hH j) j)
    simp only [queryVector,ite_true,Complex.sq_norm,Complex.normSq_apply]
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_re,pow_two] using hh

theorem middle_entry (H : Matrix.unitaryGroup A ℂ) (a x j:A) (b c e:Bool) (m n:M) :
    middle H ((a,b),((j,c),m)) ((x,e),n)=
      if b=c ∧ e=c ∧ m=n then queryVector H (c,j) a*star (queryVector H (c,j) x) else 0 := by
  cases b <;> cases c <;> cases e <;>
    simp [middle,lift,knownBasis,choiceUnitary,controlled,copyQuery,queryVector,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.one_apply,Fintype.sum_prod_type,Prod.mk.injEq,ite_and,apply_ite,
      ite_mul,mul_ite,Finset.mul_sum,Finset.sum_mul,mul_assoc] <;>
    split_ifs <;> simp_all <;> aesop

def branchAmplitude (H : Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ)
    (p:Bool×A) (m:M) : ℂ := ∑x,star (queryVector H p x)*v ((x,p.1),m)

theorem middle_branch (H : Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ)
    (a j:A) (b c:Bool) (m:M) :
    (middle H*ᵥv) ((a,b),((j,c),m))=
      if b=c then queryVector H (c,j) a*branchAmplitude H v (c,j) m else 0 := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,middle_entry]
  by_cases h:b=c
  · subst b
    simp [branchAmplitude,Finset.mul_sum,mul_assoc,ite_and]
  · simp [h]

#print axioms queryVector_normalized
#print axioms middle_branch
end
end ICO.C6ChoiceMeasurement

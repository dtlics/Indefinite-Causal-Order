import ICO.ProtocolSchedule
import ICO.LudersDilation
import ICO.RecordingPublicStep

namespace ICO.PrivateQueryStep
open Matrix QIT ICO.SequentialIsometry ICO.RecordingHistory
  ICO.RecordingPublicHistory ICO.RecordingPublicStep
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 1800000
variable {A M N H I : Type u} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

def step (U : I → CMatrix A) (K : Matrix (A×N) (A×M) ℂ) :
    Matrix (A×((I×H)×N)) (A×(H×M)) ℂ := fun o i =>
  if o.2.1.2=i.2.1 then (K*Matrix.kronecker (U o.2.1.1) (1 : CMatrix M))
    (o.1,o.2.2) (i.1,i.2.2) else 0

theorem step_branch (U : I → CMatrix A) (K : Matrix (A×N) (A×M) ℂ)
    (v : A×(H×M) → ℂ) (j:I) (e:H) (o:A×N) :
    (step U K*ᵥv) (o.1,((j,e),o.2)) =
      ((K*Matrix.kronecker (U j) (1 : CMatrix M))*ᵥ
        (fun i : A×M => v (i.1,(e,i.2)))) o := by
  simp [step,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,ite_mul]

theorem step_erasure (U : I → CMatrix A) (K : Matrix (A×N) (A×M) ℂ)
    (v : A×(H×M) → ℂ) :
    eraseHistory.map (rankOneMatrix (step U K*ᵥv)) =
      K * ICO.AllChannelDilation.oracleMap U (eraseHistory.map (rankOneMatrix v)) * K.conjTranspose := by
  rw [eraseHistory_rankOne,eraseHistory_rankOne]
  simp only [Fintype.sum_prod_type]
  have hb (j:I) (e:H) :
      (fun o : A×N => (step U K*ᵥv) (o.1,((j,e),o.2))) =
      (K*Matrix.kronecker (U j) (1 : CMatrix M))*ᵥ(fun i : A×M => v (i.1,(e,i.2))) := by
    funext o
    exact step_branch U K v j e o
  simp_rw [hb,rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  simp only [ICO.AllChannelDilation.oracleMap,MatrixMap.ofKraus,LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.mul_sum,Matrix.sum_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]

def copyRegroup (A H M : Type u) : ((A×(H×M))×A) ≃ (A×((A×H)×M)) where
  toFun x := (x.1.1,((x.2,x.1.2.1),x.1.2.2))
  invFun x := ((x.1,(x.2.1.2,x.2.2)),x.2.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The literal U†, private computational-basis copy, U sequence, followed by
an accessible isometry. No later operation reads the copied histories. -/
def luders (U : CMatrix A) (K : Matrix (A×N) (A×M) ℂ) :
    Matrix (A×((A×H)×N)) (A×(H×M)) ℂ :=
  historyKnown K * permutation (copyRegroup A H M) * ICO.LudersDilation.memorySandwich U

theorem luders_eq_step (U : CMatrix A) (K : Matrix (A×N) (A×M) ℂ) :
    luders (H:=H) U K = step (ICO.SwitchObservable.basisProjection U) K := by
  unfold luders
  rw [Matrix.mul_assoc,permutation,Matrix.one_submatrix_mul]
  ext o i
  rcases o with ⟨a,⟨⟨j,e⟩,n⟩⟩
  rcases i with ⟨b,⟨f,m⟩⟩
  by_cases hef : e=f
  all_goals
    simp [Matrix.mul_apply,Fintype.sum_prod_type,historyKnown,step,
      ICO.LudersDilation.memorySandwich,ICO.LudersDilation.sandwich_entry,
      Matrix.submatrix_apply,copyRegroup,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.one_apply,Prod.mk.injEq,ite_and,ite_mul,mul_ite,hef]

theorem luders_isometry (U : Matrix.unitaryGroup A ℂ) (K : Matrix (A×N) (A×M) ℂ)
    (hK : K.conjTranspose*K=1) :
    (luders (H:=H) (U:CMatrix A) K).conjTranspose*luders (H:=H) (U:CMatrix A) K=1 := by
  have hc := permutation_isometry (copyRegroup A H M)
  have hh := historyKnown_isometry (h:=A×H) K hK
  have hs := ICO.LudersDilation.memorySandwich_isometry (M:=H×M) U
  simp only [luders,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (historyKnown K).conjTranspose,hh,Matrix.one_mul]
  rw [←Matrix.mul_assoc (permutation (copyRegroup A H M)).conjTranspose,hc,Matrix.one_mul]
  exact hs

theorem luders_erasure (U : CMatrix A) (K : Matrix (A×N) (A×M) ℂ)
    (v : A×(H×M) → ℂ) :
    eraseHistory.map (rankOneMatrix (luders U K*ᵥv)) =
      K * ICO.AllChannelDilation.oracleMap (ICO.SwitchObservable.basisProjection U)
        (eraseHistory.map (rankOneMatrix v)) * K.conjTranspose := by
  rw [luders_eq_step]
  exact step_erasure _ K v

#print axioms luders_erasure
#print axioms step_erasure
#print axioms luders_isometry
end
end ICO.PrivateQueryStep

import ICO.AllChannelDilation

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.AllChannelDilation

namespace ICO.OracleLift
set_option maxHeartbeats 400000
noncomputable section
universe u
variable {A M I : Type u} [Fintype A] [Fintype M] [Fintype I]
  [DecidableEq A] [DecidableEq M] [DecidableEq I]

/-- Apply a matrix map to the query register and leave private memory intact. -/
def liftMap (f : MatrixMap A A) : MatrixMap (A × M) (A × M) where
  toFun X := fun p q => f (fun a b => X (a,p.2) (b,q.2)) p.1 q.1
  map_add' X Y := by
    ext p q
    exact congrFun (congrFun (f.map_add _ _) p.1) q.1
  map_smul' z X := by
    ext p q
    exact congrFun (congrFun (f.map_smul z _) p.1) q.1

def liftLinear : MatrixMap A A →ₗ[ℂ] MatrixMap (A × M) (A × M) where
  toFun := liftMap
  map_add' f g := rfl
  map_smul' z f := rfl

theorem liftMap_id : liftMap (LinearMap.id : MatrixMap A A) =
    (LinearMap.id : MatrixMap (A × M) (A × M)) := by
  ext X p q
  rfl

theorem oracleMap_lift (U : I → CMatrix A) :
    oracleMap (M:=M) U = liftMap (MatrixMap.ofKraus U) := by
  ext X p q
  rcases p with ⟨a,m⟩
  rcases q with ⟨b,n⟩
  simp [oracleMap,liftMap,MatrixMap.ofKraus,Matrix.sum_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type,Matrix.one_apply,Finset.sum_mul,Finset.mul_sum,apply_ite,mul_ite]

def mixtureKraus (t : ℝ) (U : I → CMatrix A) : Option I → CMatrix A
  | none => (Real.sqrt (1-t) : ℂ) • 1
  | some i => (Real.sqrt t : ℂ) • U i

theorem sqrt_product (t : ℝ) (ht : 0≤t) :
    (Real.sqrt t : ℂ)*(Real.sqrt t : ℂ) = (t : ℂ) := by
  exact_mod_cast Real.mul_self_sqrt ht

theorem scaled_adjoint (t : ℝ) (ht : 0≤t) (U : CMatrix A) :
    ((Real.sqrt t : ℂ) • U)ᴴ * ((Real.sqrt t : ℂ) • U) = (t : ℂ) • (Uᴴ * U) := by
  simp [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    sqrt_product t ht,Real.mul_self_sqrt ht]

theorem mixtureKraus_complete (t : ℝ) (ht : t∈Set.Icc 0 1) (U : I → CMatrix A)
    (hU : ∑ i,(U i)ᴴ * U i=1) : ∑ i,(mixtureKraus t U i)ᴴ * mixtureKraus t U i=1 := by
  rw [Fintype.sum_option]
  simp only [mixtureKraus]
  rw [scaled_adjoint (1-t) (by linarith [ht.2]),Matrix.conjTranspose_one,Matrix.one_mul]
  simp_rw [scaled_adjoint t ht.1]
  rw [← Finset.smul_sum,hU,← add_smul]
  have h : ((1-t : ℝ) : ℂ)+(t : ℂ)=1 := by push_cast; ring
  rw [h,one_smul]

theorem scaled_sandwich (t : ℝ) (ht : 0≤t) (U X : CMatrix A) :
    ((Real.sqrt t : ℂ) • U) * X * ((Real.sqrt t : ℂ) • U)ᴴ = (t : ℂ) • (U*X*Uᴴ) := by
  simp [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    sqrt_product t ht,Real.mul_self_sqrt ht]

theorem mixtureKraus_map (t : ℝ) (ht : t∈Set.Icc 0 1) (U : I → CMatrix A) :
    MatrixMap.ofKraus (mixtureKraus t U) =
      (1-t) • (LinearMap.id : MatrixMap A A) + t • MatrixMap.ofKraus U := by
  ext X a b
  simp only [MatrixMap.ofKraus,LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_option,mixtureKraus]
  simp_rw [scaled_sandwich (1-t) (by linarith [ht.2]),scaled_sandwich t ht.1]
  simp [Matrix.conjTranspose_one,← Finset.smul_sum,Complex.real_smul]

/-- Mixing each oracle with the identity before extending it to private memory
gives exactly the affine segment used by the checked circuit polarization. -/
theorem mixture_oracleMap (t : ℝ) (ht : t∈Set.Icc 0 1) (U : I → CMatrix A) :
    oracleMap (M:=M) (mixtureKraus t U) =
      LinearMap.id+t • (oracleMap (M:=M) U-LinearMap.id) := by
  rw [oracleMap_lift,mixtureKraus_map t ht U,oracleMap_lift]
  change (liftLinear.restrictScalars ℝ)
    ((1-t) • (LinearMap.id : MatrixMap A A) + t • MatrixMap.ofKraus U) = _
  rw [map_add,map_smul,map_smul]
  change (1-t) • liftMap (LinearMap.id : MatrixMap A A) + t • liftMap (MatrixMap.ofKraus U) = _
  rw [liftMap_id]
  module

#print axioms mixtureKraus_complete
#print axioms mixture_oracleMap
end
end ICO.OracleLift

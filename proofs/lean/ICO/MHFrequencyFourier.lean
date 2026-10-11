import ICO.MHDecompressionStep
import ICO.MHControlledMixture

namespace ICO.MHFrequencyFourier
open Matrix QIT ICO.MHTernaryCompression ICO.MHPurifiedFourier ICO.MHPurifiedOracle
  ICO.MHPhasePermutation ICO.MHControlledMixture ICO.MHDecompressionKnown
  ICO.MHRotatedDecompressionDefect ICO.MHRotatedTrajectory ICO.MHDecompressionStep
  ICO.MHDecompressionInitial ICO.MHDecompressionErasure ICO.MHDecompressionDefect
  ICO.MHFockDecompressionDefect
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
variable {A μ ν : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]

theorem controlled_mul {E H J L : Type*} [Fintype E] [DecidableEq E]
    [Fintype H] [Fintype J] [Fintype L]
    (V : E → Matrix L J ℂ) (W : E → Matrix J H ℂ) :
    controlledMatrix V*controlledMatrix W=controlledMatrix (fun e => V e*W e) := by
  ext o i
  by_cases h : o.2=i.2
  · simp [controlledMatrix,Matrix.mul_apply,Fintype.sum_prod_type,h]
  · simp [controlledMatrix,Matrix.mul_apply,Fintype.sum_prod_type,h]

def phaseRotated (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) : CMatrix (A×Environment A) :=
  Matrix.kronecker (after C D inverse : CMatrix A) (1 : CMatrix (Environment A))*
    (if inverse then (phaseQuery (A:=A)).conjTranspose else phaseQuery)*
      Matrix.kronecker (before C D inverse : CMatrix A) (1 : CMatrix (Environment A))

def hiddenUnitary (C D : Matrix.unitaryGroup A ℂ) (e : Environment A) : Matrix.unitaryGroup A ℂ :=
  D*phaseOracleUnitary e*C

def hiddenChoice (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) (e : Environment A) : CMatrix A :=
  if inverse then (hiddenUnitary C D e : CMatrix A).conjTranspose else hiddenUnitary C D e

theorem fourier_rotated (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) :
    queryFourier*(physicalRotated C D inverse : CMatrix (A×Environment A))=
      phaseRotated C D inverse*queryFourier := by
  have hbefore := known_operation_commutes (A:=A) (before C D inverse : CMatrix A)
  have hafter := known_operation_commutes (A:=A) (after C D inverse : CMatrix A)
  change Matrix.kronecker (before C D inverse : CMatrix A) (1 : CMatrix (Environment A))*queryFourier=
    queryFourier*Matrix.kronecker (before C D inverse : CMatrix A) (1 : CMatrix (Environment A)) at hbefore
  change Matrix.kronecker (after C D inverse : CMatrix A) (1 : CMatrix (Environment A))*queryFourier=
    queryFourier*Matrix.kronecker (after C D inverse : CMatrix A) (1 : CMatrix (Environment A)) at hafter
  have hchoice : queryFourier*(physicalChoice (A:=A) inverse : CMatrix (A×Environment A))=
      (if inverse then (phaseQuery (A:=A)).conjTranspose else phaseQuery)*queryFourier := by
    cases inverse
    · exact fourier_intertwining
    · exact fourier_inverse_intertwining
  simp only [physicalRotated,Matrix.UnitaryGroup.mul_val,spectatorUnitary,phaseRotated]
  calc
    _ = (queryFourier*Matrix.kronecker (after C D inverse : CMatrix A) (1 : CMatrix (Environment A)))*
        (physicalChoice (A:=A) inverse : CMatrix (A×Environment A))*
        Matrix.kronecker (before C D inverse : CMatrix A) (1 : CMatrix (Environment A)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [← hafter,Matrix.mul_assoc _ queryFourier, hchoice]
      simp only [Matrix.mul_assoc]
      rw [← hbefore]

theorem phaseRotated_controlled (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) :
    phaseRotated C D inverse=controlledMatrix (hiddenChoice C D inverse) := by
  cases inverse <;>
    simp only [phaseRotated,after,before,Bool.false_eq_true,if_false,if_true,
      phase_query_controlled,controlled_adjoint,← controlled_constant,controlled_mul]
  all_goals
    apply congrArg controlledMatrix
    funext e
    simp [hiddenChoice,hiddenUnitary,Matrix.UnitaryGroup.mul_val,
      Matrix.UnitaryGroup.inv_val,Matrix.star_eq_conjTranspose,phaseOracleUnitary,
      Matrix.conjTranspose_mul,Matrix.mul_assoc]

def memoryQuery (Q : CMatrix (A×Environment A)) : CMatrix ((A×μ)×Environment A) :=
  (Matrix.kronecker Q (1 : CMatrix μ)).submatrix (environmentFirst μ).symm (environmentFirst μ).symm

def memoryFourier : CMatrix ((A×μ)×Environment A) :=
  Matrix.kronecker (1 : CMatrix (A×μ)) (environmentFourier (A:=A))

theorem memoryFourier_eq : memoryFourier (A:=A) (μ:=μ)=memoryQuery (μ:=μ) queryFourier := by
  ext o i
  simp only [memoryFourier,memoryQuery,queryFourier,Matrix.submatrix_apply,environmentFirst,
    Equiv.symm_mk,Equiv.coe_fn_mk,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all <;> aesop

theorem memoryQuery_mul (Q R : CMatrix (A×Environment A)) :
    memoryQuery (μ:=μ) Q*memoryQuery R=memoryQuery (Q*R) := by
  simp only [memoryQuery,Matrix.submatrix_mul_equiv,Matrix.kronecker,
    ← Matrix.mul_kronecker_mul,Matrix.mul_one]

theorem memoryQuery_controlled (V : Environment A → CMatrix A) :
    memoryQuery (μ:=μ) (controlledMatrix V)=
      controlledMatrix (fun e => Matrix.kronecker (V e) (1 : CMatrix μ)) := by
  ext o i
  simp only [memoryQuery,controlledMatrix,Matrix.submatrix_apply,environmentFirst,
    Equiv.symm_mk,Equiv.coe_fn_mk,Matrix.kronecker,Matrix.kroneckerMap_apply]
  split_ifs <;> simp_all

theorem memory_rotated_intertwine (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) :
    memoryFourier (A:=A) (μ:=μ)*memoryQuery (physicalRotated C D inverse : CMatrix (A×Environment A))=
      controlledMatrix (fun e => Matrix.kronecker (hiddenChoice C D inverse e) (1 : CMatrix μ))*memoryFourier := by
  rw [memoryFourier_eq, memoryQuery_mul,fourier_rotated,← memoryQuery_mul,
    phaseRotated_controlled,memoryQuery_controlled]

theorem step_reindexed (K : Matrix (A×ν) (A×μ) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) :
    (physicalStep K C D inverse).submatrix (environmentFirst ν).symm (environmentFirst μ).symm=
      Matrix.kronecker K (1 : CMatrix (Environment A))*
        memoryQuery (physicalRotated C D inverse : CMatrix (A×Environment A)) := by
  rw [physicalStep,← Matrix.submatrix_mul_equiv _ _ (environmentFirst ν).symm
    (environmentFirst μ).symm (environmentFirst μ).symm]
  simp only [physicalKnown,Matrix.submatrix_submatrix,Equiv.self_comp_symm,
    Matrix.submatrix_id_id,memoryQuery]

theorem step_intertwine (K : Matrix (A×ν) (A×μ) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) :
    memoryFourier (A:=A) (μ:=ν)*
      (physicalStep K C D inverse).submatrix (environmentFirst ν).symm (environmentFirst μ).symm=
      controlledMatrix (fun e => K*Matrix.kronecker (hiddenChoice C D inverse e) (1 : CMatrix μ))*
        memoryFourier (A:=A) (μ:=μ) := by
  have hc := known_operation_commutes (A:=A) K
  change Matrix.kronecker K (1 : CMatrix (Environment A))*memoryFourier=
    memoryFourier*Matrix.kronecker K (1 : CMatrix (Environment A)) at hc
  rw [step_reindexed,← Matrix.mul_assoc,← hc]
  rw [Matrix.mul_assoc,memory_rotated_intertwine,← Matrix.mul_assoc,
    ← controlled_constant,controlled_mul]

def transform (v : (A×Environment A)×μ→ℂ) : (A×μ)×Environment A→ℂ :=
  memoryFourier*ᵥ(v ∘ (environmentFirst μ).symm)

theorem transform_step (K : Matrix (A×ν) (A×μ) ℂ)
    (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) (v : (A×Environment A)×μ→ℂ) :
    transform (physicalStep K C D inverse*ᵥv)=
      controlledMatrix (fun e => K*Matrix.kronecker (hiddenChoice C D inverse e) (1 : CMatrix μ))*ᵥ
        transform v := by
  have hr := Matrix.submatrix_mulVec_equiv (physicalStep K C D inverse)
    (v ∘ (environmentFirst μ).symm) (environmentFirst ν).symm (environmentFirst μ).symm
  simp only [Equiv.symm_symm,Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] at hr
  rw [transform,← hr,Matrix.mulVec_mulVec,step_intertwine,← Matrix.mulVec_mulVec]
  rfl

theorem transform_initial (v : A×μ→ℂ) :
    transform (frequencyInitial v)=fun o => uniformAmplitude (A:=A)*v o.1 := by
  funext o
  rcases o with ⟨⟨a,m⟩,e⟩
  simp only [transform,memoryFourier,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Function.comp_apply,
    environmentFirst,Equiv.symm_mk,Equiv.coe_fn_mk,frequencyInitial,Prod.mk.injEq,
    ite_and,ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.sum_ite_eq,
    Finset.mem_univ,if_true]
  simpa only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Finset.sum_mul,mul_assoc] using
    congrArg (fun z => z*v (a,m)) (fourier_initial e)

theorem transform_visible (v : (A×Environment A)×μ→ℂ) :
    partialTraceB (rankOneMatrix (transform v))=physicalVisible v := by
  apply private_erasure
  have h := (environmentFourierUnitary (A:=A)).property.1
  change (environmentFourier (A:=A)).conjTranspose*environmentFourier=1 at h
  rw [h,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.one_mulVec]

#print axioms transform_step
#print axioms transform_initial
#print axioms transform_visible
#print axioms fourier_rotated
#print axioms memory_rotated_intertwine
end
end ICO.MHFrequencyFourier

import ICO.C6RawWeightedEndpoint
import ICO.ProtocolResponseNorm

/-! The physical shared-Haar comparison: every recording/cache identification
and normalization premise is discharged for the actual learner trajectory. -/
namespace ICO.C6SharedPairBound
open QIT Matrix ICO.C6RawWeightedEndpoint ICO.C6RawDecoded
  ICO.C6ModeFockVacuum ICO.C6RawFlagSlices ICO.C6SharedEndpoint
  ICO.C6PairedTrajectory ICO.C6CacheDecode ICO.SequentialIsometry
  ICO.C6WeightedHistoryOutput ICO.C6CacheVisibleOutput ICO.C6UniformBounds
open scoped BigOperators MatrixOrder ComplexOrder
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 2048
set_option Elab.async false
variable {A M O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def emptyHistoryEquiv {μ : ℕ→Type} :
    (A×(Bool×μ 0)) ≃ (A×Public (A:=A) μ 0) where
  toFun x := (x.1,(x.2.1,(PUnit.unit,x.2.2)))
  invFun x := (x.1,(x.2.1,x.2.2.2))
  left_inv x := rfl
  right_inv x := by
    rcases x with ⟨a,b,η,m⟩
    cases η
    rfl

theorem smallInput_norm {μ : ℕ→Type} [∀i,Fintype (μ i)]
    [∀i,DecidableEq (μ i)] (z : A×Public (A:=A) μ 0→ℂ) :
    ‖WithLp.toLp 2 (smallInput z)‖=‖WithLp.toLp 2 z‖ := by
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (emptyHistoryEquiv (A:=A) (μ:=μ)).symm).norm_map (WithLp.toLp 2 z)

theorem smallKnown_isometry {μ : ℕ→Type} [∀i,Fintype (μ i)]
    [∀i,DecidableEq (μ i)] (i : ℕ)
    (K : Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (hK : K.conjTranspose*K=1) :
    (smallKnown K).conjTranspose*smallKnown K=1 := by
  change (grouped K).conjTranspose*grouped K=1
  rw [grouped,Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc A Bool (μ (i+1))).symm,hK]
  ext x y
  rcases x with ⟨a,b,m⟩
  rcases y with ⟨a',b',m'⟩
  simp [Matrix.submatrix_apply,Matrix.one_apply,Prod.mk.injEq,and_assoc]

theorem cacheInput_pos {q : ℕ}
    (tail : Protocol (A×Bool) ((A×Bool)×M) O q) (v : (A×Bool)×M→ℂ) :
    (cacheInput tail v).PosSemidef := rankOneMatrix_pos _

theorem cacheInput_trace {q : ℕ}
    (tail : Protocol (A×Bool) ((A×Bool)×M) O q) (v : (A×Bool)×M→ℂ)
    (hv : ‖WithLp.toLp 2 v‖=1) : (cacheInput tail v).trace=1 := by
  rw [cacheInput,vacuumCache_trace]
  apply Complex.ext
  · rw [ICO.C6FlagMass.pure_mass,smallInput_norm]
    change ‖WithLp.toLp 2 (initial tail v ∘
      (ICO.C6SharedStages.regroup (ICO.C6SharedSchedule.Memory (A:=A) tail.tailMemory 0 0)).symm)‖^2=1
    rw [initial_norm,hv]
    norm_num
  · simp [rankOneMatrix_trace,dotProduct,Complex.mul_conj]


#print axioms cacheInput_trace
end
end ICO.C6SharedPairBound

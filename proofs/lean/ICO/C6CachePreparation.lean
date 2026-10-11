import ICO.C6CacheWeights

/-! Actual basis-state preparation, with the external query discarded and
arbitrary entangled cache/reference memory retained. -/
namespace ICO.C6CachePreparation
open QIT ICO.C6CacheMap ICO.C6CacheWeighted ICO.C6CacheWeights
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1800000
variable {A M B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype B] [DecidableEq B]

def basisState (U : Matrix.unitaryGroup A ℂ) (j : A) : State A where
  matrix := (U : CMatrix A)*Matrix.single j j 1*(U : CMatrix A).conjTranspose
  pos := (QIT.posSemidef_single j).mul_mul_conjTranspose_same (U : CMatrix A)
  trace_eq_one := by
    have hu : (U : CMatrix A).conjTranspose*(U : CMatrix A)=1 := U.property.1
    rw [Matrix.trace_mul_comm,←Matrix.mul_assoc,hu,Matrix.one_mul]
    simp [Matrix.trace,Matrix.single]

def prepareBasis (U : Matrix.unitaryGroup A ℂ) (j : A) : Channel A A :=
  Channel.prepare (fun _ : A => basisState U j)

theorem prepareBasis_apply (U : Matrix.unitaryGroup A ℂ) (j : A) (X : CMatrix A) :
    (prepareBasis U j).map X=X.trace • (basisState U j).matrix := by
  simp only [prepareBasis,Channel.prepare_map,←Finset.sum_smul,Matrix.trace,Matrix.diag_apply]

def withMemory (U : Matrix.unitaryGroup A ℂ) (j : A) : Channel (A×M) (A×M) :=
  (prepareBasis U j).prod (Channel.idChannel M)

theorem withMemory_apply (U : Matrix.unitaryGroup A ℂ) (j : A) (X : CMatrix (A×M)) :
    (withMemory (M:=M) U j).map X=
      Matrix.kronecker (basisState U j).matrix (partialTraceA X) := by
  ext i k
  change (MatrixMap.kron (prepareBasis U j).map (Channel.idChannel M).map X) i k=_
  rw [MatrixMap.kron_idChannel_apply_slice,prepareBasis_apply]
  simp [Matrix.smul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.trace,Matrix.diag_apply,partialTraceA,mul_comm]

def isometryChannel (G : Matrix B (A×M) ℂ) (hG : G.conjTranspose*G=1) : Channel (A×M) B where
  map := conjugate G
  completelyPositive := conjugate_cp G
  tracePreserving := conjugate_trace_of_isometry G hG
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp G)

def birthBranch (G : Matrix B (A×M) ℂ) (hG : G.conjTranspose*G=1)
    (U : Matrix.unitaryGroup A ℂ) (j : A) : Channel (A×M) B :=
  (isometryChannel G hG).comp (withMemory U j)

theorem birthBranch_apply (G : Matrix B (A×M) ℂ) (hG : G.conjTranspose*G=1)
    (U : Matrix.unitaryGroup A ℂ) (j : A) (X : CMatrix (A×M)) :
    (birthBranch G hG U j).map X=
      G * Matrix.kronecker (basisState U j).matrix (partialTraceA X) * G.conjTranspose := by
  change conjugate G ((withMemory U j).map X)=_
  rw [withMemory_apply,conjugate_apply]

theorem birth_deficit (G : Matrix B (A×M) ℂ) (hG : G.conjTranspose*G=1)
    (U : Matrix.unitaryGroup A ℂ) (P : CMatrix A) (hP : IsStarProjection P)
    (X : CMatrix (A×M)) (hX : X.PosSemidef) :
    traceNorm (weighted (birthBranch G hG U) (fun _ => 1) X -
      weighted (birthBranch G hG U) (overlapWeight U P) X)=
      (P.trace.re/(Fintype.card A:ℝ))*X.trace.re :=
  actual_weighted_deficit _ U P hP X hX

#print axioms withMemory_apply
#print axioms birth_deficit
end
end ICO.C6CachePreparation

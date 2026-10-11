import ICO.C6CacheMap
import ICO.C6Polar

/-! Matrix covariance and genuine isometric channels used by the cache. -/
namespace ICO.C6MatrixCovariance
open Matrix QIT ICO.C6CacheMap ICO.RecordingDistance
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1000000
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem adjoint_intertwine (F : Matrix b a ℂ)
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ)
    (h : (V : CMatrix b) * F = F * (U : CMatrix a)) :
    (U : CMatrix a) * F.conjTranspose = F.conjTranspose * (V : CMatrix b) := by
  have ha := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_mul] at ha
  have hh := congrArg (fun B => (U : CMatrix a) * B * (V : CMatrix b)) ha
  have hu : (U : CMatrix a) * (U : CMatrix a).conjTranspose = 1 := U.property.2
  have hv : (V : CMatrix b).conjTranspose * (V : CMatrix b) = 1 := V.property.1
  simpa only [Matrix.mul_assoc, hv, Matrix.mul_one,
    ← Matrix.mul_assoc (U : CMatrix a) (U : CMatrix a).conjTranspose,
    hu, Matrix.one_mul] using hh

theorem encode_invariant (F : Matrix b a ℂ)
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ)
    (h : (V : CMatrix b) * F = F * (U : CMatrix a))
    (X : CMatrix a) (hX : (U : CMatrix a) * X = X * (U : CMatrix a)) :
    (V : CMatrix b) * (F * X * F.conjTranspose) =
      (F * X * F.conjTranspose) * (V : CMatrix b) := by
  have ha := adjoint_intertwine F U V h
  calc
    _ = ((V : CMatrix b) * F) * X * F.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = (F * (U : CMatrix a)) * X * F.conjTranspose := by rw [h]
    _ = F * ((U : CMatrix a) * X) * F.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = F * (X * (U : CMatrix a)) * F.conjTranspose := by rw [hX]
    _ = F * X * ((U : CMatrix a) * F.conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = F * X * (F.conjTranspose * (V : CMatrix b)) := by rw [ha]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem decode_invariant (F : Matrix b a ℂ)
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ)
    (h : (V : CMatrix b) * F = F * (U : CMatrix a))
    (X : CMatrix b) (hX : (V : CMatrix b) * X = X * (V : CMatrix b)) :
    (U : CMatrix a) * (F.conjTranspose * X * F) =
      (F.conjTranspose * X * F) * (U : CMatrix a) := by
  have ha := adjoint_intertwine F U V h
  calc
    _ = ((U : CMatrix a) * F.conjTranspose) * X * F := by simp only [Matrix.mul_assoc]
    _ = (F.conjTranspose * (V : CMatrix b)) * X * F := by rw [ha]
    _ = F.conjTranspose * ((V : CMatrix b) * X) * F := by simp only [Matrix.mul_assoc]
    _ = F.conjTranspose * (X * (V : CMatrix b)) * F := by rw [hX]
    _ = F.conjTranspose * X * ((V : CMatrix b) * F) := by simp only [Matrix.mul_assoc]
    _ = F.conjTranspose * X * (F * (U : CMatrix a)) := by rw [h]
    _ = _ := by simp only [Matrix.mul_assoc]

def isometryChannel (F : Matrix b a ℂ) (hF : F.conjTranspose * F = 1) :
    Channel a b where
  map := conjugate F
  completelyPositive := conjugate_cp F
  tracePreserving := fun X => conjugate_trace_of_isometry F hF X
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp F)

theorem adjoint_conjugate_TNI (F : Matrix b a ℂ) (hF : F.conjTranspose * F = 1) :
    MatrixMap.TraceNonincreasingCP (conjugate F.conjTranspose) := by
  refine ⟨conjugate_cp _, ?_⟩
  intro X hX
  have hP : (1 - F * F.conjTranspose).PosSemidef := by
    apply MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    · exact Matrix.posSemidef_self_mul_conjTranspose F
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.conjTranspose F, hF, Matrix.one_mul]
  have hp := QIT.cMatrix_trace_mul_posSemidef_re_nonneg hP hX
  rw [conjugate_trace, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at hp
  linarith

theorem traceNorm_isometry_conjugate (F : Matrix b a ℂ)
    (hF : F.conjTranspose * F = 1) (X : CMatrix a) (hX : X.IsHermitian) :
    traceNorm (F * X * F.conjTranspose) = traceNorm X := by
  have hx : X.conjTranspose = X := hX
  apply le_antisymm
  · simpa only [conjugate_apply] using traceNorm_contract_hermitian (conjugate F)
      (MatrixMap.traceNonincreasingCP_of_tracePreserving
        (conjugate_cp F) (isometryChannel F hF).tracePreserving) X hX
  · have hp := traceNorm_contract_hermitian (conjugate F.conjTranspose)
      (adjoint_conjugate_TNI F hF) (F * X * F.conjTranspose)
      (by simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hx, Matrix.mul_assoc])
    have he : conjugate F.conjTranspose (F * X * F.conjTranspose) = X := by
      rw [conjugate_apply, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.conjTranspose F, hF, Matrix.one_mul]
      simp only [hF, Matrix.mul_one]
    rwa [he] at hp

theorem traceNorm_unitary_conjugate (U : Matrix.unitaryGroup a ℂ) (X : CMatrix a) :
    traceNorm ((U : CMatrix a) * X * (U : CMatrix a).conjTranspose) = traceNorm X := by
  have hu : (U : CMatrix a).conjTranspose * (U : CMatrix a) = 1 := U.property.1
  have hright : traceNorm (X * (U : CMatrix a).conjTranspose) = traceNorm X := by
    apply traceNorm_eq_of_mul_conjTranspose_eq
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : CMatrix a).conjTranspose (U : CMatrix a),
      hu, Matrix.one_mul]
  calc
    _ = traceNorm (X * (U : CMatrix a).conjTranspose) := by
      rw [Matrix.mul_assoc]
      apply traceNorm_eq_of_conjTranspose_mul_eq
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U : CMatrix a).conjTranspose (U : CMatrix a),
        hu, Matrix.one_mul]
    _ = traceNorm X := hright

#print axioms traceNorm_isometry_conjugate
#print axioms traceNorm_unitary_conjugate
end
end ICO.C6MatrixCovariance

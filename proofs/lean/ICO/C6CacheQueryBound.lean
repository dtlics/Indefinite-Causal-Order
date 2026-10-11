import ICO.C6MemoryDecode
import ICO.C6BasisInvariant

/-! Basis-information bounds for the actual polar cache retrieval, with
arbitrary entangled memory. No scalar collision estimate is assumed. -/
namespace ICO.C6CacheQueryBound
open QIT Matrix ICO.C6MemoryDecode ICO.C6CacheDecode ICO.C6MemoryNatural
  ICO.C6BasisInvariant ICO.C6BasisDephase ICO.C6MatrixCovariance ICO.C6CacheMap
  ICO.C6BosonicPolar ICO.MHSectorCovariance ICO.C6LabelSymmetry
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1500000
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem invariant_cache_basis_bound (U : Matrix.unitaryGroup A ℂ) (n : ℕ)
    (X : CMatrix (Cache (A := A) (M := M) n)) (hX : X.PosSemidef)
    (hinv : CacheInvariant n X) :
    traceNorm (basisMap U (cacheHead n X) -
      (ICO.RecordingDepolarizing.withMemory (α := A)
        (μ := TensorPowerProfile (A × A) n × M)).map (cacheHead n X)) ≤
      6 * (n : ℝ) * X.trace.re / (Fintype.card A : ℝ) := by
  let ω := decode n * X * (decode n).conjTranspose
  have hω : ω.PosSemidef := hX.mul_mul_conjTranspose_same (decode n)
  have hi : CommonInvariant (n + 1) ω := decoded_invariant n X hinv
  have hb := invariant_basis_bound U n ω hω hi
  have ht : ω.trace = X.trace := by
    simpa only [ω, conjugate_apply] using conjugate_trace_of_isometry (decode n) (decode_gram n) X
  change traceNorm (basisMap U (ICO.C6DephaseChannel.headMatrix n
      (decode n * X * (decode n).conjTranspose)) -
    (ICO.RecordingDepolarizing.withMemory (α := A) (μ := TensorPower A n × (TensorPower A n × M))).map
      (ICO.C6DephaseChannel.headMatrix n (decode n * X * (decode n).conjTranspose))) ≤ _ at hb
  rw [decoded_head, basis_natural, depolarizing_natural _ (memoryDecode_gram n),
    ← Matrix.sub_mul, ← Matrix.mul_sub] at hb
  have hp : (basisMap U (cacheHead n X)).PosSemidef :=
    MatrixMap.ofKraus_mapsPositive _ _ (hX.submatrix _)
  have hq : ((ICO.RecordingDepolarizing.withMemory (α := A)
    (μ := TensorPowerProfile (A × A) n × M)).map (cacheHead n X)).PosSemidef :=
    (ICO.RecordingDepolarizing.withMemory (α := A)
      (μ := TensorPowerProfile (A × A) n × M)).mapsPositive _ (hX.submatrix _)
  rw [traceNorm_isometry_conjugate _
    (queryEmbedding_gram _ (memoryDecode_gram n)) _ (hp.isHermitian.sub hq.isHermitian), ht] at hb
  exact hb

def storedRotation (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Matrix.unitaryGroup (Cache (A := A) (M := M) n) ℂ :=
  tensorUnitary (outputRotation U 1 n) 1

def StoredInvariant (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n)) : Prop :=
  ∀ U : Matrix.unitaryGroup A ℂ,
    (storedRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n)) * X =
      X * (storedRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n))

def memoryPolar (n : ℕ) : Matrix (Cache (A := A) (M := M) (n + 1))
    (Cache (A := A) (M := M) n) ℂ :=
  Matrix.kronecker (leftPolar n) (1 : CMatrix M)

theorem memoryPolar_gram {n : ℕ} (hn : n < Fintype.card A) :
    (memoryPolar (A := A) (M := M) n).conjTranspose * memoryPolar (A := A) (M := M) n = 1 := by
  simp only [memoryPolar, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, leftPolar_isometry hn]
  simp only [Matrix.one_mul, Matrix.one_kronecker_one]

theorem memoryPolar_covariance (U : Matrix.unitaryGroup A ℂ)
    {n : ℕ} (hn : n < Fintype.card A) :
    (storedRotation (M := M) U (n + 1) : CMatrix (Cache (A := A) (M := M) (n + 1))) * memoryPolar n =
      memoryPolar n * (cacheRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n)) := by
  simp only [storedRotation, cacheRotation, tensorUnitary, memoryPolar, Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    leftPolar_covariance U 1 hn]
  simp

theorem retrieved_invariant {n : ℕ} (hn : n < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) (n + 1))) (hi : StoredInvariant (n + 1) X) :
    CacheInvariant n ((memoryPolar n).conjTranspose * X * memoryPolar n) := by
  intro U
  exact decode_invariant (memoryPolar n) (cacheRotation U n) (storedRotation U (n + 1))
    (memoryPolar_covariance U hn) X (hi U)

theorem retrieved_mass {n : ℕ} (hn : n < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) (n + 1))) (hX : X.PosSemidef) :
    ((memoryPolar n).conjTranspose * X * memoryPolar n).trace.re ≤ X.trace.re := by
  have h := (adjoint_conjugate_TNI (memoryPolar (M := M) n) (memoryPolar_gram hn)).traceNonincreasing X hX
  simpa only [conjugate_apply, Matrix.conjTranspose_conjTranspose] using h

theorem actual_retrieval_basis_bound (U : Matrix.unitaryGroup A ℂ)
    {n : ℕ} (hn : n < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) (n + 1))) (hX : X.PosSemidef)
    (hi : StoredInvariant (n + 1) X) :
    traceNorm (basisMap U (cacheHead n ((memoryPolar n).conjTranspose * X * memoryPolar n)) -
      (ICO.RecordingDepolarizing.withMemory (α := A)
        (μ := TensorPowerProfile (A × A) n × M)).map
        (cacheHead n ((memoryPolar n).conjTranspose * X * memoryPolar n))) ≤
      6 * (n : ℝ) * X.trace.re / (Fintype.card A : ℝ) := by
  apply (invariant_cache_basis_bound U n _
    (by simpa only [Matrix.conjTranspose_conjTranspose] using
      hX.mul_mul_conjTranspose_same (memoryPolar (M := M) n).conjTranspose)
    (retrieved_invariant hn X hi)).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (retrieved_mass hn X hX) (by positivity)) (by positivity)

#print axioms invariant_cache_basis_bound
#print axioms actual_retrieval_basis_bound
end
end ICO.C6CacheQueryBound

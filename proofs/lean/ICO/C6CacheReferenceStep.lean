import ICO.C6CacheReference
import ICO.MHFockEmptyRotation

/-! Reference birth invariance and the literal one-query cache bound. -/
namespace ICO.C6CacheReferenceStep
open QIT Matrix ICO.C6CacheReference ICO.C6CacheQueryBound ICO.C6CacheDecode
  ICO.C6CacheMap ICO.C6MatrixCovariance ICO.MHSectorCovariance ICO.MHSymmetric
  ICO.RecordingCopyIdentity ICO.RecordingDistance ICO.C6BosonicPolar
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1800000
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem image_stored {n : ℕ} (hn : n < Fintype.card A) :
    StoredInvariant (A := A) (M := M) (n+1) (image (memoryPolar (A := A) (M := M) n)) := by
  intro U
  have h := encode_invariant (memoryPolar (A := A) (M := M) n)
    (cacheRotation U n) (storedRotation U (n+1)) (memoryPolar_covariance U hn)
    1 (by simp)
  simpa only [image, Matrix.mul_one] using h

theorem complement_stored {n : ℕ} (hn : n < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) (n+1))) (hi : StoredInvariant (n+1) X) :
    StoredInvariant (n+1) ((1-image (memoryPolar n))*X*(1-image (memoryPolar n))) := by
  intro U
  have hp := image_stored (M := M) hn U
  have hx := hi U
  let C := 1-image (memoryPolar (A := A) (M := M) n)
  have hc : (storedRotation (M := M) U (n+1) : CMatrix (Cache (A := A) (M := M) (n+1)))*C =
      C*(storedRotation (M := M) U (n+1) : CMatrix (Cache (A := A) (M := M) (n+1))) := by
    simp only [C, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hp]
  have he := encode_invariant C (storedRotation U (n+1)) (storedRotation U (n+1)) hc X hx
  simpa only [C, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, image_adjoint] using he

theorem reference_birth_stored {n : ℕ} (hn : n < Fintype.card A)
    (hs : n+1 < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) (n+1))) (hi : StoredInvariant (n+1) X) :
    StoredInvariant (n+2) (birth (memoryPolar n) (memoryPolar (n+1))
      (uniformChannel (n+1)) X) := by
  rw [birth_apply]
  exact encode_stored hs _ (uniform_makes_input (n+1) _ (complement_stored hn X hi))

theorem stored_zero (X : CMatrix (Cache (A := A) (M := M) 0)) :
    StoredInvariant 0 X := by
  intro U
  have h : (storedRotation (M := M) U 0 : CMatrix (Cache (A := A) (M := M) 0)) = 1 := by
    simp [storedRotation, outputRotation, tensorUnitary, symmetricRotation,
      ICO.MHFockEmptyRotation.occupationRotation_zero, Matrix.kronecker,
      Matrix.one_kronecker_one]
  simp only [h, Matrix.one_mul, Matrix.mul_one]

theorem vacuum_stored (hd : 0 < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) 0)) :
    StoredInvariant 1 ((vacuumStep hd).map X) := by
  simp only [vacuumStep, Channel.comp, LinearMap.comp_apply, isometryChannel, conjugate_apply]
  exact encode_stored hd _ (uniform_makes_input 0 X (stored_zero X))

theorem unhead_difference (n : ℕ)
    (X Y : CMatrix (A × SideMemory (A := A) (M := M) n)) :
    unhead n X - unhead n Y = unhead n (X-Y) := by rfl

theorem retrieval_difference (U : Matrix.unitaryGroup A ℂ) (n : ℕ)
    (X : CMatrix (Cache (A := A) (M := M) (n+1))) :
    retrieval (memoryPolar n) (basisChannel U n) X -
      retrieval (memoryPolar n) (uniformChannel n) X =
      memoryPolar n * unhead n
        (ICO.C6BasisDephase.basisMap U
          (ICO.C6MemoryDecode.cacheHead n ((memoryPolar n).conjTranspose*X*memoryPolar n)) -
          (ICO.RecordingDepolarizing.withMemory (α := A) (μ := SideMemory (M := M) n)).map
          (ICO.C6MemoryDecode.cacheHead n ((memoryPolar n).conjTranspose*X*memoryPolar n))) *
            (memoryPolar n).conjTranspose := by
  rw [retrieval_apply, retrieval_apply, basis_apply, uniform_apply,
    ← Matrix.sub_mul, ← Matrix.mul_sub, unhead_difference]

theorem actual_retrieval_distance (U : Matrix.unitaryGroup A ℂ)
    {n : ℕ} (hn : n < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) (n+1))) (hX : X.PosSemidef)
    (hi : StoredInvariant (n+1) X) :
    traceNorm (retrieval (memoryPolar n) (basisChannel U n) X -
      retrieval (memoryPolar n) (uniformChannel n) X) ≤
      6*(n : ℝ)*X.trace.re/(Fintype.card A : ℝ) := by
  have hr : ((memoryPolar n).conjTranspose*X*memoryPolar n).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hX.mul_mul_conjTranspose_same (memoryPolar (M := M) n).conjTranspose
  have hb := actual_retrieval_basis_bound U hn X hX hi
  rw [retrieval_difference]
  rw [traceNorm_isometry_conjugate _ (memoryPolar_gram hn) _]
  · rw [unhead, traceNorm_submatrix_equiv]
    exact hb
  · have h := ((basisChannel U n).mapsPositive _ hr).isHermitian.sub
      ((uniformChannel n).mapsPositive _ hr).isHermitian
    rwa [basis_apply, uniform_apply, unhead_difference] at h

#print axioms reference_birth_stored
#print axioms vacuum_stored
#print axioms actual_retrieval_distance
end
end ICO.C6CacheReferenceStep

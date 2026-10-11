import ICO.C6CacheQueryBound
import ICO.C6ReindexChannel

/-! Literal channels on each private cache sector. The reference replaces
retrieved-label dephasing by depolarization; birth is unchanged. -/
namespace ICO.C6CacheReference
open QIT Matrix ICO.C6CacheQueryBound ICO.C6CacheDecode ICO.C6MemoryDecode
  ICO.C6CacheMap ICO.C6BasisDephase ICO.C6BasisInvariant ICO.C6MatrixCovariance
  ICO.C6BosonicPolar ICO.MHSectorCovariance ICO.MHSymmetric ICO.MHCreationCovariance
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1600000
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

abbrev SideMemory (n : ℕ) := TensorPowerProfile (A × A) n × M

def headEquiv (n : ℕ) : A × SideMemory (A := A) (M := M) n ≃ Cache (A := A) (M := M) n :=
  (Equiv.prodAssoc A (TensorPowerProfile (A × A) n) M).symm

def unhead (n : ℕ) (Y : CMatrix (A × SideMemory (A := A) (M := M) n)) :
    CMatrix (Cache (A := A) (M := M) n) :=
  Y.submatrix (headEquiv n).symm (headEquiv n).symm

def uniformChannel (n : ℕ) : Channel (Cache (A := A) (M := M) n) (Cache (A := A) (M := M) n) :=
  (ICO.C6ReindexChannel.channel (headEquiv n).symm).comp
    ((ICO.RecordingDepolarizing.withMemory (α := A) (μ := SideMemory (A := A) (M := M) n)).comp
      (ICO.C6ReindexChannel.channel (headEquiv n)))

theorem uniform_apply (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n)) :
    (uniformChannel n).map X = unhead n
      ((ICO.RecordingDepolarizing.withMemory (α := A) (μ := SideMemory (A := A) (M := M) n)).map
        (cacheHead n X)) := by
  change (ICO.C6ReindexChannel.channel (headEquiv n).symm).map
    ((ICO.RecordingDepolarizing.withMemory (α := A) (μ := SideMemory (A := A) (M := M) n)).map
      ((ICO.C6ReindexChannel.channel (headEquiv n)).map X)) = _
  rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply]
  rfl

def basisChannel (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Channel (Cache (A := A) (M := M) n) (Cache (A := A) (M := M) n) :=
  (ICO.C6ReindexChannel.channel (headEquiv n).symm).comp
    ((ICO.AllChannelDilation.oracleChannel (M := SideMemory (A := A) (M := M) n)
      (ICO.SwitchObservable.basisProjection (U : CMatrix A))
      (ICO.SwitchObservable.hidden_basis_kraus_complete _ U.property.1 U.property.2)).comp
      (ICO.C6ReindexChannel.channel (headEquiv n)))

theorem basis_apply (U : Matrix.unitaryGroup A ℂ) (n : ℕ)
    (X : CMatrix (Cache (A := A) (M := M) n)) :
    (basisChannel U n).map X = unhead n (basisMap U (cacheHead n X)) := by
  change (ICO.C6ReindexChannel.channel (headEquiv n).symm).map
    (basisMap U ((ICO.C6ReindexChannel.channel (headEquiv n)).map X)) = _
  rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply]
  rfl

def cacheStep (U : Matrix.unitaryGroup A ℂ) {n : ℕ}
    (hn : n < Fintype.card A) (hs : n + 1 < Fintype.card A) :
    Channel (Cache (A := A) (M := M) (n + 1))
      (Cache (A := A) (M := M) (n + 1) ⊕ Cache (A := A) (M := M) (n + 2)) :=
  cacheChannel (memoryPolar n) (memoryPolar_gram hn)
    (memoryPolar (n + 1)) (memoryPolar_gram hs)
    (basisChannel U n) (uniformChannel (n + 1))

def referenceStep {n : ℕ} (hn : n < Fintype.card A) (hs : n + 1 < Fintype.card A) :
    Channel (Cache (A := A) (M := M) (n + 1))
      (Cache (A := A) (M := M) (n + 1) ⊕ Cache (A := A) (M := M) (n + 2)) :=
  cacheChannel (memoryPolar n) (memoryPolar_gram hn)
    (memoryPolar (n + 1)) (memoryPolar_gram hs)
    (uniformChannel n) (uniformChannel (n + 1))

def vacuumStep (hd : 0 < Fintype.card A) :
    Channel (Cache (A := A) (M := M) 0) (Cache (A := A) (M := M) 1) :=
  (isometryChannel (memoryPolar 0) (memoryPolar_gram hd)).comp (uniformChannel 0)

def recordRotation (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    Matrix.unitaryGroup (SideMemory (A := A) (M := M) n) ℂ :=
  tensorUnitary (symmetricRotation (leftEdgeUnitary U 1) n) 1

theorem input_head_factor (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (cacheRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n)).submatrix
      (headEquiv n) (headEquiv n) =
      Matrix.kronecker (U : CMatrix A) (recordRotation (M := M) U n : CMatrix (SideMemory (A := A) (M := M) n)) := by
  ext x y
  change ((U : CMatrix A) x.1 y.1 *
    occupationRotation (leftEdgeUnitary U 1) n x.2.1 y.2.1) *
      (1 : CMatrix M) x.2.2 y.2.2 =
    (U : CMatrix A) x.1 y.1 *
      (occupationRotation (leftEdgeUnitary U 1) n x.2.1 y.2.1 *
        (1 : CMatrix M) x.2.2 y.2.2)
  ring

theorem stored_head_factor (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (storedRotation (M := M) U n : CMatrix (Cache (A := A) (M := M) n)).submatrix
      (headEquiv n) (headEquiv n) =
      (sideRotation (A := A) (recordRotation (M := M) U n) : CMatrix (A × SideMemory n)) := by
  ext x y
  simp [storedRotation, outputRotation, headEquiv, sideRotation, recordRotation,
    tensorUnitary, ICO.MHWordRotation.tensorUnitary, symmetricRotation,
    Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc]

theorem commutation_reindex {a b : Type u} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : b ≃ a) (R X : CMatrix a)
    (h : R * X = X * R) :
    R.submatrix e e * X.submatrix e e = X.submatrix e e * R.submatrix e e := by
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h]

theorem commutation_of_reindex {a b : Type u} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : b ≃ a) (R X : CMatrix a)
    (h : R.submatrix e e * X.submatrix e e = X.submatrix e e * R.submatrix e e) :
    R * X = X * R := by
  have hh := commutation_reindex e.symm (R.submatrix e e) (X.submatrix e e) h
  simpa only [Matrix.submatrix_submatrix, Function.comp_def, Equiv.apply_symm_apply,
    Matrix.submatrix_id_id] using hh

theorem head_unhead (n : ℕ) (Y : CMatrix (A × SideMemory (A := A) (M := M) n)) :
    cacheHead n (unhead n Y) = Y := by
  simp only [cacheHead, unhead, headEquiv, Matrix.submatrix_submatrix,
    Function.comp_def, Equiv.symm_apply_apply, Matrix.submatrix_id_id]
  rfl

theorem input_head_invariant (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n))
    (hi : CacheInvariant n X) (U : Matrix.unitaryGroup A ℂ) :
    Matrix.kronecker (U : CMatrix A) (recordRotation (M := M) U n : CMatrix (SideMemory (A := A) (M := M) n)) *
      cacheHead n X = cacheHead n X *
      Matrix.kronecker (U : CMatrix A) (recordRotation (M := M) U n : CMatrix (SideMemory (A := A) (M := M) n)) := by
  have hh := commutation_reindex (headEquiv (A := A) (M := M) n) _ X (hi U)
  erw [input_head_factor U n] at hh
  exact hh

theorem stored_head_invariant (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n))
    (hi : StoredInvariant n X) (U : Matrix.unitaryGroup A ℂ) :
    (sideRotation (A := A) (recordRotation (M := M) U n) :
      CMatrix (A × SideMemory (A := A) (M := M) n)) * cacheHead n X =
      cacheHead n X * (sideRotation (A := A) (recordRotation (M := M) U n) :
        CMatrix (A × SideMemory (A := A) (M := M) n)) := by
  have hh := commutation_reindex (headEquiv (A := A) (M := M) n) _ X (hi U)
  erw [stored_head_factor U n] at hh
  exact hh

theorem uniform_preserves_input (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n))
    (hi : CacheInvariant n X) : CacheInvariant n ((uniformChannel n).map X) := by
  intro U
  apply commutation_of_reindex (headEquiv (A := A) (M := M) n)
  erw [input_head_factor U n, uniform_apply]
  simp only [unhead, headEquiv, Matrix.submatrix_submatrix, Function.comp_def,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply, Matrix.submatrix_id_id]
  exact depolarizing_invariant U (recordRotation U n) _ (input_head_invariant n X hi U)

theorem uniform_makes_input (n : ℕ) (X : CMatrix (Cache (A := A) (M := M) n))
    (hi : StoredInvariant n X) : CacheInvariant n ((uniformChannel n).map X) := by
  intro U
  apply commutation_of_reindex (headEquiv (A := A) (M := M) n)
  erw [input_head_factor U n, uniform_apply]
  simp only [unhead, headEquiv, Matrix.submatrix_submatrix, Function.comp_def,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply, Matrix.submatrix_id_id]
  exact depolarizing_makes_head_invariant U (recordRotation U n) _
    (stored_head_invariant n X hi U)

theorem encode_stored {n : ℕ} (hn : n < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) n)) (hi : CacheInvariant n X) :
    StoredInvariant (n + 1) (memoryPolar n * X * (memoryPolar n).conjTranspose) := by
  intro U
  exact encode_invariant (memoryPolar n) (cacheRotation U n) (storedRotation U (n + 1))
    (memoryPolar_covariance U hn) X (hi U)

theorem reference_retrieval_stored {n : ℕ} (hn : n < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) (n + 1))) (hi : StoredInvariant (n + 1) X) :
    StoredInvariant (n + 1) (retrieval (memoryPolar n) (uniformChannel n) X) := by
  rw [retrieval_apply]
  exact encode_stored hn _ (uniform_preserves_input n _ (retrieved_invariant hn X hi))

#print axioms uniform_makes_input
#print axioms reference_retrieval_stored

#print axioms cacheStep
#print axioms referenceStep
#print axioms vacuumStep
end
end ICO.C6CacheReference

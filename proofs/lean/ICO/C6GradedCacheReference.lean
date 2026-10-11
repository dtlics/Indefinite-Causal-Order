import ICO.C6GradedCache
import ICO.C6SectorCovariance
import ICO.MHEmbeddingProjector

/-! Reference cache symmetry on the actual finite private sector register. -/
namespace ICO.C6GradedCacheReference
open QIT Matrix ICO.C6GradedCache ICO.C6SectorChannel ICO.C6SectorCovariance
  ICO.C6CacheReference ICO.C6CacheReferenceStep ICO.C6CacheQueryBound
  ICO.C6CacheDecode ICO.C6CacheMap ICO.C6MatrixCovariance
  ICO.RecordingCopyIdentity ICO.MHEmbeddingProjector
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2400000
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem embed_covariance (U : Matrix.unitaryGroup A ℂ) (Q : ℕ) (r : Fin (Q+1)) :
    (rotation (M := M) U Q : CMatrix (Graded (A := A) Q M))*embed Q r =
      embed Q r*(storedRotation (M := M) U r.val : CMatrix (Cache (A := A) (M := M) r.val)) :=
  inclusion_covariance (fun r : Fin (Q+1) => storedRotation (M := M) U r.val) r

theorem encode_invariant (Q : ℕ) (r : Fin (Q+1))
    (X : CMatrix (Cache (A := A) (M := M) r.val)) (hi : StoredInvariant r.val X) :
    Invariant Q (conjugate (embed Q r) X) := by
  intro U
  rw [conjugate_apply]
  exact ICO.C6MatrixCovariance.encode_invariant _ (storedRotation U r.val) (rotation U Q)
    (embed_covariance U Q r) X (hi U)

theorem decode_invariant (Q : ℕ) (r : Fin (Q+1))
    (X : CMatrix (Graded (A := A) Q M)) (hi : Invariant Q X) :
    StoredInvariant r.val ((embed Q r).conjTranspose*X*embed Q r) := by
  intro U
  exact ICO.C6MatrixCovariance.decode_invariant _ (storedRotation U r.val) (rotation U Q)
    (embed_covariance U Q r) X (hi U)

theorem invariant_add (Q : ℕ) (X Y : CMatrix (Graded (A := A) Q M))
    (hX : Invariant Q X) (hY : Invariant Q Y) : Invariant Q (X+Y) := by
  intro U
  rw [Matrix.mul_add, Matrix.add_mul, hX U, hY U]

theorem invariant_sum {I : Type*} [Fintype I] (Q : ℕ)
    (X : I → CMatrix (Graded (A := A) Q M)) (hX : ∀i,Invariant Q (X i)) :
    Invariant Q (∑i,X i) := by
  intro U
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [hX _ U]

theorem sumEmbed_inl (Q : ℕ) (r s : Fin (Q+1)) :
    sumEmbed (A := A) (M := M) Q r s*basisEmbedding (Sum.inl :
      Cache (A := A) (M := M) r.val → Cache (A := A) (M := M) r.val ⊕ Cache (A := A) (M := M) s.val)=
      embed Q r := by
  rw [sumEmbed, basisEmbedding_mul]
  rfl

theorem sumEmbed_inr (Q : ℕ) (r s : Fin (Q+1)) :
    sumEmbed (A := A) (M := M) Q r s*basisEmbedding (Sum.inr :
      Cache (A := A) (M := M) s.val → Cache (A := A) (M := M) r.val ⊕ Cache (A := A) (M := M) s.val)=
      embed Q s := by
  rw [sumEmbed, basisEmbedding_mul]
  rfl

theorem conjugate_comp_apply {a b c : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (F : Matrix c b ℂ) (G : Matrix b a ℂ) (X : CMatrix a) :
    conjugate F (conjugate G X)=conjugate (F*G) X := by
  simp only [conjugate_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem sum_cache_apply {n : ℕ} (Q : ℕ) (hr : n+1<Q+1) (hs : n+2<Q+1)
    (Δ : Channel (Cache (A := A) (M := M) n) (Cache (A := A) (M := M) n))
    (Ω : Channel (Cache (A := A) (M := M) (n+1)) (Cache (A := A) (M := M) (n+1)))
    (X : CMatrix (Cache (A := A) (M := M) (n+1))) :
    conjugate (sumEmbed Q ⟨n+1,hr⟩ ⟨n+2,hs⟩)
      (cacheMap (memoryPolar n) (memoryPolar (n+1)) Δ Ω X)=
      conjugate (embed Q ⟨n+1,hr⟩) (retrieval (memoryPolar n) Δ X)+
      conjugate (embed Q ⟨n+2,hs⟩) (birth (memoryPolar n) (memoryPolar (n+1)) Ω X) := by
  simp only [cacheMap, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  rw [conjugate_comp_apply, conjugate_comp_apply, sumEmbed_inl, sumEmbed_inr]

theorem local_reference_invariant (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (r : Fin (Q+1)) (X : CMatrix (Cache (A := A) (M := M) r.val))
    (hi : StoredInvariant r.val X) :
    Invariant Q ((localQuery Q hpos hQ none r).map X) := by
  rcases r with ⟨r,hr⟩
  cases r with
  | zero =>
    simp only [localQuery, Channel.comp, LinearMap.comp_apply, isometryChannel]
    exact encode_invariant Q ⟨1,by omega⟩ _ (vacuum_stored (by omega) X)
  | succ n =>
    by_cases hn : n+1<Q
    · simp only [localQuery, dif_pos hn, Channel.comp, LinearMap.comp_apply,
        isometryChannel, referenceStep, cacheChannel]
      rw [sum_cache_apply]
      exact invariant_add Q _ _
        (encode_invariant Q ⟨n+1,hr⟩ _ (reference_retrieval_stored (by omega) X hi))
        (encode_invariant Q ⟨n+2,by omega⟩ _ (reference_birth_stored (by omega) (by omega) X hi))
    · simp only [localQuery, dif_neg hn, isometryChannel]
      exact encode_invariant Q ⟨n+1,hr⟩ X hi

theorem reference_invariant (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (X : CMatrix (Graded (A := A) Q M)) (hi : Invariant Q X) :
    Invariant Q ((query Q hpos hQ none).map X) := by
  rw [query, sector_apply]
  apply invariant_sum
  intro r
  exact local_reference_invariant Q hpos hQ r _ (decode_invariant Q r X hi)

#print axioms reference_invariant
end
end ICO.C6GradedCacheReference

import ICO.C6CacheReferenceStep

/-! The actual CPTP sector cache has the retrieved-label information bound. -/
namespace ICO.C6CacheSectorBound
open QIT Matrix ICO.C6CacheReference ICO.C6CacheReferenceStep ICO.C6CacheQueryBound
  ICO.C6CacheDecode ICO.C6CacheMap ICO.C6MatrixCovariance
  ICO.RecordingCopyIdentity ICO.RecordingDistance
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1800000
universe u
variable {a b c : Type u} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

theorem cache_difference (F : Matrix b a ℂ) (G : Matrix c b ℂ)
    (Δ₀ Δ₁ : Channel a a) (Ω : Channel b b) (X : CMatrix b) :
    cacheMap F G Δ₀ Ω X - cacheMap F G Δ₁ Ω X =
      conjugate (basisEmbedding (Sum.inl : b → b⊕c))
        (retrieval F Δ₀ X-retrieval F Δ₁ X) := by
  simp only [cacheMap, LinearMap.add_apply, LinearMap.comp_apply, map_sub]
  abel

theorem cache_distance_eq (F : Matrix b a ℂ) (G : Matrix c b ℂ)
    (Δ₀ Δ₁ : Channel a a) (Ω : Channel b b) (X : CMatrix b) (hX : X.PosSemidef) :
    traceNorm (cacheMap F G Δ₀ Ω X-cacheMap F G Δ₁ Ω X) =
      traceNorm (retrieval F Δ₀ X-retrieval F Δ₁ X) := by
  rw [cache_difference, conjugate_apply]
  exact traceNorm_isometry_conjugate _ (basisEmbedding_gram _ Sum.inl_injective) _
    ((MatrixMap.isCompletelyPositive_mapsPositive _ (retrieval_cp F Δ₀) X hX).isHermitian.sub
      (MatrixMap.isCompletelyPositive_mapsPositive _ (retrieval_cp F Δ₁) X hX).isHermitian)

variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem actual_cache_step_distance (U : Matrix.unitaryGroup A ℂ) {n : ℕ}
    (hn : n < Fintype.card A) (hs : n+1 < Fintype.card A)
    (X : CMatrix (Cache (A := A) (M := M) (n+1))) (hX : X.PosSemidef)
    (hi : StoredInvariant (n+1) X) :
    traceNorm ((cacheStep U hn hs).map X-(referenceStep hn hs).map X) ≤
      6*(n : ℝ)*X.trace.re/(Fintype.card A : ℝ) := by
  simp only [cacheStep, referenceStep, cacheChannel]
  rw [cache_distance_eq _ _ _ _ _ X hX]
  exact actual_retrieval_distance U hn X hX hi

#print axioms actual_cache_step_distance
end
end ICO.C6CacheSectorBound

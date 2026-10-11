import ICO.C6GradedCacheReference

/-! A uniform information bound for literal private-sector cache queries. -/
namespace ICO.C6GradedCacheBound
open QIT Matrix ICO.C6GradedCache ICO.C6GradedCacheReference ICO.C6SectorChannel
  ICO.C6SectorCovariance ICO.C6CacheReference ICO.C6CacheReferenceStep
  ICO.C6CacheSectorBound ICO.C6CacheQueryBound ICO.C6CacheDecode ICO.C6CacheMap
  ICO.C6MatrixCovariance
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
universe u
variable {A M : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def rate (Q : ℕ) (d : ℝ) := 6*((Q-1:ℕ):ℝ)/d

theorem local_query_distance (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (U : Matrix.unitaryGroup A ℂ) (r : Fin (Q+1))
    (X : CMatrix (Cache (A := A) (M := M) r.val)) (hX : X.PosSemidef)
    (hi : StoredInvariant r.val X) :
    traceNorm ((localQuery Q hpos hQ (some U) r).map X-
      (localQuery Q hpos hQ none r).map X) ≤ rate Q (Fintype.card A)*X.trace.re := by
  have ht : 0≤X.trace.re := (Complex.nonneg_iff.mp hX.trace_nonneg).1
  have he : 0≤rate Q (Fintype.card A)*X.trace.re := by unfold rate; positivity
  rcases r with ⟨r,hr⟩
  cases r with
  | zero =>
    have hz : localQuery (M := M) Q hpos hQ (some U) ⟨0,hr⟩=
        localQuery (M := M) Q hpos hQ none ⟨0,hr⟩ := by rfl
    rw [hz, sub_self, traceNorm_zero]
    exact he
  | succ n =>
    by_cases hn : n+1<Q
    · have hnd : n<Fintype.card A := by omega
      have hs : n+1<Fintype.card A := by omega
      have hrs : (⟨n+1,hr⟩ : Fin (Q+1))≠⟨n+2,by omega⟩ := by
        intro h; have := congrArg Fin.val h
        change n+1=n+2 at this
        omega
      have ha := (cacheStep U hnd hs).mapsPositive X hX
      have hb := (referenceStep hnd hs).mapsPositive X hX
      simp only [localQuery, dif_pos hn, Channel.comp, LinearMap.comp_apply, isometryChannel]
      rw [← map_sub, conjugate_apply,
        traceNorm_isometry_conjugate _ (sumEmbed_gram Q _ _ hrs) _ (ha.isHermitian.sub hb.isHermitian)]
      apply (actual_cache_step_distance U hnd hs X hX hi).trans
      have hnq : (n:ℝ)≤((Q-1:ℕ):ℝ) := by exact_mod_cast (show n≤Q-1 by omega)
      unfold rate
      have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnq (by norm_num : (0:ℝ)≤6)) ht
      have hdiv := div_le_div_of_nonneg_right hmul (by positivity : (0:ℝ)≤Fintype.card A)
      convert hdiv using 1 <;> ring
    · dsimp only [localQuery, Nat.casesAuxOn]
      rw [dif_neg hn, dif_neg hn]
      simpa only [sub_self, traceNorm_zero] using he

theorem query_distance (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (U : Matrix.unitaryGroup A ℂ) (X : CMatrix (Graded (A := A) Q M))
    (hX : X.PosSemidef) (hi : Invariant Q X) :
    traceNorm ((query Q hpos hQ (some U)).map X-(query Q hpos hQ none).map X) ≤
      rate Q (Fintype.card A)*X.trace.re := by
  rw [query, query, sector_apply, sector_apply, ← Finset.sum_sub_distrib]
  apply (traceNorm_sum_le_sum_traceNorm Finset.univ _).trans
  have hb (r : Fin (Q+1)) := local_query_distance Q hpos hQ U r
    ((embed Q r).conjTranspose*X*embed Q r)
    (by simpa only [Matrix.conjTranspose_conjTranspose] using
      hX.mul_mul_conjTranspose_same (embed (A := A) (M := M) Q r).conjTranspose)
    (decode_invariant Q r X hi)
  have hsum := Finset.sum_le_sum (fun r (_ : r∈(Finset.univ : Finset (Fin (Q+1)))) => hb r)
  have hm := congrArg Complex.re (block_mass (H := fun r : Fin (Q+1) =>
    Cache (A := A) (M := M) r.val) X)
  simp only [Complex.re_sum] at hm
  change (∑r : Fin (Q+1),((embed Q r).conjTranspose*X*embed Q r).trace.re)=X.trace.re at hm
  rw [← Finset.mul_sum, hm] at hsum
  exact hsum

#print axioms local_query_distance
#print axioms query_distance
end
end ICO.C6GradedCacheBound

import ICO.C6ChoiceCache
import ICO.C6GradedCacheBound

/-! Reference invariance and the local information bound for the actual
pinched Bool-choice cache, with arbitrary correlated quantum side memory. -/
namespace ICO.C6ChoiceCacheBound
open QIT Matrix ICO.C6ChoiceCache ICO.C6GradedCache ICO.C6GradedCacheBound
  ICO.C6GradedCacheReference ICO.C6SectorCovariance ICO.C6MatrixCovariance
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
universe u
variable {A M:Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem choice_block_mass (Q:ℕ) (X:CMatrix (Graded (A:=A) Q (Bool×M))) :
    (∑b:Bool,(choiceBlock Q b X).trace)=X.trace := by
  have he:=block_mass (H:=fun _:Bool=>Graded (A:=A) Q M)
    (X.submatrix (choiceEquiv Q) (choiceEquiv Q))
  simp only [choice_input_block] at he
  rw [he]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.submatrix_apply]
  exact (choiceEquiv Q).sum_comp (fun x=>X x x)

theorem choice_block_invariant (Q:ℕ) (b:Bool)
    (X:CMatrix (Graded (A:=A) Q (Bool×M))) (hi:Invariant Q X) :
    Invariant Q (choiceBlock Q b X) := by
  rw [choiceBlock_eq]
  intro U
  exact ICO.C6MatrixCovariance.decode_invariant _ (rotation (M:=M) U Q)
    (rotation (M:=Bool×M) U Q) (choiceEmbed_covariance U Q b) X (hi U)

theorem choice_embed_invariant (Q:ℕ) (b:Bool)
    (X:CMatrix (Graded (A:=A) Q M)) (hi:Invariant Q X) :
    Invariant Q (choiceEmbed Q b*X*(choiceEmbed Q b).conjTranspose) := by
  intro U
  exact ICO.C6MatrixCovariance.encode_invariant _ (rotation (M:=M) U Q)
    (rotation (M:=Bool×M) U Q) (choiceEmbed_covariance U Q b) X (hi U)

theorem reference_invariant (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (X:CMatrix (Graded (A:=A) Q (Bool×M))) (hi:Invariant Q X) :
    Invariant Q ((ICO.C6ChoiceCache.query Q hpos hQ (fun _=>none)).map X) := by
  rw [query_apply]
  apply invariant_sum
  intro b
  apply choice_embed_invariant
  exact ICO.C6GradedCacheReference.reference_invariant Q hpos hQ _
    (choice_block_invariant Q b X hi)

theorem query_distance (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ)
    (X:CMatrix (Graded (A:=A) Q (Bool×M))) (hX:X.PosSemidef) (hi:Invariant Q X) :
    traceNorm ((ICO.C6ChoiceCache.query Q hpos hQ (fun b=>some (U b))).map X-
      (ICO.C6ChoiceCache.query Q hpos hQ (fun _=>none)).map X)≤
        rate Q (Fintype.card A)*X.trace.re := by
  rw [query_apply,query_apply,←Finset.sum_sub_distrib]
  apply (traceNorm_sum_le_sum_traceNorm Finset.univ _).trans
  have hb (b:Bool) : traceNorm (choiceEmbed Q b*
      (ICO.C6GradedCache.query Q hpos hQ (some (U b))).map (choiceBlock Q b X)*(choiceEmbed Q b).conjTranspose-
      choiceEmbed Q b*(ICO.C6GradedCache.query Q hpos hQ none).map (choiceBlock Q b X)*(choiceEmbed Q b).conjTranspose)≤
      rate Q (Fintype.card A)*(choiceBlock Q b X).trace.re := by
    have hp:=choiceBlock_positive Q b X hX
    have h0:=(ICO.C6GradedCache.query Q hpos hQ (some (U b))).mapsPositive _ hp
    have h1:=(ICO.C6GradedCache.query Q hpos hQ none).mapsPositive _ hp
    rw [←Matrix.sub_mul,←Matrix.mul_sub,
      traceNorm_isometry_conjugate _ (choiceEmbed_gram Q b) _ (h0.isHermitian.sub h1.isHermitian)]
    exact ICO.C6GradedCacheBound.query_distance Q hpos hQ (U b) _ hp
      (choice_block_invariant Q b X hi)
  have hs:=Finset.sum_le_sum (fun b (_:b∈(Finset.univ:Finset Bool))=>hb b)
  have hm:=congrArg Complex.re (choice_block_mass Q X)
  simp only [Complex.re_sum] at hm
  rw [←Finset.mul_sum,hm] at hs
  exact hs

#print axioms reference_invariant
#print axioms query_distance
end
end ICO.C6ChoiceCacheBound

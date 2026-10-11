import ICO.C6CacheTrajectory

/-! The literal physical ordering: a cache query followed by a known operation.
The same reference comparison holds with changing learner memory. -/
namespace ICO.C6CacheTrajectoryAfter
open QIT Matrix ICO.C6CacheDecode ICO.C6GradedCache ICO.C6GradedCacheBound
  ICO.C6GradedCacheReference ICO.C6CacheMap ICO.C6MatrixCovariance
  ICO.C6CacheTrajectory ICO.C6ChannelTrajectory ICO.RecordingDistance
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
universe u
variable {A M N : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

def choiceStep (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (D:Bool→Option (Matrix.unitaryGroup A ℂ))
    (K:Matrix (A×(Bool×N)) (A×(Bool×M)) ℂ) (hK:K.conjTranspose*K=1) :
    Channel (Graded (A:=A) Q (Bool×M)) (Graded (A:=A) Q (Bool×N)) :=
  (isometryChannel (known Q K) (known_gram Q K hK)).comp (ICO.C6ChoiceCache.query Q hpos hQ D)

theorem reference_step_invariant (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (K:Matrix (A×(Bool×N)) (A×(Bool×M)) ℂ) (hK:K.conjTranspose*K=1)
    (X:CMatrix (Graded (A:=A) Q (Bool×M))) (hi:Invariant Q X) :
    Invariant Q ((choiceStep Q hpos hQ (fun _=>none) K hK).map X) := by
  simpa only [choiceStep,Channel.comp,isometryChannel,LinearMap.comp_apply,conjugate_apply] using
    known_preserves Q K _ (ICO.C6ChoiceCacheBound.reference_invariant Q hpos hQ X hi)

theorem choice_step_distance (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:Bool→Matrix.unitaryGroup A ℂ)
    (K:Matrix (A×(Bool×N)) (A×(Bool×M)) ℂ) (hK:K.conjTranspose*K=1)
    (X:CMatrix (Graded (A:=A) Q (Bool×M))) (hX:X.PosSemidef) (hi:Invariant Q X) :
    traceNorm ((choiceStep Q hpos hQ (fun b=>some (U b)) K hK).map X-
      (choiceStep Q hpos hQ (fun _=>none) K hK).map X)≤
      rate Q (Fintype.card A)*X.trace.re := by
  let Φ:=isometryChannel (known Q K) (known_gram Q K hK)
  let S:=ICO.C6ChoiceCache.query (M:=M) Q hpos hQ (fun b=>some (U b))
  let T:=ICO.C6ChoiceCache.query (M:=M) Q hpos hQ (fun _=>none)
  have hc:=traceNorm_contract_hermitian Φ.map
    (MatrixMap.traceNonincreasingCP_of_tracePreserving Φ.completelyPositive Φ.tracePreserving)
    (S.map X-T.map X) ((S.mapsPositive _ hX).isHermitian.sub (T.mapsPositive _ hX).isHermitian)
  change traceNorm (Φ.map (S.map X)-Φ.map (T.map X))≤_
  rw [←map_sub]
  exact hc.trans (ICO.C6ChoiceCacheBound.query_distance Q hpos hQ U X hX hi)

variable {μ:ℕ→Type u} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def stages (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (D:ℕ→Bool→Option (Matrix.unitaryGroup A ℂ))
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1) (i:ℕ) :
    Channel (Graded (A:=A) Q (Bool×μ i)) (Graded (A:=A) Q (Bool×μ (i+1))) :=
  choiceStep Q hpos hQ (D i) (K i) (hK i)

theorem reference_run_invariant (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (n:ℕ) :
    Invariant Q (run (stages Q hpos hQ (fun _ _=>none) K hK) (initial Q X) n) := by
  apply run_property _ (fun i Y=>Invariant Q Y)
  · intro i Y hi
    exact reference_step_invariant Q hpos hQ (K i) (hK i) Y hi
  · exact initial_invariant Q X

theorem actual_cache_reference_distance (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (U:ℕ→Bool→Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (hX:X.PosSemidef) (n:ℕ) :
    traceNorm (run (stages Q hpos hQ (fun i b=>some (U i b)) K hK) (initial Q X) n-
      run (stages Q hpos hQ (fun _ _=>none) K hK) (initial Q X) n)≤
      (n:ℝ)*rate Q (Fintype.card A)*X.trace.re := by
  have hp:(initial Q X).PosSemidef:=
    MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) X hX
  have hb:=run_distance
    (stages Q hpos hQ (fun i b=>some (U i b)) K hK)
    (stages Q hpos hQ (fun _ _=>none) K hK) (initial Q X) hp
    (rate Q (Fintype.card A)*X.trace.re) (by
      intro i
      have hl:=choice_step_distance Q hpos hQ (U i) (K i) (hK i) _
        (run_pos _ _ hp i) (reference_run_invariant Q hpos hQ K hK X i)
      rw [run_trace,initial_trace] at hl
      exact hl) n
  simpa only [mul_assoc] using hb

#print axioms actual_cache_reference_distance
end
end ICO.C6CacheTrajectoryAfter

import ICO.C6ChoiceCacheBound
import ICO.C6ChannelTrajectory

/-! The actual mixed-state cache/reference hybrid with arbitrary isometric
operations, changing learner memory, and pinched classical box choices. -/
namespace ICO.C6CacheTrajectory
open QIT Matrix ICO.C6CacheDecode ICO.C6GradedCache ICO.C6GradedCacheBound
  ICO.C6GradedCacheReference ICO.C6CacheReferenceStep ICO.C6CacheMap
  ICO.C6MatrixCovariance
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
universe u
variable {A M N : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

def choiceStep (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (D : Bool → Option (Matrix.unitaryGroup A ℂ))
    (K : Matrix (A×(Bool×N)) (A×(Bool×M)) ℂ) (hK : K.conjTranspose*K=1) :
    Channel (Graded (A := A) Q (Bool×M)) (Graded (A := A) Q (Bool×N)) :=
  (ICO.C6ChoiceCache.query Q hpos hQ D).comp (isometryChannel (known Q K) (known_gram Q K hK))

theorem reference_step_invariant (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (K : Matrix (A×(Bool×N)) (A×(Bool×M)) ℂ) (hK : K.conjTranspose*K=1)
    (X : CMatrix (Graded (A := A) Q (Bool×M))) (hi : Invariant Q X) :
    Invariant Q ((choiceStep Q hpos hQ (fun _ => none) K hK).map X) := by
  simp only [choiceStep, Channel.comp, LinearMap.comp_apply, isometryChannel, conjugate_apply]
  exact ICO.C6ChoiceCacheBound.reference_invariant Q hpos hQ _ (known_preserves Q K X hi)

theorem choice_step_distance (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (U : Bool → Matrix.unitaryGroup A ℂ)
    (K : Matrix (A×(Bool×N)) (A×(Bool×M)) ℂ) (hK : K.conjTranspose*K=1)
    (X : CMatrix (Graded (A := A) Q (Bool×M))) (hX : X.PosSemidef) (hi : Invariant Q X) :
    traceNorm ((choiceStep Q hpos hQ (fun b => some (U b)) K hK).map X-
      (choiceStep Q hpos hQ (fun _ => none) K hK).map X) ≤
      rate Q (Fintype.card A)*X.trace.re := by
  have hb := ICO.C6ChoiceCacheBound.query_distance Q hpos hQ U
    (known Q K*X*(known Q K).conjTranspose)
    (hX.mul_mul_conjTranspose_same (known Q K)) (known_preserves Q K X hi)
  have ht : (known Q K*X*(known Q K).conjTranspose).trace=X.trace := by
    simpa only [conjugate_apply] using conjugate_trace_of_isometry (known Q K) (known_gram Q K hK) X
  rw [ht] at hb
  simpa only [choiceStep, Channel.comp, LinearMap.comp_apply, isometryChannel, conjugate_apply] using hb

def initial (Q : ℕ) (X : CMatrix (Cache (A := A) (M := Bool×M) 0)) :
    CMatrix (Graded (A := A) Q (Bool×M)) :=
  conjugate (embed Q ⟨0,Nat.zero_lt_succ Q⟩) X

theorem initial_invariant (Q : ℕ) (X : CMatrix (Cache (A := A) (M := Bool×M) 0)) :
    Invariant Q (initial Q X) :=
  ICO.C6GradedCacheReference.encode_invariant (A := A) (M := Bool×M)
    Q ⟨0,Nat.zero_lt_succ Q⟩ X (stored_zero X)

theorem initial_trace (Q : ℕ) (X : CMatrix (Cache (A := A) (M := Bool×M) 0)) :
    (initial Q X).trace=X.trace :=
  conjugate_trace_of_isometry (embed (A := A) (M := Bool×M) Q ⟨0,Nat.zero_lt_succ Q⟩)
    (embed_gram (A := A) (M := Bool×M) Q ⟨0,Nat.zero_lt_succ Q⟩) X

variable {μ : ℕ → Type u} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def stages (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (D : ℕ → Bool → Option (Matrix.unitaryGroup A ℂ))
    (K : ∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK : ∀i,(K i).conjTranspose*K i=1) (i : ℕ) :
    Channel (Graded (A := A) Q (Bool×μ i)) (Graded (A := A) Q (Bool×μ (i+1))) :=
  choiceStep Q hpos hQ (D i) (K i) (hK i)

theorem reference_run_invariant (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (K : ∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK : ∀i,(K i).conjTranspose*K i=1)
    (X : CMatrix (Cache (A := A) (M := Bool×μ 0) 0)) (n : ℕ) :
    Invariant Q (ICO.C6ChannelTrajectory.run (stages Q hpos hQ (fun _ _ => none) K hK)
      (initial Q X) n) := by
  apply ICO.C6ChannelTrajectory.run_property _ (fun i Y => Invariant Q Y)
  · intro i Y hi
    exact reference_step_invariant Q hpos hQ (K i) (hK i) Y hi
  · exact initial_invariant Q X

theorem actual_cache_reference_distance (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (U : ℕ → Bool → Matrix.unitaryGroup A ℂ)
    (K : ∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK : ∀i,(K i).conjTranspose*K i=1)
    (X : CMatrix (Cache (A := A) (M := Bool×μ 0) 0)) (hX : X.PosSemidef) (n : ℕ) :
    traceNorm (ICO.C6ChannelTrajectory.run (stages Q hpos hQ (fun i b => some (U i b)) K hK)
      (initial Q X) n-
      ICO.C6ChannelTrajectory.run (stages Q hpos hQ (fun _ _ => none) K hK)
        (initial Q X) n) ≤ (n:ℝ)*rate Q (Fintype.card A)*X.trace.re := by
  have hp : (initial Q X).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) X hX
  have hb := ICO.C6ChannelTrajectory.run_distance
    (stages Q hpos hQ (fun i b => some (U i b)) K hK)
    (stages Q hpos hQ (fun _ _ => none) K hK) (initial Q X) hp
    (rate Q (Fintype.card A)*X.trace.re)
    (by
      intro i
      have hl := choice_step_distance Q hpos hQ (U i) (K i) (hK i) _
        (ICO.C6ChannelTrajectory.run_pos _ _ hp i) (reference_run_invariant Q hpos hQ K hK X i)
      rw [ICO.C6ChannelTrajectory.run_trace,initial_trace] at hl
      exact hl) n
  simpa only [mul_assoc] using hb

#print axioms actual_cache_reference_distance
end
end ICO.C6CacheTrajectory

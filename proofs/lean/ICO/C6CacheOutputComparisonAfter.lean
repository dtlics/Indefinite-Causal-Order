import ICO.C6CacheTrajectoryAfter
import ICO.C6UniformBounds

/-! The two actual tagged-cache priors share one basis-independent reference,
including changing learner memory and arbitrary final private erasure. -/
namespace ICO.C6CacheOutputComparisonAfter
open QIT Matrix ICO.C6CacheDecode ICO.C6GradedCache ICO.C6GradedCacheBound
  ICO.C6CacheTrajectoryAfter ICO.C6ChannelTrajectory ICO.C6CacheMap
  ICO.RecordingDistance ICO.C6UniformBounds
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2000000
universe u
variable {A O : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype O] [DecidableEq O]
  {μ : ℕ → Type u} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def density (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (D : ℕ → Bool → Option (Matrix.unitaryGroup A ℂ))
    (K : ∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK : ∀i,(K i).conjTranspose*K i=1)
    (X : CMatrix (Cache (A := A) (M := Bool×μ 0) 0)) (n : ℕ)
    (Φ : MatrixMap (Graded (A := A) Q (Bool×μ n)) O) : CMatrix O :=
  Φ (run (stages Q hpos hQ D K hK) (ICO.C6CacheTrajectory.initial Q X) n)

theorem density_reference_distance (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (U : ℕ → Bool → Matrix.unitaryGroup A ℂ)
    (K : ∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK : ∀i,(K i).conjTranspose*K i=1)
    (X : CMatrix (Cache (A := A) (M := Bool×μ 0) 0)) (hX : X.PosSemidef) (n : ℕ)
    (Φ : MatrixMap (Graded (A := A) Q (Bool×μ n)) O) (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    normalizedTraceDistance (density Q hpos hQ (fun i b => some (U i b)) K hK X n Φ)
      (density Q hpos hQ (fun _ _ => none) K hK X n Φ) ≤
      (n:ℝ)*rate Q (Fintype.card A)*X.trace.re/2 := by
  have hp : (ICO.C6CacheTrajectory.initial Q X).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) X hX
  apply (distance_contract Φ hΦ _ _ (run_pos _ _ hp n) (run_pos _ _ hp n)).trans
  have hb := actual_cache_reference_distance Q hpos hQ U K hK X hX n
  unfold normalizedTraceDistance traceNormDistance
  linarith

theorem pair_output_distance (Q : ℕ) (hpos : 0<Q) (hQ : Q<Fintype.card A)
    (U V : ℕ → Bool → Matrix.unitaryGroup A ℂ)
    (K : ∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK : ∀i,(K i).conjTranspose*K i=1)
    (X : CMatrix (Cache (A := A) (M := Bool×μ 0) 0)) (hX : X.PosSemidef) (n : ℕ)
    (Φ : MatrixMap (Graded (A := A) Q (Bool×μ n)) O) (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    normalizedTraceDistance (density Q hpos hQ (fun i b => some (U i b)) K hK X n Φ)
      (density Q hpos hQ (fun i b => some (V i b)) K hK X n Φ) ≤
      (n:ℝ)*rate Q (Fintype.card A)*X.trace.re := by
  have hu := density_reference_distance Q hpos hQ U K hK X hX n Φ hΦ
  have hv := density_reference_distance Q hpos hQ V K hK X hX n Φ hΦ
  have ht := normalizedTraceDistance_triangle
    (density Q hpos hQ (fun i b => some (U i b)) K hK X n Φ)
    (density Q hpos hQ (fun _ _ => none) K hK X n Φ)
    (density Q hpos hQ (fun i b => some (V i b)) K hK X n Φ)
  rw [normalizedTraceDistance_comm _ (density Q hpos hQ (fun _ _ => none) K hK X n Φ)] at hv
  linarith

theorem unit_mass_pair_distance (q : ℕ) (hpos : 0<q) (hq : q<Fintype.card A)
    (U V : ℕ → Bool → Matrix.unitaryGroup A ℂ)
    (K : ∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK : ∀i,(K i).conjTranspose*K i=1)
    (X : CMatrix (Cache (A := A) (M := Bool×μ 0) 0)) (hX : X.PosSemidef) (ht : X.trace=1)
    (Φ : MatrixMap (Graded (A := A) q (Bool×μ q)) O) (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    normalizedTraceDistance (density q hpos hq (fun i b => some (U i b)) K hK X q Φ)
      (density q hpos hq (fun i b => some (V i b)) K hK X q Φ) ≤
      uniformCacheError q (Fintype.card A) := by
  have hb := pair_output_distance q hpos hq U V K hK X hX q Φ hΦ
  rw [ht,Complex.one_re,mul_one] at hb
  convert hb using 1 <;> unfold rate uniformCacheError <;> ring

#print axioms unit_mass_pair_distance
end
end ICO.C6CacheOutputComparisonAfter


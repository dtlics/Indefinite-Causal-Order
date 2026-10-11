import ICO.MHProtocolHaarRecording
import ICO.MHHaarRecordingTrivial
import ICO.BudgetHaarBound
import ICO.TestingBounds

/-! Full-range physical Haar indistinguishability for arbitrary finite
adaptive ordinary circuits under their original total query budget. -/
namespace ICO.OrdinaryHaarIndistinguishability
open Matrix QIT MeasureTheory ICO.SequentialIsometry ICO.ProtocolHaarOutput
  ICO.RecordingPurifiedProtocol ICO.ProtocolRecordingTrajectory ICO.RecordingOracleAlgebra
  ICO.MHProtocolHaarRecording ICO.MHHaarRecordingTrivial ICO.BudgetHaarBound
  ICO.AdaptiveHaarBound ICO.AdaptiveSequentialProtocol
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
variable {A M B O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype B] [DecidableEq B]
  [Fintype O] [DecidableEq O]

theorem protocol_haar_recording_full {q : ℕ} (tail : Protocol A (A×M) O q)
    (v : A×M→ℂ) (hv : ‖WithLp.toLp 2 v‖=1) (n : ℕ)
    (R : ℝ) (hR : 1≤R) (hd : (Fintype.card A:ℝ)=R^8) :
    normalizedTraceDistance (haarDensity tail v n)
      (visible n (run tail forwardRecording v n))≤9*(2*(n:ℝ))*(2*(n:ℝ)+1)/R := by
  by_cases hs : 4*n≤Fintype.card A
  · exact protocol_haar_recording tail v hv n hs R hR hd
  · have hmass : (rankOneMatrix v).trace.re=1 := by
      rw [rankOne_trace_re_norm_sq,hv]
      norm_num
    have hh := haar_recording_distance_le_one tail v hv.le hmass n
    have hlarge : Fintype.card A<2*(2*n) := by omega
    have ht : 1≤2*n := by have hp:=Fintype.card_pos (α:=A); omega
    have he := error_ge_one_of_large (2*n) (Fintype.card A) R hR hd hlarge ht
    exact hh.trans (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using he)

theorem circuit_haar_bound {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O (q+1) B)
    (v : B→ℂ) (hv : ‖WithLp.toLp 2 v‖≤1) (hmass : (rankOneMatrix v).trace.re=1)
    (hqd : 2*(q+1)<Fintype.card A) (r : ℝ) (hr : 1≤r)
    (hd : (Fintype.card A:ℝ)=r^16) :
    normalizedTraceDistance
      (∫U,(ludersCircuit tree U).map (rankOneMatrix v) ∂unitaryHaarMeasure (a:=A))
      ((depolarizingCircuit tree).map (rankOneMatrix v))≤
        ICO.TestingBounds.distanceBound (q+1:ℕ) (Fintype.card A) r := by
  let p := budget a₀ m₀ o₀ tree
  have hp : (rankOneMatrix (p.heading.pre*ᵥv)).trace.re=1 :=
    (congrArg Complex.re (prepared_trace p v)).trans hmass
  have hn : ‖WithLp.toLp 2 (p.heading.pre*ᵥv)‖=1 := by
    rw [rankOne_trace_re_norm_sq] at hp
    nlinarith [norm_nonneg (WithLp.toLp 2 (p.heading.pre*ᵥv))]
  have hr2 : 1≤r^2 := by nlinarith
  have hd2 : (Fintype.card A:ℝ)=(r^2)^8 := by
    rw [hd,←pow_mul]
  have hH := protocol_haar_recording_full p.heading.tail (p.heading.pre*ᵥv) hn
    (q+1) (r^2) hr2 hd2
  have hh := ICO.BudgetHaarBound.circuit_haar_bound a₀ m₀ o₀ tree v hv hmass hqd
    (9*(2*((q+1:ℕ):ℝ))*(2*((q+1:ℕ):ℝ)+1)/r^2) hH
  have hsqrt : Real.sqrt (1/((Fintype.card A:ℝ)-(2*(q+1):ℕ))) =
      1/Real.sqrt ((Fintype.card A:ℝ)-2*((q+1:ℕ):ℝ)) := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one]
  rw [hsqrt] at hh
  convert hh using 1 <;>
    simp only [ICO.TestingBounds.distanceBound,Nat.cast_add,Nat.cast_one] <;> ring

#print axioms protocol_haar_recording_full
#print axioms circuit_haar_bound
end
end ICO.OrdinaryHaarIndistinguishability

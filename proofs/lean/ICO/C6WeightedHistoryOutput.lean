import ICO.C6WeightedHistoryBound
import ICO.C6CacheOutputComparisonAfter
import ICO.C6CacheVisibleOutput

namespace ICO.C6WeightedHistoryOutput
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6WeightedHistory ICO.C6WeightedHistoryBound ICO.C6ClassicalHistoryRun
  ICO.RecordingDistance
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A O:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype O] [DecidableEq O]
  {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def density (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (n:ℕ)
    (Φ:MatrixMap (Graded (A:=A) Q (Bool×μ n)) O) : CMatrix O :=
  Φ (erase (H:=fun i=>Graded (A:=A) Q (Bool×μ i)) n (weightedRun Q hpos hQ H K X n))

theorem uniform_erased_positive (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (hX:X.PosSemidef) (n:ℕ) :
    (erase (H:=fun i=>Graded (A:=A) Q (Bool×μ i)) n (uniformRun Q hpos hQ H K X n)).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro η _
  apply Matrix.posSemidef_sum
  intro κ _
  exact run_pos _ (branches_cp Q hpos hQ H K _ (fun _ _ _ _=>by norm_num)) _
    (MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) X hX) n η κ

theorem weighted_erased_positive (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (hX:X.PosSemidef) (n:ℕ) :
    (erase (H:=fun i=>Graded (A:=A) Q (Bool×μ i)) n (weightedRun Q hpos hQ H K X n)).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro η _
  apply Matrix.posSemidef_sum
  intro κ _
  exact run_pos _ (branches_cp Q hpos hQ H K _ (weight_nonnegative H)) _
    (MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) X hX) n η κ

theorem uniform_distance (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (hX:X.PosSemidef) (n:ℕ)
    (Φ:MatrixMap (Graded (A:=A) Q (Bool×μ n)) O) (hΦ:MatrixMap.TraceNonincreasingCP Φ) :
    normalizedTraceDistance (density Q hpos hQ H K X n Φ)
      (ICO.C6CacheOutputComparisonAfter.density Q hpos hQ
        (fun _ b=>some (ICO.C6ActualResidualWeight.outcomeBasis H b)) K hK X n Φ)≤
      (∑i∈Finset.range n,(i:ℝ)/(Fintype.card A:ℝ))*X.trace.re/2 := by
  have hc:=distance_contract Φ hΦ _ _
    (uniform_erased_positive Q hpos hQ H K X hX n)
    (weighted_erased_positive Q hpos hQ H K X hX n)
  have hb:=weighted_uniform_distance Q hpos hQ H K hK X hX n
  have he:=uniform_erase Q hpos hQ H K hK X n
  rw [he] at hc
  rw [normalizedTraceDistance_comm]
  apply hc.trans
  unfold normalizedTraceDistance traceNormDistance
  rw [←he]
  linarith

theorem sum_deficit_cost (n:ℕ) (d:ℝ) :
    (∑i∈Finset.range n,(i:ℝ)/d)=(n:ℝ)*((n-1:ℕ):ℝ)/(2*d) := by
  have hs:∑i∈Finset.range n,(i:ℝ)=(n:ℝ)*((n-1:ℕ):ℝ)/2 := by
    induction n with
    | zero=>norm_num
    | succ n ih=>
      rw [Finset.sum_range_succ,ih]
      cases n with
      | zero=>norm_num
      | succ n=>simp only [Nat.add_one_sub_one,Nat.cast_add,Nat.cast_one];ring
  rw [←Finset.sum_div,hs]
  ring

theorem unit_mass_uniform_distance (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (hX:X.PosSemidef)
    (ht:X.trace=1) (n:ℕ)
    (Φ:MatrixMap (Graded (A:=A) Q (Bool×μ n)) O) (hΦ:MatrixMap.TraceNonincreasingCP Φ) :
    normalizedTraceDistance (density Q hpos hQ H K X n Φ)
      (ICO.C6CacheOutputComparisonAfter.density Q hpos hQ
        (fun _ b=>some (ICO.C6ActualResidualWeight.outcomeBasis H b)) K hK X n Φ)≤
      (n:ℝ)*((n-1:ℕ):ℝ)/(4*(Fintype.card A:ℝ)) := by
  have hb:=uniform_distance Q hpos hQ H K hK X hX n Φ hΦ
  rw [ht,Complex.one_re,mul_one,sum_deficit_cost] at hb
  convert hb using 1 <;> ring

theorem unit_mass_pair_distance (q:ℕ) (hpos:0<q) (hq:q<Fintype.card A)
    (H H':Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (hX:X.PosSemidef) (ht:X.trace=1)
    (Φ:MatrixMap (Graded (A:=A) q (Bool×μ q)) O) (hΦ:MatrixMap.TraceNonincreasingCP Φ) :
    normalizedTraceDistance (density q hpos hq H K X q Φ)
      (density q hpos hq H' K X q Φ)≤
      ICO.C6UniformBounds.uniformCacheError q (Fintype.card A)+
        (q:ℝ)*((q-1:ℕ):ℝ)/(2*(Fintype.card A:ℝ)) := by
  let U:=ICO.C6CacheOutputComparisonAfter.density q hpos hq
    (fun _ b=>some (ICO.C6ActualResidualWeight.outcomeBasis H b)) K hK X q Φ
  let V:=ICO.C6CacheOutputComparisonAfter.density q hpos hq
    (fun _ b=>some (ICO.C6ActualResidualWeight.outcomeBasis H' b)) K hK X q Φ
  have hu:=unit_mass_uniform_distance q hpos hq H K hK X hX ht q Φ hΦ
  have hv:=unit_mass_uniform_distance q hpos hq H' K hK X hX ht q Φ hΦ
  have hc:=ICO.C6CacheOutputComparisonAfter.unit_mass_pair_distance q hpos hq
    (fun _ b=>ICO.C6ActualResidualWeight.outcomeBasis H b)
    (fun _ b=>ICO.C6ActualResidualWeight.outcomeBasis H' b) K hK X hX ht Φ hΦ
  have ht₁:=normalizedTraceDistance_triangle (density q hpos hq H K X q Φ) U V
  have ht₂:=normalizedTraceDistance_triangle (density q hpos hq H K X q Φ) V
    (density q hpos hq H' K X q Φ)
  rw [normalizedTraceDistance_comm V] at ht₂
  change normalizedTraceDistance (density q hpos hq H K X q Φ) U≤_ at hu
  change normalizedTraceDistance (density q hpos hq H' K X q Φ) V≤_ at hv
  change normalizedTraceDistance U V≤_ at hc
  have he:(q:ℝ)*((q-1:ℕ):ℝ)/(2*(Fintype.card A:ℝ))=
      2*((q:ℝ)*((q-1:ℕ):ℝ)/(4*(Fintype.card A:ℝ))) := by ring
  rw [he]
  linarith

#print axioms uniform_distance
#print axioms unit_mass_uniform_distance
#print axioms unit_mass_pair_distance
end
end ICO.C6WeightedHistoryOutput

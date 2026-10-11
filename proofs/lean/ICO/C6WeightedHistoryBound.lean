import ICO.C6WeightedHistory
import ICO.C6RetainedQueryDeficit
import ICO.C6HistoryWeightBound

/-! Replacing the literal history weights by one, while retaining both private
histories. All branch differences are CP on every input, including histories
that acquired positive mass only after a previous replacement. -/
namespace ICO.C6WeightedHistoryBound
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6WeightedHistory ICO.C6RetainedChoice ICO.C6RetainedQueryDeficit
  ICO.C6ClassicalHistoryRun ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem branches_difference (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (i:ℕ) (η:History (A×Bool) i) (κ:History Bool i) (o:A×Bool) (f:Bool) :
    branches Q hpos hQ H K (fun _ _ _ _=>1) i η κ o f-
      branches Q hpos hQ H K (weight H) i η κ o f=
    (conjugate (known Q (K i))).comp
      (branch Q hpos hQ (ICO.C6ActualResidualWeight.outcomeBasis H) (fun _ _=>1) o f-
        branch Q hpos hQ (ICO.C6ActualResidualWeight.outcomeBasis H) (weight H i η) o f) := by
  ext X a b
  simp only [branches,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,Matrix.sub_apply]

theorem branches_deficit_cp (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (i:ℕ) (η:History (A×Bool) i) (κ:History Bool i) (o:A×Bool) (f:Bool) :
    MatrixMap.IsCompletelyPositive
      (branches Q hpos hQ H K (fun _ _ _ _=>1) i η κ o f-
        branches Q hpos hQ H K (weight H) i η κ o f) := by
  rw [branches_difference]
  exact MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
    (branch_deficit_cp Q hpos hQ _ _ (weight_le_one H i η) o f)

theorem branches_deficit_mass (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1)
    (i:ℕ) (η:History (A×Bool) i) (κ:History Bool i)
    (X:CMatrix (Graded (A:=A) Q (Bool×μ i))) (hX:X.PosSemidef) :
    (∑o:A×Bool,∑f:Bool,
      ((branches Q hpos hQ H K (fun _ _ _ _=>1) i η κ o f-
        branches Q hpos hQ H K (weight H) i η κ o f :
          MatrixMap (Graded (A:=A) Q (Bool×μ i)) (Graded (A:=A) Q (Bool×μ (i+1)))) X).trace.re)≤
      ((i:ℝ)/(Fintype.card A:ℝ))*X.trace.re := by
  simp_rw [branches_difference]
  simp only [LinearMap.comp_apply,
    conjugate_trace_of_isometry _ (known_gram Q (K i) (hK i))]
  exact choice_deficit_bound Q hpos hQ _ _ (weight_le_one H i η) i
    (weight_deficit H i η) X hX

theorem weighted_uniform_distance (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (hX:X.PosSemidef) (n:ℕ) :
    traceNorm (erase (H:=fun i=>Graded (A:=A) Q (Bool×μ i)) n
      (uniformRun Q hpos hQ H K X n)-
      erase (H:=fun i=>Graded (A:=A) Q (Bool×μ i)) n
        (weightedRun Q hpos hQ H K X n))≤
      (∑i∈Finset.range n,(i:ℝ)/(Fintype.card A:ℝ))*X.trace.re := by
  have h:=ICO.C6HistoryWeightBound.actual_weight_hybrid
    (branches Q hpos hQ H K (fun _ _ _ _=>1))
    (branches Q hpos hQ H K (weight H))
    (ICO.C6CacheTrajectoryAfter.stages Q hpos hQ
      (fun _ b=>some (ICO.C6ActualResidualWeight.outcomeBasis H b)) K hK)
    (uniform_sum Q hpos hQ H K hK)
    (branches_cp Q hpos hQ H K _ (fun _ _ _ _=>by norm_num))
    (branches_cp Q hpos hQ H K _ (weight_nonnegative H))
    (branches_deficit_cp Q hpos hQ H K)
    (fun i=>(i:ℝ)/(Fintype.card A:ℝ)) (fun _=>by positivity)
    (branches_deficit_mass Q hpos hQ H K hK)
    (ICO.C6CacheTrajectory.initial Q X)
    (MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) X hX) n
  rw [ICO.C6CacheTrajectory.initial_trace] at h
  exact h

#print axioms weighted_uniform_distance
end
end ICO.C6WeightedHistoryBound

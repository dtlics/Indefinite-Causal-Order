import ICO.C6RetainedChoice
import ICO.C6CacheTrajectoryAfter
import ICO.C6ClassicalHistoryRun
import ICO.C6ActualResidualWeight

/-! Canonical actual cache with two inaccessible classical histories. The
outcome history is exactly the copied (j,b) history of the physical schedule;
the independent Bool history records retrieval versus fresh birth. -/
namespace ICO.C6WeightedHistory
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6RetainedCacheCP ICO.C6RetainedChoice ICO.C6CacheSpanProjection
  ICO.C6CacheWeights ICO.C6ActualResidualWeight ICO.C6ClassicalHistoryRun
  ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def weight (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (η:History (A×Bool) i)
    (b:Bool) (j:A) : ℝ :=
  overlapWeight (outcomeBasis H b) (historyProjection (ICO.C6RetainedHistory.vectors H i η)) j

theorem weight_nonnegative (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) (b:Bool) (j:A) : 0≤weight H i η b j :=
  overlapWeight_nonnegative _ _ (spanProjection_projection _ _) _

theorem weight_le_one (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) (b:Bool) (j:A) : weight H i η b j≤1 :=
  overlapWeight_le_one _ _ (spanProjection_projection _ _) _

theorem weight_deficit (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) (b:Bool) :
    (∑j:A,(1-weight H i η b j)) ≤ (i:ℝ) := by
  unfold weight
  rw [overlapWeight_deficit]
  exact historyProjection_trace _

def branches (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (w:∀i,History (A×Bool) i→Bool→A→ℝ) :
    Branches (J:=A×Bool) (F:=Bool) (H:=fun i=>Graded (A:=A) Q (Bool×μ i)) :=
  fun i η _ outcome flag=>(conjugate (known Q (K i))).comp
    (branch Q hpos hQ (outcomeBasis H) (w i η) outcome flag)

theorem branches_cp (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (w:∀i,History (A×Bool) i→Bool→A→ℝ) (hw:∀i η b j,0≤w i η b j)
    (i:ℕ) (η:History (A×Bool) i) (κ:History Bool i) (outcome:A×Bool) (flag:Bool) :
    MatrixMap.IsCompletelyPositive (branches Q hpos hQ H K w i η κ outcome flag) :=
  MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
    (branch_cp Q hpos hQ (outcomeBasis H) (w i η) (hw i η) outcome flag)

def weightedRun (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) :=
  run (branches Q hpos hQ H K (weight H)) (ICO.C6CacheTrajectory.initial Q X)

def uniformRun (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) :=
  run (branches Q hpos hQ H K (fun _ _ _ _=>1)) (ICO.C6CacheTrajectory.initial Q X)

theorem uniform_sum (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1) (i:ℕ)
    (η:History (A×Bool) i) (κ:History Bool i) :
    (∑outcome:A×Bool,∑flag:Bool,
      branches Q hpos hQ H K (fun _ _ _ _=>1) i η κ outcome flag)=
      (ICO.C6CacheTrajectoryAfter.stages Q hpos hQ
        (fun _ b=>some (outcomeBasis H b)) K hK i).map := by
  simp only [branches,sum_post,branch_sum]
  rfl

theorem uniform_erase (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (hK:∀i,(K i).conjTranspose*K i=1)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0)) (n:ℕ) :
    erase (H:=fun i=>Graded (A:=A) Q (Bool×μ i)) n
      (uniformRun Q hpos hQ H K X n)=ICO.C6ChannelTrajectory.run
      (ICO.C6CacheTrajectoryAfter.stages Q hpos hQ
        (fun _ b=>some (outcomeBasis H b)) K hK) (ICO.C6CacheTrajectory.initial Q X) n :=
  erase_uniform _ _ (uniform_sum Q hpos hQ H K hK) _ n

#print axioms weight_deficit
#print axioms uniform_erase
end
end ICO.C6WeightedHistory

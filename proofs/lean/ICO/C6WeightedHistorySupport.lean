import ICO.C6WeightedHistory
import ICO.C6RetainedGradeSupport
import ICO.C6FlagCount

namespace ICO.C6WeightedHistorySupport
open QIT Matrix ICO.C6CacheDecode ICO.C6CacheMap ICO.C6GradedCache
  ICO.C6GradedSupport ICO.C6GradedTransport ICO.C6RetainedGradeSupport
  ICO.C6WeightedHistory ICO.C6ClassicalHistoryRun ICO.RecordingPurifiedProtocol ICO.C6FlagCount
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def historyGrade (Q n:ℕ) (hn:n≤Q) (κ:History Bool n) : Fin (Q+1) :=
  ⟨flagCount n κ,lt_of_le_of_lt ((flagCount_le n κ).trans hn) (Nat.lt_succ_self Q)⟩

theorem branches_supported (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (w:∀i,History (A×Bool) i→Bool→A→ℝ)
    (i:ℕ) (η:History (A×Bool) i) (κ:History Bool i) (o:A×Bool) (f:Bool)
    (r:Fin (Q+1)) (hr:r.val<Q)
    (X:CMatrix (Graded (A:=A) Q (Bool×μ i))) (hX:Supported Q r X) :
    Supported Q (nextGrade Q r hr f) (branches Q hpos hQ H K w i η κ o f X) := by
  simp only [branches,LinearMap.comp_apply]
  exact supported_known Q (nextGrade Q r hr f) (K i) _
    (branch_supported Q hpos hQ (ICO.C6ActualResidualWeight.outcomeBasis H)
      (w i η) r hr o f X hX)

theorem run_supported (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (w:∀i,History (A×Bool) i→Bool→A→ℝ)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0))
    (n:ℕ) (hn:n≤Q) (η:History (A×Bool) n) (κ:History Bool n) :
    Supported Q (historyGrade Q n hn κ)
      (run (branches Q hpos hQ H K w) (ICO.C6CacheTrajectory.initial Q X) n η κ) := by
  induction n with
  | zero=>exact ⟨X,rfl⟩
  | succ n ih=>
    have hprev:n≤Q:=by omega
    have hg:(historyGrade Q n hprev κ.2).val<Q:=flagCount_lt (by omega) κ.2
    have hs:=branches_supported Q hpos hQ H K w n η.2 κ.2 η.1 κ.1
      (historyGrade Q n hprev κ.2) hg _ (ih hprev η.2 κ.2)
    have he:nextGrade Q (historyGrade Q n hprev κ.2) hg κ.1=historyGrade Q (n+1) hn κ := by
      apply Fin.ext
      rfl
    rw [he] at hs
    exact hs

theorem weightedRun_supported (Q:ℕ) (hpos:0<Q) (hQ:Q<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix (A×(Bool×μ (i+1))) (A×(Bool×μ i)) ℂ)
    (X:CMatrix (Cache (A:=A) (M:=Bool×μ 0) 0))
    (n:ℕ) (hn:n≤Q) (η:History (A×Bool) n) (κ:History Bool n) :
    Supported Q (historyGrade Q n hn κ) (weightedRun Q hpos hQ H K X n η κ) :=
  run_supported Q hpos hQ H K (weight H) X n hn η κ

#print axioms weightedRun_supported
end
end ICO.C6WeightedHistorySupport

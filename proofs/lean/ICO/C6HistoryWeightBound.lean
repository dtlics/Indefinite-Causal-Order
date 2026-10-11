import ICO.C6ClassicalHistoryRun
import QIT.States.TraceNorm.PositivePart

namespace ICO.C6HistoryWeightBound
open QIT Matrix ICO.RecordingPurifiedProtocol ICO.C6ClassicalHistoryRun
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
universe u v w
variable {J : Type u} {F : Type v} [Fintype J] [DecidableEq J]
  [Fintype F] [DecidableEq F]
  {H : ℕ→Type w} [∀i,Fintype (H i)] [∀i,DecidableEq (H i)]

def mass (i:ℕ) (X:History J i→History F i→CMatrix (H i)) : ℝ :=
  ∑η,∑κ,(X η κ).trace.re

theorem erase_trace (i:ℕ) (X:History J i→History F i→CMatrix (H i)) :
    (erase i X).trace.re=mass i X := by
  simp only [erase,mass,Matrix.trace_sum,Complex.re_sum]

theorem uniform_mass (S:Branches (J:=J) (F:=F) (H:=H))
    (Φ:∀i,Channel (H i) (H (i+1)))
    (hS:∀i η κ,(∑j,∑f,S i η κ j f)=(Φ i).map)
    (X:CMatrix (H 0)) (n:ℕ) : mass n (run S X n)=X.trace.re := by
  rw [←erase_trace,erase_uniform S Φ hS,ICO.C6ChannelTrajectory.run_trace]

theorem difference_pos (S T:Branches (J:=J) (F:=F) (H:=H))
    (hS:∀i η κ j f,MatrixMap.IsCompletelyPositive (S i η κ j f))
    (hT:∀i η κ j f,MatrixMap.IsCompletelyPositive (T i η κ j f))
    (hD:∀i η κ j f,MatrixMap.IsCompletelyPositive (S i η κ j f-T i η κ j f))
    (X:CMatrix (H 0)) (hX:X.PosSemidef) (n:ℕ) :
    (erase n (run S X n)-erase n (run T X n)).PosSemidef := by
  unfold erase
  rw [←Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro η _
  rw [←Finset.sum_sub_distrib]
  exact Matrix.posSemidef_sum _ (fun κ _=>run_difference_pos S T hS hT hD X hX n η κ)

theorem weighted_mass_le (S T:Branches (J:=J) (F:=F) (H:=H))
    (Φ:∀i,Channel (H i) (H (i+1)))
    (hs:∀i η κ,(∑j,∑f,S i η κ j f)=(Φ i).map)
    (hS:∀i η κ j f,MatrixMap.IsCompletelyPositive (S i η κ j f))
    (hT:∀i η κ j f,MatrixMap.IsCompletelyPositive (T i η κ j f))
    (hD:∀i η κ j f,MatrixMap.IsCompletelyPositive (S i η κ j f-T i η κ j f))
    (X:CMatrix (H 0)) (hX:X.PosSemidef) (n:ℕ) :
    mass n (run T X n)≤X.trace.re := by
  have hp:=(Complex.nonneg_iff.mp (difference_pos S T hS hT hD X hX n).trace_nonneg).1
  rw [Matrix.trace_sub,Complex.sub_re,erase_trace,erase_trace,uniform_mass S Φ hs] at hp
  linarith

theorem local_mass_loss (S T:Branches (J:=J) (F:=F) (H:=H))
    (Φ:∀i,Channel (H i) (H (i+1)))
    (hs:∀i η κ,(∑j,∑f,S i η κ j f)=(Φ i).map)
    (i:ℕ) (η:History J i) (κ:History F i) (X:CMatrix (H i)) :
    X.trace.re-(∑j,∑f,(T i η κ j f X).trace.re)=
      ∑j,∑f,((S i η κ j f-T i η κ j f) X).trace.re := by
  have h:=congrArg (fun ψ:MatrixMap (H i) (H (i+1))=>(ψ X).trace.re) (hs i η κ)
  simp only [LinearMap.sum_apply,Matrix.trace_sum,Complex.re_sum,(Φ i).tracePreserving] at h
  simp only [LinearMap.sub_apply,Matrix.trace_sub,Complex.sub_re,
    Finset.sum_sub_distrib]
  rw [h]
  rw [(Φ i).tracePreserving]

theorem run_mass_loss_le (S T:Branches (J:=J) (F:=F) (H:=H))
    (Φ:∀i,Channel (H i) (H (i+1)))
    (hs:∀i η κ,(∑j,∑f,S i η κ j f)=(Φ i).map)
    (hT:∀i η κ j f,MatrixMap.IsCompletelyPositive (T i η κ j f))
    (ε:ℕ→ℝ)
    (hε:∀i η κ Y,Y.PosSemidef→
      (∑j,∑f,((S i η κ j f-T i η κ j f) Y).trace.re)≤ε i*Y.trace.re)
    (X:CMatrix (H 0)) (hX:X.PosSemidef) (n:ℕ) :
    mass n (run T X n)-mass (n+1) (run T X (n+1))≤ε n*mass n (run T X n) := by
  have hn:mass (n+1) (run T X (n+1))=
      ∑η:History J n,∑κ:History F n,∑j,∑f,
        (T n η κ j f (run T X n η κ)).trace.re := by
    rw [←erase_trace,sum_succ]
    simp only [Matrix.trace_sum,Complex.re_sum,run]
  rw [hn,mass,←Finset.sum_sub_distrib]
  simp_rw [←Finset.sum_sub_distrib,local_mass_loss S T Φ hs]
  calc
    _ ≤ ∑η:History J n,∑κ:History F n,ε n*(run T X n η κ).trace.re := by
      apply Finset.sum_le_sum
      intro η _
      apply Finset.sum_le_sum
      intro κ _
      exact hε n η κ _ (run_pos T hT X hX n η κ)
    _ = _ := by simp only [Finset.mul_sum]

theorem actual_weight_hybrid (S T:Branches (J:=J) (F:=F) (H:=H))
    (Φ:∀i,Channel (H i) (H (i+1)))
    (hs:∀i η κ,(∑j,∑f,S i η κ j f)=(Φ i).map)
    (hS:∀i η κ j f,MatrixMap.IsCompletelyPositive (S i η κ j f))
    (hT:∀i η κ j f,MatrixMap.IsCompletelyPositive (T i η κ j f))
    (hD:∀i η κ j f,MatrixMap.IsCompletelyPositive (S i η κ j f-T i η κ j f))
    (ε:ℕ→ℝ) (hε0:∀i,0≤ε i)
    (hε:∀i η κ Y,Y.PosSemidef→
      (∑j,∑f,((S i η κ j f-T i η κ j f) Y).trace.re)≤ε i*Y.trace.re)
    (X:CMatrix (H 0)) (hX:X.PosSemidef) (n:ℕ) :
    traceNorm (erase n (run S X n)-erase n (run T X n))≤
      (∑i∈Finset.range n,ε i)*X.trace.re := by
  have hm:∀n,X.trace.re-mass n (run T X n)≤(∑i∈Finset.range n,ε i)*X.trace.re := by
    intro n
    induction n with
    | zero=>simp [mass,run,History]
    | succ n ih=>
      have hl:=run_mass_loss_le S T Φ hs hT ε hε X hX n
      have hb:=mul_le_mul_of_nonneg_left (weighted_mass_le S T Φ hs hS hT hD X hX n) (hε0 n)
      rw [Finset.sum_range_succ]
      nlinarith
  rw [traceNorm_posSemidef_eq_trace_re _ (difference_pos S T hS hT hD X hX n),
    Matrix.trace_sub,Complex.sub_re,erase_trace,erase_trace,uniform_mass S Φ hs]
  exact hm n

#print axioms actual_weight_hybrid
end
end ICO.C6HistoryWeightBound

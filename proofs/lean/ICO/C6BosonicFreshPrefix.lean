import ICO.C6BosonicStageSupport
import ICO.C6BosonicStageLength
import ICO.C6BosonicVacuum

/-! The actual fresh recording trajectory has its required history support
at every prefix, starting from the literal empty-record embedding. -/
namespace ICO.C6BosonicFreshPrefix
open QIT ICO.C6BosonicStageSupport ICO.C6BosonicStageLength ICO.C6BosonicVacuum
  ICO.C6BosonicHistorySupport ICO.C6BosonicLengthMasks ICO.C6BosonicQueryAlgebra
  ICO.C6RetainedHistory ICO.C6HistoryControlled ICO.C6PairedTrajectory ICO.C6MatrixTrajectory
  ICO.C6FockQueryMatrix ICO.MHBoundedRecording ICO.MHRectangularAction
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem prefix_factor (H:Matrix.unitaryGroup A ℂ) (i T:ℕ) :
    controlled (M:=μ i) (prefixMask H i T)=
      publicSupport (μ:=μ) H i T*memoryMask (A:=A) i T (Public (A:=A) μ i) := by
  rw [publicSupport,memoryMask,←controlled_const,controlled_mul]
  rfl

theorem mask_prefix (H:Matrix.unitaryGroup A ℂ) (i T:ℕ) :
    memoryMask (A:=A) i T (Public (A:=A) μ i)*controlled (M:=μ i) (prefixMask H i T)=
      controlled (M:=μ i) (prefixMask H i T) := by
  rw [memoryMask,←controlled_const,controlled_mul]
  congr 1
  funext η
  unfold prefixMask
  have hc : rightLengthMask (α:=A) i T*historySupport (vectors H i η) T=
      historySupport (vectors H i η) T*rightLengthMask i T :=
    mask_family (supportSector _) i T
  rw [←Matrix.mul_assoc,hc,Matrix.mul_assoc,(mask_projection (A:=A) i T).isIdempotentElem.eq]

theorem freshRun_prefix {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (i:ℕ) :
    rectAct (controlled (M:=μ i) (prefixMask H i T))
      (run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
        (freshStage h H K) (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i)=
      run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
        (freshStage h H K) (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i := by
  induction i with
  | zero => exact prefix_initial H T z
  | succ i ih =>
    let v := run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
      (freshStage h H K) (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i
    have hv : rectAct (controlled (M:=μ i) (prefixMask H i T)) v=v := ih
    have hr : rectAct (memoryMask (A:=A) i T (Public (A:=A) μ i)) v=v := by
      calc
        _ = rectAct (memoryMask (A:=A) i T (Public (A:=A) μ i)*
              controlled (M:=μ i) (prefixMask H i T)) v := by rw [rectAct_mul,hv]
        _ = _ := by rw [mask_prefix,hv]
    have hn : rectAct (memoryMask (A:=A) (i+1) T (Public (A:=A) μ (i+1)))
        (rectAct (freshStage h H K i) v)=rectAct (freshStage h H K i) v := by
      calc
        _ = rectAct (memoryMask (A:=A) (i+1) T (Public (A:=A) μ (i+1))*freshStage h H K i*
              memoryMask i T (Public (A:=A) μ i)) v := by rw [rectAct_mul,rectAct_mul,hr]
        _ = _ := by rw [freshStage_mask,rectAct_mul,hr]
    have hb : rectAct (publicSupport (μ:=μ) H (i+1) T)
        (rectAct (freshStage h H K i) v)=rectAct (freshStage h H K i) v := by
      rw [←rectAct_mul,freshStage_history_support h ht H K i]
    change rectAct (controlled (M:=μ (i+1)) (prefixMask H (i+1) T))
      (rectAct (freshStage h H K i) v)=rectAct (freshStage h H K i) v
    rw [prefix_factor,rectAct_mul,hn,hb]

#print axioms freshRun_prefix
end
end ICO.C6BosonicFreshPrefix

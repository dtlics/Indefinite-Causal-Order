import ICO.C6HistoryHybrid
import ICO.C6SharedPolarBound

namespace ICO.C6NativeFresh
open Matrix QIT ICO.C6RetainedHistory ICO.C6HistoryControlled ICO.C6HistoryHybrid
  ICO.C6PairedTrajectory ICO.C6NativePolar ICO.C6SharedFockSchedule
  ICO.C6SharedQuerySchedule ICO.C6MatrixTrajectory ICO.MHBoundedRecording
  ICO.MHFockVisibleDistance ICO.MHDecompressionErasure ICO.MHFockRunIsometry
  ICO.MHRectangularAction
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def freshVector {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (n:ℕ) :
    EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ n) :=
  run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (freshStage h H K)
    (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) n

def freshNative {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (n:ℕ) :
    InputCutoff (α:=A) T×QueryMemory (A:=A) μ 0 (2*n)→ℂ :=
  WithLp.ofLp (freshVector h H K z n) ∘ endpointEquiv (μ:=μ) T n

theorem freshVector_norm {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) :
    ‖freshVector h H K z n‖≤1 := by
  apply run_norm _ (freshStage_norm h hd H K hK)
  rwa [ICO.MHFockRunIsometry.initial_norm T (WithLp.toLp 2 z)]

theorem freshNative_norm {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) :
    ‖WithLp.toLp 2 (freshNative h H K z n)‖≤1 := by
  have he := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (endpointEquiv (A:=A) (μ:=μ) T n).symm).norm_map (freshVector h H K z n)
  change ‖WithLp.toLp 2 (freshNative h H K z n)‖=‖freshVector h H K z n‖ at he
  exact he.le.trans (freshVector_norm h hd H K hK z hz n)

theorem polar_fresh_visible_of_prefix {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) (hn:n≤Fintype.card A)
    (hs:∀i<n,rectAct (controlled (M:=μ i) (prefixMask H i T)) (freshVector h H K z i)=
      freshVector h H K z i) :
    normalizedTraceDistance (fockVisible T (polarNative h H K z n))
      (fockVisible T (freshNative h H K z n))≤∑i∈Finset.range n,freshCost (Fintype.card A) i := by
  have hi:‖WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)‖≤1 := by
    rwa [ICO.MHFockRunIsometry.initial_norm T (WithLp.toLp 2 z)]
  have hh:=fresh_polar_distance h hd H K hK
    (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) hi n hn hs
  have he:‖WithLp.toLp 2 (polarNative h H K z n)-WithLp.toLp 2 (freshNative h H K z n)‖≤
      ∑i∈Finset.range n,freshCost (Fintype.card A) i := by
    have he := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (endpointEquiv (A:=A) (μ:=μ) T n).symm).norm_map
      (polarVector h H K z n-freshVector h H K z n)
    have hn' : ‖polarVector h H K z n-freshVector h H K z n‖≤
        ∑i∈Finset.range n,freshCost (Fintype.card A) i := by
      rw [norm_sub_rev]
      exact hh
    exact he.le.trans hn'
  exact (visible_pure_distance T _ _ (polarNative_norm h hd H K hK z hz n)
    (freshNative_norm h hd H K hK z hz n)).trans he

#print axioms polar_fresh_visible_of_prefix
end
end ICO.C6NativeFresh

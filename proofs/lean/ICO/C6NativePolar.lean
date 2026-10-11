import ICO.C6PairedHybrid
import ICO.C6SharedFockSchedule
import ICO.MHFockVisibleDistance
import ICO.MHFockRunIsometry

/-! The actual signed recording trajectory is close to the literal polar
trajectory, including private choice/outcome registers and all public maps. -/
namespace ICO.C6NativePolar
open Matrix QIT ICO.C6PairedTrajectory ICO.C6PairedHybrid ICO.C6SharedFockSchedule
  ICO.C6SharedQuerySchedule ICO.MHBoundedRecording ICO.MHFockTrajectory
  ICO.MHFockVisibleDistance ICO.MHDecompressionErasure ICO.MHFockRunIsometry
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def polarVector {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (n:ℕ) :
    EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ n) :=
  ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
    (ICO.C6PolarTrajectory.polarStage h (middleStage T H) (publicStage T K))
    (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) n

def polarNative {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (n:ℕ) :
    InputCutoff (α:=A) T×QueryMemory (A:=A) μ 0 (2*n)→ℂ :=
  WithLp.ofLp (polarVector h H K z n) ∘ endpointEquiv (μ:=μ) T n

theorem polarVector_norm {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) :
    ‖polarVector h H K z n‖≤1 := by
  apply ICO.C6MatrixTrajectory.run_norm _
    (ICO.C6PolarTrajectory.polarStage_norm h hd (middleStage T H) (publicStage T K)
      (middleStage_norm T H) (publicStage_norm T K hK))
  rwa [ICO.MHFockRunIsometry.initial_norm T (WithLp.toLp 2 z)]

theorem polarNative_norm {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) :
    ‖WithLp.toLp 2 (polarNative h H K z n)‖≤1 := by
  have he := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (endpointEquiv (A:=A) (μ:=μ) T n).symm).norm_map (polarVector h H K z n)
  change ‖WithLp.toLp 2 (polarNative h H K z n)‖=‖polarVector h H K z n‖ at he
  exact he.le.trans (polarVector_norm h hd H K hK z hz n)

theorem native_polar_distance {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) (hn:2*n≤t) :
    ‖WithLp.toLp 2 (ICO.MHFockTrajectory.run T (known H K 0)
        (fun i=>Vchoice h (ICO.DoubleQuerySchedule.direction i)) z (2*n))-
      WithLp.toLp 2 (polarNative h H K z n)‖≤
      (∑i∈Finset.range n,deletionCost (Fintype.card A) i)+
        7*(n:ℝ)*ICO.C6PolarFockBounds.delta t (Fintype.card A) := by
  have hi : ‖WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)‖≤1 := by
    rwa [ICO.MHFockRunIsometry.initial_norm T (WithLp.toLp 2 z)]
  have hh := polar_run_distance h hd H K hK
    (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) hi
    (ICO.MHFockTrajectory.initial_grade T z) n hn
  rw [native_even]
  let e := endpointEquiv (A:=A) (μ:=μ) T n
  have he := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map
    (ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
      (fullStage h H K) (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) n-
      polarVector h H K z n)
  exact he.le.trans hh

theorem native_polar_visible {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:A×Public (A:=A) μ 0→ℂ) (hz:‖WithLp.toLp 2 z‖≤1) (n:ℕ) (hn:2*n≤t) :
    normalizedTraceDistance
      (fockVisible T (ICO.MHFockTrajectory.run T (known H K 0)
        (fun i=>Vchoice h (ICO.DoubleQuerySchedule.direction i)) z (2*n)))
      (fockVisible T (polarNative h H K z n))≤
      (∑i∈Finset.range n,deletionCost (Fintype.card A) i)+
        7*(n:ℝ)*ICO.C6PolarFockBounds.delta t (Fintype.card A) := by
  have hfull := run_norm_le T (known H K 0)
    (fun i=>known_isometry H K hK 0 i)
    (fun i=>Vchoice h (ICO.DoubleQuerySchedule.direction i))
    (fun i=>Vchoice_norm_le h hd _) (WithLp.toLp 2 z) hz (2*n)
  exact (visible_pure_distance T _ _ hfull
    (polarNative_norm h hd H K hK z hz n)).trans
    (native_polar_distance h hd H K hK z hz n hn)

#print axioms native_polar_visible
end
end ICO.C6NativePolar

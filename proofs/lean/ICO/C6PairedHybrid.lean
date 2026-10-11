import ICO.C6PairedTrajectory
import ICO.C6MatrixLocalHybrid

namespace ICO.C6PairedHybrid
open Matrix QIT ICO.C6PairedTrajectory ICO.C6FockPairs ICO.C6MatrixTrajectory
  ICO.C6MatrixLocalHybrid ICO.MHBoundedRecording ICO.MHFockProjection
  ICO.MHFockTrajectory ICO.MHRectangularAction
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def deletionCost (d i:ℕ) : ℝ := Real.sqrt (2*(2*(i:ℝ)+1)/((d:ℝ)-2*i))

theorem deleted_run_distance {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0)) (hz:‖z‖≤1)
    (hgrade:Supported (fun i=>grade i.1≤0) (WithLp.ofLp z)) (n:ℕ) (hn:2*n≤t) :
    ‖ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (fullStage h H K) z n-
      ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (deletedStage h H K) z n‖≤
      ∑i∈Finset.range n,deletionCost (Fintype.card A) i := by
  refine run_distance_upto (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
    (fullStage h H K) (deletedStage h H K) z (deletionCost (Fintype.card A)) n
    (fun i _=>deletedStage_norm h hd H K hK i) ?_
  intro i hi
  have his : 2*i≤t := by omega
  have hit : 2*i+1≤T := by omega
  have hnorm := ICO.C6MatrixTrajectory.run_norm (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (fullStage h H K)
    (fullStage_norm h hd H K hK) z hz i
  have hsup := fullRun_grade h H K z hgrade i
  have hh := pair_deletion hit h his hd H (K i) (hK i)
    (WithLp.ofLp (ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (fullStage h H K) z i))
    (by simpa only [WithLp.toLp_ofLp] using hnorm) hsup
  simpa only [fullStage,deletedStage,rectAct,Matrix.toEuclideanLin_apply,
    deletionCost,Nat.cast_mul,Nat.cast_ofNat] using hh

theorem polar_run_distance {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0)) (hz:‖z‖≤1)
    (hgrade:Supported (fun i=>grade i.1≤0) (WithLp.ofLp z)) (n:ℕ) (hn:2*n≤t) :
    ‖ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (fullStage h H K) z n-
      ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
        (ICO.C6PolarTrajectory.polarStage h (middleStage T H) (publicStage T K)) z n‖≤
      (∑i∈Finset.range n,deletionCost (Fintype.card A) i)+
        7*(n:ℝ)*ICO.C6PolarFockBounds.delta t (Fintype.card A) := by
  have h1 := deleted_run_distance h hd H K hK z hz hgrade n hn
  have h2 := ICO.C6PolarTrajectory.trajectory_distance h hd (middleStage T H)
    (publicStage T K) (middleStage_norm T H) (publicStage_norm T K hK) z hz n
  have he : deletedStage h H K=
      ICO.C6PolarTrajectory.oldStage h (middleStage T H) (publicStage T K) := by
    funext i
    exact deletedStage_eq_oldStage h H K i
  rw [←he] at h2
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h1 h2)

#print axioms deleted_run_distance
#print axioms polar_run_distance
end
end ICO.C6PairedHybrid

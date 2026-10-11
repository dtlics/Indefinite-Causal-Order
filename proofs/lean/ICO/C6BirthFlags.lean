import ICO.C6RetainedHistory
import ICO.C6HistoryControlled

/-! Exact coherent expansion of the physical fresh process into retrieval
and birth branches. The Boolean histories are not erased in this module. -/
namespace ICO.C6BirthFlags
open Matrix QIT ICO.C6RetainedHistory ICO.C6HistoryControlled ICO.C6PairedTrajectory
  ICO.C6PolarFock ICO.C6BosonicFreshContraction ICO.C6BosonicFockRotated
  ICO.C6BosonicHistorySupport ICO.C6CacheSpanProjection ICO.C6MatrixTrajectory
  ICO.RecordingPurifiedProtocol ICO.MHBoundedRecording ICO.MHRectangularAction
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def flagInverse {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) (birth:Bool) : CMatrix (InputCutoff (α:=A) T) :=
  (if birth then rotatedFresh (historyUnitary (vectors H i η)) (historyIndices (vectors H i η)) T*
      polarRightOnFock h*(1-polarLeftOnFock h*(polarLeftOnFock h)ᴴ)
    else (polarLeftOnFock h)ᴴ)*historySupport (vectors H i η) T

theorem flagInverse_sum {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) : (∑b,flagInverse h H i η b)=inverseBlock h H i η := by
  simp only [Fintype.sum_bool,flagInverse,if_pos,if_false,inverseBlock,freshInverse,Matrix.add_mul]
  exact add_comm _ _

theorem controlled_sum {T i:ℕ} {M:Type} [Fintype M] [DecidableEq M]
    {J:Type} [Fintype J] (F:J→History (A×Bool) i→CMatrix (InputCutoff (α:=A) T)) :
    controlled (M:=M) (fun η=>∑j,F j η)=∑j,controlled (M:=M) (F j) := by
  ext o k
  simp only [controlled_entry,Matrix.sum_apply]
  split_ifs <;> simp

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def flagStage {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) (birth:Bool) :
    Matrix (InputCutoff (α:=A) T×Public (A:=A) μ (i+1))
      (InputCutoff (α:=A) T×Public (A:=A) μ i) ℂ :=
  publicStage T K i*Matrix.kronecker (polarLeftOnFock h) (1:CMatrix (Middle (A:=A) μ i))*
    middleStage T H i*controlled (M:=μ i) (fun η=>flagInverse h H i η birth)

theorem flagStage_sum {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) :
    (∑b,flagStage h H K i b)=freshStage h H K i := by
  simp only [flagStage,←Matrix.mul_sum,←controlled_sum,flagInverse_sum]
  rfl

def flagRun {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0)) :
    (i:ℕ)→History Bool i→EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ i)
  | 0,_=>z
  | i+1,κ=>rectAct (flagStage h H K i κ.1) (flagRun h H K z i κ.2)

theorem flagRun_sum {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0)) (n:ℕ) :
    (∑κ,flagRun h H K z n κ)=
      run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (freshStage h H K) z n := by
  induction n with
  | zero => change (∑_:PUnit,z)=z; simp
  | succ n ih =>
    change (∑κ:Bool×History Bool n,rectAct (flagStage h H K n κ.1)
      (flagRun h H K z n κ.2))=_
    rw [Fintype.sum_prod_type]
    simp only [←map_sum,ih]
    change (∑b,WithLp.toLp 2 ((flagStage h H K n b)*ᵥWithLp.ofLp
      (run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (freshStage h H K) z n)))=_
    rw [←WithLp.toLp_sum,←Matrix.sum_mulVec,flagStage_sum]
    rfl

#print axioms flagRun_sum
end
end ICO.C6BirthFlags

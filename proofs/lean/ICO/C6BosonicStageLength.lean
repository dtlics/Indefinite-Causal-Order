import ICO.C6BosonicFreshLength
import ICO.C6BosonicBlocks

/-! Each actual retained-history stage increases the right-record count by
at most one, including arbitrary changing accessible memory. -/
namespace ICO.C6BosonicStageLength
open QIT ICO.C6BosonicBlocks ICO.C6BosonicFreshLength ICO.C6BosonicLengthMasks
  ICO.C6BosonicQueryAlgebra ICO.C6BosonicHistorySupport ICO.C6CacheSpanProjection
  ICO.C6RetainedHistory ICO.C6HistoryControlled ICO.C6PairedTrajectory
  ICO.C6PolarFock ICO.C6FockQueryMatrix ICO.MHBoundedRecording ICO.MHFockKnownOperation
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def memoryMask (m T:ℕ) (M:Type) [Fintype M] [DecidableEq M] :
    CMatrix (InputCutoff (α:=A) T×M) := Matrix.kronecker (rightLengthMask m T) (1:CMatrix M)

theorem tensor_family {X M:Type*} [Fintype X] [DecidableEq X] [Fintype M] [DecidableEq M]
    (F:CMatrix X) : diagonalFamily (fun _:M=>F)=Matrix.kronecker F (1:CMatrix M) := by
  ext o i
  simp only [diagonalFamily,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  split_ifs <;> simp

theorem known_mask (m T:ℕ) {M N:Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (K:Matrix (A×N) (A×M) ℂ) :
    memoryMask (A:=A) m T N*known T K=known T K*memoryMask m T M := by
  unfold memoryMask
  rw [←tensor_family,←tensor_family]
  ext ⟨x,o⟩ ⟨y,i⟩
  have he : block (diagonalFamily (fun _:N=>rightLengthMask m T)*known T K) o i=
      block (known T K*diagonalFamily (fun _:M=>rightLengthMask m T)) o i := by
    rw [block_left_family,block_right_family,known_block]
    exact mask_family (queryFamily _) m T
  exact congrFun (congrFun he x) y

theorem forward_mask {t T:ℕ} (h:t+1≤T) (m:ℕ) {M:Type} [Fintype M] [DecidableEq M] :
    memoryMask (A:=A) m T M*Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M)=
      Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M)*memoryMask m T M := by
  simp only [memoryMask,Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,left_mask]

theorem inverse_mask {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    {M:Type} [Fintype M] [DecidableEq M] :
    memoryMask (A:=A) (i+1) T (Bool×(ICO.RecordingPurifiedProtocol.History (A×Bool) i×M))*
      controlled (M:=M) (inverseBlock h H i)*memoryMask i T _=
      controlled (M:=M) (inverseBlock h H i)*memoryMask i T _ := by
  simp only [memoryMask,←controlled_const,controlled_mul]
  congr 1
  funext η
  let B := historySupport (vectors H i η) T
  let J := ICO.C6BosonicFreshContraction.freshInverse (polarLeftOnFock h) (polarRightOnFock h)
    (ICO.C6BosonicFockRotated.rotatedFresh (historyUnitary (vectors H i η)) (historyIndices (vectors H i η)) T)
  have hb : B*rightLengthMask i T=rightLengthMask i T*B :=
    (mask_family (supportSector _) i T).symm
  have hs : rightLengthMask (i+1) T*J*rightLengthMask i T=J*rightLengthMask i T :=
    fresh_mask_step _ _ i h
  change rightLengthMask (i+1) T*(J*B)*rightLengthMask i T=(J*B)*rightLengthMask i T
  calc
    _ = (rightLengthMask (i+1) T*J*rightLengthMask i T)*B := by
      simp only [Matrix.mul_assoc]; rw [hb]
    _ = _ := by rw [hs]; simp only [Matrix.mul_assoc,hb]

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem freshStage_mask {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) :
    memoryMask (A:=A) (i+1) T (Public (A:=A) μ (i+1))*freshStage h H K i*
      memoryMask i T (Public (A:=A) μ i)=freshStage h H K i*memoryMask i T (Public (A:=A) μ i) := by
  have hp : memoryMask (A:=A) (i+1) T (Public (A:=A) μ (i+1))*publicStage T K i=
      publicStage T K i*memoryMask (i+1) T (Middle (A:=A) μ i) := by
    exact known_mask (i+1) T (ICO.C6FockPairs.publicQuery (E:=ICO.RecordingPurifiedProtocol.History (A×Bool) i) (K i))
  have hm : memoryMask (A:=A) (i+1) T (Middle (A:=A) μ i)*middleStage (μ:=μ) T H i=
      middleStage T H i*memoryMask (i+1) T (Public (A:=A) μ i) := by
    exact known_mask (i+1) T (ICO.C6FockChoiceMeasurement.middleQuery (M:=ICO.RecordingPurifiedProtocol.History (A×Bool) i×μ i) H)
  unfold freshStage
  simp only [←Matrix.mul_assoc]
  rw [hp]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (memoryMask (A:=A) (i+1) T (Middle (A:=A) μ i)),forward_mask]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (memoryMask (A:=A) (i+1) T (Middle (A:=A) μ i)) (middleStage T H i),hm]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (memoryMask (A:=A) (i+1) T (Public (A:=A) μ i)),inverse_mask]

#print axioms freshStage_mask
end
end ICO.C6BosonicStageLength

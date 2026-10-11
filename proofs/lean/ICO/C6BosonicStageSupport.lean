import ICO.C6BosonicStageBlocks
import ICO.C6BosonicHistoryClosure

/-! Exact retained-history support of the operational fresh stage. -/
namespace ICO.C6BosonicStageSupport
open QIT ICO.C6BosonicBlocks ICO.C6BosonicStageBlocks ICO.C6BosonicHistoryClosure
  ICO.C6BosonicReencoding ICO.C6BosonicQueryAlgebra ICO.C6BosonicHistorySupport
  ICO.C6RetainedHistory ICO.C6HistoryControlled ICO.C6PairedTrajectory ICO.C6ChoiceMeasurement
  ICO.C6PolarFock ICO.C6FockQueryMatrix ICO.MHBoundedRecording
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def publicSupport (H:Matrix.unitaryGroup A ℂ) (i T:ℕ) :
    CMatrix (InputCutoff (α:=A) T×Public (A:=A) μ i) :=
  controlled (fun η=>historySupport (vectors H i η) T)

def middleSupport (H:Matrix.unitaryGroup A ℂ) (i T:ℕ) :
    CMatrix (InputCutoff (α:=A) T×Middle (A:=A) μ i) :=
  diagonalFamily (fun o=>historySupport (vectors H (i+1) (o.2.1,o.2.2.1)) T)

def reencodingStage {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (i:ℕ) :
    Matrix (InputCutoff (α:=A) T×Middle (A:=A) μ i) (InputCutoff (α:=A) T×Public (A:=A) μ i) ℂ :=
  Matrix.kronecker (polarLeftOnFock h) (1:CMatrix (Middle (A:=A) μ i))*middleStage T H i

theorem inverse_history_support {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i:ℕ) :
    publicSupport (μ:=μ) H i T*controlled (M:=μ i) (inverseBlock h H i)=
      controlled (M:=μ i) (inverseBlock h H i) := by
  rw [publicSupport,controlled_mul]
  congr 1
  funext η
  simpa only [inverseBlock,Matrix.mul_assoc] using history_fresh_support (vectors H i η) h ht

theorem public_history_support (T:ℕ) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) :
    publicSupport H (i+1) T*publicStage T K i=publicStage T K i*middleSupport H i T := by
  rw [publicSupport,controlled_family]
  ext ⟨x,o⟩ ⟨y,j⟩
  have he : block (diagonalFamily (fun p=>historySupport (vectors H (i+1) p.2.1) T)*publicStage T K i) o j=
      block (publicStage T K i*middleSupport H i T) o j := by
    rw [block_left_family,middleSupport,block_right_family,public_block]
    split_ifs with hh
    · rw [hh]
      exact (query_support _ _ T).symm
    · simp
  exact congrFun (congrFun he x) y

theorem reencoding_history_support {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i:ℕ) :
    middleSupport (μ:=μ) H i T*reencodingStage (μ:=μ) h H i*publicSupport (μ:=μ) H i T=
      reencodingStage (μ:=μ) h H i*publicSupport (μ:=μ) H i T := by
  rw [middleSupport,publicSupport,controlled_family]
  apply family_absorption
  intro o j
  rw [reencodingStage,block_left_tensor,middle_block]
  split_ifs with hh
  · rcases o with ⟨b,⟨a,c⟩,η,m⟩
    rcases j with ⟨e,η',n⟩
    dsimp only at hh ⊢
    obtain ⟨hbc,hec,hem⟩ := hh
    have hη : η=η' := congrArg Prod.fst hem
    subst η'
    simpa only [vectors_snoc,Matrix.mul_assoc] using
      reencoding_support (vectors H i η) (WithLp.toLp 2 (queryVector H (c,a))) h ht
  · simp

theorem freshStage_history_support {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) :
    publicSupport H (i+1) T*freshStage h H K i=freshStage h H K i := by
  let A0 := publicSupport (μ:=μ) H i T
  let A1 := middleSupport (μ:=μ) H i T
  let A2 := publicSupport (μ:=μ) H (i+1) T
  let J := controlled (M:=μ i) (inverseBlock h H i)
  let L : Matrix (InputCutoff (α:=A) T×Middle (A:=A) μ i) (InputCutoff (α:=A) T×Public (A:=A) μ i) ℂ :=
    Matrix.kronecker (polarLeftOnFock h) (1:CMatrix (Middle (A:=A) μ i))*middleStage T H i
  let P := publicStage T K i
  have hj : A0*J=J := inverse_history_support h ht H i
  have hl : A1*L*A0=L*A0 := reencoding_history_support h ht H i
  have hp : A2*P=P*A1 := public_history_support T H K i
  have he : A2*(P*L*J)=P*L*J := by
    calc
      _ = (A2*P)*L*(A0*J) := by rw [hj]; simp only [Matrix.mul_assoc]
      _ = P*(A1*L*A0)*J := by rw [hp]; simp only [Matrix.mul_assoc]
      _ = P*(L*A0)*J := by rw [hl]
      _ = _ := by simp only [Matrix.mul_assoc]; rw [hj]
  simpa only [freshStage,L,P,Matrix.mul_assoc] using he

#print axioms freshStage_history_support
end
end ICO.C6BosonicStageSupport

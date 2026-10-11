import ICO.MHFockTrajectory
import ICO.MHRectangularAction
import ICO.MHIsometricRecordingProtocol

/-! The literal recording run is the isometric protocol run used in the
averaged hybrid argument. All public-stage isometries are constructed from
their matrices; all record support comes from the actual empty initialization. -/
namespace ICO.MHFockRunIsometry
open QIT ICO.MHFockTrajectory ICO.MHFockKnownOperation ICO.MHRectangularAction
  ICO.MHBoundedRecording ICO.MHProtocolOverlap ICO.RecordingCopyIdentity
  ICO.MHWDomainProjection ICO.MHFockOracle ICO.MHWEmbedding
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 512
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem initial_isometry (T : ℕ) {μ : Type*} [Fintype μ] [DecidableEq μ] :
    (basisEmbedding (initialEmbed (α := α) (μ := μ) T)).conjTranspose *
      basisEmbedding (initialEmbed (α := α) (μ := μ) T)=1 :=
  basisEmbedding_gram _ (initialEmbed_injective T μ)

theorem initial_norm (T : ℕ) {μ : Type*} [Fintype μ] [DecidableEq μ]
    (z : EuclideanSpace ℂ (α×μ)) :
    ‖WithLp.toLp 2 (initial T (WithLp.ofLp z))‖=‖z‖ :=
  rectAct_norm _ (initial_isometry T) z

variable {μ : ℕ→Type*} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

def publicIsometry (T : ℕ) (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (t : ℕ) :
    EuclideanSpace ℂ (InputCutoff (α := α) T×μ t)→ₗᵢ[ℂ]
      EuclideanSpace ℂ (InputCutoff (α := α) T×μ (t+1)) :=
  matrixIsometry (known T (K t)) (known_isometry T (K t) (hK t))

def oracleAction (T : ℕ) (O : ℕ→CMatrix (InputCutoff (α := α) T)) (t : ℕ) :
    EuclideanSpace ℂ (InputCutoff (α := α) T×μ t)→L[ℂ]
      EuclideanSpace ℂ (InputCutoff (α := α) T×μ t) :=
  act (Matrix.kronecker (O t) (1 : CMatrix (μ t)))

theorem run_eq_isometric (T : ℕ) (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1)
    (O : ℕ→CMatrix (InputCutoff (α := α) T)) (z : α×μ 0→ℂ) (t : ℕ) :
    WithLp.toLp 2 (MHFockTrajectory.run T K O z t)=
      MHIsometricRecordingProtocol.run (publicIsometry T K hK) (oracleAction T O)
        (WithLp.toLp 2 (initial T z)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change WithLp.toLp 2 (known T (K t)*ᵥ(Matrix.kronecker (O t) (1 : CMatrix (μ t))*ᵥ
      MHFockTrajectory.run T K O z t))=_
    rw [show MHFockTrajectory.run T K O z t=WithLp.ofLp
      (MHIsometricRecordingProtocol.run (publicIsometry T K hK) (oracleAction T O)
        (WithLp.toLp 2 (initial T z)) t) from congrArg WithLp.ofLp ih]
    rfl

theorem oracleAction_norm_le (T : ℕ) (O : ℕ→CMatrix (InputCutoff (α := α) T))
    (hO : ∀t,‖O t‖≤1) (t : ℕ) : ‖oracleAction (μ := μ) T O t‖≤1 := by
  change ‖(Matrix.toEuclideanCLM (n := InputCutoff (α := α) T×μ t) (𝕜 := ℂ))
    (Matrix.kronecker (O t) (1 : CMatrix (μ t)))‖≤1
  change ‖Matrix.kronecker (O t) (1 : CMatrix (μ t))‖≤1
  exact (tensor_identity_norm_le (μ := μ t) (O t)).trans (hO t)

theorem run_norm_le (T : ℕ) (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1)
    (O : ℕ→CMatrix (InputCutoff (α := α) T)) (hO : ∀t,‖O t‖≤1)
    (z : EuclideanSpace ℂ (α×μ 0)) (hz : ‖z‖≤1) (t : ℕ) :
    ‖WithLp.toLp 2 (MHFockTrajectory.run T K O (WithLp.ofLp z) t)‖≤1 := by
  rw [run_eq_isometric T K hK]
  exact MHIsometricRecordingProtocol.run_norm_le _ _ _ (oracleAction_norm_le T O hO)
    (by rwa [initial_norm]) t

theorem Wchoice_norm_le {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (inverse : Bool) :
    ‖Wchoice hT inverse‖≤1 := by
  cases inverse
  · exact recordW_norm_le hT
  · simpa only [Wchoice,if_true,Matrix.l2_opNorm_conjTranspose] using recordW_norm_le hT

theorem Vchoice_norm_le {q T : ℕ} (hq : q+1≤T) (hqd : q<Fintype.card α) (inverse : Bool) :
    ‖Vchoice (α := α) hq inverse‖≤1 := by
  cases inverse
  · exact fullOracle_norm_le hq hqd
  · exact fullOracle_adjoint_norm_le hq hqd

#print axioms run_eq_isometric
#print axioms run_norm_le
end
end ICO.MHFockRunIsometry

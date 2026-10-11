import ICO.MHActualQueryLoss
import ICO.MHFixedBudgetOverlap
import ICO.MHHaarStepConstants
import ICO.MHFockEmptyRotation

/-! Averaged overlap for literal signed recording trajectories, with all
domain, covariance, support, and integrability estimates discharged. -/
namespace ICO.MHActualRecordingOverlap
open Matrix QIT MeasureTheory ICO.MHActualQueryLoss ICO.MHFockTrajectory
  ICO.MHFockRunIsometry ICO.MHRotatedTrajectory ICO.MHFockRunContinuity
  ICO.MHFockSupportProjection ICO.MHFockRotation ICO.MHFockEmptyRotation
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHProtocolOverlap
  ICO.MHRecordingChoiceOperators ICO.MHDomainMeanProduct
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxSize 512
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ : ℕ→Type} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

def wVector {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (t : ℕ) (p : Rotations A) :
    EuclideanSpace ℂ (InputCutoff (α:=A) T×μ t) :=
  WithLp.toLp 2 (MHFockTrajectory.run T K (fun s => rotatedW hT p.1 p.2 (dir s)) z t)

def vVector {q T : ℕ} (hq : q+1≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (t : ℕ) : EuclideanSpace ℂ (InputCutoff (α:=A) T×μ t) :=
  WithLp.toLp 2 (MHFockTrajectory.run T K (fun s => Vchoice hq (dir s)) z t)

theorem wVector_continuous {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t : ℕ) :
    Continuous (wVector hT K dir z t) := by
  have he : wVector hT K dir z t=fun p => MHIsometricRecordingProtocol.run
      (publicIsometry T K hK) (oracleAction T (fun s => rotatedW hT p.1 p.2 (dir s)))
        (WithLp.toLp 2 (initial T z)) t := funext (fun p => run_eq_isometric T K hK _ z t)
  rw [he]
  exact MHIsometricRecordingProtocol.continuous_run _ _ _
    (fun s => rotatedAction_continuous hT (dir s) (μ s)) t

theorem wVector_norm {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (hz : ‖WithLp.toLp 2 z‖≤1) (t : ℕ) (p : Rotations A) : ‖wVector hT K dir z t p‖≤1 :=
  MHFockRunIsometry.run_norm_le T K hK _
    (fun s => rotatedW_norm_le hT p.1 p.2 (dir s)) (WithLp.toLp 2 z) hz t

theorem vVector_norm {q T : ℕ} (hq : q+1≤T) (hsize : q<Fintype.card A)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (hz : ‖WithLp.toLp 2 z‖≤1) (t : ℕ) : ‖vVector hq K dir z t‖≤1 :=
  MHFockRunIsometry.run_norm_le T K hK _
    (fun s => ICO.MHRecordingChoiceOperators.Vchoice_norm_le hq hsize (dir s))
    (WithLp.toLp 2 z) hz t

theorem restricted_vVector {q T : ℕ} (hq : q+1≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) {s : ℕ} (hs : s≤q) (inv : Bool) :
    act (Matrix.kronecker (choiceRestrictedV (A:=A) hq inv) (1:CMatrix (μ s)))
      (vVector hq K dir z s)=
    act (Matrix.kronecker (Vchoice (α:=A) hq inv) (1:CMatrix (μ s)))
      (vVector hq K dir z s) := by
  have hh := Vrun_source_fixed hq K dir z hs
  change WithLp.toLp 2 (Matrix.kronecker (Vchoice hq inv*
    ICO.MHFockAlgebra.sourceProjection (Nat.le_trans (Nat.le_succ q) hq))
      (1:CMatrix (μ s))*ᵥMHFockTrajectory.run T K _ z s)=_
  have hk : Matrix.kronecker (Vchoice (α:=A) hq inv*
      ICO.MHFockAlgebra.sourceProjection (Nat.le_trans (Nat.le_succ q) hq)) (1:CMatrix (μ s))=
    Matrix.kronecker (Vchoice hq inv) (1:CMatrix (μ s))*Matrix.kronecker
      (ICO.MHFockAlgebra.sourceProjection (Nat.le_trans (Nat.le_succ q) hq)) (1:CMatrix (μ s)) := by
    simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
  rw [hk,←Matrix.mulVec_mulVec,hh]
  rfl

theorem actual_local_loss {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q+1≤T) (hsize : q<Fintype.card A) (hsmall : 2*q≤Fintype.card A)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (hz : ‖WithLp.toLp 2 z‖≤1) (s : ℕ) (hs : s≤q)
    (R : ℝ) (hR : 1≤R) (hd : (Fintype.card A:ℝ)=R^8) :
    (∫p,(⟪wVector hT K dir z s p,
      act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
        (1:CMatrix (μ s))) (vVector hq K dir z s)⟫_ℂ).re ∂rotationMeasure A)-35*(q:ℝ)/R^2≤
    ∫p,(⟪act (Matrix.kronecker (rotatedW hT p.1 p.2 (dir s)) (1:CMatrix (μ s)))
      (wVector hT K dir z s p),
      act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix (μ s)))
        (act (Matrix.kronecker (Vchoice hq (dir s)) (1:CMatrix (μ s)))
          (vVector hq K dir z s))⟫_ℂ).re ∂rotationMeasure A := by
  have hh := query_mean_step hT hq hsize hsmall (dir s) (wVector hT K dir z s)
    (vVector hq K dir z s) (wVector_continuous hT K hK dir z s)
    (wVector_norm hT K hK dir z hz s) (vVector_norm hq hsize K hK dir z hz s)
    (fun p => rotatedRun_bij hT p.1 p.2 K dir z s)
    (Vrun_source_fixed hq K dir z hs)
  simp only [restricted_vVector hq K dir z hs (dir s)] at hh
  have hc := ICO.MHHaarStepConstants.one_step_loss_bound q R hR
  rw [←hd] at hc
  linarith

theorem actual_prefix_overlap {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q+1≤T) (hsize : q<Fintype.card A) (hsmall : 2*q≤Fintype.card A)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (hz : ‖WithLp.toLp 2 z‖=1) (R : ℝ) (hR : 1≤R)
    (hd : (Fintype.card A:ℝ)=R^8) :
    ∀s≤q,1-35*(q:ℝ)^2/R^2≤∫p,(⟪wVector hT K dir z s p,
      act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
        (1:CMatrix (μ s))) (vVector hq K dir z s)⟫_ℂ).re ∂rotationMeasure A := by
  let a := fun s => ∫p,(⟪wVector hT K dir z s p,
    act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
      (1:CMatrix (μ s))) (vVector hq K dir z s)⟫_ℂ).re ∂rotationMeasure A
  have h0 : 1≤a 0 := by
    have hp (p : Rotations A) : (⟪wVector hT K dir z 0 p,
        act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
          (1:CMatrix (μ 0))) (vVector hq K dir z 0)⟫_ℂ).re=1 := by
      change (⟪WithLp.toLp 2 (initial T z),
        act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
          (1:CMatrix (μ 0))) (WithLp.toLp 2 (initial T z))⟫_ℂ).re=1
      have hf := congrArg (WithLp.toLp 2) (empty_rotation_fixed p.1 p.2 T z)
      change act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
        (1:CMatrix (μ 0))) (WithLp.toLp 2 (initial T z))=WithLp.toLp 2 (initial T z) at hf
      rw [hf]
      have hi : (⟪WithLp.toLp 2 (initial T z),WithLp.toLp 2 (initial T z)⟫_ℂ).re=
          ‖WithLp.toLp 2 (initial T z)‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) _
      rw [hi,initial_norm,hz]
      norm_num
    simp only [a,hp,integral_const,probReal_univ,one_smul,le_refl]
  have hs : ∀s<q,a s-35*(q:ℝ)/R^2≤a (s+1) := by
    intro s hs
    have he (p : Rotations A) :
        (⟪wVector hT K dir z (s+1) p,
          act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
            (1:CMatrix (μ (s+1)))) (vVector hq K dir z (s+1))⟫_ℂ).re=
        (⟪act (Matrix.kronecker (rotatedW hT p.1 p.2 (dir s)) (1:CMatrix (μ s)))
          (wVector hT K dir z s p),
          act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix (μ s)))
            (act (Matrix.kronecker (Vchoice hq (dir s)) (1:CMatrix (μ s)))
              (vVector hq K dir z s))⟫_ℂ).re := by
      have hh := ICO.MHIsometricRecordingProtocol.known_isometry_overlap (publicIsometry T K hK s)
        (act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix (μ s))))
        (act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T)) (1:CMatrix (μ (s+1)))))
        (public_rotation_intertwining p.1 p.2 T (K s) (hK s))
        (act (Matrix.kronecker (rotatedW hT p.1 p.2 (dir s)) (1:CMatrix (μ s)))
          (wVector hT K dir z s p))
        (act (Matrix.kronecker (Vchoice hq (dir s)) (1:CMatrix (μ s)))
          (vVector hq K dir z s))
      exact congrArg Complex.re hh
    have hh := actual_local_loss hT hq hsize hsmall K hK dir z hz.le s (by omega) R hR hd
    simpa only [a,he] using hh
  intro s hs'
  have hh := ICO.MHFixedBudgetOverlap.constant_loss_recurrence a q (35*(q:ℝ)/R^2) h0 hs s hs'
  have hm := mul_le_mul_of_nonneg_right (show (s:ℝ)≤q by exact_mod_cast hs')
    (show 0≤35*(q:ℝ)/R^2 by positivity)
  have hp : (q:ℝ)*(35*(q:ℝ)/R^2)=35*(q:ℝ)^2/R^2 := by ring
  rw [hp] at hm
  dsimp only [a] at hh
  linarith

theorem actual_mean_distance {q T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (hq : q+1≤T) (hsize : q<Fintype.card A) (hsmall : 2*q≤Fintype.card A)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (dir : ℕ→Bool) (z : A×μ 0→ℂ)
    (hz : ‖WithLp.toLp 2 z‖=1) (R : ℝ) (hR : 1≤R)
    (hd : (Fintype.card A:ℝ)=R^8) {s : ℕ} (hs : s≤q) :
    (∫p,‖wVector hT K dir z s p-
      act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
        (1:CMatrix (μ s))) (vVector hq K dir z s)‖ ∂rotationMeasure A)≤9*(q:ℝ)/R := by
  let y := fun p : Rotations A =>
    act (Matrix.kronecker (fockQ p.1 p.2 T:CMatrix (InputCutoff (α:=A) T))
      (1:CMatrix (μ s))) (vVector hq K dir z s)
  have hx := wVector_continuous hT K hK dir z s
  have hy : Continuous y := (recordAction_continuous T (μ s)).clm_apply continuous_const
  have hn : ∀p,‖y p‖≤1 := by
    intro p
    change ‖act (memoryUnitary (M:=μ s) (fockQ p.1 p.2 T):CMatrix (InputCutoff (α:=A) T×μ s))
      (vVector hq K dir z s)‖≤1
    rw [ICO.MHOverlapStep.unitary_act_norm]
    exact vVector_norm hq hsize K hK dir z hz.le s
  exact ICO.MHAveragedHybrid.mean_vector_distance_le (wVector hT K dir z s) y
    (wVector_norm hT K hK dir z hz.le s) hn
    ((Complex.continuous_re.comp (hx.inner hy)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hx.sub hy).norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((hx.sub hy).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    q R (lt_of_lt_of_le zero_lt_one hR) (actual_prefix_overlap hT hq hsize hsmall K hK dir z hz R hR hd s hs)

#print axioms actual_mean_distance
#print axioms actual_prefix_overlap
#print axioms actual_local_loss
#print axioms restricted_vVector
end
end ICO.MHActualRecordingOverlap

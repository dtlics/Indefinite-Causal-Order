import ICO.MHDecompressionHybrid
import ICO.MHRectangularMeanDefect

/-! The actual frequency-oracle versus decompressed recording hybrid.  The
only analytic input is a uniform prefix recording/reference overlap. -/
namespace ICO.MHDecompressionHybridMean
open Matrix QIT MeasureTheory ICO.MHDecompressionHybrid ICO.MHDecompressionKnown
  ICO.MHDecompressionStep ICO.MHDecompressionNorm ICO.MHDecompressionErasure
  ICO.MHDecompressionInitial ICO.MHRectangularAction ICO.MHFockSpace ICO.MHBoundedRecording
  ICO.MHDomainMeanProduct ICO.MHRotatedTrajectory ICO.MHTernaryCompression
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 512
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ : ℕ→Type} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

abbrev Rotation (A : Type) [Fintype A] [DecidableEq A] :=
  Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ

theorem continuous_rectAct {Ω H E : Type*} [TopologicalSpace Ω]
    [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (M : Ω→Matrix E H ℂ) (v : Ω→EuclideanSpace ℂ H)
    (hM : Continuous M) (hv : Continuous v) : Continuous (fun ω => rectAct (M ω) (v ω)) := by
  have hraw : Continuous (fun ω => (fun i => v ω i)) := by
    apply continuous_pi
    intro i
    exact (PiLp.continuous_apply 2 (fun _ : H => ℂ) i).comp hv
  exact (PiLp.continuous_toLp 2 _).comp (hM.matrix_mulVec hraw)

def decompressedVector {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (t:ℕ) (p : Rotation A) : EuclideanSpace ℂ ((A×Environment A)×μ t) :=
  rectAct (memoryD hT (μ t)) (recordingVector hT K dir z t p)

def localError {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (t:ℕ) (p : Rotation A) : EuclideanSpace ℂ ((A×Environment A)×μ (t+1)) :=
  rectAct (physicalStep (K t) p.1 p.2 (dir t)) (decompressedVector hT K dir z t p)-
    decompressedVector hT K dir z (t+1) p

theorem decompressedVector_continuous {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (t:ℕ) : Continuous (decompressedVector hT K dir z t) :=
  continuous_rectAct _ _ continuous_const (recordingVector_continuous hT K dir z t)

theorem decompressedVector_norm {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (hK : ∀t,(K t).conjTranspose*K t=1)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (hz : ‖WithLp.toLp 2 z‖≤1) (t:ℕ) (p : Rotation A) :
    ‖decompressedVector hT K dir z t p‖≤1 := by
  rw [decompressedVector,decompression_norm hT _ (recordingVector_bij hT K dir z t p)]
  exact recordingVector_norm hT K hK dir z hz t p

theorem localError_continuous {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (t:ℕ) : Continuous (localError hT K dir z t) :=
  (continuous_rectAct _ _ (physicalStep_continuous (K t) (dir t))
    (decompressedVector_continuous hT K dir z t)).sub
    (decompressedVector_continuous hT K dir z (t+1))

theorem localError_square {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (hK : ∀t,(K t).conjTranspose*K t=1)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (hz : ‖WithLp.toLp 2 z‖≤1) (t:ℕ) (p : Rotation A) :
    ‖localError hT K dir z t p‖^2≤1-‖recordingVector hT K dir z (t+1) p‖^2 := by
  unfold localError decompressedVector
  rw [recordingVector_next]
  exact step_defect hT (K t) (hK t) p.1 p.2 (dir t) _
    (recordingVector_bij hT K dir z t p) (recordingVector_norm hT K hK dir z hz t p)

theorem mean_localError {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (hK : ∀t,(K t).conjTranspose*K t=1)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (hz : ‖WithLp.toLp 2 z‖≤1) (t q:ℕ) (R:ℝ) (hR:0<R)
    (Y : Rotation A→EuclideanSpace ℂ (InputCutoff (α:=A) T×μ (t+1)))
    (hY : Continuous Y) (hnY : ∀p,‖Y p‖≤1)
    (hoverlap : 1-35*(q:ℝ)^2/R^2≤∫ p,
      (⟪recordingVector hT K dir z (t+1) p,Y p⟫_ℂ).re ∂rotationMeasure A) :
    (∫ p, ‖localError hT K dir z t p‖ ∂rotationMeasure A)≤9*(q:ℝ)/R := by
  have hx := recordingVector_continuous hT K dir z (t+1)
  have he := localError_continuous hT K dir z t
  exact MHRectangularMeanDefect.mean_step_defect _ _ _
    (recordingVector_norm hT K hK dir z hz (t+1)) hnY
    (localError_square hT K hK dir z hz t)
    ((Complex.continuous_re.comp (hx.inner hY)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (he.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((he.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) q R hR hoverlap

theorem error_step {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (hK : ∀t,(K t).conjTranspose*K t=1)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (t:ℕ) (p : Rotation A) :
    ‖frequencyVector K dir z (t+1) p-decompressedVector hT K dir z (t+1) p‖≤
      ‖frequencyVector K dir z t p-decompressedVector hT K dir z t p‖+‖localError hT K dir z t p‖ := by
  rw [frequencyVector_next]
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (rectAct (physicalStep (K t) p.1 p.2 (dir t)) (frequencyVector K dir z t p))
    (rectAct (physicalStep (K t) p.1 p.2 (dir t)) (decompressedVector hT K dir z t p))
    (decompressedVector hT K dir z (t+1) p)
  rw [← map_sub,rectAct_norm _ (physicalStep_isometry _ (hK t) _ _ _)] at ht
  exact ht

theorem error_initial {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (dir : ℕ→Bool)
    (z : A×μ 0→ℂ) (p : Rotation A) : frequencyVector K dir z 0 p=decompressedVector hT K dir z 0 p := by
  exact congrArg (WithLp.toLp 2) (decompression_initial hT z).symm

theorem mean_error_bound {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (K : (t:ℕ)→Matrix (A×μ (t+1)) (A×μ t) ℂ) (hK : ∀t,(K t).conjTranspose*K t=1)
    (dir : ℕ→Bool) (z : A×μ 0→ℂ) (hz : ‖WithLp.toLp 2 z‖≤1) (q:ℕ) (R:ℝ) (hR:0<R)
    (Y : (s:ℕ)→Rotation A→EuclideanSpace ℂ (InputCutoff (α:=A) T×μ s))
    (hY : ∀s,Continuous (Y s)) (hnY : ∀s p,‖Y s p‖≤1)
    (hoverlap : ∀s≤q,1-35*(q:ℝ)^2/R^2≤∫ p,
      (⟪recordingVector hT K dir z s p,Y s p⟫_ℂ).re ∂rotationMeasure A) :
    (∫ p, ‖frequencyVector K dir z q p-decompressedVector hT K dir z q p‖ ∂rotationMeasure A)≤9*(q:ℝ)^2/R := by
  let a := fun t => ∫ p, ‖frequencyVector K dir z t p-decompressedVector hT K dir z t p‖ ∂rotationMeasure A
  have hi t : Integrable (fun p => ‖frequencyVector K dir z t p-decompressedVector hT K dir z t p‖) (rotationMeasure A) :=
    ((frequencyVector_continuous K dir z t).sub (decompressedVector_continuous hT K dir z t)).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h0 : a 0=0 := by simp only [a,error_initial hT K dir z,sub_self,norm_zero,integral_zero]
  have hs : ∀t<q,a (t+1)≤a t+9*(q:ℝ)/R := by
    intro t ht
    have he := (localError_continuous hT K dir z t).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ:=rotationMeasure A)
    have hh := integral_mono (hi (t+1)) ((hi t).add he) (error_step hT K hK dir z t)
    simp only [Pi.add_apply] at hh
    rw [integral_add (hi t) he] at hh
    exact hh.trans (add_le_add le_rfl (mean_localError hT K hK dir z hz t q R hR (Y (t+1)) (hY _) (hnY _) (hoverlap _ (by omega))))
  have hb : ∀t≤q,a t≤(t:ℝ)*(9*(q:ℝ)/R) := by
    intro t
    induction t with
    | zero => intro _; simp [h0]
    | succ t ih =>
      intro ht
      have htt : t<q := by omega
      have hh := hs t htt
      have hh' := ih (by omega)
      simp only [Nat.cast_add,Nat.cast_one]
      nlinarith
  calc
    _ ≤ (q:ℝ)*(9*(q:ℝ)/R) := hb q le_rfl
    _ = _ := by ring

#print axioms mean_error_bound
end
end ICO.MHDecompressionHybridMean
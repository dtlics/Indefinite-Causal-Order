import ICO.MHMeanQueryStep
import ICO.MHIsometricHybrid
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Pure-state evolution with varying public/private memory spaces. Known
operations are literal rectangular isometries and oracle steps are contractions. -/
namespace ICO.MHIsometricRecordingProtocol
open Matrix QIT MeasureTheory
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {E : ℕ→Type*} [∀ t,Fintype (E t)]

def run (K : (t:ℕ)→EuclideanSpace ℂ (E t)→ₗᵢ[ℂ]EuclideanSpace ℂ (E (t+1)))
    (O : (t:ℕ)→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (z : EuclideanSpace ℂ (E 0)) : (t:ℕ)→EuclideanSpace ℂ (E t)
  | 0 => z
  | t+1 => K t (O t (run K O z t))

theorem run_norm_le
    (K : (t:ℕ)→EuclideanSpace ℂ (E t)→ₗᵢ[ℂ]EuclideanSpace ℂ (E (t+1)))
    (O : (t:ℕ)→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (z : EuclideanSpace ℂ (E 0)) (hO : ∀ t, ‖O t‖≤1) (hz : ‖z‖≤1) (t:ℕ) :
    ‖run K O z t‖≤1 := by
  induction t with
  | zero => exact hz
  | succ t ih =>
    change ‖K t (O t (run K O z t))‖≤1
    rw [(K t).norm_map]
    have hh := (O t).le_opNorm (run K O z t)
    have hm := mul_le_mul (hO t) ih (norm_nonneg _) (by norm_num)
    exact hh.trans (by simpa using hm)

variable {Ω : Type*} [TopologicalSpace Ω]

theorem continuous_run
    (K : (t:ℕ)→EuclideanSpace ℂ (E t)→ₗᵢ[ℂ]EuclideanSpace ℂ (E (t+1)))
    (O : (t:ℕ)→Ω→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (z : EuclideanSpace ℂ (E 0)) (hO : ∀ t, Continuous (O t)) (t:ℕ) :
    Continuous (fun ω => run K (fun t => O t ω) z t) := by
  induction t with
  | zero => exact continuous_const
  | succ t ih =>
    change Continuous (fun ω => K t (O t ω (run K (fun s => O s ω) z t)))
    exact (K t).continuous.comp ((hO t).clm_apply ih)

theorem known_isometry_overlap
    {H F : Type*} [Fintype H] [Fintype F]
    (K : EuclideanSpace ℂ H→ₗᵢ[ℂ]EuclideanSpace ℂ F)
    (Q : EuclideanSpace ℂ H→L[ℂ]EuclideanSpace ℂ H)
    (Q' : EuclideanSpace ℂ F→L[ℂ]EuclideanSpace ℂ F)
    (hQ : ∀ z, Q' (K z)=K (Q z)) (x y : EuclideanSpace ℂ H) :
    ⟪K x,Q' (K y)⟫_ℂ=⟪x,Q y⟫_ℂ := by
  rw [hQ,K.inner_map_map]

variable [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

theorem run_overlap_integrable
    (K : (t:ℕ)→EuclideanSpace ℂ (E t)→ₗᵢ[ℂ]EuclideanSpace ℂ (E (t+1)))
    (O : (t:ℕ)→Ω→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (V : (t:ℕ)→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (Q : (t:ℕ)→Ω→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (z : EuclideanSpace ℂ (E 0)) (hO : ∀ t, Continuous (O t))
    (hQ : ∀ t, Continuous (Q t)) (t:ℕ) :
    Integrable (fun ω =>
      (⟪run K (fun s => O s ω) z t,Q t ω (run K V z t)⟫_ℂ).re) μ := by
  exact (Complex.continuous_re.comp ((continuous_run K O z hO t).inner
    ((hQ t).clm_apply continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem run_distance_integrable
    (K : (t:ℕ)→EuclideanSpace ℂ (E t)→ₗᵢ[ℂ]EuclideanSpace ℂ (E (t+1)))
    (O V : (t:ℕ)→Ω→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (z : EuclideanSpace ℂ (E 0)) (hO : ∀ t, Continuous (O t))
    (hV : ∀ t, Continuous (V t)) (t:ℕ) :
    Integrable (fun ω => ‖run K (fun s => O s ω) z t-
      run K (fun s => V s ω) z t‖) μ := by
  exact (((continuous_run K O z hO t).sub (continuous_run K V z hV t)).norm).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

#print axioms run_norm_le
#print axioms run_overlap_integrable
#print axioms known_isometry_overlap
end
end ICO.MHIsometricRecordingProtocol

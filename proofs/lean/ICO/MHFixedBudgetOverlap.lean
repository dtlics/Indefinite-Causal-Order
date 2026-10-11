import ICO.MHIsometricRecordingProtocol

/-! Fixed recording cutoff calculus: a budget-q local loss yields the same
uniform prefix overlap bound and the published final 9q/R vector estimate. -/
namespace ICO.MHFixedBudgetOverlap
open Matrix QIT MeasureTheory ICO.MHProtocolOverlap ICO.MHOverlapStep
  ICO.MHIsometricRecordingProtocol ICO.MHAveragedHybrid
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000

theorem constant_loss_recurrence (a : ℕ→ℝ) (q : ℕ) (δ : ℝ)
    (hinit : 1≤a 0) (hstep : ∀ t<q, a t-δ≤a (t+1)) :
    ∀ s≤q, 1-(s:ℝ)*δ≤a s := by
  intro s
  induction s with
  | zero => intro _; simpa using hinit
  | succ s ih =>
    intro hs
    have hs' : s<q := by omega
    have hh := hstep s hs'
    have hi := ih (by omega)
    simp only [Nat.cast_add,Nat.cast_one]
    linarith

variable {E : ℕ→Type*} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem run_prefix_overlap
    (K : (t:ℕ)→EuclideanSpace ℂ (E t)→ₗᵢ[ℂ]EuclideanSpace ℂ (E (t+1)))
    (O : (t:ℕ)→Ω→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (V : (t:ℕ)→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (Q : (t:ℕ)→Ω→Matrix.unitaryGroup (E t) ℂ)
    (z : EuclideanSpace ℂ (E 0)) (hz : ‖z‖=1)
    (q : ℕ) (R : ℝ) (hR : 0<R)
    (hinit : ∀ ω, act (Q 0 ω : CMatrix (E 0)) z=z)
    (hcomm : ∀ t<q, ∀ ω w,
      act (Q (t+1) ω : CMatrix (E (t+1))) (K t w)=
        K t (act (Q t ω : CMatrix (E t)) w))
    (hlocal : ∀ t<q,
      (∫ ω, (⟪run K (fun s => O s ω) z t,
        act (Q t ω : CMatrix (E t)) (run K V z t)⟫_ℂ).re ∂μ)-35*(q:ℝ)/R^2 ≤
      ∫ ω, (⟪O t ω (run K (fun s => O s ω) z t),
        act (Q t ω : CMatrix (E t)) (V t (run K V z t))⟫_ℂ).re ∂μ) :
    ∀ s≤q, 1-35*(q:ℝ)^2/R^2 ≤
      ∫ ω, (⟪run K (fun t => O t ω) z s,
        act (Q s ω : CMatrix (E s)) (run K V z s)⟫_ℂ).re ∂μ := by
  let a := fun t => ∫ ω, (⟪run K (fun s => O s ω) z t,
    act (Q t ω : CMatrix (E t)) (run K V z t)⟫_ℂ).re ∂μ
  have h0 : 1≤a 0 := by
    have he : ∀ ω, (⟪z,act (Q 0 ω : CMatrix (E 0)) z⟫_ℂ).re=1 := by
      intro ω
      rw [hinit]
      have hh : (⟪z,z⟫_ℂ).re=‖z‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) z
      rw [hh,hz]
      norm_num
    simp only [a,run,he,integral_const,probReal_univ,smul_eq_mul,one_mul,le_refl]
  have hstep : ∀ t<q, a t-35*(q:ℝ)/R^2≤a (t+1) := by
    intro t ht
    have hn (ω : Ω) :
        ⟪run K (fun s => O s ω) z (t+1),
          act (Q (t+1) ω : CMatrix (E (t+1))) (run K V z (t+1))⟫_ℂ=
        ⟪O t ω (run K (fun s => O s ω) z t),
          act (Q t ω : CMatrix (E t)) (V t (run K V z t))⟫_ℂ := by
      change ⟪K t _,act (Q (t+1) ω : CMatrix (E (t+1))) (K t _)⟫_ℂ=_
      exact known_isometry_overlap (K t) (act (Q t ω : CMatrix (E t)))
        (act (Q (t+1) ω : CMatrix (E (t+1)))) (hcomm t ht ω) _ _
    simpa only [a,hn] using hlocal t ht
  intro s hs
  have hh := constant_loss_recurrence a q (35*(q:ℝ)/R^2) h0 hstep s hs
  have hcast : (s:ℝ)≤q := by exact_mod_cast hs
  have hδ : 0≤35*(q:ℝ)/R^2 := by positivity
  have hm := mul_le_mul_of_nonneg_right hcast hδ
  dsimp only [a] at hh
  have he : (q:ℝ)*(35*(q:ℝ)/R^2)=35*(q:ℝ)^2/R^2 := by ring
  rw [he] at hm
  linarith

variable [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω]

theorem run_mean_distance
    (K : (t:ℕ)→EuclideanSpace ℂ (E t)→ₗᵢ[ℂ]EuclideanSpace ℂ (E (t+1)))
    (O : (t:ℕ)→Ω→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (V : (t:ℕ)→EuclideanSpace ℂ (E t)→L[ℂ]EuclideanSpace ℂ (E t))
    (Q : (t:ℕ)→Ω→Matrix.unitaryGroup (E t) ℂ)
    (z : EuclideanSpace ℂ (E 0)) (hz : ‖z‖≤1)
    (hnO : ∀ t ω, ‖O t ω‖≤1) (hnV : ∀ t, ‖V t‖≤1)
    (hO : ∀ t, Continuous (O t))
    (hQ : ∀ t, Continuous (fun ω => act (Q t ω : CMatrix (E t))))
    (q s : ℕ) (R : ℝ) (hR : 0<R)
    (hoverlap : 1-35*(q:ℝ)^2/R^2≤∫ ω,
      (⟪run K (fun t => O t ω) z s,
        act (Q s ω : CMatrix (E s)) (run K V z s)⟫_ℂ).re ∂μ) :
    (∫ ω, ‖run K (fun t => O t ω) z s-
      act (Q s ω : CMatrix (E s)) (run K V z s)‖ ∂μ)≤9*(q:ℝ)/R := by
  let x := fun ω => run K (fun t => O t ω) z s
  let y := fun ω => act (Q s ω : CMatrix (E s)) (run K V z s)
  have hx : Continuous x := continuous_run K O z hO s
  have hy : Continuous y := (hQ s).clm_apply continuous_const
  apply mean_vector_distance_le x y
    (fun ω => run_norm_le K _ z (fun t => hnO t ω) hz s)
    (fun ω => by
      change ‖act (Q s ω : CMatrix (E s)) (run K V z s)‖≤1
      rw [unitary_act_norm]
      exact run_norm_le K V z hnV hz s)
  · exact (Complex.continuous_re.comp (hx.inner hy)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hx.sub hy).norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((hx.sub hy).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hR
  · exact hoverlap

#print axioms run_prefix_overlap
#print axioms run_mean_distance
end
end ICO.MHFixedBudgetOverlap

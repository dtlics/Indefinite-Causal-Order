import ICO.MHProfileTurnFock

/-! The actual Haar domain-loss operator is bounded uniformly on all coherent
record sectors up to a query budget. -/
namespace ICO.MHCoherentDomainTwirl
open Matrix QIT MeasureTheory ICO.MHWordProfiles ICO.MHWordRotation ICO.MHProfileTwirl
  ICO.MHProfileTurnFock ICO.MHProfileBlocks ICO.MHFockSpace ICO.MHFockProjection
  ICO.MHWProfileLeft ICO.MHActualDomainTwirl ICO.MHBlockNorm ICO.RecordingCopyIdentity
  ICO.MHWordDomainTwirl ICO.MHBoundedRecording ICO.MHWordDistinct
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
local instance cmContinuousENorm {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

local instance familyContinuousENorm (t : ℕ) :
    ContinuousENorm (∀ s : Lengths t, CMatrix (ProfileBasis A s.val.1.val s.val.2.val)) :=
  SeminormedAddGroup.toContinuousENorm

def blocksCLM (t : ℕ) :
    (∀ s : Lengths t, CMatrix (ProfileBasis A s.val.1.val s.val.2.val)) →L[ℝ]
      CMatrix (InputCutoff (α := A) t) :=
  ({ toFun := profileBlocks t
     map_add' := by intros; ext o i; simp [profileBlocks,Matrix.blockDiagonal'_add]
     map_smul' := by intros; ext o i; simp [profileBlocks,Matrix.blockDiagonal'_smul] } :
    (∀ s : Lengths t, CMatrix (ProfileBasis A s.val.1.val s.val.2.val)) →ₗ[ℝ]
      CMatrix (InputCutoff (α := A) t)).toContinuousLinearMap

theorem integral_profileBlocks {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    (t : ℕ) (F : Ω → ∀ s : Lengths t, CMatrix (ProfileBasis A s.val.1.val s.val.2.val))
    (hF : Integrable F μ) :
    (∫ ω, profileBlocks t (F ω) ∂μ)=profileBlocks t (fun s => ∫ ω, F ω s ∂μ) := by
  have hh := (blocksCLM (A := A) t).integral_comp_comm hF
  change (∫ ω, profileBlocks t (F ω) ∂μ)=profileBlocks t (∫ ω, F ω ∂μ) at hh
  rw [hh]
  congr 1
  funext s
  exact ((ContinuousLinearMap.proj s :
    (∀ s : Lengths t, CMatrix (ProfileBasis A s.val.1.val s.val.2.val)) →L[ℝ]
      CMatrix (ProfileBasis A s.val.1.val s.val.2.val)).integral_comp_comm hF).symm

theorem profileTurn_continuous (l r : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      (profileTurn p.1 p.2 l r : CMatrix (ProfileBasis A l r))) := by
  have he (C D : Matrix.unitaryGroup A ℂ) :
      (profileTurn C D l r : CMatrix (ProfileBasis A l r))=
        (wordEmbedding l r).conjTranspose*(turn (rightSlots l r) C D : CMatrix (WordBasis A (Fin l⊕Fin r)))*wordEmbedding l r := by
    rw [Matrix.mul_assoc,turn_embedding,← Matrix.mul_assoc,wordEmbedding_gram,Matrix.one_mul]
  simp_rw [he]
  exact (continuous_const.matrix_mul (turn_continuous (rightSlots l r))).matrix_mul continuous_const

def sectorConjugation {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ)
    (s : Lengths t) : CMatrix (ProfileBasis A s.val.1.val s.val.2.val) :=
  (profileTurn p.1 p.2 s.val.1.val s.val.2.val : CMatrix (ProfileBasis A s.val.1.val s.val.2.val)).conjTranspose*
    sectorMissing hT (s.property.trans ht)*
      (profileTurn p.1 p.2 s.val.1.val s.val.2.val : CMatrix (ProfileBasis A s.val.1.val s.val.2.val))

theorem sectorConjugation_continuous {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T) :
    Continuous (sectorConjugation hT ht) := by
  apply continuous_pi
  intro s
  exact ((profileTurn_continuous s.val.1.val s.val.2.val).matrix_conjTranspose.matrix_mul
    continuous_const).matrix_mul (profileTurn_continuous s.val.1.val s.val.2.val)

theorem mean_actual_profileBlocks {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T) :
    (∫ D, ∫ C, (basisEmbedding (inputEmbed (α := A) ht)).conjTranspose*
      ((actualTurn C D T).conjTranspose*missingMatrix hT*actualTurn C D T)*
        basisEmbedding (inputEmbed ht)
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) =
    profileBlocks t (fun s : Lengths t =>
      profileTwirl s.val.1.val s.val.2.val (sectorMissing hT (s.property.trans ht))) := by
  simp_rw [compressed_missing_conjugation]
  change (∫ D, ∫ C, profileBlocks t (sectorConjugation hT ht (C,D))
    ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A))=_
  have hi (D : Matrix.unitaryGroup A ℂ) : Integrable (fun C => sectorConjugation hT ht (C,D))
      (unitaryHaarMeasure (a := A)) :=
    ((sectorConjugation_continuous hT ht).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [integral_profileBlocks t _ (hi _)]
  have hc : Continuous (fun D : Matrix.unitaryGroup A ℂ =>
      fun s : Lengths t => ∫ C, sectorConjugation hT ht (C,D) s ∂unitaryHaarMeasure (a := A)) := by
    apply continuous_pi
    intro s
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous (μ := unitaryHaarMeasure (a := A))
        (f := fun D C => sectorConjugation hT ht (C,D) s)
        (((continuous_apply s).comp (sectorConjugation_continuous hT ht)).comp
          (continuous_snd.prodMk continuous_fst)) isCompact_univ
  rw [integral_profileBlocks t _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  rfl

theorem profileBlocks_norm_le (t : ℕ)
    (F : ∀ s : Lengths t, CMatrix (ProfileBasis A s.val.1.val s.val.2.val))
    (β : ℝ) (hβ : 0≤β) (hF : ∀ s, ‖F s‖≤β) : ‖profileBlocks t F‖≤β := by
  apply (reindex_norm_le _ (profileFockEquiv t)).trans
  have hs : Real.sqrt (β^2)=β := by rw [Real.sqrt_sq_eq_abs,abs_of_nonneg hβ]
  rw [← hs]
  apply blockDiagonal'_norm_le _ _ (sq_nonneg β)
  intro s
  rw [hs]
  exact hF s

theorem six_loss_mono {x y d : ℝ} (hx : 0≤x) (hxy : x≤y) (hd : 0<d) :
    6*x*Real.sqrt (x/d)≤6*y*Real.sqrt (y/d) := by
  apply mul_le_mul
  · linarith
  · exact Real.sqrt_le_sqrt ((div_le_div_iff_of_pos_right hd).mpr hxy)
  · exact Real.sqrt_nonneg _
  · linarith

theorem actual_mean_domain_norm_le {t T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (ht : t≤T)
    (hsize : t<Fintype.card A) (hsmall : 2*t≤Fintype.card A) :
    ‖∫ D, ∫ C, (basisEmbedding (inputEmbed (α := A) ht)).conjTranspose*
      ((actualTurn C D T).conjTranspose*missingMatrix hT*actualTurn C D T)*
        basisEmbedding (inputEmbed ht)
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)‖ ≤
        6*(t : ℝ)*Real.sqrt ((t : ℝ)/Fintype.card A) := by
  rw [mean_actual_profileBlocks]
  apply profileBlocks_norm_le t _ _ (by positivity)
  intro s
  apply (actual_sector_mean_norm_le hT (s.property.trans ht)
    (lt_of_le_of_lt s.property hsize) (by omega)).trans
  apply six_loss_mono (by positivity) _ (by exact_mod_cast Fintype.card_pos (α := A))
  exact_mod_cast s.property

#print axioms actual_mean_domain_norm_le
end
end ICO.MHCoherentDomainTwirl
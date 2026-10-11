import ICO.MHWordTwirl
import ICO.MHWordDomain

namespace ICO.MHWordDomainTwirl
open Matrix QIT MeasureTheory ICO.MHWordDistinct ICO.MHWordRotation ICO.MHWordTwirl
  ICO.MHWordDomain
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A J : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype J] [DecidableEq J]

local instance cmContinuousENorm {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

local instance matrixNonUnitalCStar (n : Type) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance matrixCStar (n : Type) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩

theorem matrix_integral_mono {H Ω : Type} [Fintype H] [DecidableEq H]
    [MeasurableSpace Ω] {μ : Measure Ω} (F G : Ω → CMatrix H)
    (hF : Integrable F μ) (hG : Integrable G μ) (h : ∀ ω, F ω≤G ω) :
    (∫ ω, F ω ∂μ)≤∫ ω, G ω ∂μ := integral_mono hF hG h

theorem turn_continuous (R : Finset J) :
    Continuous (fun p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      (turn R p.1 p.2 : CMatrix (WordBasis A J))) := by
  apply continuous_pi
  intro o
  apply continuous_pi
  intro i
  change Continuous (fun p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
    (p.1 : CMatrix A) o.1 i.1 * ∏ j, (recordUnitary R p.1 p.2 j : CMatrix (A × A)) (o.2 j) (i.2 j))
  apply Continuous.mul
  · exact (continuous_subtype_val.comp continuous_fst).matrix_elem o.1 i.1
  · apply continuous_finset_prod
    intro j _
    by_cases hj : j ∈ R
    · simp only [recordUnitary,if_pos hj,ICO.MHRightCovariance.inverse_rightEdgeUnitary,
        Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.map_apply,Matrix.conjTranspose_apply]
      exact ((continuous_subtype_val.comp continuous_fst).matrix_elem (o.2 j).1 (i.2 j).1).star.mul
        (((continuous_subtype_val.comp continuous_snd).matrix_elem (i.2 j).2 (o.2 j).2).star)
    · simp only [recordUnitary,if_neg hj,ICO.MHCreationCovariance.leftEdgeUnitary_apply]
      exact ((continuous_subtype_val.comp continuous_fst).matrix_elem (o.2 j).1 (i.2 j).1).mul
        ((continuous_subtype_val.comp continuous_snd).matrix_elem (i.2 j).2 (o.2 j).2)

theorem conjugation_continuous (R : Finset J) (D : Matrix.unitaryGroup A ℂ)
    (M : CMatrix (WordBasis A J)) :
    Continuous (fun C : Matrix.unitaryGroup A ℂ =>
      (turn R C D : CMatrix (WordBasis A J)).conjTranspose*M*(turn R C D : CMatrix (WordBasis A J))) := by
  have ht : Continuous (fun C : Matrix.unitaryGroup A ℂ =>
      (turn R C D : CMatrix (WordBasis A J))) :=
    (turn_continuous R).comp (continuous_id.prodMk continuous_const)
  exact (ht.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul ht

theorem conjugation_integrable (R : Finset J) (D : Matrix.unitaryGroup A ℂ)
    (M : CMatrix (WordBasis A J)) :
    Integrable (fun C : Matrix.unitaryGroup A ℂ =>
      (turn R C D : CMatrix (WordBasis A J)).conjTranspose*M*(turn R C D : CMatrix (WordBasis A J)))
      (unitaryHaarMeasure (a := A)) :=
  (conjugation_continuous R D M).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def twirl (R : Finset J) (D : Matrix.unitaryGroup A ℂ) (M : CMatrix (WordBasis A J)) :
    CMatrix (WordBasis A J) := ∫ C, (turn R C D : CMatrix (WordBasis A J)).conjTranspose*M*
      (turn R C D : CMatrix (WordBasis A J)) ∂unitaryHaarMeasure (a := A)

theorem twirl_add (R : Finset J) (D : Matrix.unitaryGroup A ℂ) (M N : CMatrix (WordBasis A J)) :
    twirl R D (M+N)=twirl R D M+twirl R D N := by
  simp only [twirl,Matrix.mul_add,Matrix.add_mul]
  exact integral_add (conjugation_integrable R D M) (conjugation_integrable R D N)

theorem twirl_smul (R : Finset J) (D : Matrix.unitaryGroup A ℂ) (c : ℝ)
    (M : CMatrix (WordBasis A J)) : twirl R D (c•M)=c•twirl R D M := by
  simp only [twirl,Matrix.mul_smul,Matrix.smul_mul,integral_smul]

theorem twirl_sum (R : Finset J) (D : Matrix.unitaryGroup A ℂ) (S : Finset J)
    (M : J → CMatrix (WordBasis A J)) : twirl R D (∑ i∈S,M i)=∑ i∈S,twirl R D (M i) := by
  simp only [twirl,Matrix.mul_sum,Matrix.sum_mul]
  exact integral_finset_sum S (fun i _ => conjugation_integrable R D (M i))

theorem twirl_one (R : Finset J) (D : Matrix.unitaryGroup A ℂ) :
    twirl R D (1 : CMatrix (WordBasis A J))=1 := by
  have he (C : Matrix.unitaryGroup A ℂ) :
      (turn R C D : CMatrix (WordBasis A J)).conjTranspose * (turn R C D : CMatrix (WordBasis A J))=1 :=
    Matrix.mem_unitaryGroup_iff'.mp (turn R C D).property
  simp only [twirl,Matrix.mul_one,he,integral_const,probReal_univ,one_smul]

theorem conjugation_mono {H : Type} [Fintype H] [DecidableEq H]
    (T M N : CMatrix H) (h : M≤N) : T.conjTranspose*M*T≤T.conjTranspose*N*T := by
  apply Matrix.le_iff.mpr
  have hh := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same T
  simpa only [Matrix.mul_sub,Matrix.sub_mul] using hh

theorem twirl_mono (R : Finset J) (D : Matrix.unitaryGroup A ℂ)
    {M N : CMatrix (WordBasis A J)} (h : M≤N) : twirl R D M≤twirl R D N :=
  matrix_integral_mono _ _ (conjugation_integrable R D M) (conjugation_integrable R D N)
    (fun C => conjugation_mono _ _ _ h)

/-- Exact fixed-sector word-domain loss, with no twirl estimate as a premise. -/
theorem domain_twirl_le (L R : Finset J) (hdis : Disjoint L R) (hcover : L∪R=Finset.univ)
    (D : Matrix.unitaryGroup A ℂ) (κ : ℝ) (hκ : 1≤κ) :
    twirl R D (distinctProjection (A := A) (J := J)-domainModel R κ) ≤
      (κ*((2*(L.card : ℝ)+R.card)/((Fintype.card A : ℝ)+1) +
        2*(R.card : ℝ)*Real.sqrt ((Fintype.card J : ℝ)/Fintype.card A))) •
          (1 : CMatrix (WordBasis A J)) := by
  apply (twirl_mono R D (domain_loss_operator_bound L R hdis hcover κ hκ)).trans
  rw [twirl_smul,twirl_add,twirl_add,twirl_sum,twirl_sum,twirl_smul,twirl_one]
  have hl : (∑ i∈L,twirl R D (slotEquality (A := A) i)) ≤
      ∑ _i∈L,(2 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix (WordBasis A J)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact left_slot_mean_le R D i (fun hir => Finset.disjoint_left.mp hdis hi hir)
  have hr : (∑ i∈R,twirl R D (slotEquality (A := A) i-slotBell i)) ≤
      ∑ _i∈R,(1 / ((Fintype.card A : ℝ)+1)) • (1 : CMatrix (WordBasis A J)) :=
    Finset.sum_le_sum (fun i hi => right_slot_mean_le R D i hi)
  have hb := smul_le_smul_of_nonneg_left
    (add_le_add (add_le_add hl hr) (le_refl
      (((R.card : ℝ)*2*Real.sqrt ((Fintype.card J : ℝ)/Fintype.card A)) •
        (1 : CMatrix (WordBasis A J))))) (le_trans (by norm_num) hκ)
  apply hb.trans_eq
  simp only [Finset.sum_const,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,← add_smul]
  congr 1
  ring
theorem twirl_continuous (R : Finset J) (M : CMatrix (WordBasis A J)) :
    Continuous (fun D : Matrix.unitaryGroup A ℂ => twirl R D M) := by
  have ht : Continuous (fun p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      (turn R p.2 p.1 : CMatrix (WordBasis A J))) :=
    (turn_continuous R).comp (continuous_snd.prodMk continuous_fst)
  have hc := (ht.matrix_conjTranspose.matrix_mul (continuous_const (y := M))).matrix_mul ht
  simpa only [twirl,Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := unitaryHaarMeasure (a := A))
      (f := fun D C => (turn R C D : CMatrix (WordBasis A J)).conjTranspose*M*
        (turn R C D : CMatrix (WordBasis A J))) hc isCompact_univ)

theorem domain_double_twirl_le (L R : Finset J) (hdis : Disjoint L R) (hcover : L∪R=Finset.univ)
    (κ : ℝ) (hκ : 1≤κ) :
    (∫ D, twirl R D (distinctProjection (A := A) (J := J)-domainModel R κ)
      ∂unitaryHaarMeasure (a := A)) ≤
      (κ*((2*(L.card : ℝ)+R.card)/((Fintype.card A : ℝ)+1) +
        2*(R.card : ℝ)*Real.sqrt ((Fintype.card J : ℝ)/Fintype.card A))) •
          (1 : CMatrix (WordBasis A J)) := by
  have hI := (twirl_continuous R (distinctProjection-domainModel R κ)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := unitaryHaarMeasure (a := A))
  have hh := matrix_integral_mono _ _ hI (integrable_const _) (fun D => domain_twirl_le L R hdis hcover D κ hκ)
  simpa only [integral_const,probReal_univ,one_smul] using hh
#print axioms domain_double_twirl_le
#print axioms domain_twirl_le
#print axioms matrix_integral_mono
#print axioms turn_continuous
end
end ICO.MHWordDomainTwirl




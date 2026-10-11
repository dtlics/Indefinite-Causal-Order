import ICO.CausalReverse
import ICO.HaarMoments

/-!+# The Haar frame for forward and reverse unitary uses

The coordinates are grouped as `(a,x),(b,f)`. In the usual Choi convention,
the entry is the Haar average of
`conj(U[b,a]) U[f,x] U[b',a'] conj(U[f',x'])`. This grouping makes the two
Bell projections in the exact frame decomposition ordinary Kronecker factors.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix QIT ICO.CausalReverse ICO.HaarMoments
open MeasureTheory

namespace ICO.HaarFrame

noncomputable section

universe u
variable {A : Type u} [Fintype A] [DecidableEq A]

local instance frameCMatrixContinuousENorm {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

/-- The fourth Haar-entry frame in Bell-pair coordinates. -/
def haarFrame [Nonempty A] : CMatrix ((A × A) × (A × A)) :=
  fun i j => fourthMoment i.2.2 j.2.1 i.1.2 j.1.1 i.2.1 j.2.2 i.1.1 j.1.2

/-- The vector `|conj U⟩⟩ ⊗ |U⟩⟩`, after grouping Bell partners. -/
def unitaryPairVector (U : Matrix.unitaryGroup A ℂ) : (A × A) × (A × A) → ℂ :=
  fun i => star ((U : CMatrix A) i.2.1 i.1.1) * (U : CMatrix A) i.2.2 i.1.2

theorem frameIntegrand_continuous :
    Continuous (fun U : Matrix.unitaryGroup A ℂ => rankOneMatrix (unitaryPairVector U)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rankOneMatrix_apply, unitaryPairVector]
  have he (r s : A) : Continuous (fun U : Matrix.unitaryGroup A ℂ =>
      (U : CMatrix A) r s) :=
    (continuous_apply s).comp ((continuous_apply r).comp continuous_subtype_val)
  exact ((he i.2.1 i.1.1).star.mul (he i.2.2 i.1.2)).mul
    (((he j.2.1 j.1.1).star.mul (he j.2.2 j.1.2)).star)

/-- The entry-defined frame is the genuine Haar average of the rank-one
Choi-vector tests, not an abstract matrix with prescribed moments. -/
theorem haarFrame_eq_integral [Nonempty A] :
    haarFrame (A := A) =
      ∫ U : Matrix.unitaryGroup A ℂ, rankOneMatrix (unitaryPairVector U)
        ∂unitaryHaarMeasure (a := A) := by
  have hint : Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      rankOneMatrix (unitaryPairVector U)) (unitaryHaarMeasure (a := A)) :=
    frameIntegrand_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  ext i j
  rw [show (∫ U : Matrix.unitaryGroup A ℂ,
        rankOneMatrix (unitaryPairVector U) ∂unitaryHaarMeasure (a := A)) i j =
      ∫ U : Matrix.unitaryGroup A ℂ,
        rankOneMatrix (unitaryPairVector U) i j ∂unitaryHaarMeasure (a := A) by
    simpa [cMatrixEntryCLM] using
      ((cMatrixEntryCLM i j).integral_comp_comm hint).symm]
  unfold haarFrame fourthMoment
  apply integral_congr_ae
  filter_upwards [] with U
  simp only [rankOneMatrix_apply, unitaryPairVector, star_mul, star_star]
  ring

theorem identity_pair_entry (i j : A × A) :
    (1 : CMatrix (A × A)) i j = delta i.1 j.1 * delta i.2 j.2 := by
  by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
    simp [Matrix.one_apply, Prod.ext_iff, delta, h₁, h₂]

theorem bell_entry_delta [Nonempty A] (i j : A × A) :
    bellMatrix A i j = delta i.1 i.2 * delta j.1 j.2 / (Fintype.card A : ℂ) :=
  bellMatrix_entry i j

/-- Exact Haar-frame identity, proved from the two-copy Haar integral. -/
theorem haarFrame_eq_bell_complement [Nontrivial A] :
    haarFrame (A := A) =
      Matrix.kronecker (bellMatrix A) (bellMatrix A) +
        (((Fintype.card A : ℂ) ^ 2 - 1)⁻¹) •
          Matrix.kronecker (1 - bellMatrix A) (1 - bellMatrix A) := by
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : (Fintype.card A : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (ne_of_gt (Fintype.one_lt_card (α := A)))
  have hp : (Fintype.card A : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero (Fintype.card A))
  have hs : (Fintype.card A : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [show (Fintype.card A : ℂ) ^ 2 - 1 =
      ((Fintype.card A : ℂ) - 1) * ((Fintype.card A : ℂ) + 1) by ring]
    exact mul_ne_zero hm hp
  ext i j
  simp only [haarFrame, fourthMoment_delta, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply,
    identity_pair_entry, bell_entry_delta]
  simp only [delta, eq_comm]
  field_simp [hd, hs]
  <;> ring

/-- The real coefficient in the order-two Haar frame. -/
def frameBeta (A : Type u) [Fintype A] : ℝ := ((Fintype.card A : ℝ) ^ 2 - 1)⁻¹

theorem frameBeta_nonneg [Nontrivial A] : 0 ≤ frameBeta A := by
  have hd : 1 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := A)
  unfold frameBeta
  apply inv_nonneg.mpr
  nlinarith

theorem frameBeta_cast :
    (frameBeta A : ℂ) = ((Fintype.card A : ℂ) ^ 2 - 1)⁻¹ := by
  simp [frameBeta]

/-- The product of the two Bell-complement effects is bounded by the identity. -/
theorem bell_complement_tensor_le_one [Nonempty A] :
    Matrix.kronecker (1 - bellMatrix A) (1 - bellMatrix A) ≤
      (1 : CMatrix ((A × A) × (A × A))) := by
  have hc : (1 - bellMatrix A).PosSemidef := Matrix.le_iff.mp bellMatrix_le_one
  have hcle : 1 - bellMatrix A ≤ 1 := sub_le_self _ (bellMatrix_pos (A := A)).nonneg
  exact (kronecker_mono_right hc hcle).trans (kronecker_one_le_one hcle)

set_option maxHeartbeats 1000000 in
/-- The positive-operator bound used before linking the two independent Haar frames. -/
theorem haarFrame_le_bell_add_identity [Nontrivial A] :
    haarFrame (A := A) ≤
      Matrix.kronecker (bellMatrix A) (bellMatrix A) +
        (frameBeta A : ℂ) • (1 : CMatrix ((A × A) × (A × A))) := by
  rw [haarFrame_eq_bell_complement (A := A), ← frameBeta_cast (A := A)]
  have h := cMatrix_ofReal_smul_le_smul (frameBeta_nonneg (A := A))
    (bell_complement_tensor_le_one (A := A))
  rw [Matrix.le_iff] at h ⊢
  convert h using 1
  abel

end

end ICO.HaarFrame

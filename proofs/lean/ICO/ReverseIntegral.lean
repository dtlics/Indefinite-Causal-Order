import ICO.ReverseFidelity

/-!+# The linked frame is the operational reverse-composition test vector

This identifies the linked matrix with a genuine double Haar integral of
rank-one matrices for the vector
`d⁻¹ |conj U⟩⟩ |conj V⟩⟩ |UV⟩⟩`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.CausalReverse ICO.HaarFrame ICO.HaarLink ICO.ReverseFidelity

namespace ICO.ReverseIntegral

set_option maxHeartbeats 1500000

noncomputable section

universe u
variable {A : Type u} [Fintype A] [DecidableEq A]

local instance integrationCMatrixContinuousENorm {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

def pairVector (U V : Matrix.unitaryGroup A ℂ) : FrameWires A × FrameWires A → ℂ :=
  fun x => unitaryPairVector U x.1 * unitaryPairVector V x.2

def reverseAmplitude (U V : Matrix.unitaryGroup A ℂ) (i : SixWires A) : ℂ :=
  star ((U : CMatrix A) i.1.1.1.2 i.1.1.2) *
    star ((V : CMatrix A) i.1.2 i.1.1.1.1.2) *
      ((U : CMatrix A) * (V : CMatrix A)) i.2 i.1.1.1.1.1

/-- The normalized input and target Choi-vector factors contribute `1/d`. -/
def reverseVector (U V : Matrix.unitaryGroup A ℂ) : SixWires A → ℂ :=
  fun i => (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) * reverseAmplitude U V i

theorem link_pairVector (U V : Matrix.unitaryGroup A ℂ) :
    linkMatrix.mulVec (pairVector U V) = reverseAmplitude U V := by
  ext i
  have h := contraction_mul_apply frameWire
    (fun z (_ : Unit) => pairVector U V z) i ()
  change (∑ z, linkMatrix i z * pairVector U V z) = _
  rw [show (∑ z, linkMatrix i z * pairVector U V z) =
      ∑ t : A, pairVector U V (frameWire i t) by exact h]
  simp [pairVector, unitaryPairVector, frameWire, reverseAmplitude,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

theorem rankOne_pairVector (U V : Matrix.unitaryGroup A ℂ) :
    rankOneMatrix (pairVector U V) =
      Matrix.kronecker (rankOneMatrix (unitaryPairVector U))
        (rankOneMatrix (unitaryPairVector V)) := by
  ext i j
  simp [pairVector, rankOneMatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    mul_assoc, mul_left_comm, mul_comm]

theorem rankOne_real_scale {N : Type*} (r : ℝ) (v : N → ℂ) :
    rankOneMatrix (fun i => (r : ℂ) * v i) = ((r ^ 2 : ℝ) : ℂ) • rankOneMatrix v := by
  ext i j
  simp [rankOneMatrix_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Pointwise, Bell linking gives the reverse-composition test vector. -/
theorem rankOne_reverseVector (U V : Matrix.unitaryGroup A ℂ) :
    rankOneMatrix (reverseVector U V) =
      ((((Fintype.card A : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) •
        link (Matrix.kronecker (rankOneMatrix (unitaryPairVector U))
          (rankOneMatrix (unitaryPairVector V))) := by
  unfold reverseVector
  rw [rankOne_real_scale, ← link_pairVector U V,
    rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
    rankOne_pairVector]
  simp [link, inv_pow]

def kroneckerLeftCLM {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (X : CMatrix I) :
    CMatrix J →L[ℂ] CMatrix (I × J) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun Y => Matrix.kronecker X Y
       map_add' := by
         intro Y Z
         ext i j
         simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_add]
       map_smul' := by
         intro z Y
         ext i j
         simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_left_comm] } :
      CMatrix J →ₗ[ℂ] CMatrix (I × J))

def kroneckerRightCLM {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Y : CMatrix J) :
    CMatrix I →L[ℂ] CMatrix (I × J) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun X => Matrix.kronecker X Y
       map_add' := by
         intro X Z
         ext i j
         simp [Matrix.kronecker, Matrix.kroneckerMap_apply, add_mul]
       map_smul' := by
         intro z X
         ext i j
         simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc] } :
      CMatrix I →ₗ[ℂ] CMatrix (I × J))

def linkCLM : CMatrix (FrameWires A × FrameWires A) →L[ℂ] CMatrix (SixWires A) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := link
       map_add' := link_add
       map_smul' := link_smul } :
      CMatrix (FrameWires A × FrameWires A) →ₗ[ℂ] CMatrix (SixWires A))

def normalizedLinkCLM : CMatrix (FrameWires A × FrameWires A) →L[ℂ] CMatrix (SixWires A) :=
  ((((Fintype.card A : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • linkCLM

theorem frame_integrable [Nonempty A] :
    Integrable (fun U : Matrix.unitaryGroup A ℂ => rankOneMatrix (unitaryPairVector U))
      (unitaryHaarMeasure (a := A)) :=
  frameIntegrand_continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_pair_left [Nonempty A] (X : CMatrix (FrameWires A)) :
    (∫ V : Matrix.unitaryGroup A ℂ,
      Matrix.kronecker X (rankOneMatrix (unitaryPairVector V))
        ∂unitaryHaarMeasure (a := A)) = Matrix.kronecker X (haarFrame (A := A)) := by
  change (∫ V : Matrix.unitaryGroup A ℂ,
    kroneckerLeftCLM X (rankOneMatrix (unitaryPairVector V)) ∂unitaryHaarMeasure (a := A)) =
      kroneckerLeftCLM X (haarFrame (A := A))
  rw [haarFrame_eq_integral]
  exact (kroneckerLeftCLM X).integral_comp_comm (frame_integrable (A := A))

theorem integral_pair_right [Nonempty A] (Y : CMatrix (FrameWires A)) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      Matrix.kronecker (rankOneMatrix (unitaryPairVector U)) Y
        ∂unitaryHaarMeasure (a := A)) = Matrix.kronecker (haarFrame (A := A)) Y := by
  change (∫ U : Matrix.unitaryGroup A ℂ,
    kroneckerRightCLM Y (rankOneMatrix (unitaryPairVector U)) ∂unitaryHaarMeasure (a := A)) =
      kroneckerRightCLM Y (haarFrame (A := A))
  rw [haarFrame_eq_integral]
  exact (kroneckerRightCLM Y).integral_comp_comm (frame_integrable (A := A))

theorem inner_integral [Nonempty A] (U : Matrix.unitaryGroup A ℂ) :
    (∫ V : Matrix.unitaryGroup A ℂ, rankOneMatrix (reverseVector U V)
      ∂unitaryHaarMeasure (a := A)) =
        normalizedLinkCLM (Matrix.kronecker (rankOneMatrix (unitaryPairVector U))
          (haarFrame (A := A))) := by
  simp_rw [rankOne_reverseVector]
  change (∫ V : Matrix.unitaryGroup A ℂ,
      normalizedLinkCLM (Matrix.kronecker (rankOneMatrix (unitaryPairVector U))
        (rankOneMatrix (unitaryPairVector V))) ∂unitaryHaarMeasure (a := A)) = _
  have hcomm := (normalizedLinkCLM (A := A)).integral_comp_comm
    ((kroneckerLeftCLM (rankOneMatrix (unitaryPairVector U))).integrable_comp
      (frame_integrable (A := A)))
  change (∫ V : Matrix.unitaryGroup A ℂ,
      normalizedLinkCLM (Matrix.kronecker (rankOneMatrix (unitaryPairVector U))
        (rankOneMatrix (unitaryPairVector V))) ∂unitaryHaarMeasure (a := A)) =
      normalizedLinkCLM (∫ V : Matrix.unitaryGroup A ℂ,
        Matrix.kronecker (rankOneMatrix (unitaryPairVector U))
          (rankOneMatrix (unitaryPairVector V)) ∂unitaryHaarMeasure (a := A)) at hcomm
  rw [hcomm]
  rw [integral_pair_left]

/-- Exact identification of the linked test with the double independent Haar
average of the physical reverse-composition Choi test vector. -/
theorem reverseTest_eq_double_integral [Nonempty A] :
    reverseTest (A := A) =
      ∫ U : Matrix.unitaryGroup A ℂ,
        ∫ V : Matrix.unitaryGroup A ℂ, rankOneMatrix (reverseVector U V)
          ∂unitaryHaarMeasure (a := A)
        ∂unitaryHaarMeasure (a := A) := by
  simp_rw [inner_integral]
  have hcomm := (normalizedLinkCLM (A := A)).integral_comp_comm
    ((kroneckerRightCLM (haarFrame (A := A))).integrable_comp
      (frame_integrable (A := A)))
  change (∫ U : Matrix.unitaryGroup A ℂ,
      normalizedLinkCLM (Matrix.kronecker (rankOneMatrix (unitaryPairVector U))
        (haarFrame (A := A))) ∂unitaryHaarMeasure (a := A)) =
      normalizedLinkCLM (∫ U : Matrix.unitaryGroup A ℂ,
        Matrix.kronecker (rankOneMatrix (unitaryPairVector U))
          (haarFrame (A := A)) ∂unitaryHaarMeasure (a := A)) at hcomm
  rw [hcomm]
  rw [integral_pair_right]
  rfl

/-- The actual averaged Choi test obeys the causal reverse bound. -/
theorem causal_reverse_average_bound [Nontrivial A]
    (C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    tracePair C
      (∫ U : Matrix.unitaryGroup A ℂ,
        ∫ V : Matrix.unitaryGroup A ℂ, rankOneMatrix (reverseVector U V)
          ∂unitaryHaarMeasure (a := A)
        ∂unitaryHaarMeasure (a := A)) ≤
      (C.trace.re / (Fintype.card A : ℝ) ^ 3) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  rw [← reverseTest_eq_double_integral]
  exact causal_reverse_test_bound C C₂ hC hC₂ hcausal

def tracePairCLM (C : CMatrix (SixWires A)) : CMatrix (SixWires A) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := tracePair C
       map_add' := tracePair_add_right C
       map_smul' := by
         intro r X
         simp [tracePair, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul] } :
      CMatrix (SixWires A) →ₗ[ℝ] ℝ)

theorem reverseVector_inner_integrable [Nonempty A] (U : Matrix.unitaryGroup A ℂ) :
    Integrable (fun V : Matrix.unitaryGroup A ℂ => rankOneMatrix (reverseVector U V))
      (unitaryHaarMeasure (a := A)) := by
  have heq : (fun V : Matrix.unitaryGroup A ℂ => rankOneMatrix (reverseVector U V)) =
      (fun V : Matrix.unitaryGroup A ℂ => normalizedLinkCLM
        (Matrix.kronecker (rankOneMatrix (unitaryPairVector U))
          (rankOneMatrix (unitaryPairVector V)))) := by
    funext V
    exact rankOne_reverseVector U V
  rw [heq]
  change Integrable (fun V : Matrix.unitaryGroup A ℂ =>
    normalizedLinkCLM (A := A)
      (kroneckerLeftCLM (rankOneMatrix (unitaryPairVector U))
        (rankOneMatrix (unitaryPairVector V)))) (unitaryHaarMeasure (a := A))
  have hkr := (kroneckerLeftCLM (I := FrameWires A) (J := FrameWires A)
    (rankOneMatrix (unitaryPairVector U))).integrable_comp (frame_integrable (A := A))
  have hnorm := (normalizedLinkCLM (A := A)).integrable_comp hkr
  exact hnorm

theorem reverseVector_outer_integrable [Nonempty A] :
    Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      ∫ V : Matrix.unitaryGroup A ℂ, rankOneMatrix (reverseVector U V)
        ∂unitaryHaarMeasure (a := A)) (unitaryHaarMeasure (a := A)) := by
  simp_rw [inner_integral]
  change Integrable (fun U : Matrix.unitaryGroup A ℂ =>
    normalizedLinkCLM (A := A)
      (kroneckerRightCLM (haarFrame (A := A))
        (rankOneMatrix (unitaryPairVector U)))) (unitaryHaarMeasure (a := A))
  have hkr := (kroneckerRightCLM (I := FrameWires A) (J := FrameWires A)
    (haarFrame (A := A))).integrable_comp (frame_integrable (A := A))
  have hnorm := (normalizedLinkCLM (A := A)).integrable_comp hkr
  exact hnorm

/-- Pairing the averaged test with a comb equals the average of its test scores. -/
theorem tracePair_reverseTest_eq_average [Nonempty A] (C : CMatrix (SixWires A)) :
    tracePair C reverseTest =
      ∫ U : Matrix.unitaryGroup A ℂ,
        ∫ V : Matrix.unitaryGroup A ℂ, tracePair C (rankOneMatrix (reverseVector U V))
          ∂unitaryHaarMeasure (a := A)
        ∂unitaryHaarMeasure (a := A) := by
  rw [reverseTest_eq_double_integral]
  have houter := ((tracePairCLM C).integral_comp_comm
    (reverseVector_outer_integrable (A := A))).symm
  change tracePair C (∫ U : Matrix.unitaryGroup A ℂ,
      ∫ V : Matrix.unitaryGroup A ℂ, rankOneMatrix (reverseVector U V)
        ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) =
      ∫ U : Matrix.unitaryGroup A ℂ, tracePair C
        (∫ V : Matrix.unitaryGroup A ℂ, rankOneMatrix (reverseVector U V)
          ∂unitaryHaarMeasure (a := A)) ∂unitaryHaarMeasure (a := A) at houter
  rw [houter]
  apply integral_congr_ae
  filter_upwards [] with U
  exact ((tracePairCLM C).integral_comp_comm (reverseVector_inner_integrable U)).symm

/-- The reverse test's scalar Haar-averaged score is bounded by the parent
comb mass times the dimension-dependent reverse factor. -/
theorem causal_reverse_score_bound [Nontrivial A]
    (C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      ∫ V : Matrix.unitaryGroup A ℂ, tracePair C (rankOneMatrix (reverseVector U V))
        ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
      (C.trace.re / (Fintype.card A : ℝ) ^ 3) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  rw [← tracePair_reverseTest_eq_average]
  exact causal_reverse_test_bound C C₂ hC hC₂ hcausal

end

end ICO.ReverseIntegral

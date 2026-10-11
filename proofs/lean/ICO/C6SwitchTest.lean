import ICO.C6FlatUnitary
import ICO.SwitchExperiment

/-! The physical four-switch SAME-versus-MUB test.  Each repetition uses the
normalized switched channel, the maximally mixed target, and a Born measurement
of the control.  The repetitions use fresh independent target/control systems. -/
namespace ICO.C6SwitchTest
open Matrix QIT MeasureTheory ICO.SwitchObservable ICO.LudersPromise
open ICO.SwitchExperiment ICO.SwitchSampling
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def MutuallyUnbiased (U V : Matrix.unitaryGroup A ℂ) : Prop :=
  ∀ i j, Complex.normSq (((U : CMatrix A).conjTranspose * (V : CMatrix A)) i j) =
    1/(Fintype.card A : ℝ)

theorem flat_translate (U H : Matrix.unitaryGroup A ℂ)
    (hH : ∀ i j, Complex.normSq ((H : CMatrix A) i j) = 1/(Fintype.card A : ℝ)) :
    MutuallyUnbiased U (U*H) := by
  intro i j
  have hU : (U : CMatrix A).conjTranspose * (U : CMatrix A) = 1 := U.property.1
  change Complex.normSq (((U : CMatrix A).conjTranspose *
    ((U : CMatrix A) * (H : CMatrix A))) i j) = _
  rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  exact hH i j

theorem mub_interference (U V : Matrix.unitaryGroup A ℂ) (h : MutuallyUnbiased U V) :
    interference (basisProjection (U : CMatrix A)) (basisProjection (V : CMatrix A)) =
      1/(Fintype.card A : ℝ) := by
  rw [basis_interference]
  unfold MutuallyUnbiased at h
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

def basisState (U V : Matrix.unitaryGroup A ℂ) : State (A⊕A) :=
  switchedState (basisProjection (U : CMatrix A)) (basisProjection (V : CMatrix A))
    (hidden_basis_kraus_complete _ U.property.1 U.property.2)
    (hidden_basis_kraus_complete _ V.property.1 V.property.2) mixedState

def plusProbability (U V : Matrix.unitaryGroup A ℂ) : NNReal :=
  controlMeasurement.prob (basisState U V) true

theorem plusProbability_le_one (U V : Matrix.unitaryGroup A ℂ) :
    plusProbability U V ≤ 1 :=
  QIT.POVM.prob_le_one _ _ _

theorem same_probability (U : Matrix.unitaryGroup A ℂ) :
    (plusProbability U U : ℝ) = 1 := by
  unfold plusProbability basisState
  rw [switch_plus_probability, hidden_basis_high _ U.property.1 U.property.2]
  norm_num

theorem mub_probability (U V : Matrix.unitaryGroup A ℂ) (h : MutuallyUnbiased U V) :
    (plusProbability U V : ℝ) = (1+1/(Fintype.card A : ℝ))/2 := by
  unfold plusProbability basisState
  rw [switch_plus_probability, mub_interference U V h]

theorem all_plus_probability (m : ℕ) (p : NNReal) (hp : p≤1) :
    (repetitions m p hp).real {ω | ∀ i, ω i=true} = (p:ℝ)^m := by
  have he : {ω : Fin m→Bool | ∀ i, ω i=true} = {fun _ => true} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  rw [he, measureReal_def]
  simp [repetitions, Measure.pi_singleton, PMF.toMeasure_apply_singleton,
    PMF.bernoulli_apply]

def acceptSame (U V : Matrix.unitaryGroup A ℂ) : ℝ :=
  (repetitions 4 (plusProbability U V) (plusProbability_le_one U V)).real
    {ω | ∀ i, ω i=true}

theorem four_same_accepts (U : Matrix.unitaryGroup A ℂ) : acceptSame U U = 1 := by
  rw [acceptSame, all_plus_probability, same_probability]
  norm_num

theorem four_mub_error (hd : 2≤Fintype.card A) (U V : Matrix.unitaryGroup A ℂ)
    (h : MutuallyUnbiased U V) : acceptSame U V ≤ 81/256 ∧ acceptSame U V < 1/3 := by
  have hd' : (2:ℝ) ≤ Fintype.card A := by exact_mod_cast hd
  have hp : (plusProbability U V : ℝ) ≤ 3/4 := by
    rw [mub_probability U V h]
    have hdiv : 1/(Fintype.card A : ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ (by linarith : (0:ℝ)<Fintype.card A)).mpr
      linarith
    linarith
  have hfour := pow_le_pow_left₀ (NNReal.coe_nonneg (plusProbability U V)) hp 4
  rw [← all_plus_probability 4 _ (plusProbability_le_one U V)] at hfour
  change acceptSame U V ≤ (3/4:ℝ)^4 at hfour
  norm_num at hfour
  exact ⟨hfour, by linarith⟩

theorem switch_use_and_oracle_call_count : (4:ℕ)*2=8 := by decide

#print axioms four_same_accepts
#print axioms four_mub_error
end
end ICO.C6SwitchTest

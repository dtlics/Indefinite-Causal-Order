import ICO.C6OTOCEstimator
import ICO.C6OperationalDecision
import ICO.C6OTOCDecision
import ICO.SwitchExperiment
import ICO.FinitePOVMEvent

/-! Theorem 3(b) (`thm:c6`, part b) and Corollary 4 (`cor:value`) visibility
and estimator endpoints:
1. Upper bound for every pair of channels (arbitrary complete Kraus families)
   with failure probability `≤ 2 * Real.exp (-2)` (`< 1 / 3`) and success
   probability `≥ 1 - 2 * Real.exp (-2)` (`> 2 / 3`) using `m ≥ 4 / ε^2`
   (in particular `m = ⌈4 / ε^2⌉₊`) switch shots (`2 * m < 8 / ε^2 + 2` total
   oracle calls).
2. Query lower bound `(Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100 < q` stated
   directly for estimating the visibility `interference` on an arbitrary index
   type `A` with `Fintype.card A = 2 ^ n` (`1 ≤ n`). -/

namespace ICO.C6VisibilityEstimator
open Matrix QIT MeasureTheory ProbabilityTheory
open ICO.BudgetQueryTree ICO.BudgetContinuity ICO.BudgetTesting
open ICO.SwitchObservable ICO.SwitchExperiment ICO.SwitchSampling ICO.SwitchStatistics
open ICO.C6OTOCEstimator ICO.C6SwitchTest ICO.C6Decision ICO.C6OperationalDecision
open ICO.C6OTOCDecision ICO.FinitePOVMEvent
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false

section UpperBound
variable {n ι κ : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype ι] [Fintype κ]

/-- The Born-rule probability of the `|+⟩` (`true`) control outcome in a single
quantum switch shot with channel Kraus families `A` and `B` on the maximally
mixed target state. -/
def switchPlusProb (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1) : NNReal :=
  (controlMeasurement (n := n)).prob (switchedState A B hA hB mixedState) true

theorem switchPlusProb_le_one (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1) :
    switchPlusProb A B hA hB ≤ 1 :=
  QIT.POVM.prob_le_one _ _ _

theorem two_mul_switchPlusProb_sub_one (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1) :
    2 * (switchPlusProb A B hA hB : ℝ) - 1 = interference A B := by
  unfold switchPlusProb
  rw [switch_plus_probability A B hA hB]
  ring

/-- The product distribution of `m` independent quantum switch shots on channel
Kraus families `A` and `B`. -/
def switchRepetitions (m : ℕ) (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1) :
    Measure (Fin m → Bool) :=
  repetitions m (switchPlusProb A B hA hB) (switchPlusProb_le_one A B hA hB)

instance switchRepetitions_probability (m : ℕ)
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1) :
    IsProbabilityMeasure (switchRepetitions m A B hA hB) := by
  unfold switchRepetitions
  infer_instance

/-- Hoeffding tail bound for the empirical visibility estimator `estimate m`
on any pair of quantum channels `(A, B)`. -/
theorem visibility_bernoulli_error {m : ℕ} (hm : 0 < m)
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (switchRepetitions m A B hA hB).real
      {ω : Fin m → Bool | ε < |estimate m ω - interference A B|} ≤
        2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  unfold switchRepetitions
  rw [← two_mul_switchPlusProb_sub_one A B hA hB]
  exact bernoulli_error hm (switchPlusProb A B hA hB)
    (switchPlusProb_le_one A B hA hB) ε hε

/-- Whenever `4 / ε^2 ≤ m`, the empirical visibility estimator on `m` switch shots
deviates from `interference A B` by more than `ε` with probability at most `2e^{-2}`. -/
theorem sufficient_samples_exp_bound {m : ℕ} (hm : 0 < m) (p : NNReal) (hp : p ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hs : 4 / ε ^ 2 ≤ (m : ℝ)) :
    (repetitions m p hp).real {ω | ε < |estimate m ω - (2 * (p : ℝ) - 1)|} ≤
      2 * Real.exp (-2 : ℝ) := by
  have hpow : (0 : ℝ) < ε ^ 2 := sq_pos_of_pos hε
  have hs' := (div_le_iff₀ hpow).mp hs
  have he : -(m : ℝ) * ε ^ 2 / 2 ≤ -2 := by nlinarith
  exact (bernoulli_error hm p hp ε hε.le).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num))

theorem visibility_failure_le_two_exp_neg_two {m : ℕ} (hm : 0 < m)
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1)
    (ε : ℝ) (hε : 0 < ε) (hs : 4 / ε ^ 2 ≤ (m : ℝ)) :
    (switchRepetitions m A B hA hB).real
      {ω : Fin m → Bool | ε < |estimate m ω - interference A B|} ≤
        2 * Real.exp (-2 : ℝ) := by
  unfold switchRepetitions
  rw [← two_mul_switchPlusProb_sub_one A B hA hB]
  exact sufficient_samples_exp_bound hm (switchPlusProb A B hA hB)
    (switchPlusProb_le_one A B hA hB) ε hε hs

/-- Whenever `4 / ε^2 ≤ m`, the empirical visibility estimator on `m` switch shots
succeeds within additive error `ε` with probability at least `1 - 2e^{-2}`
(and strictly greater than `2 / 3`). -/
theorem visibility_success_ge_one_sub_two_exp_neg_two {m : ℕ} (hm : 0 < m)
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1)
    (ε : ℝ) (hε : 0 < ε) (hs : 4 / ε ^ 2 ≤ (m : ℝ)) :
    1 - 2 * Real.exp (-2 : ℝ) ≤
      (switchRepetitions m A B hA hB).real
        {ω : Fin m → Bool | |estimate m ω - interference A B| ≤ ε} ∧
    (2 / 3 : ℝ) <
      (switchRepetitions m A B hA hB).real
        {ω : Fin m → Bool | |estimate m ω - interference A B| ≤ ε} := by
  let μ := switchRepetitions m A B hA hB
  let F : Set (Fin m → Bool) := {ω | ε < |estimate m ω - interference A B|}
  have hcompl : Fᶜ = {ω : Fin m → Bool | |estimate m ω - interference A B| ≤ ε} := by
    ext ω
    simp [F, not_lt]
  have hF_meas : MeasurableSet F := .of_discrete
  have hprob : μ.real Fᶜ = 1 - μ.real F := by
    rw [measureReal_compl hF_meas, probReal_univ]
  have hfail : μ.real F ≤ 2 * Real.exp (-2 : ℝ) :=
    visibility_failure_le_two_exp_neg_two hm A B hA hB ε hε hs
  have htwo := two_exp_neg_two_lt_third
  rw [← hcompl, hprob]
  exact ⟨by linarith, by linarith⟩

/-- Theorem 3(b) / Corollary 4 upper bound for every pair of channels:
`m = ⌈4 / ε^2⌉₊` switch queries estimate `interference A B` within `±ε` with
failure probability `≤ 2e^{-2} < 1/3` and success probability `≥ 1 - 2e^{-2} > 2/3`. -/
theorem switch_visibility_estimation
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1)
    (ε : ℝ) (hε : 0 < ε) :
    let m := Nat.ceil (4 / ε ^ 2)
    (switchRepetitions m A B hA hB).real
      {ω : Fin m → Bool | ε < |estimate m ω - interference A B|} ≤
        2 * Real.exp (-2 : ℝ) ∧
    (switchRepetitions m A B hA hB).real
      {ω : Fin m → Bool | ε < |estimate m ω - interference A B|} < 1 / 3 ∧
    1 - 2 * Real.exp (-2 : ℝ) ≤
      (switchRepetitions m A B hA hB).real
        {ω : Fin m → Bool | |estimate m ω - interference A B| ≤ ε} ∧
    (2 / 3 : ℝ) <
      (switchRepetitions m A B hA hB).real
        {ω : Fin m → Bool | |estimate m ω - interference A B| ≤ ε} := by
  dsimp only
  have hpos : 0 < Nat.ceil (4 / ε ^ 2) :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  have hs : 4 / ε ^ 2 ≤ (Nat.ceil (4 / ε ^ 2) : ℝ) := Nat.le_ceil _
  have hfail := visibility_failure_le_two_exp_neg_two hpos A B hA hB ε hε hs
  have hsucc := visibility_success_ge_one_sub_two_exp_neg_two hpos A B hA hB ε hε hs
  exact ⟨hfail, hfail.trans_lt two_exp_neg_two_lt_third, hsucc.1, hsucc.2⟩

/-- Alias matching `THEOREMS.txt`: Theorem 3(b) / `cor:value` upper bound for
every pair of complete Kraus channels with constant `2 * Real.exp (-2) < 1 / 3`
and success probability `≥ 1 - 2 * Real.exp (-2) > 2 / 3`. -/
theorem channel_visibility_estimation
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1)
    (ε : ℝ) (hε : 0 < ε) :
    let m := Nat.ceil (4 / ε ^ 2)
    (switchRepetitions m A B hA hB).real
      {ω : Fin m → Bool | ε < |estimate m ω - interference A B|} ≤
        2 * Real.exp (-2 : ℝ) ∧
    (switchRepetitions m A B hA hB).real
      {ω : Fin m → Bool | ε < |estimate m ω - interference A B|} < 1 / 3 ∧
    1 - 2 * Real.exp (-2 : ℝ) ≤
      (switchRepetitions m A B hA hB).real
        {ω : Fin m → Bool | |estimate m ω - interference A B| ≤ ε} ∧
    (2 / 3 : ℝ) <
      (switchRepetitions m A B hA hB).real
        {ω : Fin m → Bool | |estimate m ω - interference A B| ≤ ε} :=
  switch_visibility_estimation A B hA hB ε hε

end UpperBound

section LowerBound
variable {A M O B R : Type}
  [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M]
  [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B]
  [Fintype R] [DecidableEq R]

theorem same_visibility (U : Matrix.unitaryGroup A ℂ) :
    interference (basisProjection (U : CMatrix A))
      (basisProjection (U : CMatrix A)) = 1 :=
  hidden_basis_high (U : CMatrix A) U.property.1 U.property.2

omit [DecidableEq A] [Nonempty A] in
theorem good_mub_visibility_subset (value : R → ℝ) {ε : ℝ} (hε : ε < 1 / 4)
    (hd : 2 ≤ Fintype.card A) :
    good value ε (1 / (Fintype.card A : ℝ)) ⊆ (high value)ᶜ := by
  intro r hr
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  simp only [Finset.mem_compl, high, Finset.mem_filter, Finset.mem_univ, true_and,
    not_lt]
  have hd' : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hd
  have hhalf : 1 / (Fintype.card A : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < Fintype.card A)).mpr
    linarith
  have hh := (abs_le.mp hr).2
  linarith

/-- An estimator for the visibility `interference` is accurate on the SAME/MUB
promise if it outputs a value within `ε` of `interference` with probability at
least `2/3` whenever `U = V` or `MutuallyUnbiased U V`. -/
def AccurateVisibilityOnPromise {q : ℕ} (tree : Tree (A × M) O q B)
    (ρ : State B) (E : POVM R O) (value : R → ℝ) (ε : ℝ) : Prop :=
  ∀ U V : Matrix.unitaryGroup A ℂ, U = V ∨ MutuallyUnbiased U V →
    (2 / 3 : ℝ) ≤ probability E ((tree.channel (hidden U) (hidden V)).applyState ρ)
      (good value ε (interference (basisProjection (U : CMatrix A))
        (basisProjection (V : CMatrix A))))

/-- An estimator for the visibility `interference` is accurate on all projective
dephasing channels if it outputs a value within `ε` of `interference` with
probability at least `2/3` for every pair of unitary bases `U, V`. -/
def AccurateVisibilityOnDephasers {q : ℕ} (tree : Tree (A × M) O q B)
    (ρ : State B) (E : POVM R O) (value : R → ℝ) (ε : ℝ) : Prop :=
  ∀ U V : Matrix.unitaryGroup A ℂ,
    (2 / 3 : ℝ) ≤ probability E ((tree.channel (hidden U) (hidden V)).applyState ρ)
      (good value ε (interference (basisProjection (U : CMatrix A))
        (basisProjection (V : CMatrix A))))

omit [Nonempty A] in
theorem AccurateVisibilityOnDephasers.toPromise {q : ℕ}
    {tree : Tree (A × M) O q B} {ρ : State B} {E : POVM R O}
    {value : R → ℝ} {ε : ℝ}
    (h : AccurateVisibilityOnDephasers tree ρ E value ε) :
    AccurateVisibilityOnPromise tree ρ E value ε :=
  fun U V _ => h U V

theorem visibility_estimator_gives_decision {q : ℕ} (tree : Tree (A × M) O q B)
    (ρ : State B) (E : POVM R O) (value : R → ℝ) {ε : ℝ}
    (hε : ε < 1 / 4) (hd : 2 ≤ Fintype.card A)
    (hc : AccurateVisibilityOnPromise tree ρ E value ε) :
    (∀ U, (2 / 3 : ℝ) ≤ acceptance (test E (high value)) tree ρ (hidden U) (hidden U)) ∧
    (∀ U V, MutuallyUnbiased U V →
      acceptance (test E (high value)) tree ρ (hidden U) (hidden V) ≤ 1 / 3) := by
  constructor
  · intro U
    rw [acceptance_eq]
    have h := hc U U (Or.inl rfl)
    rw [same_visibility] at h
    exact accuracy_implies_accept E _ _ _ (good_same_subset value hε) h
  · intro U V hUV
    rw [acceptance_eq]
    have h := hc U V (Or.inr hUV)
    rw [mub_interference U V hUV] at h
    exact accuracy_implies_reject E _ _ _ (good_mub_visibility_subset value hε hd) h

/-- Theorem 3(b) / Corollary 4 query lower bound stated directly for the
visibility `interference` on an arbitrary index type `A` with
`Fintype.card A = 2 ^ n` (`1 ≤ n`). -/
theorem visibility_query_lower_bound {q : ℕ} (tree : Tree (A × M) O q B)
    (ρ : State B) (E : POVM R O) (value : R → ℝ) {ε : ℝ}
    (hε : ε < 1 / 4) (n : ℕ) (hn : 1 ≤ n) (hd : Fintype.card A = 2 ^ n)
    (hc : AccurateVisibilityOnPromise tree ρ E value ε) :
    (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100 < q := by
  have hd2 : 2 ≤ Fintype.card A := by
    rw [hd]
    have hh := Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) hn
    simpa using hh
  obtain ⟨hh, hl⟩ := visibility_estimator_gives_decision tree ρ E value hε hd2 hc
  exact same_mub_query_lower_bound (test E (high value)) tree ρ n hd hh hl

/-- Theorem 3(b) / Corollary 4 query lower bound for any fixed-order estimator
that approximates the visibility `interference` within `ε < 1/4` with success
probability `≥ 2/3` on all projective dephasing pairs. -/
theorem visibility_query_lower_bound_of_dephasers {q : ℕ} (tree : Tree (A × M) O q B)
    (ρ : State B) (E : POVM R O) (value : R → ℝ) {ε : ℝ}
    (hε : ε < 1 / 4) (n : ℕ) (hn : 1 ≤ n) (hd : Fintype.card A = 2 ^ n)
    (hc : AccurateVisibilityOnDephasers tree ρ E value ε) :
    (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100 < q :=
  visibility_query_lower_bound tree ρ E value hε n hn hd hc.toPromise

/-- Alias matching `THEOREMS.txt`: Theorem 3(b) / `cor:value` lower bound
stated directly for the visibility `interference` on an arbitrary index type `A`. -/
theorem visibility_estimation_query_lower_bound {q : ℕ} (tree : Tree (A × M) O q B)
    (ρ : State B) (E : POVM R O) (value : R → ℝ) {ε : ℝ}
    (hε : ε < 1 / 4) (n : ℕ) (hn : 1 ≤ n) (hd : Fintype.card A = 2 ^ n)
    (hc : AccurateVisibilityOnPromise tree ρ E value ε) :
    (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100 < q :=
  visibility_query_lower_bound tree ρ E value hε n hn hd hc

end LowerBound

#print axioms visibility_bernoulli_error
#print axioms visibility_failure_le_two_exp_neg_two
#print axioms visibility_success_ge_one_sub_two_exp_neg_two
#print axioms switch_visibility_estimation
#print axioms channel_visibility_estimation
#print axioms visibility_estimator_gives_decision
#print axioms visibility_query_lower_bound
#print axioms visibility_query_lower_bound_of_dephasers
#print axioms visibility_estimation_query_lower_bound

end
end ICO.C6VisibilityEstimator

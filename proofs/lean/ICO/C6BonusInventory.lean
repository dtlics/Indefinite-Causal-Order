import ICO.C5Decision
import ICO.C6OperationalDecision
import ICO.C6BosonicFreshPrefix
import ICO.C6PermanentFlags
import ICO.C6RawWeightedEndpoint
import ICO.C6WeightedHistoryBound

/-! Additional paper-level consequences from the Lean inventory:
1. Lemma `lem:c6-comparison` with the paper's constant `212 / 10000`.
2. Corollary `thm:testing` as one unified statement over all channel pairs with
   `v ≥ 2/3` or `v ≤ 1/3`, including the rank-one-dephaser-only clause for `d ≥ 4`
   and the 80-switch-use upper bound.
3. Appendix C (`sec:connections`) Zanardi projection-channel swap expectations
   `1 / d` under `SAME` and `1 / d^2` under `MUB`.
4. Appendix D (`sec:capacity-qualification`) inherited `2q`-call diagnostic
   distance bound `≤ 215 / 10000` (and `≤ 212 / 10000`) for `1 ≤ q ≤ d^(1/16) / 200`,
   together with the `101 / 4000` hybrid bound at `t = 3 / 4`. -/

namespace ICO.C6BonusInventory

open Matrix QIT MeasureTheory
open ICO.SwitchObservable ICO.SwitchExperiment ICO.C6SwitchTest
open ICO.BudgetQueryTree ICO.BudgetContinuity ICO.BudgetTesting
open ICO.C6Bounds ICO.C6UniformBounds ICO.C6Decision ICO.C6OperationalDecision
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 2400000

/-- E.1 #9: The paper's sharper scalar constant `212 / 10000` in Lemma `lem:c6-comparison`. -/
theorem uniformError_le_212 {q : ℕ} {r : ℝ} (hq : 1 ≤ q) (hqr : (q : ℝ) ≤ r / 100) :
    uniformError q (r ^ 16) r ≤ 212 / 10000 := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨hr, h24, hD⟩ := radius_dimensions hq' hqr
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hd2 : r ^ 2 ≤ r ^ 16 := by linarith
  have hq2 : (q : ℝ) ^ 2 ≤ r ^ 2 / 10000 := by
    have hh := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ q) hqr
    nlinarith
  have hbase : (q : ℝ) ^ 2 / r ^ 2 ≤ 1 / 10000 := (div_le_iff₀ hr2).mpr (by linarith)
  have hm1 : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
  have hmain : 18 * (2 * (q : ℝ)) * (2 * q + 1) / r ^ 2 ≤ 108 / 10000 := by
    apply (div_le_iff₀ hr2).mpr
    nlinarith
  have hf := forwardError_le hq hqr
  have hb := birthError_le hq hqr
  have hc := creatorError_le hq' hqr
  have hc' := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 14 * q)
  have hcache : uniformCacheError q (r ^ 16) ≤ 6 * (q : ℝ) ^ 2 / r ^ 2 := by
    unfold uniformCacheError
    apply le_trans (div_le_div_of_nonneg_left (by positivity) hr2 hd2)
    apply (div_le_div_iff_of_pos_right hr2).mpr
    nlinarith
  have hnorm : 2 * (q : ℝ) * ((q - 1 : ℕ) : ℝ) / r ^ 16 ≤ 2 * (q : ℝ) ^ 2 / r ^ 2 := by
    apply le_trans (div_le_div_of_nonneg_left (by positivity) hr2 hd2)
    apply (div_le_div_iff_of_pos_right hr2).mpr
    nlinarith
  rw [uniformError_formula]
  ring_nf at hmain hf hb hc' hcache hnorm hbase ⊢
  linarith

/-- E.1 #9: Shared-basis indistinguishability (`lem:c6-comparison`) with the paper's
constant `212 / 10000`. -/
theorem same_mub_distance_212 {A M O B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] [Nonempty M] [Fintype O] [DecidableEq O] [Nonempty O]
    [Fintype B] [DecidableEq B] {q : ℕ}
    (tree : Tree (A × M) O q B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ)
    (hq : 1 ≤ q) (hqr : (q : ℝ) ≤ (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100) :
    let r := (Fintype.card A : ℝ) ^ (1 / 16 : ℝ)
    normalizedTraceDistance (sameDensity tree ρ) (mubDensity tree ρ H) ≤
        uniformError q (Fintype.card A) r ∧
      uniformError q (Fintype.card A) r ≤ 212 / 10000 ∧
      uniformError q (Fintype.card A) r < 1 / 3 := by
  have hrpow := ICO.QuantumDecision.radius_power_sixteen (Fintype.card A) (by positivity)
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hr := radius_dimensions hqreal hqr
  have hfour : 4 * q ≤ Fintype.card A := by
    have hr1 : 1 ≤ (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) := by linarith
    have h14 : (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) ≤
        ((Fintype.card A : ℝ) ^ (1 / 16 : ℝ)) ^ 4 := by
      simpa using pow_le_pow_right₀ hr1 (show (1 : ℕ) ≤ 4 by norm_num)
    rw [hrpow] at hr
    exact_mod_cast (show 4 * (q : ℝ) ≤ Fintype.card A by linarith [hr.2.2])
  have hdist := same_mub_distance tree ρ H hq hfour
  have hle : uniformError q (Fintype.card A)
      ((Fintype.card A : ℝ) ^ (1 / 16 : ℝ)) ≤ 212 / 10000 := by
    have hs := uniformError_le_212 hq hqr
    rw [hrpow] at hs
    exact hs
  exact ⟨hdist, hle, by linarith⟩

/-- E.1 #10: Zanardi's projection-channel / Choi-state swap expectation on two
orthonormal bases `U` and `V`. -/
def zanardiSwapExpectation {A : Type*} [Fintype A] [DecidableEq A] (U V : CMatrix A) : ℝ :=
  (∑ i : A, ∑ j : A, Complex.normSq ((U.conjTranspose * V) i j) ^ 2) /
    (Fintype.card A : ℝ) ^ 2

theorem zanardiSwapExpectation_eq_interference_div {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (U V : CMatrix A) :
    zanardiSwapExpectation U V =
      interference (basisProjection U) (basisProjection V) / (Fintype.card A : ℝ) := by
  rw [zanardiSwapExpectation, ICO.LudersPromise.basis_interference, div_div, sq]

theorem zanardi_swap_same {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (U : Matrix.unitaryGroup A ℂ) :
    zanardiSwapExpectation (U : CMatrix A) (U : CMatrix A) = 1 / (Fintype.card A : ℝ) := by
  rw [zanardiSwapExpectation_eq_interference_div,
    hidden_basis_high _ U.property.1 U.property.2]

theorem zanardi_swap_mub {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (U V : Matrix.unitaryGroup A ℂ) (h : MutuallyUnbiased U V) :
    zanardiSwapExpectation (U : CMatrix A) (V : CMatrix A) = 1 / (Fintype.card A : ℝ) ^ 2 := by
  rw [zanardiSwapExpectation_eq_interference_div,
    mub_interference U V h, div_div, sq]

/-- The explicit matrix-unit Kraus family `SwitchObservable.depolarizingKraus`
lifts to `RecordingDepolarizing.withMemory`. -/
theorem switch_depolarizing_oracle {A M : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] :
    ICO.AllChannelDilation.oracleChannel (M := M)
      (ICO.SwitchObservable.depolarizingKraus (n := A))
      ICO.SwitchObservable.depolarizing_kraus_complete =
      ICO.RecordingDepolarizing.withMemory (α := A) (μ := M) := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  change ICO.AllChannelDilation.oracleMap (M := M)
    (ICO.SwitchObservable.depolarizingKraus (n := A)) =
    (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map
  rw [ICO.OracleLift.oracleMap_lift]
  ext X x y
  let slice : CMatrix A := fun a b => X (a, x.2) (b, y.2)
  change MatrixMap.ofKraus (ICO.SwitchObservable.depolarizingKraus (n := A))
    slice x.1 y.1 =
    MatrixMap.kron ICO.RecordingDepolarizing.depolarizing.map (Channel.idChannel M).map X x y
  rw [MatrixMap.kron_idChannel_apply_slice]
  change (∑ p : A × A, ICO.SwitchObservable.depolarizingKraus p *
    slice * (ICO.SwitchObservable.depolarizingKraus p)ᴴ) x.1 y.1 =
    (ICO.RecordingDepolarizing.depolarizing.map slice) x.1 y.1
  rw [ICO.SwitchObservable.depolarizing_channel, ICO.RecordingDepolarizing.depolarizing_entry]
  simp [Matrix.smul_apply, Matrix.one_apply, div_eq_mul_inv, mul_comm]

/-- E.1 #4: Lower bound for any ordinary strategy that decides `v(A,B) ≥ 2/3` versus
`v(A,B) ≤ 1/3` across all complete Kraus channel pairs. -/
theorem all_channels_constant_gap_lower_bound
    {A M O B : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    [Fintype M] [DecidableEq M] [Nonempty M] [Fintype O] [DecidableEq O] [Nonempty O]
    [Fintype B] [DecidableEq B] {q : ℕ}
    (T : BinaryHypothesisTest O) (tree : Tree (A × M) O q B) (ρ : State B)
    (hhigh : ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (E : ι → CMatrix A) (F : κ → CMatrix A)
      (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1),
      (2 / 3 : ℝ) ≤ interference E F →
        (2 / 3 : ℝ) ≤ acceptance T tree ρ
          (ICO.AllChannelDilation.oracleChannel (M := M) E hE)
          (ICO.AllChannelDilation.oracleChannel (M := M) F hF))
    (hlow : ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (E : ι → CMatrix A) (F : κ → CMatrix A)
      (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1),
      interference E F ≤ 1 / 3 →
        acceptance T tree ρ
          (ICO.AllChannelDilation.oracleChannel (M := M) E hE)
          (ICO.AllChannelDilation.oracleChannel (M := M) F hF) ≤ 1 / 3) :
    (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100 < (q : ℝ) := by
  apply ICO.C5Decision.main_lower_bound T tree ρ
  · intro U
    have hU := hidden_basis_kraus_complete (U : CMatrix A) U.property.1 U.property.2
    have hv : (2 / 3 : ℝ) ≤ interference (basisProjection (U : CMatrix A))
        (basisProjection (U : CMatrix A)) := by
      rw [hidden_basis_high _ U.property.1 U.property.2]
      norm_num
    exact hhigh A A (basisProjection (U : CMatrix A)) (basisProjection (U : CMatrix A)) hU hU hv
  · have hcard : 2 ≤ Fintype.card A := Fintype.one_lt_card
    have hcardR : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hcard
    have hdep : interference (ICO.SwitchObservable.depolarizingKraus : A × A → CMatrix A)
        ICO.SwitchObservable.depolarizingKraus ≤ 1 / 3 := by
      rw [depolarizing_low]
      have hsq : (4 : ℝ) ≤ (Fintype.card A : ℝ) ^ 2 := by nlinarith
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Fintype.card A : ℝ) ^ 2)).mpr
      linarith
    have hlow_dep := hlow (A × A) (A × A)
      (ICO.SwitchObservable.depolarizingKraus (n := A))
      (ICO.SwitchObservable.depolarizingKraus (n := A))
      ICO.SwitchObservable.depolarizing_kraus_complete
      ICO.SwitchObservable.depolarizing_kraus_complete hdep
    simpa only [switch_depolarizing_oracle] using hlow_dep

/-- E.1 #4: Dephaser-only constant-gap lower bound for `4 ≤ d`, stated directly in terms
of the visibility `v ≥ 2/3` versus `v ≤ 1/3` on rank-one dephasing channels. -/
theorem measurement_only_constant_gap_lower_bound
    {A M O B : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    [Fintype M] [DecidableEq M] [Nonempty M] [Fintype O] [DecidableEq O] [Nonempty O]
    [Fintype B] [DecidableEq B] {q : ℕ}
    (T : BinaryHypothesisTest O) (tree : Tree (A × M) O q B) (ρ : State B)
    (hdim : 4 ≤ Fintype.card A)
    (hhigh : ∀ U V : Matrix.unitaryGroup A ℂ,
      (2 / 3 : ℝ) ≤ interference (basisProjection (U : CMatrix A))
        (basisProjection (V : CMatrix A)) →
        (2 / 3 : ℝ) ≤ acceptance T tree ρ (hidden U) (hidden V))
    (hlow : ∀ U V : Matrix.unitaryGroup A ℂ,
      interference (basisProjection (U : CMatrix A))
        (basisProjection (V : CMatrix A)) ≤ 1 / 3 →
        acceptance T tree ρ (hidden U) (hidden V) ≤ 1 / 3) :
    (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100 < (q : ℝ) := by
  apply ICO.C5Decision.measurement_only_lower_bound T tree ρ hdim
  · intro U
    apply hhigh U U
    rw [hidden_basis_high _ U.property.1 U.property.2]
    norm_num
  · exact hlow

/-- E.1 #4: Complete Corollary `thm:testing` (Constant-gap interference testing) packaged
as a single statement:
(1) Every ordinary strategy deciding `v ≥ 2/3` versus `v ≤ 1/3` across all channel pairs
    with success probability `≥ 2/3` has budget `q > d^(1/16) / 100`.
(2) Eighty uses of the quantum switch (`80 * 2 = 160` calls) decide `v ≥ 2/3` versus
    `v ≤ 1/3` for every pair of channels with error `< 1/3`.
(3) For `d ≥ 4` (`n ≥ 2`), the lower bound holds even when restricted to rank-one
    dephasing channels. -/
theorem constant_gap_interference_testing
    {A M O B : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    [Fintype M] [DecidableEq M] [Nonempty M] [Fintype O] [DecidableEq O] [Nonempty O]
    [Fintype B] [DecidableEq B] :
    (∀ {q : ℕ} (T : BinaryHypothesisTest O) (tree : Tree (A × M) O q B) (ρ : State B),
      (∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (E : ι → CMatrix A) (F : κ → CMatrix A)
        (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1),
        (2 / 3 : ℝ) ≤ interference E F →
          (2 / 3 : ℝ) ≤ acceptance T tree ρ
            (ICO.AllChannelDilation.oracleChannel (M := M) E hE)
            (ICO.AllChannelDilation.oracleChannel (M := M) F hF)) →
      (∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (E : ι → CMatrix A) (F : κ → CMatrix A)
        (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1),
        interference E F ≤ 1 / 3 →
          acceptance T tree ρ
            (ICO.AllChannelDilation.oracleChannel (M := M) E hE)
            (ICO.AllChannelDilation.oracleChannel (M := M) F hF) ≤ 1 / 3) →
      (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100 < (q : ℝ)) ∧
    (∀ {ι κ : Type} [Fintype ι] [Fintype κ]
      (E : ι → CMatrix A) (F : κ → CMatrix A)
      (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1),
      ((2 / 3 : ℝ) ≤ interference E F →
        (ICO.SwitchSampling.repetitions 80
          ((controlMeasurement (n := A)).prob (switchedState E F hE hF mixedState) true)
          (QIT.POVM.prob_le_one _ _ _)).real
            {ω | (∑ i, ICO.SwitchSampling.outcome i ω) < 60} < 1 / 3) ∧
      (interference E F ≤ 1 / 3 →
        (ICO.SwitchSampling.repetitions 80
          ((controlMeasurement (n := A)).prob (switchedState E F hE hF mixedState) true)
          (QIT.POVM.prob_le_one _ _ _)).real
            {ω | 60 ≤ ∑ i, ICO.SwitchSampling.outcome i ω} < 1 / 3)) ∧
    (4 ≤ Fintype.card A →
      ∀ {q : ℕ} (T : BinaryHypothesisTest O) (tree : Tree (A × M) O q B) (ρ : State B),
        (∀ U V : Matrix.unitaryGroup A ℂ,
          (2 / 3 : ℝ) ≤ interference (basisProjection (U : CMatrix A))
            (basisProjection (V : CMatrix A)) →
          (2 / 3 : ℝ) ≤ acceptance T tree ρ (hidden U) (hidden V)) →
        (∀ U V : Matrix.unitaryGroup A ℂ,
          interference (basisProjection (U : CMatrix A))
            (basisProjection (V : CMatrix A)) ≤ 1 / 3 →
          acceptance T tree ρ (hidden U) (hidden V) ≤ 1 / 3) →
        (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100 < (q : ℝ)) := by
  refine ⟨fun T tree ρ hhigh hlow =>
    all_channels_constant_gap_lower_bound T tree ρ hhigh hlow,
    fun E F hE hF => ⟨switch_eighty_high_error E F hE hF, switch_eighty_low_error E F hE hF⟩,
    fun hdim q T tree ρ hhigh hlow =>
      measurement_only_constant_gap_lower_bound T tree ρ hdim hhigh hlow⟩

/-- E.1 #12: Appendix D (`sec:capacity-qualification`) inherited `2q`-call bound:
a diagnostic with `1 ≤ q ≤ d^(1/16) / 200` contacts compiled into a `2q`-call
ordinary strategy has `SAME`-versus-`MUB` output distance at most `215 / 10000`
(and `212 / 10000`), and at `t = 3 / 4` the hybrid bound `215 / 10000 + q * t / (d + 1)`
is at most `101 / 4000 < 1 / 3`. -/
theorem capacity_inherited_same_mub_distance
    {A M O B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] [Nonempty M] [Fintype O] [DecidableEq O] [Nonempty O]
    [Fintype B] [DecidableEq B] {q : ℕ}
    (tree : Tree (A × M) O (2 * q) B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ)
    (hq : 1 ≤ q) (hqr : (q : ℝ) ≤ (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 200) :
    normalizedTraceDistance (sameDensity tree ρ) (mubDensity tree ρ H) ≤ 215 / 10000 ∧
    (215 / 10000 : ℝ) + (q : ℝ) * (3 / 4 : ℝ) / ((Fintype.card A : ℝ) + 1) ≤ 101 / 4000 ∧
    (101 / 4000 : ℝ) < 1 / 3 := by
  have h2q : 1 ≤ 2 * q := by omega
  have h2qr : ((2 * q : ℕ) : ℝ) ≤ (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 100 := by
    push_cast
    linarith
  have hd := same_mub_distance_212 tree ρ H h2q h2qr
  have hrpow := ICO.QuantumDecision.radius_power_sixteen (Fintype.card A) (by positivity)
  let r := (Fintype.card A : ℝ) ^ (1 / 16 : ℝ)
  have hqR : (1 : ℝ) ≤ (2 * q : ℕ) := by exact_mod_cast h2q
  obtain ⟨hr, _, _⟩ := radius_dimensions hqR h2qr
  have hr1 : 1 ≤ r := by
    have hr100 := ICO.TestingBounds.radius_ge_hundred hqR h2qr
    linarith
  have hr_le_r16 : r ≤ r ^ 16 := by
    simpa using pow_le_pow_right₀ hr1 (show (1 : ℕ) ≤ 16 by norm_num)
  have hr_le_d : r ≤ (Fintype.card A : ℝ) := by
    change ((Fintype.card A : ℝ) ^ (1 / 16 : ℝ)) ≤ ((Fintype.card A : ℝ) ^ (1 / 16 : ℝ)) ^ 16 at hr_le_r16
    linarith [hrpow, hr_le_r16]
  have hd_pos : 0 < (Fintype.card A : ℝ) + 1 := by positivity
  have hqt : (q : ℝ) * (3 / 4 : ℝ) / ((Fintype.card A : ℝ) + 1) ≤ (3 / 4 : ℝ) / 200 := by
    apply (div_le_iff₀ hd_pos).mpr
    have hqr' : (q : ℝ) * 200 ≤ r := by linarith
    nlinarith
  refine ⟨hd.1.trans (by linarith [hd.2.1]), by linarith, by norm_num⟩

#print axioms uniformError_le_212
#print axioms same_mub_distance_212
#print axioms zanardi_swap_same
#print axioms zanardi_swap_mub
#print axioms switch_depolarizing_oracle
#print axioms all_channels_constant_gap_lower_bound
#print axioms measurement_only_constant_gap_lower_bound
#print axioms constant_gap_interference_testing
#print axioms capacity_inherited_same_mub_distance

end
end ICO.C6BonusInventory

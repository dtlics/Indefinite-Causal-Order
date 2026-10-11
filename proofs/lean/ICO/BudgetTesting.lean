import ICO.BornAverage
import ICO.BudgetContinuity
import ICO.BudgetPreparation
import ICO.AveragedPromiseDecision

/-! The physical decision reduction for arbitrary finite adaptive circuits.
The single-Haar comparison is explicit here; the recording theorem can be
substituted without adding a probabilistic or measurement hypothesis. -/
namespace ICO.BudgetTesting
open Matrix QIT MeasureTheory ICO.BudgetQueryTree ICO.BudgetHaarBound
  ICO.BudgetContinuity ICO.BornAverage
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 600000
set_option Elab.async false
variable {A M O B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B]

def acceptance {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (first second : Channel (A×M) (A×M)) : ℝ :=
  acceptCLM T ((tree.channel first second).map ρ.matrix)

theorem acceptance_eq {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (first second : Channel (A×M) (A×M)) :
    acceptance T tree ρ first second=
      (T.acceptProb ((tree.channel first second).applyState ρ):ℝ) := by
  have he := accept_eq T ((tree.channel first second).applyState ρ)
  exact he

theorem acceptance_le_one {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (first second : Channel (A×M) (A×M)) :
    acceptance T tree ρ first second≤1 := by
  rw [acceptance_eq]
  exact_mod_cast T.prob_le_one ((tree.channel first second).applyState ρ) true

def SingleHaarBound (q : ℕ) (ρ : State B) (δ : ℝ) : Prop :=
  ∀ tree : Tree (A×M) O q B,
    normalizedTraceDistance
      (∫U,(ludersCircuit tree U).map ρ.matrix ∂unitaryHaarMeasure (a:=A))
      ((depolarizingCircuit tree).map ρ.matrix)≤δ

theorem singleHaarBound_of_prepared (q : ℕ) (ρ : State B) (δ : ℝ)
    (h : ∀ tree : Tree (A×M) O q PUnit,
      normalizedTraceDistance
        (∫U,(ludersCircuit tree U).map (rankOneMatrix (fun _ : PUnit => (1:ℂ)))
          ∂unitaryHaarMeasure (a:=A))
        ((depolarizingCircuit tree).map (rankOneMatrix (fun _ : PUnit => (1:ℂ))))≤δ) :
    SingleHaarBound (A:=A) (M:=M) (O:=O) q ρ δ := by
  intro tree
  have hh := h (ICO.BudgetPreparation.prepare tree ρ)
  simpa only [ludersCircuit,depolarizingCircuit,ICO.BudgetPreparation.prepare_output] using hh

theorem same_acceptance_bound {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (δ : ℝ)
    (h : SingleHaarBound (A:=A) (M:=M) (O:=O) q ρ δ) :
    |(∫U,acceptance T tree ρ (hidden U) (hidden U) ∂unitaryHaarMeasure (a:=A))-
      acceptance T tree ρ ICO.RecordingDepolarizing.withMemory ICO.RecordingDepolarizing.withMemory|≤δ := by
  let F := fun U => (ludersCircuit tree U).applyState ρ
  have hi : Integrable (fun U => (F U).matrix) (unitaryHaarMeasure (a:=A)) :=
    (luders_output_continuous tree ρ.matrix).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb := (abs_mean_accept_gap_le T F ((depolarizingCircuit tree).applyState ρ) hi).trans (h tree)
  simpa only [F,ludersCircuit,depolarizingCircuit,←acceptance_eq] using hb

theorem main_testing_impossible {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (δ : ℝ)
    (h : SingleHaarBound (A:=A) (M:=M) (O:=O) q ρ δ)
    (hhigh : ∀U, (2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : acceptance T tree ρ ICO.RecordingDepolarizing.withMemory
      ICO.RecordingDepolarizing.withMemory≤1/3) (hsmall : δ<1/3) : False := by
  have hi := (acceptCLM T).continuous.comp (luders_output_continuous tree ρ.matrix)
  have hint := hi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ:=unitaryHaarMeasure (a:=A))
  have hh := ICO.AveragedPromiseDecision.high_mean_ge _ hint hhigh
  change (2/3:ℝ)≤∫U,acceptance T tree ρ (hidden U) (hidden U)
    ∂unitaryHaarMeasure (a:=A) at hh
  have hb := (le_abs_self _).trans (same_acceptance_bound T tree ρ δ h)
  linarith

theorem fixed_acceptance_bound {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (δ : ℝ)
    (h : SingleHaarBound (A:=A) (M:=M) (O:=O) q ρ δ)
    (b : Bool) (Φ : Channel (A×M) (A×M)) :
    |(∫U,acceptance T tree ρ (if b then hidden U else Φ) (if b then Φ else hidden U)
        ∂unitaryHaarMeasure (a:=A))-
      acceptance T tree ρ (if b then ICO.RecordingDepolarizing.withMemory else Φ)
        (if b then Φ else ICO.RecordingDepolarizing.withMemory)|≤δ := by
  have hb := same_acceptance_bound T (tree.fixKnown b Φ) ρ δ h
  simpa only [acceptance,Tree.fixKnown_map] using hb

theorem independent_mean_lower {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (δ : ℝ)
    (h : SingleHaarBound (A:=A) (M:=M) (O:=O) q ρ δ) :
    acceptance T tree ρ ICO.RecordingDepolarizing.withMemory ICO.RecordingDepolarizing.withMemory-2*δ≤
      ∫p,acceptance T tree ρ (hidden p.1) (hidden p.2)
        ∂(unitaryHaarMeasure (a:=A)).prod (unitaryHaarMeasure (a:=A)) := by
  let μ := unitaryHaarMeasure (a:=A)
  have hprod := ((acceptCLM T).continuous.comp
    (independent_output_continuous tree ρ.matrix)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ:=μ.prod μ)
  have hfixed := ((acceptCLM T).continuous.comp
    (output_continuous tree BudgetContinuity.hidden (fun _ => ICO.RecordingDepolarizing.withMemory)
      hidden_continuous (fixed_continuous _) (fun _ => ρ.matrix) continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _) (μ:=μ)
  replace hfixed : Integrable (fun U => acceptance T tree ρ (hidden U) ICO.RecordingDepolarizing.withMemory) μ := by
    simpa only [acceptance,Function.comp_def] using hfixed
  replace hprod : Integrable (fun p => acceptance T tree ρ (hidden p.1) (hidden p.2)) (μ.prod μ) := by
    simpa only [acceptance,Function.comp_def] using hprod
  have hpoint (U : Matrix.unitaryGroup A ℂ) :
      acceptance T tree ρ (hidden U) ICO.RecordingDepolarizing.withMemory-δ≤
        ∫V,acceptance T tree ρ (hidden U) (hidden V) ∂μ := by
    have hb := (abs_le.mp (fixed_acceptance_bound T tree ρ δ h false (hidden U))).1
    simp only [Bool.false_eq_true,if_false] at hb
    change -δ≤(∫V,acceptance T tree ρ (hidden U) (hidden V) ∂μ)-
      acceptance T tree ρ (hidden U) ICO.RecordingDepolarizing.withMemory at hb
    linarith
  have hint := integral_mono (hfixed.sub (integrable_const δ)) hprod.integral_prod_left hpoint
  simp only [Pi.sub_apply] at hint
  rw [integral_sub hfixed (integrable_const δ)] at hint
  simp only [integral_const,probReal_univ,one_smul] at hint
  have hbase := (abs_le.mp (fixed_acceptance_bound T tree ρ δ h true
    ICO.RecordingDepolarizing.withMemory)).1
  simp only [ite_true] at hbase
  rw [integral_prod _ hprod]
  change _≤∫U,∫V,acceptance T tree ρ (hidden U) (hidden V) ∂μ ∂μ
  change -δ≤(∫U,acceptance T tree ρ (hidden U) ICO.RecordingDepolarizing.withMemory ∂μ)-
    acceptance T tree ρ ICO.RecordingDepolarizing.withMemory ICO.RecordingDepolarizing.withMemory at hbase
  linarith

theorem measurement_only_testing_impossible [Nontrivial A] {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (δ : ℝ)
    (h : SingleHaarBound (A:=A) (M:=M) (O:=O) q ρ δ)
    (hhigh : ∀U,(2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀U V : Matrix.unitaryGroup A ℂ, ICO.SwitchObservable.interference
      (ICO.SwitchObservable.basisProjection (U:CMatrix A))
      (ICO.SwitchObservable.basisProjection (V:CMatrix A))≤1/3 →
        acceptance T tree ρ (hidden U) (hidden V)≤1/3)
    (hsmall : 3*δ+6/((Fintype.card A:ℝ)+1)<1/3) : False := by
  let μ := unitaryHaarMeasure (a:=A)
  let bad : Set (Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ) :=
    {p | (1/3:ℝ)<ICO.SwitchObservable.interference
      (ICO.SwitchObservable.basisProjection (p.1:CMatrix A))
      (ICO.SwitchObservable.basisProjection (p.2:CMatrix A))}
  have hbad : MeasurableSet bad :=
    (isOpen_lt continuous_const ICO.LudersPromise.basis_interference_continuous).measurableSet
  have hprod := ((acceptCLM T).continuous.comp
    (independent_output_continuous tree ρ.matrix)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ:=μ.prod μ)
  have hsame := ((acceptCLM T).continuous.comp
    (luders_output_continuous tree ρ.matrix)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ:=μ)
  have hH := ICO.AveragedPromiseDecision.high_mean_ge _ hsame hhigh
  have hL := ICO.AveragedPromiseDecision.low_mean_le _ hprod bad hbad
    (fun p hp => hlow p.1 p.2 (le_of_not_gt hp))
    (fun p => acceptance_le_one T tree ρ _ _)
  have hm := ICO.LudersPromise.low_promise_failure_probability (A:=A)
  have hB := (le_abs_self _).trans (same_acceptance_bound T tree ρ δ h)
  have hI := independent_mean_lower T tree ρ δ h
  change (2/3:ℝ)≤∫U,acceptance T tree ρ (hidden U) (hidden U) ∂μ at hH
  change (∫p,acceptance T tree ρ (hidden p.1) (hidden p.2) ∂μ.prod μ)≤
    1/3+(μ.prod μ).real bad at hL
  change (μ.prod μ).real bad≤6/((Fintype.card A:ℝ)+1) at hm
  change (∫U,acceptance T tree ρ (hidden U) (hidden U) ∂μ)-
    acceptance T tree ρ ICO.RecordingDepolarizing.withMemory ICO.RecordingDepolarizing.withMemory≤δ at hB
  change acceptance T tree ρ ICO.RecordingDepolarizing.withMemory ICO.RecordingDepolarizing.withMemory-2*δ≤
    ∫p,acceptance T tree ρ (hidden p.1) (hidden p.2) ∂μ.prod μ at hI
  linarith

#print axioms main_testing_impossible
#print axioms measurement_only_testing_impossible
end
end ICO.BudgetTesting

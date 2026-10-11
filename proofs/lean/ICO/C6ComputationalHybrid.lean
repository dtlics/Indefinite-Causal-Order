import ICO.C6Decision
import ICO.C6ChoiceOutput
import ICO.C6SharedEndpoint

/-! Acceptance-level transfer for inverse-secure pseudorandom hidden devices.

The computational security of a keyed unitary family is an explicit
assumption, rather than statistical Haar closeness. The two adversaries are
the actual shared-unitary wrappers checked in C6SharedEndpoint and
C6ChoiceOutput: each channel call uses one inverse and one forward query,
with classical choice controlling only the known middle dephaser.

This module checks the two-hybrid probability guarantee for an actual
finite-memory channel learner and Born measurement. It does not formalize
asymptotic circuit running time or assert existence of a cryptographic family.
-/
namespace ICO.C6ComputationalHybrid
open Matrix QIT MeasureTheory ICO.BudgetQueryTree ICO.BudgetTesting
  ICO.BudgetContinuity ICO.C6Decision ICO.BornAverage
  ICO.QuantumDecision
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {A M O B K : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B] [Fintype K]

structure KeyDistribution (K : Type) [Fintype K] where
  weight : K → ℝ
  nonnegative : ∀k,0≤weight k
  total : ∑k,weight k=1

def haarAccept {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (H : Matrix.unitaryGroup A ℂ) : ℝ :=
  ∫ U, acceptance T tree ρ (hidden U) (hidden (U*H))
    ∂unitaryHaarMeasure (a:=A)

def keyedAccept {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B)
    (family : K → Matrix.unitaryGroup A ℂ) (p : KeyDistribution K)
    (H : Matrix.unitaryGroup A ℂ) : ℝ :=
  ∑k, p.weight k*acceptance T tree ρ (hidden (family k)) (hidden (family k*H))

theorem haar_acceptance_distance {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (H : Matrix.unitaryGroup A ℂ) :
    |haarAccept T tree ρ 1-haarAccept T tree ρ H|≤
      normalizedTraceDistance (sameDensity tree ρ) (mubDensity tree ρ H) := by
  let F := fun U : Matrix.unitaryGroup A ℂ =>
    (tree.channel (hidden U) (hidden U)).applyState ρ
  let G := fun U : Matrix.unitaryGroup A ℂ =>
    (tree.channel (hidden U) (hidden (U*H))).applyState ρ
  have hiF : Integrable (fun U => (F U).matrix) (unitaryHaarMeasure (a:=A)) :=
    (luders_output_continuous tree ρ.matrix).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiG : Integrable (fun U => (G U).matrix) (unitaryHaarMeasure (a:=A)) :=
    (correlated_output_continuous tree ρ.matrix H).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hf := accept_gap_le_traceDistance T (averageState F hiF) (averageState G hiG)
  have hg := accept_gap_le_traceDistance T (averageState G hiG) (averageState F hiF)
  rw [State.normalizedTraceDistance_comm] at hg
  rw [accept_average T F hiF,accept_average T G hiG] at hf hg
  have hb := abs_le.mpr ⟨by linarith, hf⟩
  simpa only [haarAccept,F,G,←acceptance_eq,mul_one,sameDensity,mubDensity,
    averageState,State.normalizedTraceDistance] using hb

/-- `h₀,h₁` are the computational distinguishing-advantage guarantees for
the two actual inverse/forward simulators. Their sum is essential: one
comparison with Haar would not cover both correlated device priors. -/
theorem keyed_relation_advantage {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B)
    (family : K → Matrix.unitaryGroup A ℂ) (p : KeyDistribution K)
    (H : Matrix.unitaryGroup A ℂ) (ε₀ ε₁ δ : ℝ)
    (h₀ : |keyedAccept T tree ρ family p 1-haarAccept T tree ρ 1|≤ε₀)
    (h₁ : |keyedAccept T tree ρ family p H-haarAccept T tree ρ H|≤ε₁)
    (hHaar : normalizedTraceDistance (sameDensity tree ρ) (mubDensity tree ρ H)≤δ) :
    |keyedAccept T tree ρ family p 1-keyedAccept T tree ρ family p H|≤ε₀+δ+ε₁ := by
  have hh := (haar_acceptance_distance T tree ρ H).trans hHaar
  have hs₁ := abs_sub_le (keyedAccept T tree ρ family p 1)
    (haarAccept T tree ρ 1) (keyedAccept T tree ρ family p H)
  have hs₂ := abs_sub_le (haarAccept T tree ρ 1)
    (haarAccept T tree ρ H) (keyedAccept T tree ρ family p H)
  rw [abs_sub_comm (haarAccept T tree ρ H) (keyedAccept T tree ρ family p H)] at hs₂
  linarith

#print axioms haar_acceptance_distance
#print axioms keyed_relation_advantage
end
end ICO.C6ComputationalHybrid

import ICO.C6UniformDecision
import ICO.C6OTOC
import ICO.FinitePOVMEvent

/-! Estimation-to-decision for the actual privately phase-averaged OTOC.
The estimator has access only to the two dephasing channels. Its finite POVM
output is thresholded classically, without additional queries. The physical
correlated-prior comparison is explicitly retained as a premise in this file.
No claim about coherent access to clock-phase unitaries is made. -/
namespace ICO.C6OTOCDecision
open Matrix QIT ICO.BudgetQueryTree ICO.BudgetContinuity ICO.BudgetTesting
open ICO.C6SwitchTest ICO.C6Decision ICO.C6OTOC ICO.FinitePOVMEvent
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {d : ℕ} [NeZero d]
  {M O B R : Type} [Fintype M] [DecidableEq M]
  [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
  [Fintype R] [DecidableEq R]

def good (value : R → ℝ) (ε x : ℝ) : Finset R :=
  Finset.univ.filter (fun r => |value r-x|≤ε)

def high (value : R → ℝ) : Finset R :=
  Finset.univ.filter (fun r => (3/4:ℝ)<value r)

theorem same_phase (U : Matrix.unitaryGroup (ZMod d) ℂ) :
    phaseOTOC (U:CMatrix (ZMod d)) (U:CMatrix (ZMod d)) = 1 := by
  have h := phaseOTOC_born U U
  rw [same_probability] at h
  linarith

theorem mub_phase (U V : Matrix.unitaryGroup (ZMod d) ℂ)
    (h : MutuallyUnbiased U V) :
    phaseOTOC (U:CMatrix (ZMod d)) (V:CMatrix (ZMod d)) = 1/(d:ℝ) := by
  rw [phaseOTOC_eq_interference, mub_interference U V h, ZMod.card]

theorem good_same_subset (value : R → ℝ) {ε : ℝ} (hε : ε<1/4) :
    good value ε 1 ⊆ high value := by
  intro r hr
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  simp only [high, Finset.mem_filter, Finset.mem_univ, true_and]
  have hh := (abs_le.mp hr).1
  linarith

theorem good_mub_subset (value : R → ℝ) {ε : ℝ} (hε : ε<1/4)
    (hd : 2≤d) : good value ε (1/(d:ℝ)) ⊆ (high value)ᶜ := by
  intro r hr
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  simp only [Finset.mem_compl, high, Finset.mem_filter, Finset.mem_univ, true_and,
    not_lt]
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  have hhalf : 1/(d:ℝ)≤1/2 := by
    apply (div_le_iff₀ (by linarith : (0:ℝ)<d)).mpr
    linarith
  have hh := (abs_le.mp hr).2
  linarith

/-- It suffices for the estimator to succeed on the SAME/MUB promise;
an estimator valid on all pairs satisfies this condition in particular. -/
def AccurateOnPromise {q : ℕ} (tree : Tree ((ZMod d)×M) O q B)
    (ρ : State B) (E : POVM R O) (value : R → ℝ) (ε : ℝ) : Prop :=
  ∀ U V : Matrix.unitaryGroup (ZMod d) ℂ, U=V ∨ MutuallyUnbiased U V →
    (2/3:ℝ)≤probability E ((tree.channel (hidden U) (hidden V)).applyState ρ)
      (good value ε (phaseOTOC (U:CMatrix (ZMod d)) (V:CMatrix (ZMod d))))

theorem estimator_gives_decision {q : ℕ} (tree : Tree ((ZMod d)×M) O q B)
    (ρ : State B) (E : POVM R O) (value : R → ℝ) {ε : ℝ}
    (hε : ε<1/4) (hd : 2≤d) (hc : AccurateOnPromise tree ρ E value ε) :
    (∀ U, (2/3:ℝ)≤acceptance (test E (high value)) tree ρ (hidden U) (hidden U)) ∧
    (∀ U V, MutuallyUnbiased U V →
      acceptance (test E (high value)) tree ρ (hidden U) (hidden V)≤1/3) := by
  constructor
  · intro U
    rw [acceptance_eq]
    have h := hc U U (Or.inl rfl)
    rw [same_phase] at h
    exact accuracy_implies_accept E _ _ _ (good_same_subset value hε) h
  · intro U V hUV
    rw [acceptance_eq]
    have h := hc U V (Or.inr hUV)
    rw [mub_phase U V hUV] at h
    exact accuracy_implies_reject E _ _ _ (good_mub_subset value hε hd) h

theorem lower_bound_of_comparison {q : ℕ} (tree : Tree ((ZMod d)×M) O q B)
    (ρ : State B) (E : POVM R O) (value : R → ℝ) {ε : ℝ}
    (hε : ε<1/4) (n : ℕ) (hn : 1≤n) (hd : d=2^n)
    (hcomparison : ∀ H : Matrix.unitaryGroup (ZMod d) ℂ,
      (∀ i j, Complex.normSq ((H:CMatrix (ZMod d)) i j)=1/(d:ℝ)) →
      1≤q → 2*q<d → 4*q≤d →
      normalizedTraceDistance (sameDensity tree ρ) (mubDensity tree ρ H)≤
        ICO.C6UniformBounds.uniformError q d ((d:ℝ)^(1/16:ℝ)))
    (hc : AccurateOnPromise tree ρ E value ε) : (d:ℝ)^(1/16:ℝ)/100 < q := by
  have hd2 : 2≤d := by
    rw [hd]
    have hh := Nat.pow_le_pow_right (by decide : (1:ℕ)≤2) hn
    simpa using hh
  obtain ⟨hh,hl⟩ := estimator_gives_decision tree ρ E value hε hd2 hc
  have hb := ICO.C6UniformDecision.lower_bound_of_comparison
    (test E (high value)) tree ρ n (by simpa only [ZMod.card] using hd)
    (by simpa only [ZMod.card] using hcomparison) hh hl
  simpa only [ZMod.card] using hb

#print axioms estimator_gives_decision
#print axioms lower_bound_of_comparison
end
end ICO.C6OTOCDecision

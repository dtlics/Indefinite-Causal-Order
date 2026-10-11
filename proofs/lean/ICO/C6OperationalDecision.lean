import ICO.C6SharedPairBound
import ICO.C6SharedOutput
import ICO.C6UniformDecision
import ICO.C6OTOCDecision
import ICO.C6ComputationalHybrid

/-! Operational consequences of the actual correlated-Haar experiment.
The physical comparison is proved for literal adaptive trees and arbitrary
mixed inputs. Only the keyed-family transfer keeps computational-security
hypotheses; it does not assume a quantum transcript bound. -/
namespace ICO.C6OperationalDecision
open Matrix QIT MeasureTheory ICO.BudgetQueryTree ICO.BudgetContinuity
  ICO.BudgetTesting ICO.C6Decision ICO.C6UniformBounds ICO.C6SwitchTest
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M O B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B]

theorem uniformError_nonneg (q : ℕ) (d r : ℝ) (hd : 0≤d) :
    0≤uniformError q d r := by
  rw [uniformError_formula]
  unfold ICO.C6Bounds.forwardError ICO.C6Bounds.creatorError
    ICO.C6Bounds.birthError uniformCacheError
  positivity

theorem empty_channel_unique {I : Type} [Fintype I] [DecidableEq I] [IsEmpty I]
    (Φ Ψ : Channel I I) : Φ=Ψ := by
  have hm : Φ.map=Ψ.map := by
    ext X i j
    exact isEmptyElim i
  cases Φ
  cases Ψ
  cases hm
  rfl

theorem empty_memory_density [IsEmpty M] {q : ℕ}
    (tree : Tree (A×M) O q B) (ρ : State B)
    (H₀ H₁ : Matrix.unitaryGroup A ℂ) :
    mubDensity tree ρ H₀=mubDensity tree ρ H₁ := by
  unfold mubDensity
  apply integral_congr_ae
  filter_upwards [] with U
  rw [empty_channel_unique (hidden (M:=M) (U*H₀)) (hidden (M:=M) (U*H₁))]


/-- Literal mixed-input adaptive output comparison. The hidden orientations
are correlated through one Haar unitary; the relative bases are arbitrary.
The empty-memory case is included, with no padding or nonemptiness premise. -/
theorem mixed_tree_comparison {q : ℕ}
    (tree : Tree (A×M) O q B) (ρ : State B)
    (H₀ H₁ : Matrix.unitaryGroup A ℂ) (hq : 1≤q)
    (hfour : 4*q≤Fintype.card A) (r : ℝ) (hr : 1≤r)
    (hd : (Fintype.card A:ℝ)=r^16) :
    normalizedTraceDistance (mubDensity tree ρ H₀) (mubDensity tree ρ H₁)≤
      uniformError q (Fintype.card A) r := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hm =>
    letI := hm
    rw [empty_memory_density tree ρ H₀ H₁,normalizedTraceDistance_self]
    exact uniformError_nonneg _ _ _ (by positivity)
  | inr hm =>
    letI := hm
    letI : Nonempty O := ((tree.channel (hidden (1:Matrix.unitaryGroup A ℂ))
      (hidden (1:Matrix.unitaryGroup A ℂ))).applyState ρ).nonempty
    letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    cases q with
    | zero => omega
    | succ q =>
      let a₀ : A := Classical.arbitrary A
      let m₀ : M := Classical.arbitrary M
      let o₀ : O := Classical.arbitrary O
      let p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀
        (ICO.BudgetPreparation.prepare tree ρ)
      let v := p.heading.pre*ᵥ(fun _ : PUnit=>(1:ℂ))
      have hv : ‖WithLp.toLp 2 v‖=1 :=
        ICO.C6SharedOutput.prepared_norm_eq p _ ICO.BudgetPreparation.initial_mass
      have hdim : (Fintype.card A:ℝ)=(r^2)^8 := by
        rw [hd]
        ring
      have hpair := ICO.C6SharedPairBound.shared_haar_pair p.heading.tail H₀ H₁ v
        (q+1) hv (by omega) hfour (r^2) (by nlinarith) hdim
      rw [Real.sqrt_sq (by linarith : 0≤r)] at hpair
      exact (ICO.C6SharedOutput.mixed_pair_contract a₀ m₀ o₀ tree ρ H₀ H₁).trans hpair

/-- The paper's explicit Haar bound for the complete adaptive tree and mixed
input. It contains no recording/cache/transcript-comparison hypothesis. -/
theorem adaptive_pair_distance {q : ℕ}
    (tree : Tree (A×M) O q B) (ρ : State B)
    (H₀ H₁ : Matrix.unitaryGroup A ℂ) (hq : 1≤q)
    (hfour : 4*q≤Fintype.card A) :
    normalizedTraceDistance (mubDensity tree ρ H₀) (mubDensity tree ρ H₁)≤
      uniformError q (Fintype.card A) ((Fintype.card A:ℝ)^(1/16:ℝ)) := by
  exact mixed_tree_comparison tree ρ H₀ H₁ hq hfour _
    (Real.one_le_rpow (by exact_mod_cast Fintype.card_pos (α:=A)) (by norm_num))
    (ICO.QuantumDecision.radius_power_sixteen _ (by positivity)).symm

/-- The displayed shared-basis indistinguishability formula, in the paper's
half-trace convention and literal dimension powers. -/
theorem adaptive_pair_distance_explicit {q : ℕ}
    (tree : Tree (A×M) O q B) (ρ : State B)
    (H₀ H₁ : Matrix.unitaryGroup A ℂ) (hq : 1≤q)
    (hfour : 4*q≤Fintype.card A) :
    normalizedTraceDistance (mubDensity tree ρ H₀) (mubDensity tree ρ H₁)≤
      18*(2*(q:ℝ))*(2*(q:ℝ)+1)/(Fintype.card A:ℝ)^(1/8:ℝ)+
      2*ICO.C6Bounds.forwardError q (Fintype.card A)+
      14*(q:ℝ)*ICO.C6Bounds.creatorError (2*(q:ℝ)) (Fintype.card A)+
      2*ICO.C6Bounds.birthError q (Fintype.card A)+
      8*(q:ℝ)*((q-1:ℕ):ℝ)/(Fintype.card A:ℝ) := by
  have hh := adaptive_pair_distance tree ρ H₀ H₁ hq hfour
  have hp : ((Fintype.card A:ℝ)^(1/16:ℝ))^2=
      (Fintype.card A:ℝ)^(1/8:ℝ) := by
    rw [←Real.rpow_two,←Real.rpow_mul (by positivity : (0:ℝ)≤Fintype.card A)]
    norm_num
  rw [uniformError_formula,hp] at hh
  unfold uniformCacheError at hh
  convert hh using 1; ring

theorem same_mub_distance {q : ℕ}
    (tree : Tree (A×M) O q B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ) (hq : 1≤q)
    (hfour : 4*q≤Fintype.card A) :
    normalizedTraceDistance (sameDensity tree ρ) (mubDensity tree ρ H)≤
      uniformError q (Fintype.card A) ((Fintype.card A:ℝ)^(1/16:ℝ)) := by
  have hh := adaptive_pair_distance tree ρ 1 H hq hfour
  simpa only [mubDensity,sameDensity,mul_one] using hh

/-- The operational SAME/MUB lower bound, with arbitrary finite quantum
memory, classical adaptive box choice, mixed input, and a binary final POVM. -/
theorem same_mub_query_lower_bound {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B) (n : ℕ)
    (hd : Fintype.card A=2^n)
    (hhigh : ∀ U, (2/3:ℝ)≤acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀ U V, MutuallyUnbiased U V →
      acceptance T tree ρ (hidden U) (hidden V)≤1/3) :
    (Fintype.card A:ℝ)^(1/16:ℝ)/100 < q := by
  apply ICO.C6UniformDecision.lower_bound_of_comparison T tree ρ n hd
    (fun H _ hq _ hfour=>same_mub_distance tree ρ H hq hfour) hhigh hlow

section OTOC
variable {d : ℕ} [NeZero d] {R : Type} [Fintype R] [DecidableEq R]

theorem otoc_query_lower_bound {q : ℕ} (tree : Tree ((ZMod d)×M) O q B)
    (ρ : State B) (E : POVM R O) (value : R→ℝ) {ε : ℝ}
    (hε : ε<1/4) (n : ℕ) (hn : 1≤n) (hd : d=2^n)
    (hc : ICO.C6OTOCDecision.AccurateOnPromise tree ρ E value ε) :
    (d:ℝ)^(1/16:ℝ)/100 < q := by
  apply ICO.C6OTOCDecision.lower_bound_of_comparison tree ρ E value hε n hn hd
    (fun H _ hq _ hfour=>?_) hc
  simpa only [ZMod.card] using same_mub_distance tree ρ H hq
    (by simpa only [ZMod.card] using hfour)
end OTOC

section Computational
variable [Nontrivial A] {K : Type} [Fintype K]

/-- Two computational-security assumptions, with the physical Haar term fully
proved. This is a finite-advantage transfer, not an existence assertion for a
cryptographic family or a formalization of asymptotic running time. -/
theorem keyed_relation_advantage {q : ℕ} (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O q B) (ρ : State B)
    (family : K→Matrix.unitaryGroup A ℂ)
    (p : ICO.C6ComputationalHybrid.KeyDistribution K)
    (H : Matrix.unitaryGroup A ℂ) (hq : 1≤q) (hfour : 4*q≤Fintype.card A)
    (ε₀ ε₁ : ℝ)
    (h₀ : |ICO.C6ComputationalHybrid.keyedAccept T tree ρ family p 1-
      ICO.C6ComputationalHybrid.haarAccept T tree ρ 1|≤ε₀)
    (h₁ : |ICO.C6ComputationalHybrid.keyedAccept T tree ρ family p H-
      ICO.C6ComputationalHybrid.haarAccept T tree ρ H|≤ε₁) :
    |ICO.C6ComputationalHybrid.keyedAccept T tree ρ family p 1-
      ICO.C6ComputationalHybrid.keyedAccept T tree ρ family p H|≤
      ε₀+uniformError q (Fintype.card A) ((Fintype.card A:ℝ)^(1/16:ℝ))+ε₁ := by
  exact ICO.C6ComputationalHybrid.keyed_relation_advantage T tree ρ family p H
    ε₀ ε₁ _ h₀ h₁ (same_mub_distance tree ρ H hq hfour)

omit [Nontrivial A] in
/-- With no oracle calls even keyed correlated priors give exactly the same
Born probability; no pseudorandomness assumption is necessary. -/
theorem keyed_zero_advantage (T : BinaryHypothesisTest O)
    (tree : Tree (A×M) O 0 B) (ρ : State B)
    (family : K→Matrix.unitaryGroup A ℂ)
    (p : ICO.C6ComputationalHybrid.KeyDistribution K)
    (H : Matrix.unitaryGroup A ℂ) :
    |ICO.C6ComputationalHybrid.keyedAccept T tree ρ family p 1-
      ICO.C6ComputationalHybrid.keyedAccept T tree ρ family p H|=0 := by
  have he : ICO.C6ComputationalHybrid.keyedAccept T tree ρ family p 1=
      ICO.C6ComputationalHybrid.keyedAccept T tree ρ family p H := by
    unfold ICO.C6ComputationalHybrid.keyedAccept
    apply Finset.sum_congr rfl
    intro k hk
    have hh := congrArg (fun f : MatrixMap B O=>ICO.BornAverage.acceptCLM T (f ρ.matrix))
      (ICO.BudgetHaarBound.zero_budget_map tree rfl
        (hidden (family k)) (hidden (family k*1))
        (hidden (family k)) (hidden (family k*H)))
    change acceptance T tree ρ (hidden (family k)) (hidden (family k*1))=
      acceptance T tree ρ (hidden (family k)) (hidden (family k*H)) at hh
    rw [hh]
  rw [he,sub_self,abs_zero]
end Computational

#print axioms adaptive_pair_distance
#print axioms adaptive_pair_distance_explicit
#print axioms same_mub_query_lower_bound
#print axioms otoc_query_lower_bound
#print axioms keyed_relation_advantage
#print axioms keyed_zero_advantage
end
end ICO.C6OperationalDecision

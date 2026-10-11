import ICO.C6SharedEndpoint
import ICO.ProtocolHaarOutput
import ICO.BudgetPreparation
import ICO.AdaptiveHaarBound
import ICO.C6Decision

/-! Actual terminal-channel semantics for the correlated shared-unitary prior.
All private copied outcomes are erased only after the full evolution. -/
namespace ICO.C6SharedOutput
open Matrix QIT MeasureTheory ICO.C6SharedEndpoint ICO.C6SharedBasis
  ICO.SequentialIsometry ICO.RecordingPurifiedProtocol ICO.RecordingHistory
  ICO.PureHybrid ICO.ProtocolHaarOutput ICO.AverageCoherence
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {A M O B : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
  [Fintype B] [DecidableEq B]

local instance matrixNonUnitalCStar {I : Type} [Fintype I] [DecidableEq I] :
    NonUnitalCStarAlgebra (CMatrix I) := ⟨⟩
local instance cmContinuousENorm {I : Type} [Fintype I] [DecidableEq I] :
    ContinuousENorm (CMatrix I) := SeminormedAddGroup.toContinuousENorm

theorem basis_continuous (H : Matrix.unitaryGroup A ℂ) :
    Continuous (fun U : Matrix.unitaryGroup A ℂ=>basis U H) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun U : Matrix.unitaryGroup A ℂ=>
      Matrix.kronecker (U:CMatrix A) (1:CMatrix Bool)*
        (knownBasis H:CMatrix (A×Bool))) :=
    (kronecker_one_continuous continuous_subtype_val).matrix_mul continuous_const
  convert hc using 1
  funext U
  change (basis U H:CMatrix (A×Bool))=_
  rw [basis_factor]
  change (shared U:CMatrix (A×Bool))*(knownBasis H:CMatrix (A×Bool))=_
  rw [shared_matrix]

theorem visible_continuous {q : ℕ}
    (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A×Bool)×M→ℂ) (n : ℕ) :
    Continuous (fun U : Matrix.unitaryGroup A ℂ=>eraseHistory.map (rankOneMatrix
      (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v n))) := by
  exact (visibleDensity_continuous tail v n).comp (basis_continuous H)

theorem haarDensity_pos {q : ℕ}
    (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A×Bool)×M→ℂ) (n : ℕ) :
    (ICO.C6SharedEndpoint.haarDensity tail H v n).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [ICO.C6SharedEndpoint.haarDensity]
  apply integral_nonneg
  intro U
  exact (eraseHistory.mapsPositive _
    (Matrix.posSemidef_vecMulVec_self_star
      (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v n))).nonneg

theorem haarDensity_trace {q : ℕ}
    (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A×Bool)×M→ℂ) (n : ℕ) :
    (ICO.C6SharedEndpoint.haarDensity tail H v n).trace=(rankOneMatrix v).trace := by
  have hi := (visible_continuous tail H v n).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ:=unitaryHaarMeasure (a:=A))
  have ht := (ICO.MHTraceIntegral.traceMulCLM
    (1:CMatrix ((A×Bool)×tail.tailMemory n))).integral_comp_comm hi
  change (∫U,(eraseHistory.map (rankOneMatrix
    (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v n))*1).trace
      ∂unitaryHaarMeasure (a:=A))=
    ((ICO.C6SharedEndpoint.haarDensity tail H v n)*1).trace at ht
  simp only [Matrix.mul_one] at ht
  rw [←ht]
  have hconst (U : Matrix.unitaryGroup A ℂ) :
      (eraseHistory.map (rankOneMatrix
        (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v n))).trace=
      (rankOneMatrix v).trace := by
    rw [ICO.ProtocolLudersTrajectory.run_erasure]
    exact tailEvolution_trace tail _
      (ICO.SwitchObservable.hidden_basis_kraus_complete _
        (basis U H).property.1 (basis U H).property.2) _ n
  simp_rw [hconst]
  simp

theorem haarDensity_output {q : ℕ}
    (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A×Bool)×M→ℂ) :
    tail.terminalChannel.map (ICO.C6SharedEndpoint.haarDensity tail H v (q+1))=
      ∫U,tail.map (ICO.SwitchObservable.basisProjection (basis U H:CMatrix (A×Bool)))
        (ICO.AllChannelDilation.oracleMap
          (ICO.SwitchObservable.basisProjection (basis U H:CMatrix (A×Bool)))
            (rankOneMatrix v)) ∂unitaryHaarMeasure (a:=A) := by
  have hi := (visible_continuous tail H v (q+1)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ:=unitaryHaarMeasure (a:=A))
  have ht := tail.terminalChannel.map.toContinuousLinearMap.integral_comp_comm hi
  change (∫U,tail.terminalChannel.map (eraseHistory.map (rankOneMatrix
    (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v (q+1))))
      ∂unitaryHaarMeasure (a:=A))=
    tail.terminalChannel.map (ICO.C6SharedEndpoint.haarDensity tail H v (q+1)) at ht
  rw [←ht]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [ICO.ProtocolLudersTrajectory.run_erasure]
  exact tail.tailEvolution_output _ _

theorem compiled_output {q : ℕ} (p : Protocol (A×Bool) B O (q+1))
    (H : Matrix.unitaryGroup A ℂ) (v : B→ℂ) :
    p.heading.tail.terminalChannel.map
      (ICO.C6SharedEndpoint.haarDensity p.heading.tail H (p.heading.pre*ᵥv) (q+1))=
      ∫U,p.map (ICO.SwitchObservable.basisProjection (basis U H:CMatrix (A×Bool)))
        (rankOneMatrix v) ∂unitaryHaarMeasure (a:=A) := by
  rw [haarDensity_output]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [Protocol.heading_map]
  simp only [LinearMap.comp_apply,singleMap_apply,
    rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]

theorem prepared_norm_eq {q : ℕ} (p : Protocol (A×Bool) B O (q+1))
    (v : B→ℂ) (hmass : (rankOneMatrix v).trace.re=1) :
    ‖WithLp.toLp 2 (p.heading.pre*ᵥv)‖=1 := by
  have hp := (congrArg Complex.re (ICO.AdaptiveHaarBound.prepared_trace p v)).trans hmass
  rw [ICO.ProtocolHaarOutput.rankOne_trace_re_norm_sq] at hp
  nlinarith [norm_nonneg (WithLp.toLp 2 (p.heading.pre*ᵥv))]

theorem tree_output {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O (q+1) B)
    (H : Matrix.unitaryGroup A ℂ) (v : B→ℂ) :
    let p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ tree
    p.heading.tail.terminalChannel.map
      (ICO.C6SharedEndpoint.haarDensity p.heading.tail H (p.heading.pre*ᵥv) (q+1))=
      ∫U,(tree.channel (ICO.BudgetContinuity.hidden U)
        (ICO.BudgetContinuity.hidden (U*H))).map (rankOneMatrix v)
          ∂unitaryHaarMeasure (a:=A) := by
  dsimp only
  rw [compiled_output]
  apply integral_congr_ae
  filter_upwards [] with U
  simpa only [ICO.C6SharedBasis.kraus,Bool.false_eq_true,ite_false,ite_true,
    ICO.BudgetContinuity.hidden] using
      ICO.C6ChoiceOutput.sequential_map a₀ m₀ o₀ tree U H (rankOneMatrix v)

theorem mixed_tree_output {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O (q+1) B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ) :
    let p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ)
    p.heading.tail.terminalChannel.map
      (ICO.C6SharedEndpoint.haarDensity p.heading.tail H
        (p.heading.pre*ᵥ(fun _ : PUnit=>(1:ℂ))) (q+1))=
      ICO.C6Decision.mubDensity tree ρ H := by
  have hh := tree_output a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ) H
    (fun _ : PUnit=>(1:ℂ))
  simpa only [ICO.BudgetPreparation.prepare_output,ICO.C6Decision.mubDensity] using hh

theorem mubDensity_one {q : ℕ} (tree : ICO.BudgetQueryTree.Tree (A×M) O q B)
    (ρ : State B) : ICO.C6Decision.mubDensity tree ρ 1=ICO.C6Decision.sameDensity tree ρ := by
  simp only [ICO.C6Decision.mubDensity,ICO.C6Decision.sameDensity,mul_one]

theorem mixed_pair_contract {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O (q+1) B) (ρ : State B)
    (H₀ H₁ : Matrix.unitaryGroup A ℂ) :
    let p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ)
    let v := p.heading.pre*ᵥ(fun _ : PUnit=>(1:ℂ))
    normalizedTraceDistance (ICO.C6Decision.mubDensity tree ρ H₀)
      (ICO.C6Decision.mubDensity tree ρ H₁)≤
      normalizedTraceDistance (ICO.C6SharedEndpoint.haarDensity p.heading.tail H₀ v (q+1))
        (ICO.C6SharedEndpoint.haarDensity p.heading.tail H₁ v (q+1)) := by
  dsimp only
  rw [←mixed_tree_output a₀ m₀ o₀ tree ρ H₀,←mixed_tree_output a₀ m₀ o₀ tree ρ H₁]
  exact ICO.RecordingDistance.distance_contract _
    (ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀
      (ICO.BudgetPreparation.prepare tree ρ)).heading.tail.terminalChannel.traceNonincreasingCP_map _ _
    (haarDensity_pos _ H₀ _ _) (haarDensity_pos _ H₁ _ _)

#print axioms basis_continuous
#print axioms haarDensity_pos
#print axioms haarDensity_trace
#print axioms compiled_output
#print axioms mixed_tree_output
#print axioms mixed_pair_contract
end
end ICO.C6SharedOutput

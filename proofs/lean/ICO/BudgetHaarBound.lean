import ICO.AdaptiveHaarBound

namespace ICO.BudgetHaarBound
open Matrix QIT MeasureTheory ICO.SequentialIsometry ICO.AdaptiveHaarBound
  ICO.RecordingPurifiedProtocol ICO.ProtocolHaarOutput ICO.AdaptiveSequentialProtocol
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
variable {A M B O : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype B] [DecidableEq B]
  [Fintype O] [DecidableEq O]

def ludersCircuit {q : ℕ} (tree : ICO.BudgetQueryTree.Tree (A×M) O q B)
    (U : Matrix.unitaryGroup A ℂ) : Channel B O :=
  let oracle := ICO.AllChannelDilation.oracleChannel (M:=M)
    (ICO.SwitchObservable.basisProjection (U:CMatrix A))
    (ICO.SwitchObservable.hidden_basis_kraus_complete _ U.property.1 U.property.2)
  tree.channel oracle oracle

def depolarizingCircuit {q : ℕ} (tree : ICO.BudgetQueryTree.Tree (A×M) O q B) : Channel B O :=
  tree.channel ICO.RecordingDepolarizing.withMemory ICO.RecordingDepolarizing.withMemory

theorem channel_eq_of_map_eq {C D : Type} [Fintype C] [DecidableEq C]
    [Fintype D] [DecidableEq D] (Φ Ψ : Channel C D) (h : Φ.map=Ψ.map) : Φ=Ψ := by
  cases Φ
  cases Ψ
  cases h
  rfl

theorem depolarizing_oracle :
    ICO.AllChannelDilation.oracleChannel (M:=M) (depolarizingKraus (A:=A)) depolarizingKraus_complete =
      ICO.RecordingDepolarizing.withMemory := by
  apply channel_eq_of_map_eq
  exact depolarizingKraus_memory

theorem budget_luders_map {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O q B) (U : Matrix.unitaryGroup A ℂ) (X : CMatrix B) :
    (budget a₀ m₀ o₀ tree).map (ICO.SwitchObservable.basisProjection (U:CMatrix A)) X =
      (ludersCircuit tree U).map X :=
  budget_map a₀ m₀ o₀ tree _
    (ICO.SwitchObservable.hidden_basis_kraus_complete _ U.property.1 U.property.2) X

theorem budget_depolarizing_map {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O q B) (X : CMatrix B) :
    (budget a₀ m₀ o₀ tree).map depolarizingKraus X = (depolarizingCircuit tree).map X := by
  rw [budget_map _ _ _ _ _ depolarizingKraus_complete,depolarizing_oracle]
  rfl

/-- Arbitrary finite adaptive total-query-budget strategies, including early
stopping, satisfy the desired physical comparison once the single Haar-to-
recording estimate is supplied for their explicitly compiled schedule. -/
theorem circuit_haar_bound {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O (q+1) B)
    (v : B → ℂ) (hv : ‖WithLp.toLp 2 v‖≤1) (hmass : (rankOneMatrix v).trace.re=1)
    (hqd : 2*(q+1)<Fintype.card A) (ε : ℝ)
    (hHaar : let p := budget a₀ m₀ o₀ tree
      normalizedTraceDistance (haarDensity p.heading.tail (p.heading.pre*ᵥv) (q+1))
        (visible (q+1) (ICO.ProtocolRecordingTrajectory.run p.heading.tail
          ICO.RecordingOracleAlgebra.forwardRecording (p.heading.pre*ᵥv) (q+1))) ≤ ε) :
    normalizedTraceDistance
      (∫ U, (ludersCircuit tree U).map (rankOneMatrix v) ∂unitaryHaarMeasure (a:=A))
      ((depolarizingCircuit tree).map (rankOneMatrix v)) ≤
      2*ε + 4*(q+1 : ℕ)*Real.sqrt (1/((Fintype.card A : ℝ)-(2*(q+1) : ℕ))) +
        (q+1 : ℕ)^2/(Fintype.card A : ℝ) := by
  have h := protocol_haar_bound (budget a₀ m₀ o₀ tree) v hv hmass hqd ε hHaar
  simp_rw [budget_luders_map,budget_depolarizing_map] at h
  exact h

theorem zero_budget_map {q : ℕ} (tree : ICO.BudgetQueryTree.Tree (A×M) O q B) (hq : q=0)
    (first second third fourth : Channel (A×M) (A×M)) :
    (tree.channel first second).map=(tree.channel third fourth).map := by
  induction tree with
  | stop after => rfl
  | query b after ih => omega
  | node instrument next ih =>
    change (∑ j,((next j).channel first second).map.comp
      (ICO.InstrumentCompression.branchMap instrument j)) =
      ∑ j,((next j).channel third fourth).map.comp (ICO.InstrumentCompression.branchMap instrument j)
    simp_rw [ih _ hq]

theorem zero_budget_distance (tree : ICO.BudgetQueryTree.Tree (A×M) O 0 B) (X : CMatrix B) :
    normalizedTraceDistance
      (∫ U, (ludersCircuit tree U).map X ∂unitaryHaarMeasure (a:=A))
      ((depolarizingCircuit tree).map X)=0 := by
  have he (U : Matrix.unitaryGroup A ℂ) :
      (ludersCircuit tree U).map X=(depolarizingCircuit tree).map X := by
    exact congrArg (fun f : MatrixMap B O => f X) (zero_budget_map tree rfl _ _ _ _)
  simp_rw [he]
  simp [normalizedTraceDistance_self]

#print axioms zero_budget_distance
#print axioms circuit_haar_bound
end
end ICO.BudgetHaarBound

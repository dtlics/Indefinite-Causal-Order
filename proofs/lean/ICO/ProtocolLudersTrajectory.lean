import ICO.PrivateQueryStep
import ICO.RecordingPurifiedProtocol
import ICO.AdaptiveSequentialProtocol

namespace ICO.ProtocolLudersTrajectory
open Matrix QIT ICO.SequentialIsometry ICO.RecordingHistory
  ICO.RecordingPurifiedProtocol ICO.SwitchObservable
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 2000000
variable {A M B O : Type u} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype B] [DecidableEq B]
  [Fintype O] [DecidableEq O]

/-- Literal purified Lüders evolution. Every step adds an inaccessible copied
basis index; public computation acts only on A and the declared memory. -/
def run {q : ℕ} (tail : Protocol A (A×M) O q) (U : CMatrix A) (v : A×M → ℂ) :
    (t : ℕ) → A×(History A t×tail.tailMemory t) → ℂ
  | 0 => fun o => v (o.1,o.2.2)
  | t+1 => ICO.PrivateQueryStep.luders U (tail.tailKnown t) *ᵥ run tail U v t

theorem run_erasure {q : ℕ} (tail : Protocol A (A×M) O q)
    (U : CMatrix A) (v : A×M → ℂ) (t : ℕ) :
    eraseHistory.map (rankOneMatrix (run tail U v t)) =
      tail.tailEvolution (basisProjection U) (rankOneMatrix v) t := by
  induction t with
  | zero =>
    rw [eraseHistory_rankOne]
    change (∑ e : PUnit.{u+1}, rankOneMatrix (fun o : A×M => v o)) = rankOneMatrix v
    simp
  | succ t ih =>
    rw [run]
    calc
      _ = tail.tailKnown t * ICO.AllChannelDilation.oracleMap (basisProjection U)
          (eraseHistory.map (rankOneMatrix (run tail U v t))) * (tail.tailKnown t).conjTranspose :=
        ICO.PrivateQueryStep.luders_erasure (H:=History A t) U (tail.tailKnown t) (run tail U v t)
      _ = _ := by rw [ih]; rfl

def output {q : ℕ} (p : Protocol A B O (q+1)) (U : CMatrix A) (v : B → ℂ) : CMatrix O :=
  MatrixMap.ofKraus (erasedKraus p.heading.tail.tailFinal)
    (eraseHistory.map (rankOneMatrix
      (run p.heading.tail U (p.heading.pre*ᵥv) (q+1))))

theorem output_map {q : ℕ} (p : Protocol A B O (q+1)) (U : CMatrix A) (v : B → ℂ) :
    output p U v = p.map (basisProjection U) (rankOneMatrix v) := by
  rw [output,run_erasure,Protocol.tailEvolution_output,Protocol.heading_map]
  simp only [LinearMap.comp_apply,singleMap_apply,
    rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]

#print axioms run_erasure
#print axioms output_map
end

section Budget
variable {A M B O : Type} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype B] [DecidableEq B]
  [Fintype O] [DecidableEq O]

/-- Exact actual-channel semantics for every adaptive finite total-budget
strategy on coincident hidden-basis Lüders oracles. -/
theorem budget_output {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : ICO.BudgetQueryTree.Tree (A×M) O (q+1) B)
    (U : Matrix.unitaryGroup A ℂ) (v : B → ℂ) :
    output (ICO.AdaptiveSequentialProtocol.budget a₀ m₀ o₀ tree) (U:CMatrix A) v =
      (tree.channel
        (ICO.AllChannelDilation.oracleChannel (basisProjection (U:CMatrix A))
          (hidden_basis_kraus_complete _ U.property.1 U.property.2))
        (ICO.AllChannelDilation.oracleChannel (basisProjection (U:CMatrix A))
          (hidden_basis_kraus_complete _ U.property.1 U.property.2))).map (rankOneMatrix v) := by
  rw [output_map,ICO.AdaptiveSequentialProtocol.budget_map]

#print axioms budget_output
end Budget
end ICO.ProtocolLudersTrajectory

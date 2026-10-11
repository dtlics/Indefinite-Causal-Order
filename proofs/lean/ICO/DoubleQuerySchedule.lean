import ICO.LudersUnitaryStages
import ICO.ProtocolLudersTrajectory

namespace ICO.DoubleQuerySchedule
open Matrix QIT ICO.SequentialIsometry ICO.RecordingPurifiedProtocol
  ICO.RecordingPublicStep ICO.LudersUnitaryStages
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 2400000
variable {A : Type u} [Fintype A] [DecidableEq A]
variable (μ : ℕ → Type u) [∀ t,Fintype (μ t)] [∀ t,DecidableEq (μ t)]

/-- Two-stage memory family, starting before the k-th Lüders query. The odd
stage has just acquired its new private copy; the next even stage has executed
public computation and advanced the physical time. -/
def Memory (k : ℕ) : ℕ → Type u
  | 0 => History A k×μ k
  | 1 => A×(History A k×μ k)
  | n+2 => Memory (k+1) n

instance memoryFinite (k n : ℕ) : Fintype (Memory (A:=A) μ k n) := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => exact inferInstanceAs (Fintype (History A k×μ k))
  | one => exact inferInstanceAs (Fintype (A×(History A k×μ k)))
  | more n ih ih' => exact ih (k+1)

instance memoryDecide (k n : ℕ) : DecidableEq (Memory (A:=A) μ k n) := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => exact inferInstanceAs (DecidableEq (History A k×μ k))
  | one => exact inferInstanceAs (DecidableEq (A×(History A k×μ k)))
  | more n ih ih' => exact ih (k+1)

def direction : ℕ → Bool
  | 0 => true
  | 1 => false
  | n+2 => direction n

variable {μ}

def known (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ) (k : ℕ) (n : ℕ) :
    Matrix (A×Memory (A:=A) μ k (n+1)) (A×Memory (A:=A) μ k n) ℂ := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => exact copyQuery
  | one => exact publicStep (h:=History A k) (K k)
  | more n ih ih' => exact ih (k+1)

theorem known_isometry (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (hK : ∀t,(K t).conjTranspose*K t=1) (k n : ℕ) :
    (known K k n).conjTranspose*known K k n=1 := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => exact copyQuery_isometry
  | one => exact publicStep_isometry (K k) (hK k)
  | more n ih ih' => exact ih (k+1)

def oracle (U : CMatrix A) (n : ℕ) : CMatrix A :=
  if direction n then U.conjTranspose else U

def runFrom (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (U : CMatrix A) (k : ℕ) (v : A×Memory (A:=A) μ k 0 → ℂ) :
    (n : ℕ) → A×Memory (A:=A) μ k n → ℂ
  | 0 => v
  | n+1 => known K k n *ᵥ
      ((Matrix.kronecker (oracle U n) (1 : CMatrix (Memory (A:=A) μ k n))) *ᵥ
        runFrom K U k v n)

theorem runFrom_two (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (U : CMatrix A) (k : ℕ) (v : A×Memory (A:=A) μ k 0 → ℂ) :
    runFrom K U k v 2=ICO.PrivateQueryStep.luders U (K k) *ᵥ v := by
  change publicStep (h:=History A k) (K k) *ᵥ
    (Matrix.kronecker U (1 : CMatrix (A×(History A k×μ k))) *ᵥ
      (copyQuery *ᵥ (Matrix.kronecker U.conjTranspose
        (1 : CMatrix (History A k×μ k)) *ᵥ v))) = _
  simpa only [step, Matrix.mulVec_mulVec, Matrix.mul_assoc] using
    congrArg (fun W => W *ᵥ v) (step_eq_luders (H:=History A k) U (K k))

theorem runFrom_shift (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (U : CMatrix A) (k : ℕ) (v : A×Memory (A:=A) μ k 0 → ℂ) (n : ℕ) :
    runFrom K U k v (n+2)=
      runFrom K U (k+1) (ICO.PrivateQueryStep.luders U (K k) *ᵥ v) n := by
  induction n with
  | zero => exact runFrom_two K U k v
  | succ n ih =>
    change known K (k+1) n *ᵥ
      ((Matrix.kronecker (oracle U n) (1 : CMatrix (Memory (A:=A) μ (k+1) n))) *ᵥ
        runFrom K U k v (n+2)) = _
    rw [ih]
    rfl

theorem memory_even_eq (k n : ℕ) :
    Memory (A:=A) μ k (2*n)=(History A (k+n)×μ (k+n)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have hn : 2*(n+1)=2*n+2 := by omega
    rw [hn]
    change Memory (A:=A) μ (k+1) (2*n)=_
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih (k+1)

def stateEquiv (Q : Type u) (k n : ℕ) :
    Q×Memory (A:=A) μ k (2*n) ≃ Q×(History A (k+n)×μ (k+n)) :=
  Equiv.cast (congrArg (fun X => Q×X) (memory_even_eq (A:=A) (μ:=μ) k n))

theorem heq_cast_fun {I J : Type u} (h : I=J) (f : I → ℂ) (g : J → ℂ)
    (hf : HEq f g) : f=g ∘ Equiv.cast h := by
  cases h
  exact eq_of_heq hf

theorem runFrom_even_heq (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (U : CMatrix A) (x : (t : ℕ) → A×(History A t×μ t) → ℂ)
    (hx : ∀t,x (t+1)=ICO.PrivateQueryStep.luders U (K t) *ᵥ x t) (k n : ℕ) :
    HEq (runFrom K U k (x k) (2*n)) (x (k+n)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have hn : 2*(n+1)=2*n+2 := by omega
    rw [hn,runFrom_shift]
    have hh : ICO.PrivateQueryStep.luders (H:=History A k) U (K k) *ᵥ x k=x (k+1) := (hx k).symm
    have hh' := congrArg (fun z => runFrom K U (k+1) z (2*n)) hh
    apply HEq.trans (heq_of_eq hh')
    have hdep : ∀a b,a=b → HEq (x a) (x b) := by
      intro a b h
      cases h
      rfl
    exact (ih (k+1)).trans (hdep _ _ (by omega))

theorem runFrom_even (K : (t : ℕ) → Matrix (A×μ (t+1)) (A×μ t) ℂ)
    (U : CMatrix A) (x : (t : ℕ) → A×(History A t×μ t) → ℂ)
    (hx : ∀t,x (t+1)=ICO.PrivateQueryStep.luders U (K t) *ᵥ x t) (k n : ℕ) :
    runFrom K U k (x k) (2*n)=x (k+n) ∘ stateEquiv A k n :=
  heq_cast_fun _ _ _ (runFrom_even_heq K U x hx k n)

def zeroEquiv (Q : Type u) (n : ℕ) :
    Q×Memory (A:=A) μ 0 (2*n) ≃ Q×(History A n×μ n) :=
  Equiv.cast (congrArg (fun X => Q×X) (by
    simpa only [Nat.zero_add] using memory_even_eq (A:=A) (μ:=μ) 0 n))

theorem dependent_heq {I : Type*} {T : I → Type*} (f : (i : I) → T i)
    {i j : I} (h : i=j) : HEq (f i) (f j) := by
  cases h
  rfl

theorem physical_even {M O : Type u} [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] {q : ℕ} (tail : Protocol A (A×M) O q)
    (U : CMatrix A) (v : A×M → ℂ) (n : ℕ) :
    runFrom tail.tailKnown U 0 (ICO.ProtocolLudersTrajectory.run tail U v 0) (2*n)=
      ICO.ProtocolLudersTrajectory.run tail U v n ∘ zeroEquiv (A:=A) (μ:=tail.tailMemory) A n := by
  have h := runFrom_even_heq tail.tailKnown U (ICO.ProtocolLudersTrajectory.run tail U v)
    (fun t => rfl) 0 n
  apply heq_cast_fun
  exact h.trans (dependent_heq (ICO.ProtocolLudersTrajectory.run tail U v) (Nat.zero_add n))

#print axioms known_isometry
#print axioms physical_even
#print axioms runFrom_even_heq
#print axioms runFrom_shift
end
end ICO.DoubleQuerySchedule

import ICO.C6SharedStages

namespace ICO.C6SharedSchedule
open Matrix QIT ICO.SequentialIsometry ICO.RecordingPurifiedProtocol
  ICO.RecordingPublicStep ICO.C6SharedStages ICO.C6SharedBasis
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable (μ : ℕ→Type) [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

abbrev Memory (k n:ℕ) := ICO.DoubleQuerySchedule.Memory (A:=A×Bool) μ k n

variable {μ}
def knownTagged (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ) (k n:ℕ) :
    Matrix ((A×Bool)×Memory (A:=A) μ k (n+1)) ((A×Bool)×Memory (A:=A) μ k n) ℂ := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => exact middle H
  | one => exact publicStep (h:=History (A×Bool) k) (K k)
  | more n ih ih' => exact ih (k+1)

theorem knownTagged_isometry (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (hK:∀t,(K t)ᴴ*K t=1) (k n:ℕ) :
    (knownTagged H K k n)ᴴ*knownTagged H K k n=1 := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => exact middle_isometry H
  | one => exact publicStep_isometry (K k) (hK k)
  | more n ih ih' => exact ih (k+1)

def taggedOracle (U : Matrix.unitaryGroup A ℂ) (n:ℕ) : CMatrix (A×Bool) :=
  if ICO.DoubleQuerySchedule.direction n then (shared U:CMatrix (A×Bool))ᴴ else shared U

def taggedRun (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (U : Matrix.unitaryGroup A ℂ) (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) :
    (n:ℕ)→(A×Bool)×Memory (A:=A) μ k n→ℂ
  | 0 => v
  | n+1 => knownTagged H K k n *ᵥ
    (lift (taggedOracle U n) *ᵥ taggedRun H K U k v n)

theorem taggedRun_two (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (U : Matrix.unitaryGroup A ℂ) (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) :
    taggedRun H K U k v 2 =
      ICO.PrivateQueryStep.luders (basis U H:CMatrix (A×Bool)) (K k)*ᵥv := by
  change publicStep (h:=History (A×Bool) k) (K k)*ᵥ
    (lift (shared U:CMatrix (A×Bool))*ᵥ(middle H*ᵥ
      (lift (shared U:CMatrix (A×Bool))ᴴ*ᵥv)))=_
  simpa only [step,Matrix.mulVec_mulVec,Matrix.mul_assoc] using
    congrArg (fun W=>W*ᵥv) (step_eq_luders (E:=History (A×Bool) k) U H (K k))

theorem taggedRun_shift (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (U : Matrix.unitaryGroup A ℂ) (k:ℕ) (v:(A×Bool)×Memory (A:=A) μ k 0→ℂ) (n:ℕ) :
    taggedRun H K U k v (n+2) = taggedRun H K U (k+1)
      (ICO.PrivateQueryStep.luders (basis U H:CMatrix (A×Bool)) (K k)*ᵥv) n := by
  induction n with
  | zero => exact taggedRun_two H K U k v
  | succ n ih =>
    change knownTagged H K (k+1) n*ᵥ(lift (taggedOracle U n)*ᵥ
      taggedRun H K U k v (n+2))=_
    rw [ih]
    rfl

theorem taggedRun_even_heq (H : Matrix.unitaryGroup A ℂ)
    (K : (t:ℕ)→Matrix ((A×Bool)×μ (t+1)) ((A×Bool)×μ t) ℂ)
    (U : Matrix.unitaryGroup A ℂ)
    (x:(t:ℕ)→(A×Bool)×(History (A×Bool) t×μ t)→ℂ)
    (hx:∀t,x (t+1)=ICO.PrivateQueryStep.luders (basis U H:CMatrix (A×Bool)) (K t)*ᵥx t)
    (k n:ℕ) : HEq (taggedRun H K U k (x k) (2*n)) (x (k+n)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have hn : 2*(n+1)=2*n+2 := by omega
    rw [hn,taggedRun_shift]
    have hh := congrArg (fun z=>taggedRun H K U (k+1) z (2*n)) (hx k).symm
    apply HEq.trans (heq_of_eq hh)
    exact (ih (k+1)).trans
      (ICO.DoubleQuerySchedule.dependent_heq x (by omega : k+1+n=k+(n+1)))

theorem tagged_physical_even {M O : Type} [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] {q:ℕ} (tail : Protocol (A×Bool) ((A×Bool)×M) O q)
    (U H : Matrix.unitaryGroup A ℂ) (v:(A×Bool)×M→ℂ) (n:ℕ) :
    taggedRun H tail.tailKnown U 0
      (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v 0) (2*n)=
      ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v n ∘
        ICO.DoubleQuerySchedule.zeroEquiv (A:=A×Bool) (μ:=tail.tailMemory) (A×Bool) n := by
  have hh := taggedRun_even_heq H tail.tailKnown U
    (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v) (fun t=>rfl) 0 n
  apply ICO.DoubleQuerySchedule.heq_cast_fun
  exact hh.trans (ICO.DoubleQuerySchedule.dependent_heq
    (ICO.ProtocolLudersTrajectory.run tail (basis U H:CMatrix (A×Bool)) v) (Nat.zero_add n))

#print axioms tagged_physical_even
end
end ICO.C6SharedSchedule

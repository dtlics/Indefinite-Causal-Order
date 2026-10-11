import ICO.C6PairedTrajectory
import ICO.C6SharedQuerySchedule

/-! The paired Fock trajectory is exactly the even-time subsequence of the
signed recording trajectory used in the actual Haar comparison. -/
namespace ICO.C6SharedFockSchedule
open Matrix QIT ICO.C6FockPairs ICO.C6PairedTrajectory ICO.C6SharedSchedule
  ICO.C6SharedQuerySchedule ICO.C6SharedStages ICO.C6FockChoiceMeasurement
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockOracle ICO.MHFockTrajectory
  ICO.MHFockKnownOperation ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def choice {T:ℕ} (F B:CMatrix (InputCutoff (α:=A) T)) (n:ℕ) :=
  if ICO.DoubleQuerySchedule.direction n then B else F

def runFrom {T:ℕ} (F B:CMatrix (InputCutoff (α:=A) T)) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (k:ℕ)
    (v:InputCutoff (α:=A) T×QueryMemory (A:=A) μ k 0→ℂ) :
    (n:ℕ)→InputCutoff (α:=A) T×QueryMemory (A:=A) μ k n→ℂ
  | 0 => v
  | n+1 => ICO.MHFockKnownOperation.known T (ICO.C6SharedQuerySchedule.known H K k n)*ᵥ
    (Matrix.kronecker (choice F B n) (1:CMatrix (QueryMemory (A:=A) μ k n))*ᵥ
      runFrom F B H K k v n)

theorem runFrom_two {T:ℕ} (F B:CMatrix (InputCutoff (α:=A) T)) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (k:ℕ)
    (v:InputCutoff (α:=A) T×QueryMemory (A:=A) μ k 0→ℂ) :
    runFrom F B H K k v 2=pair (E:=History (A×Bool) k) F B H (K k)*ᵥv := by
  change ICO.MHFockKnownOperation.known T (publicQuery (E:=History (A×Bool) k) (K k))*ᵥ
    (Matrix.kronecker F (1:CMatrix (Bool×((A×Bool)×(History (A×Bool) k×μ k))))*ᵥ
      (ICO.MHFockKnownOperation.known T (middleQuery H)*ᵥ
        (Matrix.kronecker B (1:CMatrix (Public (A:=A) μ k))*ᵥv)))=_
  simp only [pair,Matrix.mulVec_mulVec,Matrix.mul_assoc]

theorem runFrom_shift {T:ℕ} (F B:CMatrix (InputCutoff (α:=A) T)) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (k:ℕ)
    (v:InputCutoff (α:=A) T×QueryMemory (A:=A) μ k 0→ℂ) (n:ℕ) :
    runFrom F B H K k v (n+2)=
      runFrom F B H K (k+1) (pair (E:=History (A×Bool) k) F B H (K k)*ᵥv) n := by
  induction n with
  | zero => exact runFrom_two F B H K k v
  | succ n ih =>
    change ICO.MHFockKnownOperation.known T (ICO.C6SharedQuerySchedule.known H K (k+1) n)*ᵥ
      (Matrix.kronecker (choice F B n) (1:CMatrix (QueryMemory (A:=A) μ (k+1) n))*ᵥ
        runFrom F B H K k v (n+2))=_
    rw [ih]
    rfl

theorem even_heq {T:ℕ} (F B:CMatrix (InputCutoff (α:=A) T)) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (x:∀i,InputCutoff (α:=A) T×Public (A:=A) μ i→ℂ)
    (hx:∀i,x (i+1)=pair (E:=History (A×Bool) i) F B H (K i)*ᵥx i) (k n:ℕ) :
    HEq (runFrom F B H K k (x k) (2*n)) (x (k+n)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,runFrom_shift]
    have hh := congrArg (fun z=>runFrom F B H K (k+1) z (2*n)) (hx k).symm
    apply HEq.trans (heq_of_eq hh)
    exact (ih (k+1)).trans (ICO.DoubleQuerySchedule.dependent_heq x (by omega : k+1+n=k+(n+1)))

def endpointEquiv (T n:ℕ) :
    (InputCutoff (α:=A) T×QueryMemory (A:=A) μ 0 (2*n)) ≃
      (InputCutoff (α:=A) T×Public (A:=A) μ n) :=
  Equiv.cast (congrArg (fun X=>InputCutoff (α:=A) T×(Bool×X)) (by
    simpa only [Nat.zero_add] using
      ICO.DoubleQuerySchedule.memory_even_eq (A:=A×Bool) (μ:=μ) 0 n))

theorem native_run {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (n:ℕ) :
    ICO.MHFockTrajectory.run T (ICO.C6SharedQuerySchedule.known H K 0)
      (fun i=>Vchoice h (ICO.DoubleQuerySchedule.direction i)) z n=
    runFrom (fullOracle h) (fullOracle h)ᴴ H K 0 (ICO.MHFockTrajectory.initial T z) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ICO.MHFockTrajectory.run,runFrom,ih]
    rfl

theorem native_even {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (n:ℕ) :
    ICO.MHFockTrajectory.run T (ICO.C6SharedQuerySchedule.known H K 0)
      (fun i=>Vchoice h (ICO.DoubleQuerySchedule.direction i)) z (2*n)=
    WithLp.ofLp (ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (fullStage h H K)
      (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) n) ∘ endpointEquiv (μ:=μ) T n := by
  rw [native_run]
  have hh := even_heq (fullOracle h) (fullOracle h)ᴴ H K
    (fun i=>WithLp.ofLp (ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (fullStage h H K)
      (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i)) (fun i=>rfl) 0 n
  apply ICO.DoubleQuerySchedule.heq_cast_fun
  exact hh.trans (ICO.DoubleQuerySchedule.dependent_heq
    (fun i=>WithLp.ofLp (ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (fullStage h H K)
      (WithLp.toLp 2 (ICO.MHFockTrajectory.initial T z)) i)) (Nat.zero_add n))

#print axioms native_even
end
end ICO.C6SharedFockSchedule

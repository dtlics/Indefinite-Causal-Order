import ICO.MHFockTrajectory

/-! Reachability and bijection support as literal projection equations,
including arbitrary entangled spectator memory. -/
namespace ICO.MHFockSupportProjection
open QIT ICO.MHFockTrajectory ICO.MHFockProjection ICO.MHFockAlgebra
  ICO.MHBoundedRecording ICO.MHBijectionProfiles ICO.MHFockLabels ICO.MHWDomainProjection
open scoped Matrix
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 512

theorem supported_diagonal {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (P : a→Prop) [DecidablePred P] (v : a×b→ℂ)
    (hv : Supported (fun i => P i.1) v) :
    Matrix.kronecker (Matrix.diagonal (fun i => if P i then (1:ℂ) else 0))
      (1 : CMatrix b)*ᵥv=v := by
  simp only [Matrix.kronecker,←Matrix.diagonal_one,Matrix.diagonal_kronecker_diagonal]
  ext i
  simp only [Matrix.mulVec_diagonal,mul_one]
  by_cases hi : P i.1
  · simp [hi]
  · have hz : v i=0 := by by_contra hn; exact hi (hv i hn)
    simp [hi,hz]

variable {α : Type*} [Fintype α] [DecidableEq α]
  {μ : Type*} [Fintype μ] [DecidableEq μ]

theorem source_fixed {q T : ℕ} (hq : q≤T) (v : InputCutoff (α := α) T×μ→ℂ)
    (hv : Supported (fun i => grade i.1≤q) v) :
    Matrix.kronecker (sourceProjection (α := α) hq) (1 : CMatrix μ)*ᵥv=v := by
  rw [sourceProjection_diagonal]
  exact supported_diagonal _ _ hv

theorem bij_fixed {T : ℕ} (v : InputCutoff (α := α) T×μ→ℂ)
    (hv : Supported (fun i => BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2) v) :
    Matrix.kronecker (bijProjection (α := α) T) (1 : CMatrix μ)*ᵥv=v := by
  classical
  exact supported_diagonal _ _ hv

variable {ν : ℕ→Type*} [∀t,Fintype (ν t)] [∀t,DecidableEq (ν t)]

theorem Vrun_source_fixed {q T : ℕ} (hq : q+1≤T)
    (K : (t:ℕ)→Matrix (α×ν (t+1)) (α×ν t) ℂ) (dir : ℕ→Bool)
    (z : α×ν 0→ℂ) {s : ℕ} (hs : s≤q) :
    Matrix.kronecker (sourceProjection (α := α) (Nat.le_trans (Nat.le_succ q) hq))
      (1 : CMatrix (ν s))*ᵥrun T K (fun t => Vchoice hq (dir t)) z s=
      run T K (fun t => Vchoice hq (dir t)) z s := by
  apply source_fixed
  intro i hi
  exact (Vrun_grade hq K dir z s i hi).trans hs

theorem Wrun_source_fixed {q T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (hq : q≤T)
    (K : (t:ℕ)→Matrix (α×ν (t+1)) (α×ν t) ℂ) (dir : ℕ→Bool)
    (z : α×ν 0→ℂ) {s : ℕ} (hs : s≤q) :
    Matrix.kronecker (sourceProjection (α := α) hq)
      (1 : CMatrix (ν s))*ᵥrun T K (fun t => Wchoice hT (dir t)) z s=
      run T K (fun t => Wchoice hT (dir t)) z s := by
  apply source_fixed
  intro i hi
  exact (Wrun_grade hT K dir z s i hi).trans hs

theorem Wrun_bij_fixed {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (K : (t:ℕ)→Matrix (α×ν (t+1)) (α×ν t) ℂ) (dir : ℕ→Bool)
    (z : α×ν 0→ℂ) (s : ℕ) :
    Matrix.kronecker (bijProjection (α := α) T)
      (1 : CMatrix (ν s))*ᵥrun T K (fun t => Wchoice hT (dir t)) z s=
      run T K (fun t => Wchoice hT (dir t)) z s :=
  bij_fixed _ (Wrun_bij hT K dir z s)

#print axioms Vrun_source_fixed
#print axioms Wrun_bij_fixed
end
end ICO.MHFockSupportProjection

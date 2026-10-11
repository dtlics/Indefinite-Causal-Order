import ICO.MHFiniteSignedTrajectory

/-! Every finite-set signed recording trajectory is exactly the occupation
trajectory up to its fixed query budget, not merely a compressed surrogate. -/
namespace ICO.MHFockFiniteTrajectory
open QIT ICO.MHFockFiniteKnown ICO.MHFiniteSignedTrajectory ICO.MHFockTrajectory
  ICO.MHFockKnownOperation ICO.MHFockLowInput ICO.MHFockNodup ICO.MHBoundedRecording
  ICO.RecordingOperatorSupport ICO.RecordingOracleAlgebra ICO.RecordingCopyIdentity
  ICO.MHEmbeddingProjector
open scoped Matrix
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 512
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem choice_low_intertwining {q T : ℕ} (hq : q+1≤T)
    (hT : 2*Fintype.card (α×α)≤T) (hqd : q<Fintype.card α) (inverse : Bool) :
    Vchoice hq inverse*basisEmbedding (setEmbedding hT)*oldSourceCutoff q=
      basisEmbedding (setEmbedding hT)*oldChoice inverse*oldSourceCutoff q := by
  cases inverse
  · exact fullOracle_nodup_low hq hT hqd
  · exact fullOracle_nodup_adjoint_low hq hT hqd

theorem memory_choice_low_intertwining {q T : ℕ} (hq : q+1≤T)
    (hT : 2*Fintype.card (α×α)≤T) (hqd : q<Fintype.card α) (inverse : Bool)
    {μ : Type*} [Fintype μ] [DecidableEq μ] :
    Matrix.kronecker (Vchoice hq inverse) (1 : CMatrix μ)*basisEmbedding (setMemory hT)*
      Matrix.kronecker (oldSourceCutoff q) (1 : CMatrix μ)=
    basisEmbedding (setMemory hT)*Matrix.kronecker (oldChoice inverse) (1 : CMatrix μ)*
      Matrix.kronecker (oldSourceCutoff q) (1 : CMatrix μ) := by
  rw [setMemory_matrix]
  simp only [Matrix.kronecker,←Matrix.mul_kronecker_mul,Matrix.mul_one]
  rw [choice_low_intertwining hq hT hqd inverse]

theorem initial_intertwining {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    {μ : Type*} [Fintype μ] [DecidableEq μ] (z : α×μ→ℂ) :
    initial T z=basisEmbedding (setMemory hT)*ᵥfiniteInitial z := by
  rw [finiteInitial,Matrix.mulVec_mulVec,basisEmbedding_mul]
  rfl

variable {μ : ℕ→Type*} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

theorem run_intertwining {q T : ℕ} (hq : q+1≤T)
    (hT : 2*Fintype.card (α×α)≤T) (hqd : q<Fintype.card α)
    (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ) (dir : ℕ→Bool) (z : α×μ 0→ℂ) :
    ∀s≤q,MHFockTrajectory.run T K (fun t => Vchoice hq (dir t)) z s=
      basisEmbedding (setMemory hT)*ᵥMHFiniteSignedTrajectory.run K dir z s := by
  intro s
  induction s with
  | zero => intro _; exact initial_intertwining hT z
  | succ s ih =>
    intro hs
    have hs' : s≤q := by omega
    have he := ih hs'
    have hp := MHFiniteSignedTrajectory.run_cutoff K dir z hs'
    have horacle :
        Matrix.kronecker (Vchoice hq (dir s)) (1 : CMatrix (μ s))*ᵥ
          (basisEmbedding (setMemory hT)*ᵥMHFiniteSignedTrajectory.run K dir z s)=
        basisEmbedding (setMemory hT)*ᵥ
          (Matrix.kronecker (oldChoice (α := α) (dir s)) (1 : CMatrix (μ s))*ᵥ
            MHFiniteSignedTrajectory.run K dir z s) := by
      calc
        Matrix.kronecker (Vchoice hq (dir s)) (1 : CMatrix (μ s))*ᵥ
          (basisEmbedding (setMemory hT)*ᵥMHFiniteSignedTrajectory.run K dir z s) =
          (Matrix.kronecker (Vchoice hq (dir s)) (1 : CMatrix (μ s))*
          basisEmbedding (setMemory hT)*Matrix.kronecker (oldSourceCutoff q) (1 : CMatrix (μ s)))*ᵥ
            MHFiniteSignedTrajectory.run K dir z s := by
              simp only [←Matrix.mulVec_mulVec,hp]
        _ = (basisEmbedding (setMemory hT)*Matrix.kronecker (oldChoice (α := α) (dir s))
          (1 : CMatrix (μ s))*Matrix.kronecker (oldSourceCutoff q) (1 : CMatrix (μ s)))*ᵥ
            MHFiniteSignedTrajectory.run K dir z s :=
              congrArg (fun M => M*ᵥMHFiniteSignedTrajectory.run K dir z s)
                (memory_choice_low_intertwining hq hT hqd (dir s) (μ := μ s))
        _ = basisEmbedding (setMemory hT)*ᵥ
          (Matrix.kronecker (oldChoice (α := α) (dir s)) (1 : CMatrix (μ s))*ᵥ
            MHFiniteSignedTrajectory.run K dir z s) := by simp only [←Matrix.mulVec_mulVec,hp]
    change known T (K s)*ᵥ(Matrix.kronecker (Vchoice hq (dir s)) (1 : CMatrix (μ s))*ᵥ
      MHFockTrajectory.run T K (fun t => Vchoice hq (dir t)) z s)=_
    rw [he,horacle,Matrix.mulVec_mulVec,known_set_intertwining,←Matrix.mulVec_mulVec]
    rfl

#print axioms run_intertwining
end
end ICO.MHFockFiniteTrajectory

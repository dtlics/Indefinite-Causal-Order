import ICO.MHFockFiniteKnown
import ICO.MHFockSupportProjection
import ICO.MHFockReachability

/-! Finite-set recording trajectories under arbitrary signed calls and
rectangular accessible operations. The low-record support is derived. -/
namespace ICO.MHFiniteSignedTrajectory
open QIT ICO.MHFockTrajectory ICO.MHFockFiniteKnown ICO.MHFockKnownOperation
  ICO.MHFockNodup ICO.MHFockProjection ICO.MHFockReachability ICO.MHFockSupportProjection
  ICO.MHOracleCutoff ICO.RecordingOperatorSupport ICO.RecordingOracleAlgebra
  ICO.RecordingCopyIdentity ICO.MHEmbeddingProjector
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 512
variable {α : Type*} [Fintype α] [DecidableEq α]

def oldChoice (inverse : Bool) : CMatrix (Basis α) :=
  if inverse then (forwardRecording (α := α)).conjTranspose else forwardRecording

theorem oldChoice_grade (inverse : Bool) (o i : Basis α) (h : oldChoice inverse o i≠0) :
    setGrade o≤setGrade i+1 := by
  have hforward (o i : Basis α) (hh : forwardRecording o i≠0) :
      setGrade o≤setGrade i+1 ∧ setGrade i≤setGrade o+1 :=
    fullOracle_grade_bound setGrade leftInsertion rightInsertion leftInsertion_grade rightInsertion_grade o i hh
  cases inverse
  · exact (hforward o i h).1
  · exact (hforward i o (by intro hz; exact h (by simp [oldChoice,Matrix.conjTranspose_apply,hz]))).2

def finiteEmpty {μ : Type*} (i : α×μ) : Basis α×μ := ((i.1,∅,∅),i.2)

def finiteInitial {μ : Type*} [Fintype μ] [DecidableEq μ] (z : α×μ→ℂ) : Basis α×μ→ℂ :=
  basisEmbedding finiteEmpty*ᵥz

theorem finiteInitial_grade {μ : Type*} [Fintype μ] [DecidableEq μ] (z : α×μ→ℂ) :
    Supported (fun i : Basis α×μ => setGrade i.1≤0) (finiteInitial z) := by
  refine mulVec_support (basisEmbedding finiteEmpty) z (fun _ => True) _ (fun _ _ => trivial) ?_
  intro o i hi _
  have he := basisEmbedding_support finiteEmpty o i hi
  simp [he,finiteEmpty,setGrade]

theorem known_grade {μ ν : Type*} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (K : Matrix (α×ν) (α×μ) ℂ) (o : Basis α×ν) (i : Basis α×μ)
    (hi : knownOperation K o i≠0) : setGrade o.1=setGrade i.1 := by
  have he : o.1.2=i.1.2 := by by_contra hn; exact hi (by simp [knownOperation,hn])
  exact congrArg (fun p : Finset (α×α)×Finset (α×α) => p.1.card+p.2.card) he

variable {μ : ℕ→Type*} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

def run (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ) (dir : ℕ→Bool)
    (z : α×μ 0→ℂ) : (t:ℕ)→Basis α×μ t→ℂ
  | 0 => finiteInitial z
  | t+1 => knownOperation (K t)*ᵥ
      (Matrix.kronecker (oldChoice (α := α) (dir t)) (1 : CMatrix (μ t))*ᵥrun K dir z t)

theorem run_grade (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ) (dir : ℕ→Bool)
    (z : α×μ 0→ℂ) (t : ℕ) :
    Supported (fun i : Basis α×μ t => setGrade i.1≤t) (run K dir z t) := by
  induction t with
  | zero => exact finiteInitial_grade z
  | succ t ih =>
    change Supported _ (knownOperation (K t)*ᵥ
      (Matrix.kronecker (oldChoice (α := α) (dir t)) (1 : CMatrix (μ t))*ᵥrun K dir z t))
    refine mulVec_support (knownOperation (K t)) _ (fun i : Basis α×μ t => setGrade i.1≤t+1) _ ?_ ?_
    · refine mulVec_support (Matrix.kronecker (oldChoice (α := α) (dir t)) (1 : CMatrix (μ t)))
        (run K dir z t) _ _ ih ?_
      intro o i hi hg
      have ho : oldChoice (α := α) (dir t) o.1 i.1≠0 := by
        intro hz
        exact hi (by simp [Matrix.kronecker,Matrix.kroneckerMap_apply,hz])
      exact (oldChoice_grade (dir t) o.1 i.1 ho).trans (by omega)
    · intro o i hi hg
      rw [known_grade _ _ _ hi]
      exact hg

theorem run_cutoff (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ) (dir : ℕ→Bool)
    (z : α×μ 0→ℂ) {s q : ℕ} (hs : s≤q) :
    Matrix.kronecker (oldSourceCutoff (α := α) q) (1 : CMatrix (μ s))*ᵥrun K dir z s=run K dir z s := by
  apply supported_diagonal
  intro i hi
  exact (run_grade K dir z s i hi).trans hs

#print axioms run_cutoff
end
end ICO.MHFiniteSignedTrajectory

import ICO.MHFockKnownOperation
import ICO.MHWReachability

/-! Literal pure recording trajectories with arbitrary changing public
memory. Record support is proved by induction from the empty register. -/
namespace ICO.MHFockTrajectory
open QIT ICO.MHBoundedRecording ICO.MHFockLabels ICO.MHFockSpace ICO.MHFockProjection
  ICO.MHBijectionProfiles ICO.MHFockKnownOperation ICO.MHFockReachability
  ICO.MHWReachability ICO.MHWEmbedding ICO.MHWDomainProjection ICO.MHFockOracle
  ICO.RecordingCopyIdentity ICO.RecordingMultisetBridge ICO.RecordingProcess
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 512

def Supported {a : Type*} (P : a→Prop) (v : a→ℂ) : Prop := ∀ i,v i≠0→P i

theorem mulVec_support {a b : Type*} [Fintype a] (M : Matrix b a ℂ) (v : a→ℂ)
    (P : a→Prop) (Q : b→Prop) (hv : Supported P v)
    (hM : ∀o i,M o i≠0→P i→Q o) : Supported Q (M*ᵥv) := by
  intro o ho
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hm,hv'⟩ := mul_ne_zero_iff.mp hi
  exact hM o i hm (hv i hv')

variable {α : Type*} [Fintype α] [DecidableEq α]

def emptyFock (T : ℕ) (x : α) : InputCutoff (α := α) T :=
  labelFock (x,0,0) (by simp)

theorem empty_label (T : ℕ) (x : α) : fockLabel (emptyFock T x)=(x,0,0) :=
  fockLabel_labelFock _ _

theorem empty_grade (T : ℕ) (x : α) : grade (emptyFock T x)=0 := rfl

def initialEmbed (T : ℕ) {μ : Type*} (i : α×μ) : InputCutoff (α := α) T×μ :=
  (emptyFock T i.1,i.2)

theorem initialEmbed_injective (T : ℕ) (μ : Type*) :
    Function.Injective (initialEmbed (α := α) T (μ := μ)) := by
  intro i j he
  apply Prod.ext
  · exact congrArg (fun v : InputCutoff (α := α) T×μ => (fockLabel v.1).1) he
  · exact congrArg (fun v : InputCutoff (α := α) T×μ => v.2) he

def initial (T : ℕ) {μ : Type*} [Fintype μ] [DecidableEq μ] (z : α×μ→ℂ) :
    InputCutoff (α := α) T×μ→ℂ := basisEmbedding (initialEmbed T)*ᵥz

theorem initial_grade (T : ℕ) {μ : Type*} [Fintype μ] [DecidableEq μ] (z : α×μ→ℂ) :
    Supported (fun i : InputCutoff (α := α) T×μ => grade i.1≤0) (initial T z) := by
  change Supported _ (basisEmbedding (initialEmbed T)*ᵥz)
  refine mulVec_support (basisEmbedding (initialEmbed T)) z (fun _ => True) _ (fun _ _ => trivial) ?_
  intro o i hi _
  have he := basisEmbedding_support (initialEmbed T) o i hi
  simp only [he,initialEmbed,empty_grade,le_refl]

theorem initial_bij (T : ℕ) {μ : Type*} [Fintype μ] [DecidableEq μ] (z : α×μ→ℂ) :
    Supported (fun i : InputCutoff (α := α) T×μ =>
      BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2) (initial T z) := by
  change Supported _ (basisEmbedding (initialEmbed T)*ᵥz)
  refine mulVec_support (basisEmbedding (initialEmbed T)) z (fun _ => True) _ (fun _ _ => trivial) ?_
  intro o i hi _
  have he := basisEmbedding_support (initialEmbed T) o i hi
  simp [he,initialEmbed,empty_label,BijMultiset]

theorem oracle_memory_support {μ : Type*} [Fintype μ] [DecidableEq μ]
    {T : ℕ} (O : CMatrix (InputCutoff (α := α) T))
    (o i : InputCutoff (α := α) T×μ)
    (h : Matrix.kronecker O (1 : CMatrix μ) o i≠0) : O o.1 i.1≠0 := by
  intro hz
  exact h (by simp [Matrix.kronecker,Matrix.kroneckerMap_apply,hz])

variable {μ : ℕ→Type*} [∀ t,Fintype (μ t)] [∀ t,DecidableEq (μ t)]

def run (T : ℕ) (K : (t : ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ)
    (O : ℕ→CMatrix (InputCutoff (α := α) T)) (z : α×μ 0→ℂ) :
    (t : ℕ)→InputCutoff (α := α) T×μ t→ℂ
  | 0 => initial T z
  | t+1 => known T (K t)*ᵥ(Matrix.kronecker (O t) (1 : CMatrix (μ t))*ᵥrun T K O z t)

theorem run_grade (T : ℕ) (K : (t : ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ)
    (O : ℕ→CMatrix (InputCutoff (α := α) T)) (z : α×μ 0→ℂ)
    (hO : ∀t o i,O t o i≠0→grade o≤grade i+1) (t : ℕ) :
    Supported (fun i : InputCutoff (α := α) T×μ t => grade i.1≤t) (run T K O z t) := by
  induction t with
  | zero => exact initial_grade T z
  | succ t ih =>
    change Supported _ (known T (K t)*ᵥ(Matrix.kronecker (O t) (1 : CMatrix (μ t))*ᵥrun T K O z t))
    refine mulVec_support (known T (K t)) _ (fun i : InputCutoff (α := α) T×μ t => grade i.1≤t+1) _ ?_ ?_
    · refine mulVec_support (Matrix.kronecker (O t) (1 : CMatrix (μ t))) (run T K O z t) _ _ ih ?_
      intro o i hi hg
      have hh := hO t o.1 i.1 (oracle_memory_support (O t) o i hi)
      omega
    · intro o i hi hg
      rw [known_grade T (K t) o i hi]
      exact hg

theorem run_bij (T : ℕ) (K : (t : ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ)
    (O : ℕ→CMatrix (InputCutoff (α := α) T)) (z : α×μ 0→ℂ)
    (hO : ∀t o i,O t o i≠0→BijMultiset (fockLabel o).2.1 (fockLabel o).2.2) (t : ℕ) :
    Supported (fun i : InputCutoff (α := α) T×μ t =>
      BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2) (run T K O z t) := by
  cases t with
  | zero => exact initial_bij T z
  | succ t =>
    change Supported _ (known T (K t)*ᵥ(Matrix.kronecker (O t) (1 : CMatrix (μ t))*ᵥrun T K O z t))
    refine mulVec_support (known T (K t)) _ (fun i : InputCutoff (α := α) T×μ t =>
      BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2) _ ?_ ?_
    · refine mulVec_support (Matrix.kronecker (O t) (1 : CMatrix (μ t))) (run T K O z t) (fun _ => True) _ (fun _ _ => trivial) ?_
      intro o i hi _
      exact hO t o.1 i.1 (oracle_memory_support (O t) o i hi)
    · intro o i hi hb
      exact (known_bij T (K t) o i hi).mpr hb

def Wchoice {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (inverse : Bool) : CMatrix (InputCutoff (α := α) T) :=
  if inverse then (recordW hT).conjTranspose else recordW hT

def Vchoice {q T : ℕ} (hq : q+1≤T) (inverse : Bool) : CMatrix (InputCutoff (α := α) T) :=
  if inverse then (fullOracle hq).conjTranspose else fullOracle hq

theorem Wrun_grade {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (K : (t : ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ) (dir : ℕ→Bool) (z : α×μ 0→ℂ) (t : ℕ) :
    Supported (fun i : InputCutoff (α := α) T×μ t => grade i.1≤t)
      (run T K (fun s => Wchoice hT (dir s)) z t) := by
  apply run_grade
  intro s o i hi
  cases hdir : dir s
  · simp only [Wchoice,hdir,Bool.false_eq_true,if_false] at hi
    exact (recordW_grade_step hT o i hi).1
  · simp only [Wchoice,hdir,if_true] at hi
    exact (recordW_inverse_grade_step hT o i hi).1

theorem Wrun_bij {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (K : (t : ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ) (dir : ℕ→Bool) (z : α×μ 0→ℂ) (t : ℕ) :
    Supported (fun i : InputCutoff (α := α) T×μ t =>
      BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2)
      (run T K (fun s => Wchoice hT (dir s)) z t) := by
  apply run_bij
  intro s o i hi
  cases hdir : dir s
  · simp only [Wchoice,hdir,Bool.false_eq_true,if_false] at hi
    exact recordW_output_bij hT o i hi
  · simp only [Wchoice,hdir,if_true] at hi
    exact recordW_inverse_output_bij hT o i hi

theorem Vrun_grade {q T : ℕ} (hq : q+1≤T)
    (K : (t : ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ) (dir : ℕ→Bool) (z : α×μ 0→ℂ) (t : ℕ) :
    Supported (fun i : InputCutoff (α := α) T×μ t => grade i.1≤t)
      (run T K (fun s => Vchoice hq (dir s)) z t) := by
  apply run_grade
  intro s o i hi
  cases hdir : dir s
  · simp only [Vchoice,hdir,Bool.false_eq_true,if_false] at hi
    exact (fullOracle_grade_step hq o i hi).1
  · simp only [Vchoice,hdir,if_true] at hi
    exact (fullOracle_inverse_grade_step hq o i hi).1

end
end ICO.MHFockTrajectory

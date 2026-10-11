import ICO.MHFockPublicRotation
import ICO.MHFockRunIsometry
import ICO.MHFockSupportProjection

/-! Actual rotated W trajectories retain bijective records and grow by at
most one record per oracle call, also for arbitrary inverse-call schedules. -/
namespace ICO.MHRotatedTrajectory
open QIT ICO.MHFockTrajectory ICO.MHFockKnownOperation ICO.MHFockPublicRotation
  ICO.MHFockRotation ICO.MHFockProjection ICO.MHFockLabels ICO.MHBijectionProfiles
  ICO.MHBoundedRecording ICO.MHWReachability ICO.MHFockRunIsometry
  ICO.MHFockSupportProjection ICO.MHSectorCovariance ICO.MHWDomainProjection
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 512
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem query_known_entry (C : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (o i : InputCutoff (α := α) T) :
    known T (Matrix.kronecker (C : CMatrix α) (1 : CMatrix Unit)) (o,()) (i,())=
      (fockQuery C T : CMatrix (InputCutoff (α := α) T)) o i := by
  rw [←query_tensor_known]
  simp [Matrix.kronecker,Matrix.kroneckerMap_apply]

theorem query_grade (C : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (o i : InputCutoff (α := α) T)
    (h : (fockQuery C T : CMatrix (InputCutoff (α := α) T)) o i≠0) : grade o=grade i :=
  known_grade T (Matrix.kronecker (C : CMatrix α) (1 : CMatrix Unit)) (o,()) (i,())
    (by rwa [query_known_entry])

theorem query_bij (C : Matrix.unitaryGroup α ℂ) (T : ℕ)
    (o i : InputCutoff (α := α) T)
    (h : (fockQuery C T : CMatrix (InputCutoff (α := α) T)) o i≠0) :
    BijMultiset (fockLabel o).2.1 (fockLabel o).2.2 ↔
      BijMultiset (fockLabel i).2.1 (fockLabel i).2.2 :=
  known_bij T (Matrix.kronecker (C : CMatrix α) (1 : CMatrix Unit)) (o,()) (i,())
    (by rwa [query_known_entry])

def before (C D : Matrix.unitaryGroup α ℂ) (inverse : Bool) : Matrix.unitaryGroup α ℂ :=
  if inverse then D⁻¹ else C

def after (C D : Matrix.unitaryGroup α ℂ) (inverse : Bool) : Matrix.unitaryGroup α ℂ :=
  if inverse then C⁻¹ else D

def rotatedW {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (C D : Matrix.unitaryGroup α ℂ) (inverse : Bool) : CMatrix (InputCutoff (α := α) T) :=
  (fockQuery (after C D inverse) T : CMatrix (InputCutoff (α := α) T))*Wchoice hT inverse*
    (fockQuery (before C D inverse) T : CMatrix (InputCutoff (α := α) T))

theorem Wchoice_grade {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (inverse : Bool)
    (o i : InputCutoff (α := α) T) (h : Wchoice hT inverse o i≠0) : grade o≤grade i+1 := by
  cases inverse
  · exact (recordW_grade_step hT o i h).1
  · exact (recordW_inverse_grade_step hT o i h).1

theorem Wchoice_bij {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (inverse : Bool)
    (o i : InputCutoff (α := α) T) (h : Wchoice hT inverse o i≠0) :
    BijMultiset (fockLabel o).2.1 (fockLabel o).2.2 := by
  cases inverse
  · exact recordW_output_bij hT o i h
  · exact recordW_inverse_output_bij hT o i h

theorem rotatedW_grade {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (C D : Matrix.unitaryGroup α ℂ) (inverse : Bool)
    (o i : InputCutoff (α := α) T) (h : rotatedW hT C D inverse o i≠0) : grade o≤grade i+1 := by
  obtain ⟨j,hj,hji⟩ := mul_entry_nonzero _ _ o i h
  obtain ⟨k,hok,hkj⟩ := mul_entry_nonzero _ _ o j hj
  have h1 := query_grade (after C D inverse) T o k hok
  have h2 := Wchoice_grade hT inverse k j hkj
  have h3 := query_grade (before C D inverse) T j i hji
  omega

theorem rotatedW_bij {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (C D : Matrix.unitaryGroup α ℂ) (inverse : Bool)
    (o i : InputCutoff (α := α) T) (h : rotatedW hT C D inverse o i≠0) :
    BijMultiset (fockLabel o).2.1 (fockLabel o).2.2 := by
  obtain ⟨j,hj,_⟩ := mul_entry_nonzero _ _ o i h
  obtain ⟨k,hok,hkj⟩ := mul_entry_nonzero _ _ o j hj
  exact (query_bij (after C D inverse) T o k hok).mpr (Wchoice_bij hT inverse k j hkj)

theorem rotatedW_norm_le {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (C D : Matrix.unitaryGroup α ℂ) (inverse : Bool) : ‖rotatedW hT C D inverse‖≤1 := by
  have hn := norm_mul_le
    ((fockQuery (after C D inverse) T : CMatrix (InputCutoff (α := α) T))*Wchoice hT inverse)
    (fockQuery (before C D inverse) T : CMatrix (InputCutoff (α := α) T))
  have hl := norm_mul_le (fockQuery (after C D inverse) T : CMatrix (InputCutoff (α := α) T))
    (Wchoice hT inverse)
  have ha := unitary_norm_le (fockQuery (after C D inverse) T)
  have hb := unitary_norm_le (fockQuery (before C D inverse) T)
  have hw := Wchoice_norm_le hT inverse
  have hprod : ‖(fockQuery (after C D inverse) T : CMatrix (InputCutoff (α := α) T))*Wchoice hT inverse‖≤1 :=
    hl.trans ((mul_le_mul ha hw (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  exact hn.trans ((mul_le_mul hprod hb (norm_nonneg _) (by norm_num)).trans_eq (by ring))

variable {μ : ℕ→Type*} [∀t,Fintype (μ t)] [∀t,DecidableEq (μ t)]

theorem rotatedRun_grade {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (C D : Matrix.unitaryGroup α ℂ) (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ)
    (dir : ℕ→Bool) (z : α×μ 0→ℂ) (s : ℕ) :
    Supported (fun i : InputCutoff (α := α) T×μ s => grade i.1≤s)
      (run T K (fun t => rotatedW hT C D (dir t)) z s) :=
  run_grade T K _ z (fun t => rotatedW_grade hT C D (dir t)) s

theorem rotatedRun_bij {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (C D : Matrix.unitaryGroup α ℂ) (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ)
    (dir : ℕ→Bool) (z : α×μ 0→ℂ) (s : ℕ) :
    Supported (fun i : InputCutoff (α := α) T×μ s =>
      BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2)
      (run T K (fun t => rotatedW hT C D (dir t)) z s) :=
  run_bij T K _ z (fun t => rotatedW_bij hT C D (dir t)) s

theorem rotatedRun_bij_fixed {T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (C D : Matrix.unitaryGroup α ℂ) (K : (t:ℕ)→Matrix (α×μ (t+1)) (α×μ t) ℂ)
    (dir : ℕ→Bool) (z : α×μ 0→ℂ) (s : ℕ) :
    Matrix.kronecker (bijProjection T) (1 : CMatrix (μ s))*ᵥ
      run T K (fun t => rotatedW hT C D (dir t)) z s=
      run T K (fun t => rotatedW hT C D (dir t)) z s :=
  bij_fixed _ (rotatedRun_bij hT C D K dir z s)

#print axioms rotatedRun_bij_fixed
end
end ICO.MHRotatedTrajectory

import ICO.C6FockCutoff
import ICO.C6ForwardAlgebra
import ICO.C6QueryPreparation

/-! Actual forward-oracle replacement on arbitrary pure-query branches,
including every finite spectator and every private measurement outcome. -/
namespace ICO.C6LocalDeletion
open Matrix QIT ICO.C6FockCompression ICO.C6FockCutoff ICO.C6ForwardAlgebra
open ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockSwap ICO.MHFockOracle
open ICO.MHFockKnownOperation ICO.MHBlockNorm
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {A : Type*} [Fintype A] [DecidableEq A]

def deletion {s t T : ℕ} (ht : t+1≤T) (ψ : A→ℂ) :
    Matrix (InputCutoff (α:=A) T) (Records (α:=A) T) ℂ :=
  (fullOracle ht-leftOnFock ht)*fockQuery T ψ*recordCutoff (s+1) T

theorem deletion_norm {s t T : ℕ} (hs : s+1≤T) (ht : t+1≤T) (hst : s≤t)
    (hd : t<Fintype.card A) (ψ : A→ℂ) (hψ : ∑ y,‖ψ y‖^2≤1) :
    ‖deletion (s:=s) ht ψ‖≤Real.sqrt (2*(s+1:ℝ)/((Fintype.card A:ℝ)-s)) := by
  have hs0 : (0:ℝ)<Fintype.card A-s := by
    have hh : (s:ℝ)<Fintype.card A := by exact_mod_cast lt_of_le_of_lt hst hd
    linarith
  have he : deletion (s:=s) ht ψ = errorFactor (leftOnFock (α:=A) ht) (rightOnFock (α:=A) ht)*
      ((rightOnFock (α:=A) ht).conjTranspose*fockQuery T ψ*recordCutoff (s+1) T) := by
    rw [deletion,fullOracle_difference]
    simp only [Matrix.mul_assoc]
  rw [he]
  calc
    _ ≤ ‖errorFactor (leftOnFock (α:=A) ht) (rightOnFock ht)‖*
        ‖(rightOnFock ht).conjTranspose*fockQuery T ψ*recordCutoff (s+1) T‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ Real.sqrt 2*Real.sqrt ((s+1:ℝ)/((Fintype.card A:ℝ)-s)) :=
      mul_le_mul (actual_factor_norm ht hd)
        (right_fock_low_compression hs ht hst ψ hψ (lt_of_le_of_lt hst hd))
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]; congr 1; ring

variable {M : Type*} [Fintype M] [DecidableEq M]

theorem deletion_memory_norm {s t T : ℕ} (hs : s+1≤T) (ht : t+1≤T) (hst : s≤t)
    (hd : t<Fintype.card A) (ψ : A→ℂ) (hψ : ∑ y,‖ψ y‖^2≤1) :
    ‖Matrix.kronecker (deletion (s:=s) ht ψ) (1:CMatrix M)‖≤
      Real.sqrt (2*(s+1:ℝ)/((Fintype.card A:ℝ)-s)) :=
  (tensor_identity_norm_le (deletion (s:=s) ht ψ)).trans (deletion_norm hs ht hst hd ψ hψ)

theorem private_branch_square_bound {J : Type*} [Fintype J]
    {s t T : ℕ} (hs : s+1≤T) (ht : t+1≤T) (hst : s≤t) (hd : t<Fintype.card A)
    (ψ : J→A→ℂ) (hψ : ∀j,∑ y,‖ψ j y‖^2≤1)
    (v : J→Records (α:=A) T×M→ℂ) :
    (∑ j:J, ∑ i:InputCutoff (α:=A) T×M,
      ‖(Matrix.kronecker (deletion (s:=s) ht (ψ j)) (1:CMatrix M)*ᵥv j) i‖^2)≤
      (2*(s+1:ℝ)/((Fintype.card A:ℝ)-s))*(∑ j:J,∑ R:Records (α:=A) T×M,‖v j R‖^2) := by
  have hs0 : (0:ℝ)<Fintype.card A-s := by
    have hh : (s:ℝ)<Fintype.card A := by exact_mod_cast lt_of_le_of_lt hst hd
    linarith
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact square_sum_le_of_norm _ _ (by positivity)
    (deletion_memory_norm hs ht hst hd (ψ j) (hψ j)) (v j)

theorem record_memory_fixed {s T : ℕ} (v : Records (α:=A) T×M→ℂ)
    (hv : ∀i, ¬recordGrade i.1≤s → v i=0) :
    Matrix.kronecker (recordCutoff (A:=A) s T) (1:CMatrix M)*ᵥv=v := by
  rw [recordCutoff,ICO.RecordingRemovalNorm.diagonal_tensor]
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : recordGrade i.1≤s
  · simp [h]
  · simp [h,hv i h]

theorem deletion_actual {s t T : ℕ} (ht : t+1≤T) (ψ : A→ℂ)
    (v : Records (α:=A) T×M→ℂ)
    (hv : Matrix.kronecker (recordCutoff (A:=A) (s+1) T) (1:CMatrix M)*ᵥv=v) :
    Matrix.kronecker (deletion (s:=s) ht ψ) (1:CMatrix M)*ᵥv=
      Matrix.kronecker (fullOracle ht-leftOnFock ht) (1:CMatrix M)*ᵥ
        (Matrix.kronecker (fockQuery T ψ) (1:CMatrix M)*ᵥv) := by
  have h1 := Matrix.mul_kronecker_mul
    ((fullOracle (α:=A) ht-leftOnFock ht)*fockQuery T ψ)
    (recordCutoff (A:=A) (s+1) T) (1:CMatrix M) (1:CMatrix M)
  have h2 := Matrix.mul_kronecker_mul
    (fullOracle (α:=A) ht-leftOnFock ht) (fockQuery T ψ) (1:CMatrix M) (1:CMatrix M)
  simp only [Matrix.one_mul] at h1 h2
  rw [deletion]
  simp only [Matrix.kronecker] at hv ⊢
  rw [h1,←Matrix.mulVec_mulVec,hv,h2,←Matrix.mulVec_mulVec]

/-- A normalized post-measurement purification may contain any finite private
outcome family and arbitrary quantum memory. Only the actual pure-query
factorization and total-length support are used in the local replacement. -/
theorem normalized_private_deletion {J : Type*} [Fintype J]
    {s t T : ℕ} (hs : s+1≤T) (ht : t+1≤T) (hst : s≤t) (hd : t<Fintype.card A)
    (ψ : J→A→ℂ) (hψ : ∀j,∑ y,‖ψ j y‖^2=1)
    (v : J→Records (α:=A) T×M→ℂ)
    (hv : ∀j i, ¬recordGrade i.1≤s+1 → v j i=0)
    (hmass : (∑j:J,∑i:InputCutoff (α:=A) T×M,
      ‖(Matrix.kronecker (fockQuery T (ψ j)) (1:CMatrix M)*ᵥv j) i‖^2)≤1) :
    (∑j:J,∑i:InputCutoff (α:=A) T×M,
      ‖(Matrix.kronecker (fullOracle ht-leftOnFock ht) (1:CMatrix M)*ᵥ
        (Matrix.kronecker (fockQuery T (ψ j)) (1:CMatrix M)*ᵥv j)) i‖^2)≤
      2*(s+1:ℝ)/((Fintype.card A:ℝ)-s) := by
  have h := private_branch_square_bound hs ht hst hd ψ (fun j => (hψ j).le) v
  have he (j:J) := deletion_actual ht (ψ j) (v j) (record_memory_fixed (v j) (hv j))
  simp_rw [he] at h
  have hm : (∑j:J,∑R:Records (α:=A) T×M,‖v j R‖^2)≤1 := by
    simpa only [ICO.C6QueryPreparation.prepared_mass T _ (hψ _)] using hmass
  have hs0 : (0:ℝ)<Fintype.card A-s := by
    have hh : (s:ℝ)<Fintype.card A := by exact_mod_cast lt_of_le_of_lt hst hd
    linarith
  have hc : (0:ℝ) ≤ 2*(s+1:ℝ)/((Fintype.card A:ℝ)-s) := by positivity
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left hm hc)

theorem private_deletion_norm {J : Type*} [Fintype J]
    {s t T : ℕ} (hs : s+1≤T) (ht : t+1≤T) (hst : s≤t) (hd : t<Fintype.card A)
    (ψ : J→A→ℂ) (hψ : ∀j,∑ y,‖ψ j y‖^2=1)
    (v : J→Records (α:=A) T×M→ℂ)
    (hv : ∀j i, ¬recordGrade i.1≤s+1 → v j i=0)
    (hmass : (∑j:J,∑i:InputCutoff (α:=A) T×M,
      ‖(Matrix.kronecker (fockQuery T (ψ j)) (1:CMatrix M)*ᵥv j) i‖^2)≤1) :
    ‖WithLp.toLp 2 (fun z:J×(InputCutoff (α:=A) T×M) =>
      (Matrix.kronecker (fullOracle ht-leftOnFock ht) (1:CMatrix M)*ᵥ
        (Matrix.kronecker (fockQuery T (ψ z.1)) (1:CMatrix M)*ᵥv z.1)) z.2)‖≤
      Real.sqrt (2*(s+1:ℝ)/((Fintype.card A:ℝ)-s)) := by
  have hh := normalized_private_deletion hs ht hst hd ψ hψ v hv hmass
  have hd' : (0:ℝ)<Fintype.card A-s := by
    have hlt : (s:ℝ)<Fintype.card A := by exact_mod_cast lt_of_le_of_lt hst hd
    linarith
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  simpa only [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,WithLp.ofLp_toLp] using hh

#print axioms private_branch_square_bound
#print axioms normalized_private_deletion
#print axioms private_deletion_norm
end
end ICO.C6LocalDeletion

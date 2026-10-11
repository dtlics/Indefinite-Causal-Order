import ICO.MHWRestricted

/-! One physical forward or inverse recording query changes total record
length by at most one; this holds on arbitrary multiset inputs. -/
namespace ICO.MHFockReachability
open QIT ICO.MHFockOracle ICO.MHFockSpace ICO.MHFockSwap ICO.MHFockProjection
  ICO.MHFockAlgebra ICO.MHBoundedRecording ICO.RecordingCopyIdentity
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
variable {a : Type*} [Fintype a] [DecidableEq a]

theorem complement_grade (g : a→ℕ) (M : CMatrix a)
    (hM : ∀o i,M o i≠0→g o=g i) (o i : a) (h : (1-M) o i≠0) : g o=g i := by
  by_cases he : o=i
  · simpa [he]
  · apply hM
    intro hz
    exact h (by simp [Matrix.sub_apply,Matrix.one_apply_ne he,hz])

theorem fullOracle_grade_bound (g : a→ℕ) (A B : CMatrix a)
    (hA : ∀o i,A o i≠0→g o=g i+1) (hB : ∀o i,B o i≠0→g o=g i+1)
    (o i : a) (h : ICO.MHOracleCovariance.fullOracle A B o i≠0) :
    g o≤g i+1 ∧ g i≤g o+1 := by
  have hpA := grade_image_preserved g A hA
  have hpB := grade_image_preserved g B hB
  have hc : (A*(1-B*B.conjTranspose)) o i≠0 ∨ ((1-A*A.conjTranspose)*B.conjTranspose) o i≠0 := by
    by_contra hn
    push Not at hn
    exact h (by simp [ICO.MHOracleCovariance.fullOracle,Matrix.add_apply,hn.1,hn.2])
  rcases hc with hL|hR
  · obtain ⟨k,hAk,hPi⟩ := mul_entry_nonzero _ _ o i hL
    have ha := hA o k hAk
    have hp := complement_grade g _ hpB k i hPi
    omega
  · obtain ⟨k,hPk,hBi⟩ := mul_entry_nonzero _ _ o i hR
    have hb := hB i k (by intro hz; exact hBi (by simp [Matrix.conjTranspose_apply,hz]))
    have hp := complement_grade g _ hpA o k hPk
    omega

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fullOracle_grade_step {t T : ℕ} (ht : t+1≤T)
    (o i : InputCutoff (α := α) T) (h : fullOracle ht o i≠0) :
    grade o≤grade i+1 ∧ grade i≤grade o+1 :=
  fullOracle_grade_bound grade (leftOnFock ht) (rightOnFock ht)
    (leftOnFock_grade ht) (rightOnFock_grade ht) o i h

theorem fullOracle_inverse_grade_step {t T : ℕ} (ht : t+1≤T)
    (o i : InputCutoff (α := α) T) (h : (fullOracle ht).conjTranspose o i≠0) :
    grade o≤grade i+1 ∧ grade i≤grade o+1 := by
  have hz : fullOracle ht i o≠0 := by
    intro he
    exact h (by simp [Matrix.conjTranspose_apply,he])
  exact (fullOracle_grade_step ht i o hz).symm

theorem cutoff_reachability {u v T : ℕ} (hu : u≤T) (hv : v≤T) (M : CMatrix (InputCutoff (α := α) T))
    (hM : ∀o i,M o i≠0→grade i≤u→grade o≤v) :
    sourceProjection hv*M*sourceProjection hu=M*sourceProjection hu := by
  rw [sourceProjection_diagonal,sourceProjection_diagonal]
  ext o i
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : grade i≤u
  · by_cases hz : M o i=0
    · simp [hz]
    · simp [hi,hM o i hz hi]
  · simp [hi]

theorem fullOracle_reachable {t T : ℕ} (ht : t+1≤T) :
    sourceProjection ht*fullOracle (α := α) ht*
      sourceProjection (Nat.le_trans (Nat.le_succ t) ht)=
      fullOracle ht*sourceProjection (Nat.le_trans (Nat.le_succ t) ht) := by
  apply cutoff_reachability
  intro o i hi hg
  have hh := (fullOracle_grade_step ht o i hi).1
  omega

theorem fullOracle_inverse_reachable {t T : ℕ} (ht : t+1≤T) :
    sourceProjection ht*(fullOracle (α := α) ht).conjTranspose*
      sourceProjection (Nat.le_trans (Nat.le_succ t) ht)=
      (fullOracle ht).conjTranspose*sourceProjection (Nat.le_trans (Nat.le_succ t) ht) := by
  apply cutoff_reachability
  intro o i hi hg
  have hh := (fullOracle_inverse_grade_step ht o i hi).1
  omega

end
end ICO.MHFockReachability

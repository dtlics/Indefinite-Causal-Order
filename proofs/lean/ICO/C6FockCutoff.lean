import ICO.C6RightCompression

namespace ICO.C6FockCutoff
open Matrix QIT ICO.C6FockCompression ICO.C6RightCompression ICO.MHBoundedRecording
open ICO.MHFockSpace ICO.MHFockKnownOperation ICO.MHFockProjection ICO.MHFockAlgebra
open ICO.MHFockEntries ICO.MHFockSwap ICO.MHFockOracle
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A : Type*} [Fintype A] [DecidableEq A]

def recordGrade {T : ℕ} (R : Records (α:=A) T) : ℕ := R.1.val.1.val+R.1.val.2.val

def recordCutoff (s T : ℕ) : CMatrix (Records (α:=A) T) :=
  Matrix.diagonal (fun R => if recordGrade R≤s then 1 else 0)

theorem recordCutoff_projection (s T : ℕ) : IsStarProjection (recordCutoff (A:=A) s T) := by
  refine ⟨?_,?_⟩
  · change recordCutoff s T*recordCutoff s T=recordCutoff (A:=A) s T
    rw [recordCutoff,Matrix.diagonal_mul_diagonal]
    congr 1
    funext R
    split_ifs <;> simp
  · change (recordCutoff (A:=A) s T).conjTranspose=recordCutoff s T
    ext i j
    by_cases h : i=j
    · subst j; simp [recordCutoff,Matrix.conjTranspose_apply]
    · simp [recordCutoff,Matrix.conjTranspose_apply,h,Ne.symm h]

theorem query_cutoff {s T : ℕ} (hs : s≤T) (ψ : A→ℂ) :
    sourceProjection (α:=A) hs*fockQuery T ψ=fockQuery T ψ*recordCutoff s T := by
  ext i R
  rw [sourceProjection_diagonal,Matrix.diagonal_mul,recordCutoff,Matrix.mul_diagonal]
  by_cases h : records i=R
  · subst R
    simp only [fockQuery,if_pos rfl]
    change (if grade i≤s then (1:ℂ) else 0)*ψ i.2.1 =
      ψ i.2.1*(if grade i≤s then 1 else 0)
    exact mul_comm _ _
  · simp [fockQuery,h]

theorem left_lower_cutoff {s t T : ℕ} (hs : s+1≤T) (ht : t+1≤T) (hst : s≤t) :
    leftOnFock (α:=A) hs=leftOnFock ht*sourceProjection (by omega : s≤T) := by
  ext o i
  rw [sourceProjection_diagonal,Matrix.mul_diagonal,
    leftOnFock_coefficient hs,leftOnFock_coefficient ht]
  by_cases hg : grade i≤s
  · have hgt : grade i≤t := hg.trans hst
    by_cases hp : ICO.RecordingMultisetBridge.MultisetLeftStep
        (ICO.MHFockLabels.fockLabel i) (ICO.MHFockLabels.fockLabel o)
    · rw [if_pos ⟨hg,hp⟩,if_pos ⟨hgt,hp⟩,if_pos hg,mul_one]
    · rw [if_neg (fun h => hp h.2),if_neg (fun h => hp h.2)]
      simp
  · rw [if_neg (fun h => hg h.1),if_neg hg,mul_zero]

theorem right_lower_cutoff {s t T : ℕ} (hs : s+1≤T) (ht : t+1≤T) (hst : s≤t) :
    rightOnFock (α:=A) hs=rightOnFock ht*sourceProjection (by omega : s≤T) := by
  rw [rightOnFock,rightOnFock,left_lower_cutoff hs ht hst,swapMatrix_selfAdjoint]
  simp only [Matrix.mul_assoc]
  rw [(source_commute_swap (α:=A) (by omega:s≤T)).eq]

theorem lower_adjoint_cutoff {s T : ℕ} (V : CMatrix (InputCutoff (α:=A) T))
    (hV : ∀o i,V o i≠0→grade o=grade i+1) (hs : s+1≤T) :
    sourceProjection (α:=A) (by omega:s≤T)*V.conjTranspose*sourceProjection hs=
      V.conjTranspose*sourceProjection hs := by
  ext o i
  simp only [sourceProjection_diagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.conjTranspose_apply]
  by_cases hi : grade i≤s+1
  · by_cases hz : V i o=0
    · simp [hz]
    · have ho : grade o≤s := by have hh := hV i o hz; omega
      simp [hi,ho]
  · simp [hi]

theorem right_query_lower {s t T : ℕ} (hs : s+1≤T) (ht : t+1≤T) (hst : s≤t)
    (ψ : A→ℂ) :
    (rightOnFock (α:=A) ht).conjTranspose*fockQuery T ψ*recordCutoff (s+1) T=
      (rightOnFock (α:=A) hs).conjTranspose*fockQuery T ψ*recordCutoff (s+1) T := by
  have hc := lower_adjoint_cutoff (rightOnFock (α:=A) ht) (rightOnFock_grade ht) hs
  have he : (rightOnFock (α:=A) hs).conjTranspose=
      sourceProjection (α:=A) (by omega:s≤T)*(rightOnFock (α:=A) ht).conjTranspose := by
    rw [right_lower_cutoff hs ht hst,Matrix.conjTranspose_mul]
    have hp : (sourceProjection (α:=A) (by omega:s≤T)).conjTranspose=sourceProjection (by omega:s≤T) :=
      (sourceProjection_projection (α:=A) (by omega:s≤T)).isSelfAdjoint.star_eq
    rw [hp]
  rw [he]
  simp only [Matrix.mul_assoc]
  rw [←query_cutoff hs ψ]
  simp only [←Matrix.mul_assoc]
  rw [hc]

theorem right_fock_low_compression {s t T : ℕ} (hs : s+1≤T) (ht : t+1≤T) (hst : s≤t)
    (ψ : A→ℂ) (hψ : ∑ y,‖ψ y‖^2≤1) (hd : s<Fintype.card A) :
    ‖(rightOnFock (α:=A) ht).conjTranspose*fockQuery T ψ*recordCutoff (s+1) T‖≤
      Real.sqrt ((s+1:ℝ)/((Fintype.card A:ℝ)-s)) := by
  rw [right_query_lower hs ht hst ψ]
  have hp := IsStarProjection.norm_le _ (recordCutoff_projection (A:=A) (s+1) T)
  calc
    _ ≤ ‖(rightOnFock (α:=A) hs).conjTranspose*fockQuery T ψ‖*
      ‖recordCutoff (A:=A) (s+1) T‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ Real.sqrt ((s+1:ℝ)/((Fintype.card A:ℝ)-s))*1 :=
      mul_le_mul (right_fock_compression hs ψ hψ hd) hp (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

#print axioms right_fock_low_compression
end
end ICO.C6FockCutoff

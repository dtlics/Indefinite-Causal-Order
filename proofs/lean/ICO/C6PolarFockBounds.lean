import ICO.C6PolarFock
import ICO.MHOracleCovariance

/-! Uniform replacement bounds on the full coherent multiset cutoff. -/
namespace ICO.C6PolarFockBounds
open QIT ICO.C6BosonicPolar ICO.C6PolarFock ICO.MHBoundedRecording ICO.MHFockSpace
  ICO.MHFockAlgebra ICO.MHFockProjection ICO.MHFockSwap ICO.MHFockOracle
  ICO.MHERecordingApprox ICO.MHBlockNorm ICO.RecordingCopyIdentity
  ICO.RecordingOracleAlgebra ICO.RecordingProcess
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {α:Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem boundedPolar_difference (t:ℕ) :
    boundedSymmetricInsertion (α:=α) t-boundedPolar t=
      Matrix.blockDiagonal' (fun k:Block (α:=α) t =>
        symmetricInsertion (α:=α) k.1.val.1.val-leftPolar k.1.val.1.val) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  simp only [boundedSymmetricInsertion,boundedPolar,Matrix.sub_apply,Matrix.blockDiagonal'_apply']
  split_ifs <;> simp

theorem boundedPolar_distance (t:ℕ) (ht:t<Fintype.card α) :
    ‖boundedSymmetricInsertion (α:=α) t-boundedPolar t‖≤(t:ℝ)/Fintype.card α := by
  rw [boundedPolar_difference]
  have hnonneg : (0:ℝ)≤(t:ℝ)/Fintype.card α := by positivity
  rw [←Real.sqrt_sq hnonneg]
  apply blockDiagonal'_norm_le _ _ (by positivity)
  intro k
  rw [Real.sqrt_sq hnonneg]
  have hk : k.1.val.1.val≤t := by have hh:=k.1.property; omega
  exact (leftPolar_distance (lt_of_le_of_lt hk ht)).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hk) (Nat.cast_nonneg _))

theorem symmetric_polar_distance {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α) :
    ‖symmetricOnFock (α:=α) h-polarLeftOnFock h‖≤(t:ℝ)/Fintype.card α := by
  have hOut := isometry_matrix_norm_le (basisEmbedding (outputEmbed (α:=α) h)) (outputEmbed_gram h)
  have hIn := isometry_matrix_norm_le
    (basisEmbedding (inputEmbed (α:=α) (Nat.le_trans (Nat.le_succ t) h)))
    (inputEmbed_gram (Nat.le_trans (Nat.le_succ t) h))
  have hAdj : ‖(basisEmbedding (inputEmbed (α:=α) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose‖≤1 := by
    rwa [Matrix.l2_opNorm_conjTranspose]
  rw [symmetricOnFock,polarLeftOnFock,←Matrix.sub_mul,←Matrix.mul_sub]
  calc
    _ ≤ (‖basisEmbedding (outputEmbed (α:=α) h)‖*
        ‖boundedSymmetricInsertion (α:=α) t-boundedPolar t‖)*
        ‖(basisEmbedding (inputEmbed (α:=α) (Nat.le_trans (Nat.le_succ t) h))).conjTranspose‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*((t:ℝ)/Fintype.card α))*1 :=
      mul_le_mul (mul_le_mul hOut (boundedPolar_distance t ht)
        (norm_nonneg _) (by norm_num)) hAdj (norm_nonneg _) (by positivity)
    _ = _ := by ring

def delta (t d:ℕ) : ℝ := Real.sqrt (2*(t:ℝ)*(t+1)/d)+(t:ℝ)/d

theorem left_polar_distance {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α) :
    ‖leftOnFock (α:=α) h-polarLeftOnFock h‖≤delta t (Fintype.card α) := by
  calc
    _ ≤ ‖leftOnFock (α:=α) h-symmetricOnFock h‖+
        ‖symmetricOnFock (α:=α) h-polarLeftOnFock h‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (leftOnFock (α:=α) h) (symmetricOnFock h) (polarLeftOnFock h)
    _ ≤ _ := add_le_add (leftOnFock_difference_norm_le h ht) (symmetric_polar_distance h ht)

theorem right_polar_distance {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α) :
    ‖rightOnFock (α:=α) h-polarRightOnFock h‖≤delta t (Fintype.card α) := by
  have hS := swapMatrix_norm_le (α:=α) T
  have hAdj : ‖(swapMatrix (α:=α) T).conjTranspose‖≤1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  rw [rightOnFock,polarRightOnFock,←Matrix.sub_mul,←Matrix.mul_sub]
  calc
    _ ≤ (‖swapMatrix (α:=α) T‖*‖leftOnFock (α:=α) h-polarLeftOnFock h‖)*
        ‖(swapMatrix (α:=α) T).conjTranspose‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*delta t (Fintype.card α))*1 :=
      mul_le_mul (mul_le_mul hS (left_polar_distance h ht)
        (norm_nonneg _) (by norm_num)) hAdj (norm_nonneg _) (by unfold delta; positivity)
    _ = _ := by ring

theorem right_norm_le {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α) :
    ‖rightOnFock (α:=α) h‖≤1 := by
  have hh := IsStarProjection.norm_le _
    (sourceProjection_projection (α:=α) (Nat.le_trans (Nat.le_succ t) h))
  rw [←rightOnFock_gram h ht,Matrix.l2_opNorm_conjTranspose_mul_self] at hh
  nlinarith [norm_nonneg (rightOnFock (α:=α) h)]

theorem oracle_polar_distance {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α) :
    ‖fullOracle (α:=α) h-polarOracle h‖≤6*delta t (Fintype.card α) := by
  have hQA : IsStarProjection (leftOnFock (α:=α) h*(leftOnFock h).conjTranspose) :=
    image_projection (leftOnFock h) (sourceProjection (Nat.le_trans (Nat.le_succ t) h))
      (leftOnFock_gram h ht) (leftOnFock_domain h)
  have hQB : IsStarProjection (rightOnFock (α:=α) h*(rightOnFock h).conjTranspose) :=
    image_projection (rightOnFock h) (sourceProjection (Nat.le_trans (Nat.le_succ t) h))
      (rightOnFock_gram h ht) (rightOnFock_domain h)
  exact ICO.MHOracleCovariance.fullOracle_difference_norm_le
    (leftOnFock h) (rightOnFock h) (polarLeftOnFock h) (polarRightOnFock h)
    (delta t (Fintype.card α)) (leftOnFock_norm_le h ht) (right_norm_le h ht)
    (polarLeftOnFock_norm_le h ht) (polarRightOnFock_norm_le h ht)
    hQA hQB (left_polar_distance h ht) (right_polar_distance h ht)

#print axioms boundedPolar_distance
#print axioms oracle_polar_distance
end
end ICO.C6PolarFockBounds

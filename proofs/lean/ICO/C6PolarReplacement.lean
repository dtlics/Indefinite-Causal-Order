import ICO.C6PolarFockBounds
import ICO.MHFockKnownOperation
import ICO.MHRectangularAction

/-! Actual V/A to W/F replacement with arbitrary rectangular middle operations. -/
namespace ICO.C6PolarReplacement
open QIT ICO.C6PolarFock ICO.C6PolarFockBounds ICO.MHBoundedRecording ICO.MHFockSpace
  ICO.MHFockOracle ICO.MHFockAlgebra ICO.MHFockKnownOperation ICO.MHRectangularAction
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {H K:Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

theorem triple_difference (A A':CMatrix K) (B B':CMatrix H) (L:Matrix K H ℂ)
    (a b:ℝ) (hA':‖A'‖≤1) (hB:‖B‖≤1) (hL:‖L‖≤1)
    (ha:‖A-A'‖≤a) (hb:‖B-B'‖≤b) : ‖A*L*B-A'*L*B'‖≤a+b := by
  have he : A*L*B-A'*L*B'=(A-A')*L*B+A'*L*(B-B') := by
    simp only [Matrix.sub_mul,Matrix.mul_sub]
    abel
  have h1 : ‖(A-A')*L*B‖≤a := by
    calc
      _ ≤ (‖A-A'‖*‖L‖)*‖B‖ := (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (‖A-A'‖*1)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hL (norm_nonneg _)) hB (norm_nonneg _) (by positivity)
      _ ≤ a := by simpa using ha
  have h2 : ‖A'*L*(B-B')‖≤b := by
    calc
      _ ≤ (‖A'‖*‖L‖)*‖B-B'‖ := (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (1*1)*‖B-B'‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul hA' hL (norm_nonneg _) (by norm_num)) (norm_nonneg _)
      _ ≤ b := by simpa using hb
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)


theorem tensor_sub {A B C:Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (X Y:Matrix B A ℂ) :
    Matrix.kronecker (X-Y) (1:CMatrix C)=Matrix.kronecker X (1:CMatrix C)-Matrix.kronecker Y (1:CMatrix C) := by
  ext i j
  simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply,sub_mul]

variable {α M N:Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

def oldPair {t T:ℕ} (h:t+1≤T)
    (L:Matrix (InputCutoff (α:=α) T×N) (InputCutoff (α:=α) T×M) ℂ) : Matrix (InputCutoff (α:=α) T×N) (InputCutoff (α:=α) T×M) ℂ :=
  Matrix.kronecker (leftOnFock (α:=α) h) (1:CMatrix N)*L*
    Matrix.kronecker (fullOracle (α:=α) h).conjTranspose (1:CMatrix M)

def polarPair {t T:ℕ} (h:t+1≤T)
    (L:Matrix (InputCutoff (α:=α) T×N) (InputCutoff (α:=α) T×M) ℂ) : Matrix (InputCutoff (α:=α) T×N) (InputCutoff (α:=α) T×M) ℂ :=
  Matrix.kronecker (polarLeftOnFock (α:=α) h) (1:CMatrix N)*L*
    Matrix.kronecker (polarOracle (α:=α) h).conjTranspose (1:CMatrix M)

theorem oldPair_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α)
    (L:Matrix (InputCutoff (α:=α) T×N) (InputCutoff (α:=α) T×M) ℂ) (hL:‖L‖≤1) :
    ‖oldPair h L‖≤1 := by
  have hA := (tensor_identity_norm_le (μ:=N) (leftOnFock (α:=α) h)).trans (leftOnFock_norm_le h ht)
  have hB := (tensor_identity_norm_le (μ:=M) (fullOracle (α:=α) h).conjTranspose).trans
    (fullOracle_adjoint_norm_le h ht)
  exact (Matrix.l2_opNorm_mul _ _).trans (by
    have hh := Matrix.l2_opNorm_mul (Matrix.kronecker (leftOnFock (α:=α) h) (1:CMatrix N)) L
    have hx := mul_le_mul hA hL (norm_nonneg L) (by norm_num)
    have hy := mul_le_mul (hh.trans hx) hB (norm_nonneg _) (by norm_num)
    simpa only [one_mul] using hy)

theorem polarPair_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α)
    (L:Matrix (InputCutoff (α:=α) T×N) (InputCutoff (α:=α) T×M) ℂ) (hL:‖L‖≤1) :
    ‖polarPair h L‖≤1 := by
  have hA := (tensor_identity_norm_le (μ:=N) (polarLeftOnFock (α:=α) h)).trans (polarLeftOnFock_norm_le h ht)
  have hW : ‖(polarOracle (α:=α) h).conjTranspose‖≤1 := by
    rw [Matrix.l2_opNorm_conjTranspose]; exact polarOracle_norm_le h ht
  have hB := (tensor_identity_norm_le (μ:=M) (polarOracle (α:=α) h).conjTranspose).trans hW
  exact (Matrix.l2_opNorm_mul _ _).trans (by
    have hh := Matrix.l2_opNorm_mul (Matrix.kronecker (polarLeftOnFock (α:=α) h) (1:CMatrix N)) L
    have hx := mul_le_mul hA hL (norm_nonneg L) (by norm_num)
    have hy := mul_le_mul (hh.trans hx) hB (norm_nonneg _) (by norm_num)
    simpa only [one_mul] using hy)

theorem pair_difference {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α)
    (L:Matrix (InputCutoff (α:=α) T×N) (InputCutoff (α:=α) T×M) ℂ) (hL:‖L‖≤1) :
    ‖oldPair h L-polarPair h L‖≤7*delta t (Fintype.card α) := by
  have hA := (tensor_identity_norm_le (μ:=N) (polarLeftOnFock (α:=α) h)).trans (polarLeftOnFock_norm_le h ht)
  have hB := (tensor_identity_norm_le (μ:=M) (fullOracle (α:=α) h).conjTranspose).trans
    (fullOracle_adjoint_norm_le h ht)
  have ha : ‖Matrix.kronecker (leftOnFock (α:=α) h) (1:CMatrix N)-
      Matrix.kronecker (polarLeftOnFock (α:=α) h) (1:CMatrix N)‖≤delta t (Fintype.card α) := by
    rw [←tensor_sub]
    exact (tensor_identity_norm_le _).trans (left_polar_distance h ht)
  have hb : ‖Matrix.kronecker (fullOracle (α:=α) h).conjTranspose (1:CMatrix M)-
      Matrix.kronecker (polarOracle (α:=α) h).conjTranspose (1:CMatrix M)‖≤6*delta t (Fintype.card α) := by
    rw [←tensor_sub,←Matrix.conjTranspose_sub]
    exact (tensor_identity_norm_le _).trans (by
      rw [Matrix.l2_opNorm_conjTranspose]; exact oracle_polar_distance h ht)
  have hh := triple_difference _ _ _ _ L _ _ hA hB hL ha hb
  convert hh using 1 <;> try rfl
  ring

#print axioms pair_difference
end
end ICO.C6PolarReplacement

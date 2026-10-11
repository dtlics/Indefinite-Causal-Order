import ICO.MHSymmetric
import ICO.MHProfileTranspose

/-! Exact symbol-transpose covariance on unrestricted symmetric occupation records. -/

namespace ICO.MHSymbolTranspose
open Matrix QIT ICO.MHSymmetric ICO.MHProfileTranspose
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
variable {α : Type*} [Fintype α] [DecidableEq α]

def wordTranspose (n : ℕ) : TensorPower (α × α) n ≃ TensorPower (α × α) n :=
  (tensorPowerEquiv n).trans ((Equiv.piCongrRight (fun _ : Fin n => Equiv.prodComm α α)).trans
    (tensorPowerEquiv n).symm)

theorem wordTranspose_symbol {n : ℕ} (w : TensorPower (α × α) n) (k : Fin n) :
    tensorPowerEquiv n (wordTranspose n w) k = (tensorPowerEquiv n w k).swap := by
  simp [wordTranspose, Equiv.trans_apply]

theorem wordTranspose_involutive {n : ℕ} (w : TensorPower (α × α) n) :
    wordTranspose n (wordTranspose n w) = w := by
  apply (tensorPowerEquiv n).injective
  funext k
  rw [wordTranspose_symbol, wordTranspose_symbol, Prod.swap_swap]

theorem wordTranspose_count {n : ℕ} (w : TensorPower (α × α) n) (x y : α) :
    tensorPowerTypeProfile n (wordTranspose n w) (x,y) = tensorPowerTypeProfile n w (y,x) := by
  unfold tensorPowerTypeProfile
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro k
  rw [wordTranspose_symbol]
  simp only [Prod.ext_iff, Prod.swap, and_comm]

theorem wordTranspose_class {n : ℕ} (p : TensorPowerProfile (α × α) n)
    (w : TensorPower (α × α) n) :
    wordTranspose n w ∈ tensorPowerProfileClass (profileTranspose n p) ↔
      w ∈ tensorPowerProfileClass p := by
  simp only [mem_tensorPowerProfileClass, funext_iff]
  constructor
  · intro h z
    rcases z with ⟨x,y⟩
    have hh := h (y,x)
    simpa only [wordTranspose_count, profileTranspose_count] using hh
  · intro h z
    rcases z with ⟨x,y⟩
    rw [wordTranspose_count, profileTranspose_count]
    exact h (y,x)

def classTranspose {n : ℕ} (p : TensorPowerProfile (α × α) n) :
    ↥(tensorPowerProfileClass p) ≃ ↥(tensorPowerProfileClass (profileTranspose n p)) where
  toFun w := ⟨wordTranspose n w.val, (wordTranspose_class p w.val).2 w.property⟩
  invFun w := ⟨wordTranspose n w.val, by
    have h := (wordTranspose_class (profileTranspose n p) w.val).2 w.property
    simpa only [profileTranspose_involutive] using h⟩
  left_inv w := by apply Subtype.ext; exact wordTranspose_involutive w.val
  right_inv w := by apply Subtype.ext; exact wordTranspose_involutive w.val

theorem profileTranspose_class_card {n : ℕ} (p : TensorPowerProfile (α × α) n) :
    (tensorPowerProfileClass (profileTranspose n p)).card = (tensorPowerProfileClass p).card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (classTranspose p)).symm

theorem occupationEmbedding_transpose {n : ℕ} (p : TensorPowerProfile (α × α) n)
    (w : TensorPower (α × α) n) :
    occupationEmbedding n (wordTranspose n w) (profileTranspose n p) = occupationEmbedding n w p := by
  simp only [occupationEmbedding, tensorPowerProfileUnitVector,
    wordTranspose_class, profileTranspose_class_card]

theorem tensorPower_transpose (U V : Matrix.unitaryGroup (α × α) ℂ)
    (hV : ∀ i j, (V : CMatrix (α × α)) i j = (U : CMatrix (α × α)) i.swap j.swap)
    (n : ℕ) (w v : TensorPower (α × α) n) :
    (unitaryTensorPowerMatrix V n : CMatrix (TensorPower (α × α) n)) w v =
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (α × α) n)) (wordTranspose n w) (wordTranspose n v) := by
  rw [unitaryTensorPowerMatrix_apply_eq_fin_prod, unitaryTensorPowerMatrix_apply_eq_fin_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [wordTranspose_symbol, wordTranspose_symbol]
  exact hV _ _

theorem occupationRotation_transpose (U V : Matrix.unitaryGroup (α × α) ℂ)
    (hV : ∀ i j, (V : CMatrix (α × α)) i j = (U : CMatrix (α × α)) i.swap j.swap)
    (n : ℕ) (p q : TensorPowerProfile (α × α) n) :
    occupationRotation V n p q = occupationRotation U n (profileTranspose n p) (profileTranspose n q) := by
  simp only [occupationRotation, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [tensorPower_transpose U V hV]
  conv_lhs =>
    arg 2
    ext w
    rw [← occupationEmbedding_transpose q w]
    arg 1
    arg 2
    ext v
    rw [← occupationEmbedding_transpose p v]
  have hs (f : TensorPower (α × α) n → ℂ) :
      (∑ w, f (wordTranspose n w)) = ∑ w, f w := (wordTranspose n).sum_comp f
  calc
    _ = ∑ w, (∑ v, star (occupationEmbedding n v (profileTranspose n p)) *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (α × α) n)) v (wordTranspose n w)) *
        occupationEmbedding n (wordTranspose n w) (profileTranspose n q) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hs (fun v => star (occupationEmbedding n v (profileTranspose n p)) *
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (α × α) n)) v (wordTranspose n w))]
    _ = _ := hs (fun w => (∑ v, star (occupationEmbedding n v (profileTranspose n p)) *
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower (α × α) n)) v w) *
      occupationEmbedding n w (profileTranspose n q))

#print axioms occupationRotation_transpose
end
end ICO.MHSymbolTranspose


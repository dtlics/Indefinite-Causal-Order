import ICO.HaarFrame
import ICO.HaarSecondMoment

/-! # Local equality-projector twirls used in the Ma--Huang collision estimate -/

open scoped Matrix.Norms.L2Operator
open Matrix QIT MeasureTheory ICO.HaarMoments ICO.HaarFrame ICO.CausalReverse

namespace ICO.EqualityTwirl
set_option maxHeartbeats 600000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem row_fourth_sum (a b c d : A) :
    (∑ x, fourthMoment x x c d x x a b) =
      (delta a c * delta b d + delta a d * delta b c) / ((Fintype.card A : ℂ) + 1) := by
  have hself (x : A) : delta x x = 1 := by simp [delta]
  simp_rw [fourthMoment_delta, hself]
  simp only [one_mul, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : (Fintype.card A : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (ne_of_gt (Fintype.one_lt_card (α := A)))
  have hp : (Fintype.card A : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (Fintype.card A)
  have hs : (Fintype.card A : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [show (Fintype.card A : ℂ) ^ 2 - 1 =
      ((Fintype.card A : ℂ) - 1) * ((Fintype.card A : ℂ) + 1) by ring]
    exact mul_ne_zero hm hp
  field_simp [hd, hp, hs]
  ring

def equalityProjector : CMatrix (A × A) :=
  Matrix.diagonal (fun i => if i.1 = i.2 then 1 else 0)

def sameTensor (U : Matrix.unitaryGroup A ℂ) : CMatrix (A × A) :=
  Matrix.kronecker (U : CMatrix A) (U : CMatrix A)

def conjugateTensor (U : Matrix.unitaryGroup A ℂ) : CMatrix (A × A) :=
  Matrix.kronecker (U : CMatrix A) ((U : CMatrix A).map star)

theorem same_integrand_entry (U : Matrix.unitaryGroup A ℂ) (i j : A × A) :
    ((sameTensor U).conjTranspose * equalityProjector (A := A) * sameTensor U) i j =
      ∑ x, star ((U : CMatrix A) x i.1 * (U : CMatrix A) x i.2) *
        ((U : CMatrix A) x j.1 * (U : CMatrix A) x j.2) := by
  simp [sameTensor, equalityProjector, Matrix.mul_apply, Matrix.diagonal,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite]

theorem conjugate_integrand_entry (U : Matrix.unitaryGroup A ℂ) (i j : A × A) :
    ((conjugateTensor U).conjTranspose * equalityProjector (A := A) * conjugateTensor U) i j =
      ∑ x, star ((U : CMatrix A) x i.1) * (U : CMatrix A) x i.2 *
        ((U : CMatrix A) x j.1 * star ((U : CMatrix A) x j.2)) := by
  simp [conjugateTensor, equalityProjector, Matrix.mul_apply, Matrix.diagonal,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite, Matrix.map_apply, mul_comm]

end
end ICO.EqualityTwirl


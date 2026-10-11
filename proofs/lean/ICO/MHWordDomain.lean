import ICO.MHWordDistinct

/-! A concrete operator bound for the fresh-input plus Bell-image model
on distinct ordered records. Its recording-oracle identification is separate. -/
namespace ICO.MHWordDomain
open Matrix QIT ICO.MHWordDistinct
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {A J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype J] [DecidableEq J]

theorem sandwich_order {H : Type*} [Fintype H] [DecidableEq H]
    (P X Y : CMatrix H) (hP : IsSelfAdjoint P) (h : X ≤ Y) :
    P*X*P ≤ P*Y*P := by
  apply Matrix.le_iff.mpr
  have hh := (Matrix.le_iff.mp h).mul_mul_conjTranspose_same P
  have he : P.conjTranspose = P := hP.star_eq
  simpa only [he,Matrix.mul_sub,Matrix.sub_mul] using hh

theorem slotEquality_nonneg (j : J) : 0 ≤ slotEquality (A := A) j := by
  classical
  apply Matrix.nonneg_iff_posSemidef.mpr
  rw [slotEquality_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro v
  change (0 : ℂ) ≤ if v.1 = (v.2 j).1 then 1 else 0
  split_ifs <;> norm_num

def domainModel (R : Finset J) (κ : ℝ) : CMatrix (WordBasis A J) :=
  distinctProjection * (freshProjection + κ • (∑ j ∈ R, slotBell j)) * distinctProjection

theorem domain_loss_operator_bound (L R : Finset J)
    (hdis : Disjoint L R) (hcover : L ∪ R = Finset.univ)
    (κ : ℝ) (hκ : 1 ≤ κ) :
    distinctProjection (A := A) (J := J) - domainModel R κ ≤
      κ • ((∑ j ∈ L, slotEquality j) + (∑ j ∈ R, (slotEquality j-slotBell j)) +
        ((R.card : ℝ) * 2 * Real.sqrt ((Fintype.card J : ℝ)/Fintype.card A)) •
          (1 : CMatrix (WordBasis A J))) := by
  classical
  let P := distinctProjection (A := A) (J := J)
  let E : CMatrix (WordBasis A J) := ∑ j : J, slotEquality j
  let B : CMatrix (WordBasis A J) := ∑ j ∈ R, slotBell j
  have hp : IsStarProjection P := distinct_projection
  have hE : 0 ≤ E := Finset.sum_nonneg (fun j _ => slotEquality_nonneg j)
  have hκ0 : 0 ≤ κ := le_trans (by norm_num) hκ
  have hscale : E ≤ κ • E := by
    simpa using smul_le_smul_of_nonneg_right hκ hE
  have hbase : (1-freshProjection (A := A) (J := J))-κ•B ≤ κ•(E-B) := by
    have hh := sub_le_sub_right (collision_union_bound.trans hscale) (κ•B)
    simpa only [smul_sub] using hh
  have he : P-domainModel R κ = P*((1-freshProjection)-κ•B)*P := by
    simp only [domainModel,P,B,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_add,
      Matrix.add_mul,Matrix.mul_one,hp.isIdempotentElem.eq]
    abel
  rw [he]
  have hs := sandwich_order P _ _ hp.isSelfAdjoint hbase
  apply hs.trans
  rw [Matrix.mul_smul,Matrix.smul_mul]
  apply smul_le_smul_of_nonneg_left _ hκ0
  have hsum : E-B = (∑ j ∈ L, slotEquality j) +
      (∑ j ∈ R, (slotEquality j-slotBell j)) := by
    dsimp only [E,B]
    have hh := Finset.sum_union hdis (f := fun j : J => slotEquality (A := A) j)
    rw [hcover] at hh
    rw [hh]
    simp only [Finset.sum_sub_distrib]
    abel
  rw [hsum,Matrix.mul_add,Matrix.add_mul]
  simp only [Matrix.mul_sum,Matrix.sum_mul]
  have hL : (∑ j ∈ L, P*slotEquality j*P) ≤ ∑ j ∈ L, slotEquality j :=
    Finset.sum_le_sum (fun j _ => equality_compression j)
  have hR : (∑ j ∈ R, P*(slotEquality j-slotBell j)*P) ≤
      (∑ j ∈ R, (slotEquality j-slotBell j)) +
        ((R.card : ℝ)*2*Real.sqrt ((Fintype.card J : ℝ)/Fintype.card A)) •
          (1 : CMatrix (WordBasis A J)) := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ R) => word_record_compression (A := A) j)
    simp only [Finset.sum_add_distrib,Finset.sum_const] at hh
    convert hh using 1
    rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    congr 2
    ring
  simpa only [add_assoc] using add_le_add hL hR

#print axioms domain_loss_operator_bound
end
end ICO.MHWordDomain

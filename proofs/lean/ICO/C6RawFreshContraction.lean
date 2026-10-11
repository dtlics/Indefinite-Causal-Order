import ICO.C6BosonicFresh
import ICO.C6BosonicRightSupport

/-! Raw inverse births into an unoccupied label subspace are contractions.
The zero-occupation restriction is an actual bosonic projection. -/
namespace ICO.C6RawFreshContraction
open QIT ICO.C6BosonicFresh ICO.C6BosonicCompression ICO.C6BosonicRight
  ICO.C6BosonicPolar ICO.C6BosonicSupport ICO.C6BosonicCCR
  ICO.MHCreationCoefficients ICO.MHOccupationCounts ICO.MHOccupationCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem creator_zero_occupation (S:Finset A) (n:ℕ) (x y:A) (hx:x∈S)
    (p:TensorPowerProfile (A×A) (n+1)) (q:TensorPowerProfile (A×A) n)
    (hp:labelNumber S p=0) : creator n (x,y) p q=0 := by
  have hn:p≠incrementProfile (x,y) q := by
    intro he
    rw [he,labelNumber_increment,if_pos hx] at hp
    omega
  simp only [creator,creationOccupation_basis_entry,if_neg hn]

theorem normalCompression_zero_occupation (S:Finset A) (n:ℕ) :
    normalCompression S n*targetNumberProjection S (n+1) 0=0 := by
  ext i j
  simp only [targetNumberProjection,Matrix.mul_diagonal,Matrix.zero_apply]
  by_cases hj:labelNumber S j.2=0
  · rw [if_pos hj,mul_one]
    unfold normalCompression
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro p hp
    rw [creator_zero_occupation S n x i.1 hx j.2 p hj,star_zero,mul_zero]
  · rw [if_neg hj,mul_zero]

theorem number_projection (S:Finset A) (n k:ℕ) :
    IsStarProjection (targetNumberProjection (A:=A) S n k) := by
  constructor
  · change targetNumberProjection S n k*targetNumberProjection S n k=targetNumberProjection S n k
    ext i j
    simp only [targetNumberProjection,Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply]
    split_ifs <;> simp
  · exact targetNumberProjection_adjoint S n k

theorem compressedCreator_zero_gram (S:Finset A) (n:ℕ) :
    (compressedCreator S n*targetNumberProjection S n 0).conjTranspose*
      (compressedCreator S n*targetNumberProjection S n 0)=
      (S.card:ℂ) • targetNumberProjection S n 0 := by
  let P:=targetNumberProjection (A:=A) S n 0
  have hP:P*P=P:=(number_projection S n 0).isIdempotentElem.eq
  rw [Matrix.conjTranspose_mul,targetNumberProjection_adjoint]
  change P*(compressedCreator S n).conjTranspose*(compressedCreator S n*P)=_
  rw [Matrix.mul_assoc,←Matrix.mul_assoc (compressedCreator S n).conjTranspose]
  have he:(compressedCreator S n).conjTranspose*compressedCreator S n*P=(S.card:ℂ) • P := by
    cases n with
    | zero => rw [compressedCreator_vacuum_gram,Matrix.smul_mul,Matrix.one_mul]
    | succ n =>
      rw [compressedCreator_succ_gram,Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul]
      change (S.card:ℂ) • P+normalCompression S n*targetNumberProjection S (n+1) 0=_
      rw [normalCompression_zero_occupation,add_zero]
  rw [he,Matrix.mul_smul,hP]

theorem compressedCreator_zero_norm_sq (S:Finset A) (n:ℕ) :
    ‖compressedCreator S n*targetNumberProjection S n 0‖^2≤(S.card:ℝ) := by
  rw [pow_two,←Matrix.l2_opNorm_conjTranspose_mul_self,compressedCreator_zero_gram,
    norm_smul,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left (IsStarProjection.norm_le _ (number_projection S n 0))
    (Nat.cast_nonneg S.card)).trans_eq (mul_one _)

theorem raw_fresh_norm_sq (S:Finset A) (n:ℕ) :
    ‖queryProjection S (n+1)*rightInsertion (A:=A) n*targetNumberProjection S n 0‖^2≤
      (S.card:ℝ)/Fintype.card A := by
  rw [projected_rightInsertion,Matrix.smul_mul,norm_smul,mul_pow,inverse_root_norm_square]
  exact (mul_le_mul_of_nonneg_left (compressedCreator_zero_norm_sq S n)
    (by positivity)).trans_eq (by ring)

theorem raw_fresh_norm (S:Finset A) (n:ℕ) :
    ‖queryProjection S (n+1)*rightInsertion (A:=A) n*targetNumberProjection S n 0‖≤1 := by
  have h:=raw_fresh_norm_sq S n
  have hd:0<(Fintype.card A:ℝ):=by exact_mod_cast Fintype.card_pos (α:=A)
  have hs:(S.card:ℝ)≤Fintype.card A:=by exact_mod_cast Finset.card_le_univ S
  have hq:(S.card:ℝ)/Fintype.card A≤1:=(div_le_one hd).2 hs
  nlinarith [norm_nonneg (queryProjection S (n+1)*rightInsertion (A:=A) n*targetNumberProjection S n 0)]

#print axioms compressedCreator_zero_gram
#print axioms raw_fresh_norm
end
end ICO.C6RawFreshContraction

import ICO.C6BosonicCompression
import ICO.C6BosonicInverseRoot

/-! The sharp finite-dimensional bound for the fresh-birth query compression. -/
namespace ICO.C6BosonicFresh
open QIT ICO.C6BosonicRight ICO.C6BosonicPolar ICO.C6BosonicBounds
  ICO.C6BosonicCompression ICO.C6BosonicInverseRoot ICO.C6Polar
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem compressedCreator_vacuum_gram (S : Finset A) :
    (compressedCreator S 0).conjTranspose * compressedCreator S 0 =
      (S.card : ℂ) • (1 : CMatrix (Sector (A:=A) 0)) := by
  ext i j
  rw [compressedCreator_gram_entry]
  simp only [creator_vacuum_gram,Prod.mk.injEq,true_and]
  have hp := vacuum_unique i.2 j.2
  by_cases h : i.1=j.1 <;> simp [h,hp,Matrix.smul_apply,Matrix.one_apply,Prod.ext_iff]

theorem compressedCreator_square_bound (S : Finset A) (n : ℕ) :
    ‖compressedCreator (A:=A) S n‖^2 ≤ (S.card : ℝ)+n := by
  rw [pow_two,←Matrix.l2_opNorm_conjTranspose_mul_self]
  cases n with
  | zero =>
    rw [compressedCreator_vacuum_gram,norm_smul,Complex.norm_natCast,norm_one]
    simp
  | succ n =>
    rw [compressedCreator_succ_gram]
    have hc : ‖(S.card : ℂ) • (1 : CMatrix (Sector (A:=A) (n+1)))‖=(S.card : ℝ) := by
      rw [norm_smul,Complex.norm_natCast,norm_one,mul_one]
    calc
      _ ≤ ‖(S.card : ℂ) • (1 : CMatrix (Sector (A:=A) (n+1)))‖+
          ‖normalCompression S n‖ := norm_add_le _ _
      _ ≤ (S.card : ℝ)+(n+1) := by rw [hc]; exact add_le_add le_rfl (normalCompression_norm S n)
      _ = _ := by norm_num

theorem projected_rightInsertion (S : Finset A) (n : ℕ) :
    queryProjection S (n+1)*rightInsertion (A:=A) n =
      (Real.sqrt (Fintype.card A) : ℂ)⁻¹ • compressedCreator S n := by
  rw [rightInsertion,Matrix.mul_smul]
  rfl

theorem inverse_root_norm_square :
    ‖(Real.sqrt (Fintype.card A) : ℂ)⁻¹‖^2 = 1/(Fintype.card A : ℝ) := by
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

theorem query_compressed_rightInsertion_square (S : Finset A) (n : ℕ) :
    ‖queryProjection S (n+1)*rightInsertion (A:=A) n‖^2 ≤
      ((S.card : ℝ)+n)/Fintype.card A := by
  rw [projected_rightInsertion,norm_smul,mul_pow,inverse_root_norm_square]
  exact (mul_le_mul_of_nonneg_left (compressedCreator_square_bound S n)
    (by positivity)).trans_eq (by ring)

/-- If there are `n` old right particles and the selected query subspace has
dimension k, its squared overlap with the next polar creator is at most
`(k+n)/(d-n)`. Replacing n by r-1 gives the manuscript's compression bound. -/
theorem query_compressed_rightPolar_square (S : Finset A) {n : ℕ}
    (hn : n<Fintype.card A) :
    ‖queryProjection S (n+1)*rightPolar (A:=A) n‖^2 ≤
      ((S.card : ℝ)+n)/((Fintype.card A : ℝ)-n) := by
  have hd : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos (α:=A)
  have hn' : (n:ℝ)<Fintype.card A := by exact_mod_cast hn
  have hδ : (n:ℝ)/Fintype.card A<1 := (div_lt_one hd).2 hn'
  have h := compressed_polar_square_bound (rightInsertion (A:=A) n)
    (queryProjection S (n+1)) ((n:ℝ)/Fintype.card A)
    (((S.card:ℝ)+n)/Fintype.card A) hδ (rightInsertion_gram_defect n)
    (query_compressed_rightInsertion_square S n)
  change ‖queryProjection S (n+1)*rightPolar n‖^2 ≤ _ at h
  have he : (((S.card:ℝ)+n)/Fintype.card A)/(1-(n:ℝ)/Fintype.card A)=
      ((S.card:ℝ)+n)/((Fintype.card A:ℝ)-n) := by
    field_simp
  rwa [he] at h

#print axioms query_compressed_rightPolar_square
end
end ICO.C6BosonicFresh

import ICO.C6BosonicGram
import ICO.C6BosonicCCR
import ICO.MHOccupationCovariance
import ICO.MHOccupationCounts
import ICO.MHERecordingApprox
import ICO.MHCreationCovariance
import QIT.Symmetry.SymmetricSubspace

/-! Uniform Gram defect for the actual normalized multiset creator. -/
namespace ICO.C6BosonicBounds
open QIT ICO.C6BosonicGram ICO.C6BosonicCCR ICO.MHOccupationCovariance
  ICO.MHOccupationCounts ICO.MHERecordingApprox ICO.MHCreationCovariance
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {a : Type*} [Fintype a] [DecidableEq a]

theorem vacuum_count (p : TensorPowerProfile a 0) (z : a) : p.val z = 0 := by
  have hs := tensorPowerTypeProfile_sum_of_mem_profiles 0 p.property
  have hh := Finset.single_le_sum (fun x (_ : x ∈ (Finset.univ : Finset a)) =>
    Nat.zero_le (p.val x)) (Finset.mem_univ z)
  omega

theorem vacuum_unique (p q : TensorPowerProfile a 0) : p=q := by
  apply Subtype.ext
  funext z
  rw [vacuum_count, vacuum_count]

theorem creator_vacuum_gram (z w : a) (p q : TensorPowerProfile a 0) :
    ((creator 0 z).conjTranspose * creator 0 w) p q = if z=w then 1 else 0 := by
  have hpq := vacuum_unique p q
  subst q
  rw [creator_gram_entry]
  by_cases h : z=w
  · subst w
    simp [vacuum_count]
  · have hi : incrementProfile z p ≠ incrementProfile w p := by
      intro he
      have hc := congrArg (fun q : TensorPowerProfile a 1 => q.val z) he
      change (incrementProfile z p).val z = (incrementProfile w p).val z at hc
      simp [incrementProfile_apply,vacuum_count,h,Ne.symm h] at hc
    simp [h,hi]

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem occupationLeftCreator_vacuum :
    (occupationLeftCreator (α := A) 0).conjTranspose * occupationLeftCreator (α := A) 0 =
      (Fintype.card A : ℂ) • (1 : CMatrix (A × TensorPowerProfile (A×A) 0)) := by
  ext i j
  have he : ((occupationLeftCreator (α := A) 0).conjTranspose *
      occupationLeftCreator (α := A) 0) i j =
      ∑ y : A, ((creator 0 (i.1,y)).conjTranspose * creator 0 (j.1,y)) i.2 j.2 := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,occupationLeftCreator,
      creator,Fintype.sum_prod_type]
  rw [he]
  simp only [creator_vacuum_gram, Prod.mk.injEq, and_true]
  have hp : i.2=j.2 := vacuum_unique _ _
  by_cases h : i.1=j.1 <;> simp [h,hp,Matrix.smul_apply,Matrix.one_apply,Prod.ext_iff]

theorem symmetricInsertion_eq (n : ℕ) :
    symmetricInsertion (α := A) n =
      (Real.sqrt (Fintype.card A) : ℂ)⁻¹ • occupationLeftCreator (α := A) n := by
  ext o i
  rfl

theorem inverse_root_square :
    star ((Real.sqrt (Fintype.card A) : ℂ)⁻¹) *
      (Real.sqrt (Fintype.card A) : ℂ)⁻¹ = (Fintype.card A : ℂ)⁻¹ := by
  have hs : (Real.sqrt (Fintype.card A) : ℂ) * (Real.sqrt (Fintype.card A) : ℂ) =
      (Fintype.card A : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    rfl
  have hc : star ((Real.sqrt (Fintype.card A) : ℂ)⁻¹) =
      (Real.sqrt (Fintype.card A) : ℂ)⁻¹ := by simp
  rw [hc, ← mul_inv_rev, hs]

theorem symmetricInsertion_gram (n : ℕ) :
    (symmetricInsertion (α := A) n).conjTranspose * symmetricInsertion (α := A) n =
      (Fintype.card A : ℂ)⁻¹ •
        ((occupationLeftCreator (α := A) n).conjTranspose * occupationLeftCreator (α := A) n) := by
  rw [symmetricInsertion_eq, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, inverse_root_square]

variable [Nonempty A]

theorem symmetricInsertion_vacuum_gram :
    (symmetricInsertion (α := A) 0).conjTranspose * symmetricInsertion (α := A) 0 = 1 := by
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [symmetricInsertion_gram,occupationLeftCreator_vacuum,smul_smul,
    inv_mul_cancel₀ hd,one_smul]

theorem symmetricInsertion_succ_defect (n : ℕ) :
    (symmetricInsertion (α := A) (n+1)).conjTranspose * symmetricInsertion (α := A) (n+1) - 1 =
      (Fintype.card A : ℂ)⁻¹ • normalGram (A := A) n := by
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [symmetricInsertion_gram,occupationLeftCreator_gram,smul_add,smul_smul,
    inv_mul_cancel₀ hd,one_smul]
  abel

/-- The actual creator has Gram between `1 ± n/d`.  This operator-norm
form is directly suitable for constructing its polar isometry. -/
theorem symmetricInsertion_gram_defect (n : ℕ) :
    ‖(symmetricInsertion (α := A) n).conjTranspose * symmetricInsertion (α := A) n - 1‖ ≤
      (n : ℝ) / Fintype.card A := by
  cases n with
  | zero => simp [symmetricInsertion_vacuum_gram]
  | succ n =>
    rw [symmetricInsertion_succ_defect, norm_smul, norm_inv, Complex.norm_natCast]
    have hh := mul_le_mul_of_nonneg_left (normalGram_norm_le (A := A) n)
      (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card A)))
    simpa only [Nat.cast_succ,div_eq_mul_inv,mul_comm] using hh

#print axioms symmetricInsertion_gram_defect
end
end ICO.C6BosonicBounds

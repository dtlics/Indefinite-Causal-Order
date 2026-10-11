import ICO.C6BosonicPolar
import ICO.MHProfileTranspose
import ICO.MHProfileBlocks

/-! The inverse creator on actual multiset sectors.  The transpose transport
identifies its Gram bound with the already proved left-creator bound. -/
namespace ICO.C6BosonicRight
open QIT ICO.C6Polar ICO.C6BosonicPolar ICO.C6BosonicBounds ICO.MHProfileTranspose
  ICO.MHOccupationCounts ICO.MHCreationCoefficients ICO.MHOccupationCovariance
  ICO.MHERecordingApprox ICO.MHCreationCovariance ICO.MHProfileBlocks
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def sectorTranspose (n : ℕ) : Sector (A:=A) n ≃ Sector (A:=A) n :=
  Equiv.prodCongr (Equiv.refl A) (profileTranspose n)

def rightInsertion (n : ℕ) : Matrix (Sector (A:=A) (n+1)) (Sector (A:=A) n) ℂ :=
  (Real.sqrt (Fintype.card A) : ℂ)⁻¹ • occupationRightCreator (α:=A) n

theorem rightInsertion_transpose (n : ℕ) : rightInsertion (A:=A) n =
    (symmetricInsertion (α:=A) n).submatrix (sectorTranspose (n+1)) (sectorTranspose n) := by
  ext o i
  simp only [rightInsertion,Matrix.submatrix_apply,sectorTranspose,Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, Equiv.refl_apply,symmetricInsertion_eq,Matrix.smul_apply,smul_eq_mul,
    occupationRightCreator,occupationLeftCreator,creationOccupation_basis_entry]
  have hc : (profileTranspose n i.2).val (i.1,o.1)=i.2.val (o.1,i.1) :=
    profileTranspose_count i.2 i.1 o.1
  rw [hc]
  have hi : profileTranspose (n+1) o.2 = incrementProfile (i.1,o.1) (profileTranspose n i.2) ↔
      o.2=incrementProfile (o.1,i.1) i.2 := by
    rw [←profileTranspose_increment]
    exact (profileTranspose (n+1)).injective.eq_iff
  simp only [hi]

theorem rightInsertion_gram (n : ℕ) :
    (rightInsertion (A:=A) n).conjTranspose*rightInsertion n =
      ((symmetricInsertion (α:=A) n).conjTranspose*symmetricInsertion n).submatrix
        (sectorTranspose n) (sectorTranspose n) := by
  rw [rightInsertion_transpose,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]

theorem rightInsertion_gram_defect (n : ℕ) :
    ‖(rightInsertion (A:=A) n).conjTranspose * (rightInsertion (A:=A) n) - 1‖ ≤
      (n:ℝ)/Fintype.card A := by
  rw [rightInsertion_gram]
  have he : ((symmetricInsertion (α:=A) n).conjTranspose * (symmetricInsertion (α:=A) n)).submatrix
        (sectorTranspose n) (sectorTranspose n) - 1 =
      ((symmetricInsertion (α:=A) n).conjTranspose * (symmetricInsertion (α:=A) n) - 1).submatrix
        (sectorTranspose n) (sectorTranspose n) := by
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv]
  rw [he]
  exact (reindex_norm_le _ (sectorTranspose n)).trans (symmetricInsertion_gram_defect n)

theorem rightInsertion_defect_lt_one {n : ℕ} (hn : n<Fintype.card A) :
    ‖gram (rightInsertion (A:=A) n)-1‖<1 := by
  apply (rightInsertion_gram_defect n).trans_lt
  apply (div_lt_one (by exact_mod_cast Fintype.card_pos (α:=A))).2
  exact_mod_cast hn

def rightPolar (n : ℕ) : Matrix (Sector (A:=A) (n+1)) (Sector (A:=A) n) ℂ :=
  polar (rightInsertion (A:=A) n)

theorem rightPolar_isometry {n : ℕ} (hn : n<Fintype.card A) :
    (rightPolar (A:=A) n).conjTranspose * (rightPolar (A:=A) n) = 1 :=
  polar_isometry _ (rightInsertion_defect_lt_one hn)

theorem rightPolar_distance {n : ℕ} (hn : n<Fintype.card A) :
    ‖rightInsertion (A:=A) n-rightPolar n‖≤(n:ℝ)/Fintype.card A :=
  (polar_distance_le_of_defect_lt_one _ (rightInsertion_defect_lt_one hn)).trans
    (rightInsertion_gram_defect n)

#print axioms rightInsertion_gram_defect
#print axioms rightPolar_isometry
end
end ICO.C6BosonicRight

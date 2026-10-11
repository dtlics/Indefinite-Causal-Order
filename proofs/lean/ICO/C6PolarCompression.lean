import ICO.C6PolarReindex
import ICO.C6BosonicFreshRotated

/-! Sharp query compression transported through actual profile transposition. -/
namespace ICO.C6PolarCompression
open QIT ICO.C6PolarReindex ICO.C6BosonicPolar ICO.C6BosonicRight
  ICO.C6BosonicFreshRotated ICO.MHProfileTranspose ICO.MHProfileBlocks
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {a b:Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem rectangular_reindex_norm_le {a' b':Type*}
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (M:Matrix b a ℂ) (eo:b'≃b) (ei:a'≃a) :
    ‖M.submatrix eo ei‖≤‖M‖ := by
  have hh := reindex_norm_le (M.conjTranspose*M) ei
  have he : (M.submatrix eo ei).conjTranspose*(M.submatrix eo ei)=
      (M.conjTranspose*M).submatrix ei ei := by
    rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  rw [←he,Matrix.l2_opNorm_conjTranspose_mul_self,Matrix.l2_opNorm_conjTranspose_mul_self] at hh
  nlinarith [norm_nonneg (M.submatrix eo ei),norm_nonneg M]

variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem queryTensor_transpose (P:CMatrix A) (n:ℕ) :
    (Matrix.kronecker P (1:CMatrix (TensorPowerProfile (A×A) n))).submatrix
      (sectorTranspose n) (sectorTranspose n)=Matrix.kronecker P (1:CMatrix (TensorPowerProfile (A×A) n)) := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,sectorTranspose,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,Equiv.refl_apply]
  simp only [(profileTranspose n).injective.eq_iff]

theorem leftPolar_transpose (n:ℕ) :
    leftPolar (A:=A) n=(rightPolar (A:=A) n).submatrix (sectorTranspose (n+1)) (sectorTranspose n) := by
  ext i j
  rw [Matrix.submatrix_apply,rightPolar_transpose,Matrix.submatrix_apply]
  have hi : sectorTranspose (n+1) (sectorTranspose (n+1) i)=i := by
    exact Prod.ext rfl (profileTranspose_involutive i.2)
  have hj : sectorTranspose n (sectorTranspose n j)=j := by
    exact Prod.ext rfl (profileTranspose_involutive j.2)
  rw [hi,hj]

theorem rotated_leftPolar_square (U:Matrix.unitaryGroup A ℂ) (S:Finset A)
    {n:ℕ} (hn:n<Fintype.card A) :
    ‖rotatedQueryProjection U S (n+1)*leftPolar (A:=A) n‖^2≤
      ((S.card:ℝ)+n)/((Fintype.card A:ℝ)-n) := by
  have he : rotatedQueryProjection U S (n+1)*leftPolar (A:=A) n=
      (rotatedQueryProjection U S (n+1)*rightPolar (A:=A) n).submatrix
        (sectorTranspose (n+1)) (sectorTranspose n) := by
    symm
    rw [←Matrix.submatrix_mul_equiv _ _ _ (sectorTranspose (n+1)) _]
    rw [rotatedQueryProjection,queryTensor_transpose,←leftPolar_transpose]
  rw [he]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (rectangular_reindex_norm_le _ _ _) 2).trans (rotated_rightPolar_square U S hn)

#print axioms rotated_leftPolar_square
end
end ICO.C6PolarCompression

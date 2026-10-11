import ICO.C6CacheVisible

/-! The literal graded-cache erasure commutes with every known operation. -/
namespace ICO.C6CacheVisibleGraded
open QIT Matrix ICO.C6GradedCache ICO.C6CacheKnownOperation
  ICO.C6CacheReference ICO.C6CacheQueryBound ICO.C6CacheDecode ICO.C6SectorChannel
  ICO.C6MatrixCovariance ICO.C6CacheVisible ICO.RecordingCopyIdentity
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
universe u
variable {A M N : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem known_embed (Q : ℕ) (r : Fin (Q+1)) (K : Matrix (A×N) (A×M) ℂ) :
    known Q K*embed (A := A) (M := M) Q r =
      embed (A := A) (M := N) Q r*externalLift r.val K := by
  have he : known Q K*embed (A := A) (M := M) Q r =
      (known Q K).submatrix id (Sigma.mk r) := by
    simp only [embed, inclusion, basisEmbedding]
    change known Q K*(1 : CMatrix (Graded (A := A) Q M)).submatrix
      (Equiv.refl _) (Sigma.mk r)=_
    rw [Matrix.mul_submatrix_one (Equiv.refl _) (Sigma.mk r)]
    rfl
  rw [he]
  ext ⟨s,x⟩ a
  by_cases h : s=r
  · subst s
    simp [known, Matrix.submatrix_apply, Matrix.mul_apply, embed, inclusion,
      basisEmbedding, Matrix.one_apply, Sigma.mk.inj_iff]
  · simp [known, Matrix.submatrix_apply, Matrix.mul_apply, embed, inclusion,
      basisEmbedding, Matrix.one_apply, Sigma.mk.inj_iff, h]
    exact Matrix.blockDiagonal'_apply_ne (fun s => externalLift s.val K) x a h

theorem known_conjTranspose (Q : ℕ) (K : Matrix (A×N) (A×M) ℂ) :
    (known Q K).conjTranspose = known Q K.conjTranspose := by
  simp only [known, Matrix.blockDiagonal'_conjTranspose, externalLift,
    Matrix.conjTranspose_submatrix, Matrix.kronecker,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem known_decode (Q : ℕ) (r : Fin (Q+1)) (K : Matrix (A×N) (A×M) ℂ) :
    (embed (A := A) (M := N) Q r).conjTranspose*known Q K =
      externalLift r.val K*(embed (A := A) (M := M) Q r).conjTranspose := by
  have h := congrArg Matrix.conjTranspose (known_embed Q r K.conjTranspose)
  simpa only [Matrix.conjTranspose_mul, known_conjTranspose,
    Matrix.conjTranspose_conjTranspose, externalLift, Matrix.conjTranspose_submatrix,
    Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one] using h

theorem known_sector (Q : ℕ) (r : Fin (Q+1)) (K : Matrix (A×N) (A×M) ℂ)
    (X : CMatrix (Graded (A := A) Q M)) :
    (embed (A := A) (M := N) Q r).conjTranspose*(known Q K*X*(known Q K).conjTranspose)*
      embed (A := A) (M := N) Q r =
      externalLift r.val K*((embed (A := A) (M := M) Q r).conjTranspose*X*
        embed (A := A) (M := M) Q r)*(externalLift r.val K).conjTranspose := by
  have ht := congrArg Matrix.conjTranspose (known_decode Q r K)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at ht
  simp only [← Matrix.mul_assoc]
  rw [known_decode]
  simp only [Matrix.mul_assoc]
  rw [ht]

theorem visible_known (Q : ℕ) (K : Matrix (A×N) (A×M) ℂ)
    (X : CMatrix (Graded (A := A) Q M)) :
    (visible Q).map (known Q K*X*(known Q K).conjTranspose) =
      K*(visible Q).map X*K.conjTranspose := by
  rw [visible_apply, visible_apply]
  simp_rw [known_sector, sectorVisible_known]
  rw [Matrix.mul_sum, Matrix.sum_mul]

#print axioms visible_known
end
end ICO.C6CacheVisibleGraded

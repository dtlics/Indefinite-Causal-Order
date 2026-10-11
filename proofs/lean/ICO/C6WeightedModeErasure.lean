import ICO.C6RightImageErasure

/-! Exact branch weights for unnormalized fresh right-label residuals.
Zero residuals vanish identically; nonzero residuals append an inert image
with their actual squared norm, rather than an independently assumed weight. -/
namespace ICO.C6WeightedModeErasure
open QIT ICO.C6OrthogonalModeBirth ICO.C6RightImageErasure
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]
variable {H:Type*} [Fintype H] [DecidableEq H]

theorem selectedRaw_smul (n:ℕ) (c:ℂ) (v:A→ℂ) :
    selectedRaw n (c • v)=c • selectedRaw n v := by
  ext o i
  simp only [selectedRaw,Pi.smul_apply,smul_eq_mul,Matrix.smul_apply,
    mul_assoc,Finset.mul_sum]

theorem selectedRaw_zero (n:ℕ) : selectedRaw (A:=A) n 0=0 := by
  ext o i
  simp [selectedRaw]

theorem scaled_erasure {R E:Type*} [Fintype R] [DecidableEq R]
    [Fintype E] [DecidableEq E] (B:Matrix E R ℂ) (c:ℂ) (X:CMatrix (H×R)) :
    partialTraceB (Matrix.kronecker (1:CMatrix H) (c • B)*X*
      (Matrix.kronecker (1:CMatrix H) (c • B)).conjTranspose)=
      (c*star c) • partialTraceB (Matrix.kronecker (1:CMatrix H) B*X*
        (Matrix.kronecker (1:CMatrix H) B).conjTranspose) := by
  simp only [Matrix.kronecker,Matrix.kronecker_smul,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,partialTraceB_smul]
  rw [mul_comm (star c) c]

theorem weighted_fresh_erasure {n:ℕ} (v:EuclideanSpace ℂ A)
    (w:Fin n→EuclideanSpace ℂ A) (horth:Orthonormal ℂ (Fin.cons v w))
    (c:ℂ) (X:CMatrix (H×(A×(Fin n→A)))) :
    let B:=selectedRaw n (c • fun x=>v x)*Matrix.kronecker (1:CMatrix A) (directEncoding w)
    partialTraceB (Matrix.kronecker (1:CMatrix H) B*X*
      (Matrix.kronecker (1:CMatrix H) B).conjTranspose)=
      ((c*star c)/(Fintype.card A:ℂ)) • partialTraceB X := by
  dsimp only
  rw [selectedRaw_smul,Matrix.smul_mul,scaled_erasure]
  have he := fresh_mode_erasure v w horth X
  dsimp only at he
  rw [he,smul_smul]
  rfl

theorem zero_residual_erasure {n:ℕ} (w:Fin n→EuclideanSpace ℂ A)
    (X:CMatrix (H×(A×(Fin n→A)))) :
    let B:=selectedRaw (A:=A) n 0*Matrix.kronecker (1:CMatrix A) (directEncoding w)
    partialTraceB (Matrix.kronecker (1:CMatrix H) B*X*
      (Matrix.kronecker (1:CMatrix H) B).conjTranspose)=0 := by
  simp only [selectedRaw_zero,Matrix.zero_mul,Matrix.kronecker,Matrix.kronecker_zero,
    Matrix.conjTranspose_zero]
  ext x y
  simp [QIT.partialTraceB]

def normalized (r:EuclideanSpace ℂ A) : EuclideanSpace ℂ A := (‖r‖:ℂ)⁻¹ • r

theorem residual_decomposition (r:EuclideanSpace ℂ A) (hr:r≠0) :
    (fun x=>r x)=(‖r‖:ℂ) • (fun x=>normalized r x) := by
  have hn : (‖r‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr)
  funext x
  simp only [normalized,PiLp.smul_apply,Pi.smul_apply,smul_eq_mul]
  rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]

/-- The weight is derived from the literal residual vector.  In particular
it is zero exactly when the fresh residual is zero. -/
theorem residual_erasure {n:ℕ} (r:EuclideanSpace ℂ A) (hr:r≠0)
    (w:Fin n→EuclideanSpace ℂ A)
    (horth:Orthonormal ℂ (Fin.cons (normalized r) w))
    (X:CMatrix (H×(A×(Fin n→A)))) :
    let B:=selectedRaw n (fun x=>r x)*Matrix.kronecker (1:CMatrix A) (directEncoding w)
    partialTraceB (Matrix.kronecker (1:CMatrix H) B*X*
      (Matrix.kronecker (1:CMatrix H) B).conjTranspose)=
      (((‖r‖^2/(Fintype.card A:ℝ):ℝ):ℂ)) • partialTraceB X := by
  dsimp only
  rw [residual_decomposition r hr]
  have he := weighted_fresh_erasure (normalized r) w horth (‖r‖:ℂ) X
  dsimp only at he
  rw [he]
  congr 1
  simp [Complex.star_def,Complex.conj_ofReal,pow_two]

#print axioms weighted_fresh_erasure
#print axioms zero_residual_erasure
#print axioms residual_erasure
end
end ICO.C6WeightedModeErasure

import ICO.C4DiamondTheorem

/-! Full-control switch channels and their actual plus-state preparation. -/
namespace ICO.FullSwitchChannel
open Matrix QIT ICO.SwitchChoiWitness ICO.ClassicalDilation ICO.GramWitness
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def controlled (T S : CMatrix A) : CMatrix (A × Bool) :=
  fun x y => if x.2 = y.2 then (if x.2 then S x.1 y.1 else T x.1 y.1) else 0

theorem controlled_mul (T S U V : CMatrix A) :
    controlled T S * controlled U V = controlled (T*U) (S*V) := by
  ext ⟨x,b⟩ ⟨y,c⟩
  cases b <;> cases c <;>
    simp [controlled, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool]

theorem controlled_star (T S : CMatrix A) :
    (controlled T S).conjTranspose = controlled T.conjTranspose S.conjTranspose := by
  ext ⟨x,b⟩ ⟨y,c⟩
  cases b <;> cases c <;> simp [controlled, Matrix.conjTranspose_apply]

theorem controlled_one : controlled (1 : CMatrix A) 1 = 1 := by
  ext ⟨x,b⟩ ⟨y,c⟩
  cases b <;> cases c <;> simp [controlled, Matrix.one_apply]

def plusMatrix : Matrix (A × Bool) A ℂ := pairRows 1 1

theorem plus_isometry : (plusMatrix (A := A)).conjTranspose * (plusMatrix (A := A)) = 1 := by
  rw [plusMatrix, pairRows_gram]
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, ← add_smul]
  norm_num

def plusChannel : Channel A (A × Bool) := isometryChannel plusMatrix plus_isometry

theorem controlled_plus (T S : CMatrix A) : controlled T S * plusMatrix = pairRows T S := by
  ext ⟨x,b⟩ y
  cases b <;> simp [controlled, plusMatrix, pairRows, Matrix.mul_apply,
    Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply, mul_comm]

def pair (U V : Matrix.unitaryGroup A ℂ) : CMatrix (A × Bool) :=
  controlled ((V : CMatrix A)*(U : CMatrix A)) ((U : CMatrix A)*(V : CMatrix A))

theorem pair_complete (U V : Matrix.unitaryGroup A ℂ) : (pair U V).conjTranspose * pair U V = 1 := by
  rw [pair, controlled_star, controlled_mul]
  have hVU := Matrix.UnitaryGroup.star_mul_self (V*U)
  have hUV := Matrix.UnitaryGroup.star_mul_self (U*V)
  change (((V : CMatrix A)*(U : CMatrix A)).conjTranspose) *
    ((V : CMatrix A)*(U : CMatrix A)) = 1 at hVU
  change (((U : CMatrix A)*(V : CMatrix A)).conjTranspose) *
    ((U : CMatrix A)*(V : CMatrix A)) = 1 at hUV
  rw [hVU,hUV,controlled_one]

def fullKraus {r s : ℕ} (U : Fin r → Matrix.unitaryGroup A ℂ)
    (V : Fin s → Matrix.unitaryGroup A ℂ) (ij : Fin r × Fin s) : CMatrix (A × Bool) :=
  uniformCoefficient r s • pair (U ij.1) (V ij.2)

theorem fullKraus_plus {r s : ℕ} (U : Fin r → Matrix.unitaryGroup A ℂ)
    (V : Fin s → Matrix.unitaryGroup A ℂ) (ij : Fin r × Fin s) :
    fullKraus U V ij * plusMatrix = mixtureKraus U V ij := by
  simp only [fullKraus, Matrix.smul_mul, pair, controlled_plus, mixtureKraus, pairKraus]

theorem fullKraus_complete {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (U : Fin r → Matrix.unitaryGroup A ℂ) (V : Fin s → Matrix.unitaryGroup A ℂ) :
    (∑ ij, (fullKraus U V ij).conjTranspose * fullKraus U V ij) = 1 := by
  have hentry (ij : Fin r × Fin s) :
      (fullKraus U V ij).conjTranspose * fullKraus U V ij =
        ((r : ℂ)*(s : ℂ))⁻¹ • (1 : CMatrix (A × Bool)) := by
    simp only [fullKraus, Matrix.conjTranspose_smul, uniformCoefficient_star,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, uniformCoefficient_square, pair_complete]
  simp_rw [hentry]
  rw [← Finset.sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  simp [hr', hs', Nat.cast_mul]
  have hc : (r : ℂ)*(s : ℂ)*((s : ℂ)⁻¹*(r : ℂ)⁻¹) = 1 := by field_simp
  rw [hc, one_smul]

def fullChannel {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (U : Fin r → Matrix.unitaryGroup A ℂ) (V : Fin s → Matrix.unitaryGroup A ℂ) :
    Channel (A × Bool) (A × Bool) where
  map := MatrixMap.ofKraus (fullKraus U V)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using fullKraus_complete hr hs U V)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem full_plus_map {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (U : Fin r → Matrix.unitaryGroup A ℂ) (V : Fin s → Matrix.unitaryGroup A ℂ) :
    ((fullChannel hr hs U V).comp plusChannel).map = (mixtureSwitchChannel hr hs U V).map := by
  ext X i j
  change MatrixMap.ofKraus (fullKraus U V)
    ((isometryChannel plusMatrix plus_isometry).map X) i j =
      MatrixMap.ofKraus (mixtureKraus U V) X i j
  rw [isometryChannel_apply]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : fullKraus U V ij * (plusMatrix * X * (plusMatrix (A := A)).conjTranspose) *
      (fullKraus U V ij).conjTranspose =
      (fullKraus U V ij * (plusMatrix (A := A))) * X *
        (fullKraus U V ij * (plusMatrix (A := A))).conjTranspose := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he,fullKraus_plus]

#print axioms fullChannel
#print axioms full_plus_map
end
end ICO.FullSwitchChannel

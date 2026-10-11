import ICO.C6BosonicCCR
import ICO.MHCreationCovariance
import QIT.Symmetry.SymmetricSubspace
import QIT.Util.Matrix

/-! Decoding one of the particles from a normalized occupation register is
an actual isometry.  This identifies the one-particle exchange compression
used to bound the Gram of query-coupled bosonic creation. -/
namespace ICO.C6BosonicDecode
open QIT ICO.C6BosonicCCR ICO.MHCreationCovariance
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
variable {a : Type*} [Fintype a] [DecidableEq a]

def annihilationStack (n : ℕ) :
    Matrix (a × TensorPowerProfile a n) (TensorPowerProfile a (n+1)) ℂ :=
  fun o i => star (creator n o.1 i o.2)

theorem annihilationStack_gram (n : ℕ) :
    (annihilationStack (a := a) n).conjTranspose * annihilationStack (a := a) n =
      ((n+1 : ℕ) : ℂ) • (1 : CMatrix (TensorPowerProfile a (n+1))) := by
  ext p q
  have hh : ((annihilationStack (a := a) n).conjTranspose * annihilationStack (a := a) n) p q =
      ∑ z : a, (creator n z * (creator n z).conjTranspose) p q := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, annihilationStack,
      star_star, Fintype.sum_prod_type]
  rw [hh]
  simp only [creator_self_image, Matrix.diagonal_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply]
  by_cases hpq : p=q
  · subst q
    simp only [if_pos rfl, ite_true, mul_one]
    have hsum := tensorPowerTypeProfile_sum_of_mem_profiles (n+1) p.property
    exact_mod_cast hsum
  · simp [hpq]

def particleDecode (n : ℕ) :
    Matrix (a × TensorPowerProfile a n) (TensorPowerProfile a (n+1)) ℂ :=
  (Real.sqrt (n+1) : ℂ)⁻¹ • annihilationStack n

theorem inv_sqrt_sq (n : ℕ) :
    star (Real.sqrt (n+1) : ℂ)⁻¹ * (Real.sqrt (n+1) : ℂ)⁻¹ *
      ((n+1 : ℕ) : ℂ) = 1 := by
  have hs : (Real.sqrt (n+1) : ℂ)*(Real.sqrt (n+1) : ℂ) = ((n+1 : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hc : star ((Real.sqrt (n+1) : ℂ)⁻¹) = (Real.sqrt (n+1) : ℂ)⁻¹ := by simp
  rw [hc]
  rw [← mul_inv_rev, hs, inv_mul_cancel₀ hn]

theorem particleDecode_gram (n : ℕ) :
    (particleDecode (a := a) n).conjTranspose * particleDecode (a := a) n =
      (1 : CMatrix (TensorPowerProfile a (n+1))) := by
  rw [particleDecode, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, annihilationStack_gram, smul_smul]
  rw [inv_sqrt_sq, one_smul]

#print axioms particleDecode_gram
end
end ICO.C6BosonicDecode

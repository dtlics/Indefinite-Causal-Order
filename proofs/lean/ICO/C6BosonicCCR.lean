import ICO.MHCreationCoefficients
import ICO.MHOccupationSupport
import ICO.MHCreationCovariance
import ICO.MHOccupationCounts
import ICO.MHSymmetric
import QIT.Symmetry.SymmetricSubspace

/-! Occupation-basis identities used by the C6 polar cache.  The creator
below is the already constructed symmetric-tensor creator, not a new formal
operator with postulated canonical commutation relations. -/
namespace ICO.C6BosonicCCR
open QIT ICO.MHSymmetric ICO.MHCreationCovariance
  ICO.MHCreationCoefficients ICO.MHOccupationCounts ICO.MHOccupationSupport
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000
variable {a : Type*} [Fintype a] [DecidableEq a]

abbrev creator (n : ℕ) (z : a) := creationOccupation n (basisVector z)

theorem increment_tail {n : ℕ} (p : TensorPowerProfile a (n+1))
    (z : a) (hz : 0 < p.val z) :
    incrementProfile z (p.tailAfterHead z hz) = p := by
  apply Subtype.ext
  funext w
  rw [incrementProfile_apply, TensorPowerProfile.tailAfterHead_apply]
  by_cases h : z = w
  · subst w
    split_ifs <;> omega
  · simp [h, Ne.symm h]

theorem tail_increment {n : ℕ} (p : TensorPowerProfile a n) (z : a)
    (hz : 0 < (incrementProfile z p).val z) :
    (incrementProfile z p).tailAfterHead z hz = p := by
  apply incrementProfile_injective z
  exact increment_tail _ z hz

theorem creator_gram_entry (n : ℕ) (z w : a)
    (p q : TensorPowerProfile a n) :
    ((creator n z).conjTranspose * creator n w) p q =
      if incrementProfile z p = incrementProfile w q then
        (Real.sqrt (p.val z + 1) : ℂ) * (Real.sqrt (q.val w + 1) : ℂ)
      else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, creator, creationOccupation_basis_entry]
  rw [Finset.sum_eq_single (incrementProfile z p)]
  · simp only [if_pos rfl, map_natCast, starRingEnd_apply, Complex.conj_ofReal]
    by_cases h : incrementProfile z p = incrementProfile w q <;> simp [h]
  · intro r _ hr
    simp [hr]
  · simp

theorem creator_self_gram (n : ℕ) (z : a) :
    (creator n z).conjTranspose * creator n z =
      Matrix.diagonal (fun p : TensorPowerProfile a n => (p.val z + 1 : ℂ)) := by
  ext p q
  rw [creator_gram_entry, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst q
    simp only [if_pos rfl]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  · have hi : incrementProfile z p ≠ incrementProfile z q :=
      fun hi => h (incrementProfile_injective z hi)
    simp [h, hi]

theorem creator_image_entry (n : ℕ) (z w : a)
    (p q : TensorPowerProfile a (n+1)) :
    (creator n w * (creator n z).conjTranspose) p q =
      ∑ r : TensorPowerProfile a n,
        if p = incrementProfile w r ∧ q = incrementProfile z r then
          (Real.sqrt (r.val w + 1) : ℂ) * (Real.sqrt (r.val z + 1) : ℂ)
        else 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Matrix.conjTranspose_apply, creator, creationOccupation_basis_entry]
  by_cases hp : p = incrementProfile w r <;>
    by_cases hq : q = incrementProfile z r <;> simp [hp, hq]

theorem creator_self_image (n : ℕ) (z : a) :
    creator n z * (creator n z).conjTranspose =
      Matrix.diagonal (fun p : TensorPowerProfile a (n+1) => (p.val z : ℂ)) := by
  ext p q
  rw [creator_image_entry, Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    by_cases hz : 0 < p.val z
    · let r := p.tailAfterHead z hz
      have hr : p = incrementProfile z r := (increment_tail p z hz).symm
      rw [Finset.sum_eq_single r]
      · rw [if_pos ⟨hr,hr⟩, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (by positivity)]
        have hc : r.val z + 1 = p.val z := by
          rw [hr, incrementProfile_self]
        exact_mod_cast hc
      · intro s _ hs
        rw [if_neg]
        rintro ⟨he,_⟩
        exact hs (incrementProfile_injective z (he.symm.trans hr))
      · simp
    · have hz0 : p.val z = 0 := by omega
      rw [hz0, Nat.cast_zero]
      apply Finset.sum_eq_zero
      intro r _
      rw [if_neg]
      rintro ⟨he,_⟩
      have hc := congrArg (fun p : TensorPowerProfile a (n+1) => p.val z) he
      change p.val z = (incrementProfile z r).val z at hc
      rw [incrementProfile_self, hz0] at hc
      omega
  · rw [if_neg hpq]
    apply Finset.sum_eq_zero
    intro r _
    rw [if_neg]
    exact fun h => hpq (h.1.trans h.2.symm)

/-- The equal-mode canonical commutator follows from the actual occupation
coefficients, including the boundary where that mode is empty. -/
theorem same_mode_CCR (n : ℕ) (z : a) :
    (creator (n+1) z).conjTranspose * creator (n+1) z =
      (1 : CMatrix (TensorPowerProfile a (n+1))) +
        creator n z * (creator n z).conjTranspose := by
  rw [creator_self_gram, creator_self_image]
  ext p q
  simp only [Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply]
  by_cases h : p=q <;> simp [h, add_comm]

theorem increment_commute (n : ℕ) (z w : a) (r : TensorPowerProfile a n) :
    incrementProfile z (incrementProfile w r) =
      incrementProfile w (incrementProfile z r) := by
  apply Subtype.ext
  funext x
  simp only [incrementProfile_apply]
  omega

theorem common_predecessor {n : ℕ} (z w : a) (hzw : z ≠ w)
    (p q : TensorPowerProfile a (n+1))
    (h : incrementProfile z p = incrementProfile w q) :
    ∃ r : TensorPowerProfile a n,
      p = incrementProfile w r ∧ q = incrementProfile z r := by
  have hc := congrArg (fun s : TensorPowerProfile a (n+1+1) => s.val w) h
  change (incrementProfile z p).val w = (incrementProfile w q).val w at hc
  rw [incrementProfile_apply, incrementProfile_self, if_neg hzw, zero_add] at hc
  have hp : 0 < p.val w := by omega
  let r := p.tailAfterHead w hp
  have hpr : p = incrementProfile w r := (increment_tail p w hp).symm
  refine ⟨r, hpr, ?_⟩
  apply incrementProfile_injective w
  rw [← h, hpr, increment_commute]

/-- Distinct modes commute across creation/annihilation, proved entrywise
using their unique shared predecessor. -/
theorem different_mode_CCR (n : ℕ) (z w : a) (hzw : z ≠ w) :
    (creator (n+1) z).conjTranspose * creator (n+1) w =
      creator n w * (creator n z).conjTranspose := by
  ext p q
  rw [creator_gram_entry, creator_image_entry]
  by_cases h : incrementProfile z p = incrementProfile w q
  · rw [if_pos h]
    obtain ⟨r,hp,hq⟩ := common_predecessor z w hzw p q h
    rw [Finset.sum_eq_single r]
    · rw [if_pos ⟨hp,hq⟩]
      rw [hp,hq]
      simp only [incrementProfile_apply, if_neg hzw, if_neg (Ne.symm hzw), zero_add]
      exact mul_comm _ _
    · intro s _ hs
      rw [if_neg]
      rintro ⟨he,_⟩
      exact hs (incrementProfile_injective w (he.symm.trans hp))
    · simp
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro r _
    rw [if_neg]
    rintro ⟨hp,hq⟩
    apply h
    rw [hp,hq,increment_commute]

theorem canonical_commutator (n : ℕ) (z w : a) :
    (creator (n+1) z).conjTranspose * creator (n+1) w =
      (if z=w then 1 else 0) + creator n w * (creator n z).conjTranspose := by
  by_cases h : z=w
  · subst w
    simp only [if_pos rfl]
    exact same_mode_CCR n z
  · simp only [if_neg h, zero_add]
    exact different_mode_CCR n z w h

#print axioms same_mode_CCR
#print axioms canonical_commutator
end
end ICO.C6BosonicCCR

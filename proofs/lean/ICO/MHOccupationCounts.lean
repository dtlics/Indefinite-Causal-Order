import QIT.Symmetry.SymmetricSubspace
import Mathlib.Tactic

/-! Full multiset occupation profiles and the exact insertion count ratio.
The ratio gives the corrected bosonic amplitude `sqrt(count + 1)`. -/

namespace ICO.MHOccupationCounts

open QIT
open scoped BigOperators

noncomputable section

variable {a : Type*} [Fintype a] [DecidableEq a]

def occupationMultiset (n : ℕ) : TensorPowerProfile a n ≃ Sym a n :=
  TensorPowerProfile.equivWeakCompositions.trans (Sym.equivNatSumOfFintype a n).symm

theorem occupationMultiset_count (n : ℕ) (p : TensorPowerProfile a n) (z : a) :
    (occupationMultiset n p : Multiset a).count z = p.val z := by
  have h := congrArg (fun q : {p : a → ℕ // ∑ z, p z = n} => q.val z)
    ((Sym.equivNatSumOfFintype a n).apply_symm_apply
      (TensorPowerProfile.equivWeakCompositions p))
  exact h

def incrementProfile {n : ℕ} (z : a) (p : TensorPowerProfile a n) :
    TensorPowerProfile a (n + 1) :=
  ⟨tensorPowerTypeProfile (n + 1) (z, p.rep), tensorPowerTypeProfile_mem_profiles _ _⟩

theorem incrementProfile_apply {n : ℕ} (z : a) (p : TensorPowerProfile a n) (w : a) :
    (incrementProfile z p).val w = (if z = w then 1 else 0) + p.val w := by
  simp only [incrementProfile, tensorPowerTypeProfile_succ, TensorPowerProfile.rep_typeProfile]

theorem incrementProfile_self {n : ℕ} (z : a) (p : TensorPowerProfile a n) :
    (incrementProfile z p).val z = p.val z + 1 := by
  simp [incrementProfile_apply, Nat.add_comm]

theorem incrementProfile_update {n : ℕ} (z : a) (p : TensorPowerProfile a n) :
    (incrementProfile z p).val = Function.update p.val z (p.val z + 1) := by
  funext w
  by_cases h : z = w
  · subst w; simp [incrementProfile_self]
  · simp [incrementProfile_apply, h, Ne.symm h]

theorem incrementProfile_multiset {n : ℕ} (z : a) (p : TensorPowerProfile a n) :
    (occupationMultiset (n + 1) (incrementProfile z p) : Multiset a) =
      z ::ₘ (occupationMultiset n p : Multiset a) := by
  apply Multiset.ext.mpr
  intro w
  rw [occupationMultiset_count, Multiset.count_cons, occupationMultiset_count,
    incrementProfile_apply]
  by_cases h : z = w
  · simp [h, Nat.add_comm]
  · simp [h, Ne.symm h, Nat.add_comm]

theorem increment_factorial_product {n : ℕ} (z : a) (p : TensorPowerProfile a n) :
    (∏ w : a, ((incrementProfile z p).val w).factorial) =
      (p.val z + 1) * ∏ w : a, (p.val w).factorial := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ z), incrementProfile_self,
    Nat.factorial_succ]
  have hrest : (∏ w ∈ Finset.univ.erase z, ((incrementProfile z p).val w).factorial) =
      ∏ w ∈ Finset.univ.erase z, (p.val w).factorial := by
    apply Finset.prod_congr rfl
    intro w hw
    simp [incrementProfile_apply, Ne.symm (Finset.mem_erase.mp hw).1]
  rw [hrest, mul_assoc]
  congr 1
  exact Finset.mul_prod_erase Finset.univ (fun w => (p.val w).factorial) (Finset.mem_univ z)

/-- Appending a symbol raises the type-class multiplicity by the exact
factor `(n+1)/(count+1)`, including when the symbol is already present. -/
theorem increment_class_card_ratio {n : ℕ} (z : a) (p : TensorPowerProfile a n) :
    (p.val z + 1) * (tensorPowerProfileClass (incrementProfile z p)).card =
      (n + 1) * (tensorPowerProfileClass p).card := by
  rw [tensorPowerProfileClass_card_eq_multinomial,
    tensorPowerProfileClass_card_eq_multinomial]
  have hp := Nat.multinomial_spec (s := (Finset.univ : Finset a)) (f := p.val)
  have hq := Nat.multinomial_spec (s := (Finset.univ : Finset a))
    (f := (incrementProfile z p).val)
  rw [tensorPowerTypeProfile_sum_of_mem_profiles n p.property] at hp
  rw [tensorPowerTypeProfile_sum_of_mem_profiles (n + 1) (incrementProfile z p).property,
    increment_factorial_product] at hq
  apply Nat.eq_of_mul_eq_mul_left
    (show 0 < ∏ w : a, (p.val w).factorial from Finset.prod_pos (fun _ _ => Nat.factorial_pos _))
  calc
    (∏ w : a, (p.val w).factorial) *
        ((p.val z + 1) * Nat.multinomial Finset.univ (incrementProfile z p).val) =
        ((p.val z + 1) * ∏ w : a, (p.val w).factorial) *
          Nat.multinomial Finset.univ (incrementProfile z p).val := by ring
    _ = (n + 1).factorial := hq
    _ = (n + 1) * n.factorial := Nat.factorial_succ n
    _ = (∏ w : a, (p.val w).factorial) *
        ((n + 1) * Nat.multinomial Finset.univ p.val) := by rw [← hp]; ring

end
end ICO.MHOccupationCounts


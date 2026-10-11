import ICO.MHOccupationCounts

/-! Counting bounds on unrestricted multiset records, including repetitions. -/

namespace ICO.MHOccupationSupport

open QIT ICO.MHOccupationCounts
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 1000000

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem incrementProfile_injective {n : ℕ} (z : a) :
    Function.Injective (incrementProfile (n := n) z) := by
  intro p q h
  apply Subtype.ext
  funext w
  have hw := congrArg (fun s : TensorPowerProfile a (n + 1) => s.val w) h
  simpa only [incrementProfile_apply, Nat.add_left_cancel_iff] using hw

theorem predecessor_weight_sum_le {n : ℕ} (z : a) (q : TensorPowerProfile a (n + 1)) :
    (∑ p : TensorPowerProfile a n,
      if q = incrementProfile z p then p.val z + 1 else 0) ≤ q.val z := by
  by_cases hex : ∃ p : TensorPowerProfile a n, q = incrementProfile z p
  · obtain ⟨p, hp⟩ := hex
    have heq : (∑ r : TensorPowerProfile a n,
        if q = incrementProfile z r then r.val z + 1 else 0) = p.val z + 1 := by
      rw [Finset.sum_eq_single p]
      · simp [hp]
      · intro r _ hr
        rw [if_neg]
        intro h
        exact hr ((incrementProfile_injective z) (h.symm.trans hp))
      · simp
    rw [heq, hp, incrementProfile_self]
  · simp only [not_exists] at hex
    simp [hex]

variable {α : Type*} [Fintype α] [DecidableEq α]

def outputMultiplicity {n : ℕ} (p : TensorPowerProfile (α × α) n) (y : α) : ℕ :=
  ∑ x, p.val (x, y)

def usedOutputs {l r : ℕ} (p : TensorPowerProfile (α × α) l)
    (q : TensorPowerProfile (α × α) r) : Finset α :=
  Finset.univ.filter fun y => 0 < outputMultiplicity p y + outputMultiplicity q y

theorem outputMultiplicity_sum {n : ℕ} (p : TensorPowerProfile (α × α) n) :
    ∑ y, outputMultiplicity p y = n := by
  unfold outputMultiplicity
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact tensorPowerTypeProfile_sum_of_mem_profiles n p.property

theorem outputMultiplicity_le {n : ℕ} (p : TensorPowerProfile (α × α) n) (y : α) :
    outputMultiplicity p y ≤ n := by
  calc
    _ ≤ ∑ z, outputMultiplicity p z :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
    _ = n := outputMultiplicity_sum p

theorem entry_le_outputMultiplicity {n : ℕ} (p : TensorPowerProfile (α × α) n) (x y : α) :
    p.val (x, y) ≤ outputMultiplicity p y := by
  unfold outputMultiplicity
  exact Finset.single_le_sum (f := fun z => p.val (z, y))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)

theorem mem_usedOutputs {l r : ℕ} (p : TensorPowerProfile (α × α) l)
    (q : TensorPowerProfile (α × α) r) (y : α) :
    y ∈ usedOutputs p q ↔ 0 < outputMultiplicity p y + outputMultiplicity q y := by
  simp [usedOutputs]

theorem usedOutputs_card_le {l r : ℕ} (p : TensorPowerProfile (α × α) l)
    (q : TensorPowerProfile (α × α) r) :
    (usedOutputs p q).card ≤ l + r := by
  calc
    (usedOutputs p q).card = ∑ _y ∈ usedOutputs p q, 1 := by simp
    _ ≤ ∑ y ∈ usedOutputs p q, (outputMultiplicity p y + outputMultiplicity q y) := by
      apply Finset.sum_le_sum
      intro y hy
      exact (mem_usedOutputs p q y).mp hy
    _ ≤ ∑ y : α, (outputMultiplicity p y + outputMultiplicity q y) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro _ _ _
      exact Nat.zero_le _
    _ = l + r := by rw [Finset.sum_add_distrib, outputMultiplicity_sum, outputMultiplicity_sum]

theorem fresh_count_zero {l r : ℕ} (p : TensorPowerProfile (α × α) l)
    (q : TensorPowerProfile (α × α) r) (x y : α) (hy : y ∉ usedOutputs p q) :
    p.val (x, y) = 0 := by
  have h := (mem_usedOutputs p q y).not.mp hy
  have hentry := entry_le_outputMultiplicity p x y
  omega

theorem predecessor_output_weight_sum_le {n : ℕ}
    (q : TensorPowerProfile (α × α) (n + 1)) (y : α) :
    (∑ x : α, ∑ p : TensorPowerProfile (α × α) n,
      if q = incrementProfile (x, y) p then p.val (x, y) + 1 else 0) ≤ n + 1 := by
  calc
    _ ≤ ∑ x : α, q.val (x, y) := Finset.sum_le_sum (fun x _ => predecessor_weight_sum_le (x, y) q)
    _ ≤ n + 1 := outputMultiplicity_le q y

theorem outputMultiplicity_increment {n : ℕ} (p : TensorPowerProfile (α × α) n)
    (x y z : α) :
    outputMultiplicity (incrementProfile (x, y) p) z =
      (if y = z then 1 else 0) + outputMultiplicity p z := by
  unfold outputMultiplicity
  simp only [incrementProfile_apply, Finset.sum_add_distrib]
  congr 1
  by_cases h : y = z
  · subst z; simp
  · simp [h]

theorem fresh_total_multiplicity {n r : ℕ} (p : TensorPowerProfile (α × α) n)
    (q : TensorPowerProfile (α × α) r) (x y : α) (hy : y ∉ usedOutputs p q) :
    outputMultiplicity (incrementProfile (x, y) p) y + outputMultiplicity q y = 1 := by
  have h := (mem_usedOutputs p q y).not.mp hy
  rw [outputMultiplicity_increment]
  simp only [ite_true]
  omega

theorem collision_total_multiplicity {n r : ℕ} (p : TensorPowerProfile (α × α) n)
    (q : TensorPowerProfile (α × α) r) (x y : α) (hy : y ∈ usedOutputs p q) :
    2 ≤ outputMultiplicity (incrementProfile (x, y) p) y + outputMultiplicity q y := by
  have h := (mem_usedOutputs p q y).mp hy
  rw [outputMultiplicity_increment]
  simp only [ite_true]
  omega

/-- A fresh output label appears exactly once after insertion, so it uniquely
determines both the removed pair and the preceding multiset. -/
theorem fresh_predecessor_unique {n r : ℕ} (q : TensorPowerProfile (α × α) r)
    (p p' : TensorPowerProfile (α × α) n) (x x' y : α)
    (hy : y ∉ usedOutputs p q) (hy' : y ∉ usedOutputs p' q)
    (h : incrementProfile (x, y) p = incrementProfile (x', y) p') :
    x = x' ∧ p = p' := by
  have hcount := congrArg (fun s : TensorPowerProfile (α × α) (n + 1) => s.val (x, y)) h
  dsimp only at hcount
  rw [incrementProfile_apply, incrementProfile_apply,
    fresh_count_zero p q x y hy, fresh_count_zero p' q x y hy'] at hcount
  simp only [ite_true, Nat.add_zero] at hcount
  have hx : x = x' := by
    by_contra hne
    have hn : (x', y) ≠ (x, y) := by intro hh; exact hne (congrArg Prod.fst hh).symm
    simp [hn] at hcount
  refine ⟨hx, ?_⟩
  subst x'
  exact incrementProfile_injective (x, y) h

end
end ICO.MHOccupationSupport

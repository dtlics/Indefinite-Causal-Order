import ICO.MHOccupationCounts

/-! Exact transposition of finite multiset occupation records. -/

namespace ICO.MHProfileTranspose

open QIT ICO.MHOccupationCounts
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 1000000

variable {α : Type*} [Fintype α] [DecidableEq α]

def profileTranspose (n : ℕ) : TensorPowerProfile (α × α) n ≃ TensorPowerProfile (α × α) n :=
  (occupationMultiset n).trans ((Sym.equivCongr (Equiv.prodComm α α)).trans (occupationMultiset n).symm)

theorem profileTranspose_multiset {n : ℕ} (p : TensorPowerProfile (α × α) n) :
    occupationMultiset n (profileTranspose n p) = (occupationMultiset n p).map Prod.swap := by
  simp [profileTranspose, Equiv.trans_apply, Sym.equivCongr]

theorem profileTranspose_count {n : ℕ} (p : TensorPowerProfile (α × α) n) (x y : α) :
    (profileTranspose n p).val (x, y) = p.val (y, x) := by
  rw [← occupationMultiset_count n (profileTranspose n p) (x, y), profileTranspose_multiset,
    Sym.coe_map]
  have h := Multiset.count_map_eq_count' Prod.swap (occupationMultiset n p : Multiset (α × α))
    (Equiv.prodComm α α).injective (y, x)
  simpa only [Prod.swap_prod_mk, occupationMultiset_count] using h

theorem profileTranspose_involutive {n : ℕ} (p : TensorPowerProfile (α × α) n) :
    profileTranspose n (profileTranspose n p) = p := by
  apply Subtype.ext
  funext z
  rcases z with ⟨x, y⟩
  rw [profileTranspose_count, profileTranspose_count]

theorem profileTranspose_increment {n : ℕ} (p : TensorPowerProfile (α × α) n) (x y : α) :
    profileTranspose (n + 1) (incrementProfile (x, y) p) =
      incrementProfile (y, x) (profileTranspose n p) := by
  apply Subtype.ext
  funext z
  rcases z with ⟨u, v⟩
  rw [profileTranspose_count, incrementProfile_apply, incrementProfile_apply, profileTranspose_count]
  simp only [Prod.mk.injEq, and_comm]

end
end ICO.MHProfileTranspose

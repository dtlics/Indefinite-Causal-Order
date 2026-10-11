import ICO.MHPermutationExtensions
import Mathlib.Data.Fintype.Perm

namespace ICO.MHPermutationFibers
open ICO.PathRecordingSupport ICO.MHPermutationExtensions
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 700000

theorem compatible_swap (R : Relation A A) (y z : A)
    (hy : FreshRight y R) (hz : FreshRight z R)
    (π : Equiv.Perm A) (hπ : Compatible π R) :
    Compatible (π.trans (Equiv.swap y z)) R := by
  intro e he
  rcases e with ⟨a,b⟩
  have hey : b≠y := by intro h; subst b; exact hy a he
  have hez : b≠z := by intro h; subst b; exact hz a he
  simp only [Equiv.trans_apply,hπ (a,b) he,Equiv.swap_apply_of_ne_of_ne hey hez]

def swapFiber (R : Relation A A) (x y z : A)
    (hy : FreshRight y R) (hz : FreshRight z R) :
    ↥(completions (insert (x,y) R)) ≃ ↥(completions (insert (x,z) R)) where
  toFun π := ⟨π.val.trans (Equiv.swap y z),by
    have hπ := (compatible_insert_iff π.val R x y).mp ((mem_completions _ _).mp π.property)
    apply (mem_completions _ _).mpr
    apply (compatible_insert_iff _ R x z).mpr
    exact ⟨by simp [Equiv.trans_apply,hπ.1],compatible_swap R y z hy hz π.val hπ.2⟩⟩
  invFun π := ⟨π.val.trans (Equiv.swap y z),by
    have hπ := (compatible_insert_iff π.val R x z).mp ((mem_completions _ _).mp π.property)
    apply (mem_completions _ _).mpr
    apply (compatible_insert_iff _ R x y).mpr
    exact ⟨by simp [Equiv.trans_apply,hπ.1],compatible_swap R y z hy hz π.val hπ.2⟩⟩
  left_inv π := by
    apply Subtype.ext
    ext a
    simp [Equiv.trans_apply]
  right_inv π := by
    apply Subtype.ext
    ext a
    simp [Equiv.trans_apply]

/-- Every fresh output has exactly the same number of permutation completions;
the equality follows from an explicit involution on actual permutations. -/
theorem completion_fibers_equal (R : Relation A A) (x y z : A)
    (hy : FreshRight y R) (hz : FreshRight z R) :
    (completions (insert (x,y) R)).card=(completions (insert (x,z) R)).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (swapFiber R x y z hy hz)

#print axioms completion_fibers_equal
end
end ICO.MHPermutationFibers

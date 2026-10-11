import ICO.MHCompletionCounting
import ICO.MHTernaryCompression

namespace ICO.MHRecordExtension
open Matrix ICO.PathRecordingSupport ICO.MHPermutationExtensions
  ICO.MHTernaryProfile ICO.MHTernaryCompression ICO.MHCompletionCounting
open scoped BigOperators
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 800000

theorem profile_insert_left (L R : Relation A A) (x y : A)
    (hx : FreshLeft x (L∪R)) :
    profile (insert (x,y) L) R = profile L R + Pi.single x (1 : ZMod 3) := by
  classical
  have hL : ¬ Source L x := by rintro ⟨z,hz⟩; exact hx z (Finset.mem_union_left R hz)
  have hR : ¬ Source R x := by rintro ⟨z,hz⟩; exact hx z (Finset.mem_union_right L hz)
  funext a
  by_cases ha : a=x
  · subst a
    have hi : Source (insert (x,y) L) x := ⟨y,Finset.mem_insert_self _ _⟩
    simp [profile,hi,hL,hR]
  · have hi : Source (insert (x,y) L) a ↔ Source L a := by
      simp only [Source,Finset.mem_insert,Prod.mk.injEq]
      constructor
      · rintro ⟨z,⟨he,hz⟩|hz⟩
        · exact (ha he).elim
        · exact ⟨z,hz⟩
      · rintro ⟨z,hz⟩; exact ⟨z,Or.inr hz⟩
    simp [profile,hi,Pi.single_eq_of_ne ha]

theorem profile_insert_right (L R : Relation A A) (x y : A)
    (hx : FreshLeft x (L∪R)) :
    profile L (insert (x,y) R) = profile L R - Pi.single x (1 : ZMod 3) := by
  classical
  have hL : ¬ Source L x := by rintro ⟨z,hz⟩; exact hx z (Finset.mem_union_left R hz)
  have hR : ¬ Source R x := by rintro ⟨z,hz⟩; exact hx z (Finset.mem_union_right L hz)
  funext a
  by_cases ha : a=x
  · subst a
    have hi : Source (insert (x,y) R) x := ⟨y,Finset.mem_insert_self _ _⟩
    simp [profile,hi,hL,hR,show (2:ZMod 3) = -1 by decide]
  · have hi : Source (insert (x,y) R) a ↔ Source R a := by
      simp only [Source,Finset.mem_insert,Prod.mk.injEq]
      constructor
      · rintro ⟨z,⟨he,hz⟩|hz⟩
        · exact (ha he).elim
        · exact ⟨z,hz⟩
      · rintro ⟨z,hz⟩; exact ⟨z,Or.inr hz⟩
    simp [profile,hi,Pi.single_eq_of_ne ha]

def leftExtend (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) : Record A :=
  ⟨(insert (x,y) R.val.1,R.val.2),by
    constructor
    · exact Finset.disjoint_insert_left.mpr ⟨fun he => hx y (Finset.mem_union_right _ he),R.property.1⟩
    · rw [Finset.insert_union]
      exact ⟨leftUnique_insert R.property.2.1 hx,rightUnique_insert R.property.2.2 hy⟩⟩

def rightExtend (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) : Record A :=
  ⟨(R.val.1,insert (x,y) R.val.2),by
    constructor
    · exact Finset.disjoint_insert_right.mpr ⟨fun he => hx y (Finset.mem_union_left _ he),R.property.1⟩
    · rw [Finset.union_insert]
      exact ⟨leftUnique_insert R.property.2.1 hx,rightUnique_insert R.property.2.2 hy⟩⟩

theorem count_leftExtend (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) :
    count R=(Fintype.card A-(R.val.1∪R.val.2).card)*count (leftExtend R x y hx hy) := by
  simpa only [count,leftExtend,Finset.insert_union] using
    completions_recursion (R.val.1∪R.val.2) R.property.2.2 x y hx hy

theorem amplitude_leftExtend (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) :
    amplitude R = (((Real.sqrt ((Fintype.card A-(R.val.1∪R.val.2).card : Nat) : ℝ))⁻¹ : ℝ) : ℂ) *
      amplitude (leftExtend R x y hx hy) := by
  unfold amplitude
  rw [count_leftExtend R x y hx hy,Nat.cast_mul,Real.sqrt_mul (by positivity),_root_.mul_inv_rev]
  push_cast
  ring

theorem count_rightExtend (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) :
    count R=(Fintype.card A-(R.val.1∪R.val.2).card)*count (rightExtend R x y hx hy) := by
  simpa only [count,rightExtend,Finset.union_insert] using
    completions_recursion (R.val.1∪R.val.2) R.property.2.2 x y hx hy

theorem amplitude_rightExtend (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) :
    amplitude R = (((Real.sqrt ((Fintype.card A-(R.val.1∪R.val.2).card : Nat) : ℝ))⁻¹ : ℝ) : ℂ) *
      amplitude (rightExtend R x y hx hy) := by
  unfold amplitude
  rw [count_rightExtend R x y hx hy,Nat.cast_mul,Real.sqrt_mul (by positivity),_root_.mul_inv_rev]
  push_cast
  ring

#print axioms amplitude_leftExtend
end
end ICO.MHRecordExtension

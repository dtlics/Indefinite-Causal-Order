import ICO.MHPermutationFibers

namespace ICO.MHCompletionCounting
open ICO.PathRecordingSupport ICO.MHPermutationExtensions ICO.MHPermutationFibers
open scoped BigOperators
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 700000

def freshOutputs (R : Relation A A) : Finset A := by
  classical
  exact Finset.univ.filter (fun y => FreshRight y R)

@[simp] theorem mem_freshOutputs (R : Relation A A) (y : A) :
    y∈freshOutputs R ↔ FreshRight y R := by
  classical
  simp [freshOutputs]

def completionPartition (R : Relation A A) (x : A) (hx : FreshLeft x R) :
    ↥(completions R) ≃ ((y : ↥(freshOutputs R)) × ↥(completions (insert (x,y.val) R))) where
  toFun π := by
    have hp : Compatible π.val R := (mem_completions _ _).mp π.property
    refine ⟨⟨π.val x,(mem_freshOutputs _ _).mpr (compatible_fresh_image π.val R hp x hx)⟩,
      ⟨π.val,?_⟩⟩
    exact (mem_completions _ _).mpr ((compatible_insert_iff _ _ _ _).mpr ⟨rfl,hp⟩)
  invFun p := ⟨p.2.val,(mem_completions _ _).mpr
    (((compatible_insert_iff _ _ _ _).mp ((mem_completions _ _).mp p.2.property)).2)⟩
  left_inv π := by apply Subtype.ext; rfl
  right_inv p := by
    rcases p with ⟨⟨y,hy⟩,⟨π,hπ⟩⟩
    have he : π x=y := ((compatible_insert_iff _ _ _ _).mp ((mem_completions _ _).mp hπ)).1
    subst y
    rfl

theorem completions_partition_card (R : Relation A A) (x : A) (hx : FreshLeft x R) :
    (completions R).card = ∑ y : ↥(freshOutputs R),(completions (insert (x,y.val) R)).card := by
  simpa only [Fintype.card_sigma,Fintype.card_coe] using Fintype.card_congr (completionPartition R x hx)

theorem completions_balanced_count (R : Relation A A) (x y : A)
    (hx : FreshLeft x R) (hy : FreshRight y R) :
    (completions R).card = (freshOutputs R).card*(completions (insert (x,y) R)).card := by
  rw [completions_partition_card R x hx]
  have h (z : ↥(freshOutputs R)) : (completions (insert (x,z.val) R)).card=
      (completions (insert (x,y) R)).card :=
    completion_fibers_equal R x z.val y ((mem_freshOutputs _ _).mp z.property) hy
  simp_rw [h]
  simp

theorem freshOutputs_card (R : Relation A A) (hR : RightUnique R) :
    (freshOutputs R).card=Fintype.card A-R.card := by
  classical
  have he : freshOutputs R = Finset.univ \ R.image Prod.snd := by
    ext y
    simp only [mem_freshOutputs,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro hf he
      obtain ⟨⟨a,b⟩,hab,hb⟩ := he
      change b=y at hb
      subst b
      exact hf a hab
    · intro hn a ha
      exact hn ⟨(a,y),ha,rfl⟩
  have hi : Set.InjOn Prod.snd (R : Set (A × A)) := by
    intro e he f hf hh
    rcases e with ⟨a,b⟩
    rcases f with ⟨c,d⟩
    change b=d at hh
    subst d
    exact Prod.ext (hR he hf) rfl
  rw [he,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,
    Finset.card_image_of_injOn hi]

/-- Exact conditional normalization for a fresh query, derived by an explicit
partition and permutation bijections. This is the factor appearing in W. -/
theorem completions_recursion (R : Relation A A) (hR : RightUnique R) (x y : A)
    (hx : FreshLeft x R) (hy : FreshRight y R) :
    (completions R).card = (Fintype.card A-R.card)*(completions (insert (x,y) R)).card := by
  rw [completions_balanced_count R x y hx hy,freshOutputs_card R hR]

#print axioms completions_recursion
end
end ICO.MHCompletionCounting

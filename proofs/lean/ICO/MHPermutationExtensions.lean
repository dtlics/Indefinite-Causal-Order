import ICO.PathRecordingSupport
import Mathlib.Logic.Equiv.Fintype

/-! Concrete permutation completions of the bijective records used by the
phase/permutation purification. No completion or counting fact is assumed. -/
namespace ICO.MHPermutationExtensions
open ICO.PathRecordingSupport
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 500000

def Compatible (π : Equiv.Perm A) (R : Relation A A) : Prop :=
  ∀ e∈R,π e.1=e.2

theorem exists_compatible (R : Relation A A) (hL : LeftUnique R) (hR : RightUnique R) :
    ∃ π : Equiv.Perm A,Compatible π R := by
  have hf : Function.Injective (fun e : ↥R => e.val.1) := by
    intro e f h
    apply Subtype.ext
    apply Prod.ext h
    exact hL e.property (by simpa [h] using f.property)
  have hg : Function.Injective (fun e : ↥R => e.val.2) := by
    intro e f h
    apply Subtype.ext
    apply Prod.ext _ h
    exact hR e.property (by simpa [h] using f.property)
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun e : ↥R => e.val.1) (fun e : ↥R => e.val.2) hf hg
  exact ⟨π,fun e he => hπ ⟨e,he⟩⟩

theorem compatible_insert_iff (π : Equiv.Perm A) (R : Relation A A) (x y : A) :
    Compatible π (insert (x,y) R) ↔ π x=y ∧ Compatible π R := by
  simp only [Compatible,Finset.forall_mem_insert,Prod.fst,Prod.snd]

theorem compatible_fresh_image (π : Equiv.Perm A) (R : Relation A A)
    (h : Compatible π R) (x : A) (hx : FreshLeft x R) : FreshRight (π x) R := by
  intro a ha
  have he : π a=π x := h (a,π x) ha
  have : a=x := π.injective he
  subst a
  exact hx (π x) ha

def completions (R : Relation A A) : Finset (Equiv.Perm A) := by
  classical
  exact Finset.univ.filter (fun π => Compatible π R)

@[simp] theorem mem_completions (R : Relation A A) (π : Equiv.Perm A) :
    π∈completions R ↔ Compatible π R := by
  classical
  simp [completions]

theorem completions_nonempty (R : Relation A A) (hL : LeftUnique R) (hR : RightUnique R) :
    (completions R).Nonempty := by
  obtain ⟨π,h⟩ := exists_compatible R hL hR
  exact ⟨π,(mem_completions R π).mpr h⟩

theorem completions_card_pos (R : Relation A A) (hL : LeftUnique R) (hR : RightUnique R) :
    0<(completions R).card := Finset.card_pos.mpr (completions_nonempty R hL hR)

#print axioms exists_compatible
end
end ICO.MHPermutationExtensions

import ICO.MHPermutationExtensions
import Mathlib.Data.ZMod.Basic

/-! Ternary Fourier labels distinguish forward and inverse bijective records.
The profile is actual data, not an assumed orthogonality certificate. -/
namespace ICO.MHTernaryProfile
open ICO.PathRecordingSupport ICO.MHPermutationExtensions
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 600000

def Source (L : Relation A A) (x : A) : Prop := ∃ y,(x,y)∈L

def profile (L R : Relation A A) (x : A) : ZMod 3 := by
  classical
  exact if Source L x then 1 else if Source R x then 2 else 0

theorem sources_disjoint (L R : Relation A A) (hd : Disjoint L R)
    (hu : LeftUnique (L ∪ R)) (x : A) : ¬(Source L x ∧ Source R x) := by
  rintro ⟨⟨y,hy⟩,⟨z,hz⟩⟩
  have he : y=z := hu (Finset.mem_union_left R hy) (Finset.mem_union_right L hz)
  subst z
  exact Finset.disjoint_left.mp hd hy hz

theorem profile_eq_one (L R : Relation A A) (x : A) : profile L R x=1 ↔ Source L x := by
  classical
  by_cases hL : Source L x <;> by_cases hR : Source R x <;>
    simp [profile,hL,hR,show (2:ZMod 3)≠1 by decide]

theorem profile_eq_two (L R : Relation A A) (hd : Disjoint L R)
    (hu : LeftUnique (L ∪ R)) (x : A) : profile L R x=2 ↔ Source R x := by
  classical
  have h := sources_disjoint L R hd hu x
  by_cases hL : Source L x <;> by_cases hR : Source R x <;>
    simp_all [profile,show (1:ZMod 3)≠2 by decide,show (0:ZMod 3)≠2 by decide]

theorem compatible_source_ext (π : Equiv.Perm A) (L K : Relation A A)
    (hL : Compatible π L) (hK : Compatible π K)
    (hs : ∀ x,Source L x ↔ Source K x) : L=K := by
  apply Finset.ext
  intro e
  rcases e with ⟨x,y⟩
  constructor
  · intro he
    obtain ⟨z,hz⟩ := (hs x).mp ⟨y,he⟩
    have hy : π x=y := hL (x,y) he
    have hzz : π x=z := hK (x,z) hz
    simpa [← hy,← hzz] using hz
  · intro he
    obtain ⟨z,hz⟩ := (hs x).mpr ⟨y,he⟩
    have hy : π x=y := hK (x,y) he
    have hzz : π x=z := hL (x,z) hz
    simpa [← hy,← hzz] using hz

/-- Distinct admissible record pairs have disjoint support in the joint
permutation and ternary-Fourier-label basis. -/
theorem profile_injective_on_compatible (π : Equiv.Perm A) (L R K S : Relation A A)
    (hdLR : Disjoint L R) (huLR : LeftUnique (L ∪ R))
    (hdKS : Disjoint K S) (huKS : LeftUnique (K ∪ S))
    (hpLR : Compatible π (L ∪ R)) (hpKS : Compatible π (K ∪ S))
    (he : profile L R=profile K S) : L=K ∧ R=S := by
  have hL : Compatible π L := fun e h => hpLR e (Finset.mem_union_left R h)
  have hR : Compatible π R := fun e h => hpLR e (Finset.mem_union_right L h)
  have hK : Compatible π K := fun e h => hpKS e (Finset.mem_union_left S h)
  have hS : Compatible π S := fun e h => hpKS e (Finset.mem_union_right K h)
  constructor
  · apply compatible_source_ext π L K hL hK
    intro x
    rw [← profile_eq_one L R x,← profile_eq_one K S x,he]
  · apply compatible_source_ext π R S hR hS
    intro x
    rw [← profile_eq_two L R hdLR huLR x,← profile_eq_two K S hdKS huKS x,he]

#print axioms profile_injective_on_compatible
end
end ICO.MHTernaryProfile

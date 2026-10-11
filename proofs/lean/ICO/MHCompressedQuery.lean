import ICO.MHRecordExtension
import ICO.MHPurifiedOracle

namespace ICO.MHCompressedQuery
open Matrix ICO.PathRecordingSupport ICO.MHPermutationExtensions
  ICO.MHTernaryProfile ICO.MHTernaryCompression ICO.MHRecordExtension ICO.MHPurifiedOracle
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 900000

def queryState (x : A) (R : Record A) : A × Environment A → ℂ := by
  classical
  exact fun o => if o.1=x then state R o.2 else 0

def stepCoefficient (R : Record A) : ℂ :=
  (((Real.sqrt ((Fintype.card A-(R.val.1∪R.val.2).card : Nat) : ℝ))⁻¹ : ℝ) : ℂ)

theorem supports_leftExtend (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) (π : Equiv.Perm A) (z : A → ZMod 3) :
    supports (leftExtend R x y hx hy) (π,z) ↔
      supports R (π,z-Pi.single x 1) ∧ π x=y := by
  change (Compatible π (insert (x,y) R.val.1 ∪ R.val.2) ∧
    z=profile (insert (x,y) R.val.1) R.val.2) ↔
      (Compatible π (R.val.1∪R.val.2) ∧ z-Pi.single x 1=profile R.val.1 R.val.2) ∧ π x=y
  rw [Finset.insert_union,compatible_insert_iff,profile_insert_left _ _ x y hx]
  constructor
  · rintro ⟨⟨hxy,hπ⟩,hz⟩
    exact ⟨⟨hπ,sub_eq_iff_eq_add.mpr hz⟩,hxy⟩
  · rintro ⟨⟨hπ,hz⟩,hxy⟩
    exact ⟨⟨hxy,hπ⟩,sub_eq_iff_eq_add.mp hz⟩

theorem fresh_component (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) (π : Equiv.Perm A) (z : A → ZMod 3) :
    (if π x=y then state R (π,z-Pi.single x 1) else 0) =
      stepCoefficient R * state (leftExtend R x y hx hy) (π,z) := by
  classical
  by_cases hs : supports (leftExtend R x y hx hy) (π,z)
  · obtain ⟨hp,hxy⟩ := (supports_leftExtend R x y hx hy π z).mp hs
    simp [state,hs,hp,hxy,stepCoefficient,amplitude_leftExtend R x y hx hy]
  · have hn := mt (supports_leftExtend R x y hx hy π z).mpr hs
    by_cases hxy : π x=y
    · have hp : ¬supports R (π,z-Pi.single x 1) := by intro hp; exact hn ⟨hp,hxy⟩
      simp [state,hs,hp,hxy]
    · simp [state,hs,hxy]

/-- The actual permutation-frequency oracle maps a fresh record basis vector
onto the normalized fresh left-insertion superposition, pointwise. -/
theorem query_fresh_entry (R : Record A) (x : A)
    (hx : FreshLeft x (R.val.1∪R.val.2)) (y : A) (e : Environment A) :
    (queryMatrix *ᵥ queryState x R) (y,e) =
      if hy : FreshRight y (R.val.1∪R.val.2) then
        stepCoefficient R * state (leftExtend R x y hx hy) e else 0 := by
  classical
  rcases e with ⟨π,z⟩
  rw [queryMatrix_mulVec]
  change (if π.symm y=x then state R (π,z-Pi.single (π.symm y) 1) else 0)=_
  by_cases hy : FreshRight y (R.val.1∪R.val.2)
  · rw [dif_pos hy]
    have he : (if π.symm y=x then state R (π,z-Pi.single (π.symm y) 1) else 0)=
        if π x=y then state R (π,z-Pi.single x 1) else 0 := by
      by_cases hxy : π x=y
      · have hi : π.symm y=x := by rw [←hxy]; simp
        simp [hxy,hi]
      · have hi : π.symm y≠x := by intro h; exact hxy (by rw [←h]; simp)
        simp [hxy,hi]
    rw [he]
    exact fresh_component R x y hx hy π z
  · rw [dif_neg hy]
    by_cases hxy : π.symm y=x
    · rw [if_pos hxy]
      have hp : ¬supports R (π,z-Pi.single (π.symm y) 1) := by
        intro hp
        apply hy
        have hi : π x=y := by rw [←hxy]; simp
        rw [←hi]
        exact compatible_fresh_image π _ hp.1 x hx
      simp [state,hp]
    · simp [hxy]

theorem supports_rightExtend (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) (π : Equiv.Perm A) (z : A → ZMod 3) :
    supports (rightExtend R x y hx hy) (π,z) ↔
      supports R (π,z+Pi.single x 1) ∧ π x=y := by
  change (Compatible π (R.val.1 ∪ insert (x,y) R.val.2) ∧
    z=profile R.val.1 (insert (x,y) R.val.2)) ↔
      (Compatible π (R.val.1∪R.val.2) ∧ z+Pi.single x 1=profile R.val.1 R.val.2) ∧ π x=y
  rw [Finset.union_insert,compatible_insert_iff,profile_insert_right _ _ x y hx]
  constructor
  · rintro ⟨⟨hxy,hπ⟩,hz⟩
    exact ⟨⟨hπ,eq_sub_iff_add_eq.mp hz⟩,hxy⟩
  · rintro ⟨⟨hπ,hz⟩,hxy⟩
    exact ⟨⟨hxy,hπ⟩,eq_sub_iff_add_eq.mpr hz⟩

theorem fresh_inverse_component (R : Record A) (x y : A)
    (hx : FreshLeft x (R.val.1∪R.val.2))
    (hy : FreshRight y (R.val.1∪R.val.2)) (π : Equiv.Perm A) (z : A → ZMod 3) :
    (if π x=y then state R (π,z+Pi.single x 1) else 0) =
      stepCoefficient R * state (rightExtend R x y hx hy) (π,z) := by
  classical
  by_cases hs : supports (rightExtend R x y hx hy) (π,z)
  · obtain ⟨hp,hxy⟩ := (supports_rightExtend R x y hx hy π z).mp hs
    simp [state,hs,hp,hxy,stepCoefficient,amplitude_rightExtend R x y hx hy]
  · have hn := mt (supports_rightExtend R x y hx hy π z).mpr hs
    by_cases hxy : π x=y
    · have hp : ¬supports R (π,z+Pi.single x 1) := by intro hp; exact hn ⟨hp,hxy⟩
      simp [state,hs,hp,hxy]
    · simp [state,hs,hxy]

/-- The inverse purified oracle realizes fresh right insertion exactly. -/
theorem inverse_query_fresh_entry (R : Record A) (y : A)
    (hy : FreshRight y (R.val.1∪R.val.2)) (x : A) (e : Environment A) :
    (queryMatrix.conjTranspose *ᵥ queryState y R) (x,e) =
      if hx : FreshLeft x (R.val.1∪R.val.2) then
        stepCoefficient R * state (rightExtend R x y hx hy) e else 0 := by
  classical
  rcases e with ⟨π,z⟩
  rw [queryMatrix_conjTranspose_mulVec]
  change (if π x=y then state R (π,z+Pi.single x 1) else 0)=_
  by_cases hx : FreshLeft x (R.val.1∪R.val.2)
  · rw [dif_pos hx]
    exact fresh_inverse_component R x y hx hy π z
  · rw [dif_neg hx]
    by_cases hxy : π x=y
    · rw [if_pos hxy]
      have hp : ¬supports R (π,z+Pi.single x 1) := by
        intro hp
        apply hx
        intro a ha
        have he : π x=a := hp.1 (x,a) ha
        have hh : a=y := he.symm.trans hxy
        subst a
        exact hy x (by simpa only [hxy] using ha)
      simp [state,hp]
    · simp [hxy]

#print axioms query_fresh_entry
end
end ICO.MHCompressedQuery

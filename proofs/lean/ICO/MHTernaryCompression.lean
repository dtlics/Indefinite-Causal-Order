import ICO.MHTernaryProfile
import Mathlib.Data.Fintype.Perm

/-! Explicit orthonormal purification states in the permutation/ternary-Fourier
basis. Their coefficients are computed from the actual completion set. -/
namespace ICO.MHTernaryCompression
open Matrix ICO.PathRecordingSupport ICO.MHPermutationExtensions ICO.MHTernaryProfile
open scoped BigOperators
noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]
set_option maxHeartbeats 1000000

def Valid (p : Relation A A × Relation A A) : Prop :=
  Disjoint p.1 p.2 ∧ LeftUnique (p.1 ∪ p.2) ∧ RightUnique (p.1 ∪ p.2)

abbrev Record (A : Type*) [DecidableEq A] :=
  {p : Relation A A × Relation A A // Valid p}

abbrev Environment (A : Type*) := Equiv.Perm A × (A → ZMod 3)

def count (R : Record A) : Nat := (completions (R.val.1 ∪ R.val.2)).card
def amplitude (R : Record A) : ℂ := ((Real.sqrt (count R : ℝ))⁻¹ : ℝ)

def supports (R : Record A) (e : Environment A) : Prop :=
  Compatible e.1 (R.val.1 ∪ R.val.2) ∧ e.2=profile R.val.1 R.val.2

def state (R : Record A) (e : Environment A) : ℂ := by
  classical
  exact if supports R e then amplitude R else 0

theorem count_pos (R : Record A) : 0<count R :=
  completions_card_pos _ R.property.2.1 R.property.2.2

theorem amplitude_square (R : Record A) : star (amplitude R)*amplitude R=(count R : ℂ)⁻¹ := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤count R by positivity)
  have hr : (Real.sqrt (count R : ℝ))⁻¹*(Real.sqrt (count R : ℝ))⁻¹=(count R : ℝ)⁻¹ := by
    rw [← pow_two,inv_pow,hs]
  simpa [amplitude] using congrArg (fun x : ℝ => (x : ℂ)) hr

theorem support_unique (R S : Record A) (e : Environment A)
    (hR : supports R e) (hS : supports S e) : R=S := by
  apply Subtype.ext
  apply Prod.ext
  · exact (profile_injective_on_compatible e.1 R.val.1 R.val.2 S.val.1 S.val.2
      R.property.1 R.property.2.1 S.property.1 S.property.2.1 hR.1 hS.1
      (hR.2.symm.trans hS.2)).1
  · exact (profile_injective_on_compatible e.1 R.val.1 R.val.2 S.val.1 S.val.2
      R.property.1 R.property.2.1 S.property.1 S.property.2.1 hR.1 hS.1
      (hR.2.symm.trans hS.2)).2

theorem state_norm (R : Record A) : (∑ e : Environment A,star (state R e)*state R e)=1 := by
  classical
  have hc : (count R : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt (count_pos R))
  have hterm (e : Environment A) : star (state R e)*state R e =
      if Compatible e.1 (R.val.1 ∪ R.val.2) ∧ e.2=profile R.val.1 R.val.2
      then star (amplitude R)*amplitude R else 0 := by
    by_cases he : supports R e
    · have hh : Compatible e.1 (R.val.1 ∪ R.val.2) ∧ e.2=profile R.val.1 R.val.2 := he
      simp [state,he,hh]
    · have hh : ¬ (Compatible e.1 (R.val.1 ∪ R.val.2) ∧ e.2=profile R.val.1 R.val.2) := he
      simp [state,he,hh]
  simp_rw [hterm]
  simp only [Fintype.sum_prod_type]
  rw [amplitude_square]
  have hinner (π : Equiv.Perm A) :
      (∑ z : A → ZMod 3,if Compatible π (R.val.1 ∪ R.val.2) ∧ z=profile R.val.1 R.val.2
        then (count R : ℂ)⁻¹ else 0) =
        if Compatible π (R.val.1 ∪ R.val.2) then (count R : ℂ)⁻¹ else 0 := by
    by_cases hp : Compatible π (R.val.1 ∪ R.val.2) <;> simp [hp]
  trans (∑ π : Equiv.Perm A,if Compatible π (R.val.1 ∪ R.val.2)
    then (count R : ℂ)⁻¹ else 0)
  · apply Finset.sum_congr rfl
    intro π hπ
    exact hinner π
  simp only [← Finset.sum_filter]
  change (∑ _π∈completions (R.val.1 ∪ R.val.2),(count R : ℂ)⁻¹)=1
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_inv_cancel₀ hc

theorem state_orthonormal (R S : Record A) :
    (∑ e : Environment A,star (state R e)*state S e)=if R=S then 1 else 0 := by
  classical
  by_cases h : R=S
  · subst S
    simpa using state_norm R
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro e he
    by_cases hR : supports R e
    · have hS : ¬ supports S e := fun hS => h (support_unique R S e hR hS)
      simp [state,hS]
    · simp [state,hR]

instance finiteRecord : Finite (Record A) := inferInstanceAs (Finite {p : Relation A A × Relation A A // Valid p})

noncomputable instance fintypeRecord : Fintype (Record A) := Fintype.ofFinite _

def decompression : Matrix (Environment A) (Record A) ℂ := fun e R => state R e
def compression : Matrix (Record A) (Environment A) ℂ := decompression.conjTranspose

/-- The record purification is an actual finite matrix isometry. Its adjoint
compresses each admissible record state back to the corresponding basis vector. -/
theorem decompression_isometry :
    (decompression (A:=A)).conjTranspose * decompression (A:=A) =
      (1 : Matrix (Record A) (Record A) ℂ) := by
  classical
  ext R S
  simpa only [decompression,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply]
    using state_orthonormal R S

theorem compression_decompression : compression (A:=A) * decompression (A:=A) = (1 : Matrix (Record A) (Record A) ℂ) :=
  decompression_isometry

#print axioms state_orthonormal
#print axioms decompression_isometry
end
end ICO.MHTernaryCompression

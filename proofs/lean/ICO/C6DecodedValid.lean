import ICO.C6DecodedHistory

/-! The literal decoded trajectory cannot produce a birth in an inactive
residual mode. Its nonzero branches therefore carry orthonormal modes. -/
namespace ICO.C6DecodedValid
open QIT Matrix ICO.C6DecodedHistory ICO.C6AcceptedBirthFactor
  ICO.C6ActualAcceptedModes ICO.C6AcceptedModes ICO.C6FlagCount
  ICO.RecordingPurifiedProtocol ICO.C6ActualResidualWeight
noncomputable section
set_option maxHeartbeats 1400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ : ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem actual_valid (H : Matrix.unitaryGroup A ℂ)
    (K : ∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z : ImageCache (A:=A) 0 (Bool×μ 0)→ℂ) (n : ℕ)
    (η : History (A×Bool) n) (κ : History Bool n)
    (hv : run H K z n η κ≠0) : Valid (rightVectors H n η) κ := by
  induction n with
  | zero=>intro i; exact i.elim0
  | succ n ih=>
    rcases η with ⟨⟨j,b⟩,η⟩
    rcases κ with ⟨f,κ⟩
    have hp : run H K z n η κ≠0 := by
      intro hh
      exact hv (by rw [run_succ,hh,Matrix.mulVec_zero])
    rw [rightVectors_snoc,valid_snoc]
    refine ⟨ih η κ hp, ?_⟩
    intro hf hh
    subst f
    have hr : nextResidual H n η b j=0 := by
      simpa only [nextResidual,rightVectors_snoc] using hh
    have ha : birthAmplitude H n η b j=0 := by simp only [birthAmplitude,hr,norm_zero,
      Complex.ofReal_zero,zero_div]
    apply hv
    have hz : core (M:=Bool×μ n) (outcomeBasis H b) j
        (birthAmplitude H n η b j) (flagCount n κ) true = 0 := by
      simp only [core_true, ha, zero_smul]
      rfl
    have hs : stage H K n η κ j b true = 0 := by
      change knownImages (flagCount n κ+if true then 1 else 0) (ICO.C6RawFlagSlices.smallKnown (K n)) *
        core (M:=Bool×μ n) (outcomeBasis H b) j
          (birthAmplitude H n η b j) (flagCount n κ) true *
        choiceImages (flagCount n κ) b = 0
      rw [hz, Matrix.mul_zero]
      erw [Matrix.zero_mul]
      rfl
    rw [run_succ, hs, Matrix.zero_mulVec]

theorem invalid_zero (H : Matrix.unitaryGroup A ℂ)
    (K : ∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z : ImageCache (A:=A) 0 (Bool×μ 0)→ℂ) (n : ℕ)
    (η : History (A×Bool) n) (κ : History Bool n)
    (hv : ¬Valid (rightVectors H n η) κ) : run H K z n η κ=0 := by
  by_contra hh
  exact hv (actual_valid H K z n η κ hh)

theorem actual_modes_orthonormal (H : Matrix.unitaryGroup A ℂ)
    (K : ∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z : ImageCache (A:=A) 0 (Bool×μ 0)→ℂ) (n : ℕ)
    (η : History (A×Bool) n) (κ : History Bool n)
    (hv : run H K z n η κ≠0) : Orthonormal ℂ (modes (rightVectors H n η) κ) :=
  modes_orthonormal _ _ (actual_valid H K z n η κ hv)

#print axioms invalid_zero
#print axioms actual_modes_orthonormal
end
end ICO.C6DecodedValid

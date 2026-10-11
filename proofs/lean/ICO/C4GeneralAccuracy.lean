import ICO.C4SwitchTheorem

/-! The full fixed-accuracy range of the physical C4 theorem. -/
namespace ICO.C4PhysicalEnsemble
open Matrix QIT
noncomputable section
set_option maxHeartbeats 800000
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

theorem fixed_accuracy_fourth_power {ε : ℝ} (hε : ε < 1/2)
    {k q : ℕ} (hk : 0 < k) (hgap : 2 ≤ (1/2-ε)*(k : ℝ))
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A)
    (hdim : 52*(k : ℝ)^2 ≤ 3*(1/2-ε)*Fintype.card A)
    (haccurate : ∀ r (UV : Sample A r),
      (switchTarget UV).normalizedTraceDistance (ordinary tree UV) ≤ ε) :
    3*(1/2-ε)*Fintype.card A < 52*(k : ℝ)^2*(q : ℝ)^4 := by
  have hd : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hδ : (0 : ℝ) < 1/2-ε := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  by_cases hq : q = 0
  · subst q
    obtain ⟨UV, hUV⟩ := exists_switch_error_bound (r := 0) tree
    have hacc := haccurate 0 UV
    norm_num at hUV ⊢
    change (1/2 : ℝ) * traceNorm ((switchTarget UV).matrix - (ordinary tree UV).matrix) ≤ ε at hacc
    have hgram : (13 : ℝ)/(3*Fintype.card A) ≤ (1/2-ε)/4 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [sq_nonneg ((k : ℝ)-1)]
    linarith
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let r := k*q^2-1
    have hsize : r+1 = k*q^2 := by
      dsimp [r]
      have : 0 < k*q^2 := Nat.mul_pos hk (pow_pos hqpos 2)
      omega
    have hr : (r : ℝ)+1 = k*(q : ℝ)^2 := by exact_mod_cast hsize
    have hn : (((r+1)*(r+1) : ℕ) : ℝ) = (k : ℝ)^2*(q : ℝ)^4 := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hr]
      ring
    have hqp : (0 : ℝ) < q := by exact_mod_cast hqpos
    by_contra hlarge
    have hlarge' : 52*(k : ℝ)^2*(q : ℝ)^4 ≤ 3*(1/2-ε)*Fintype.card A :=
      le_of_not_gt hlarge
    obtain ⟨UV, hUV⟩ := exists_switch_error_bound (r := r) tree
    have hacc := haccurate r UV
    have hgram : 13 * (((r+1)*(r+1) : ℕ) : ℝ)/(3*Fintype.card A) ≤ (1/2-ε)/4 := by
      rw [hn]
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    have hcollision : (q : ℝ)*(q-1)/(2*(r+1)) ≤ (1/2-ε)/4 := by
      rw [hr]
      apply (div_le_iff₀ (by positivity)).2
      have := mul_le_mul_of_nonneg_right hgap (sq_nonneg (q : ℝ))
      nlinarith
    linarith

/-- For every fixed accuracy below one half, a positive dimension-independent
constant bounds the fourth power of the required total query budget. -/
theorem exists_fixed_accuracy_constant (ε : ℝ) (hε : ε < 1/2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
        [Fintype M] [DecidableEq M] [Nonempty M] {q : ℕ}
        (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A),
        C ≤ Fintype.card A →
        (∀ r (UV : Sample A r),
          (switchTarget UV).normalizedTraceDistance (ordinary tree UV) ≤ ε) →
        (Fintype.card A : ℝ) < C*(q : ℝ)^4 := by
  have hδ : (0 : ℝ) < 1/2-ε := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (2/(1/2-ε))
  have hkn : 0 < k := by
    have hp : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast hp
  have hgap : 2 ≤ (1/2-ε)*(k : ℝ) := by
    have := (div_lt_iff₀ hδ).1 hk
    nlinarith
  refine ⟨52*(k : ℝ)^2/(3*(1/2-ε)), by positivity, ?_⟩
  intro A M _ _ _ _ _ _ q tree hdim hacc
  have hd' : 52*(k : ℝ)^2 ≤ 3*(1/2-ε)*Fintype.card A := by
    have := (div_le_iff₀ (show 0 < 3*(1/2-ε) by positivity)).1 hdim
    nlinarith
  have hb := fixed_accuracy_fourth_power hε hkn hgap tree hd' hacc
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ (show 0 < 3*(1/2-ε) by positivity)).2
  convert hb using 1 <;> ring

#print axioms fixed_accuracy_fourth_power
#print axioms exists_fixed_accuracy_constant
end
end ICO.C4PhysicalEnsemble

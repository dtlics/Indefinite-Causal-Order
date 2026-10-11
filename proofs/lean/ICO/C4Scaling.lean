import ICO.C4PhysicalBound

/-! An explicit fourth-power query lower bound, now from the physical theorem. -/

namespace ICO.C4PhysicalEnsemble
open Matrix QIT
noncomputable section
set_option maxHeartbeats 800000
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Nonempty M]

/-- Uniform error `1/48` on the concrete mixed-unitary switch instances forces
`q > d^(1/4)/8`, expressed without a fractional-power convention. -/
theorem query_fourth_power_lower_bound {q : ℕ}
    (tree : ICO.BudgetQueryTree.Tree (A × M) (A × Bool) q A)
    (hdim : 64 ≤ Fintype.card A)
    (haccurate : ∀ r (UV : Sample A r),
      (ideal UV).normalizedTraceDistance (ordinary tree UV) ≤ 1/48) :
    (Fintype.card A : ℝ) < 4096 * (q : ℝ)^4 := by
  have hd : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hd64 : (64 : ℝ) ≤ Fintype.card A := by exact_mod_cast hdim
  by_cases hq : q = 0
  · subst q
    obtain ⟨UV, hUV⟩ := exists_distance_bound (r := 0) tree
    have hacc := haccurate 0 UV
    norm_num at hUV ⊢
    change (1/2 : ℝ) * traceNorm ((ideal UV).matrix - (ordinary tree UV).matrix) ≤ 1/48 at hacc
    have hg : (13 : ℝ)/(3*Fintype.card A) ≤ 13/(3*64) := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
      nlinarith
    linarith
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let r := 8*q^2-1
    have hsize : r+1 = 8*q^2 := by
      dsimp [r]
      have : 0 < q^2 := pow_pos hqpos 2
      omega
    have hr : (r : ℝ)+1 = 8*(q : ℝ)^2 := by exact_mod_cast hsize
    have hn : (((r+1)*(r+1) : ℕ) : ℝ) = 64*(q : ℝ)^4 := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hr]
      ring
    have hqp : (0 : ℝ) < q := by exact_mod_cast hqpos
    by_contra hlarge
    have hlarge' : 4096*(q : ℝ)^4 ≤ Fintype.card A := le_of_not_gt hlarge
    obtain ⟨UV, hUV⟩ := exists_distance_bound (r := r) tree
    have hacc := haccurate r UV
    have hgram : 13 * (((r+1)*(r+1) : ℕ) : ℝ)/(3*Fintype.card A) ≤ 13/192 := by
      rw [hn]
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    have hcollision : (q : ℝ)*(q-1)/(2*(r+1)) ≤ 1/16 := by
      rw [hr]
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    linarith

#print axioms query_fourth_power_lower_bound
end
end ICO.C4PhysicalEnsemble

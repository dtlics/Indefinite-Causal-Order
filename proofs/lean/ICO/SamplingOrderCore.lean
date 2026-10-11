import ICO.SamplingCP

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.FreshSamplingMaps ICO.SamplingCP

namespace ICO.SamplingOrderCore
set_option maxHeartbeats 600000
noncomputable section
variable {H O B I : Type} [Fintype H] [Fintype O] [Fintype B] [Fintype I]
variable [DecidableEq H] [DecidableEq O] [DecidableEq B] [DecidableEq I]

theorem cp_zero : MatrixMap.IsCompletelyPositive (0 : MatrixMap B O) := by
  change (MatrixMap.choi (0 : MatrixMap B O)).PosSemidef
  have h : MatrixMap.choi (0 : MatrixMap B O) = 0 := by ext i j; rfl
  rw [h]
  exact Matrix.PosSemidef.zero

theorem cp_add (f g : MatrixMap B O) (hf : MatrixMap.IsCompletelyPositive f)
    (hg : MatrixMap.IsCompletelyPositive g) : MatrixMap.IsCompletelyPositive (f + g) := by
  have h : MatrixMap.choi (f + g) = MatrixMap.choi f + MatrixMap.choi g := by ext i j; rfl
  change (MatrixMap.choi (f + g)).PosSemidef
  rw [h]
  exact hf.add hg

theorem cp_comp_difference (f g : MatrixMap H O) (k : MatrixMap B H)
    (hfg : MatrixMap.IsCompletelyPositive (f - g)) (hk : MatrixMap.IsCompletelyPositive k) :
    MatrixMap.IsCompletelyPositive (f.comp k - g.comp k) := by
  exact MatrixMap.isCompletelyPositive_comp (f - g) k hfg hk

theorem cp_sum_difference (f g : I → MatrixMap B O)
    (h : ∀ i, MatrixMap.IsCompletelyPositive (f i - g i)) :
    MatrixMap.IsCompletelyPositive ((∑ i, f i) - ∑ i, g i) := by
  rw [← Finset.sum_sub_distrib]
  exact ICO.FirstQueryInstrument.cp_sum _ h

theorem cp_scaled_difference (a b : ℝ) (ha : 0 ≤ a) (hba : b ≤ a)
    (f g : MatrixMap B O) (hfg : MatrixMap.IsCompletelyPositive (f - g))
    (hg : MatrixMap.IsCompletelyPositive g) :
    MatrixMap.IsCompletelyPositive ((a : ℂ) • f - (b : ℂ) • g) := by
  have h : (a : ℂ) • f - (b : ℂ) • g =
      (a : ℂ) • (f - g) + ((a - b : ℝ) : ℂ) • g := by
    ext X i j
    simp
    ring
  rw [h]
  exact cp_add _ _ (cp_scale a ha _ hfg) (cp_scale (a-b) (sub_nonneg.mpr hba) _ hg)

theorem fresh_sub_common_cp {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    MatrixMap.IsCompletelyPositive (freshMap tree oracles S T - commonMap tree oracles S T) := by
  induction tree generalizing S T with
  | stop after => rw [fresh_stop, common_stop, sub_self]; exact cp_zero
  | query second after ih =>
    cases second
    · rw [fresh_left, common_left]
      by_cases hS : S = ∅
      · subst S
        simpa using (cp_zero (B := H) (O := O))
      · have hc : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
        have hle : S.card ≤ r := by simpa using Finset.card_le_univ S
        have hweight : (r : ℝ)⁻¹ ≤ (S.card : ℝ)⁻¹ :=
          inv_anti₀ (by exact_mod_cast hc) (by exact_mod_cast hle)
        have hh := cp_scaled_difference (B := H) (O := O) (S.card : ℝ)⁻¹ (r : ℝ)⁻¹ (by positivity) hweight
        simp only [Complex.ofReal_inv, Complex.ofReal_natCast] at hh
        apply hh
        · apply cp_sum_difference
          intro a
          exact cp_comp_difference _ _ _ (ih (S.erase a.val) T)
            (oracles (.inl a.val)).completelyPositive
        · apply ICO.FirstQueryInstrument.cp_sum
          intro a
          exact MatrixMap.isCompletelyPositive_comp _ _ (common_cp after oracles (S.erase a.val) T)
            (oracles (.inl a.val)).completelyPositive
    · rw [fresh_right, common_right]
      by_cases hT : T = ∅
      · subst T
        simpa using (cp_zero (B := H) (O := O))
      · have hc : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
        have hle : T.card ≤ r := by simpa using Finset.card_le_univ T
        have hweight : (r : ℝ)⁻¹ ≤ (T.card : ℝ)⁻¹ :=
          inv_anti₀ (by exact_mod_cast hc) (by exact_mod_cast hle)
        have hh := cp_scaled_difference (B := H) (O := O) (T.card : ℝ)⁻¹ (r : ℝ)⁻¹ (by positivity) hweight
        simp only [Complex.ofReal_inv, Complex.ofReal_natCast] at hh
        apply hh
        · apply cp_sum_difference
          intro b
          exact cp_comp_difference _ _ _ (ih S (T.erase b.val))
            (oracles (.inr b.val)).completelyPositive
        · apply ICO.FirstQueryInstrument.cp_sum
          intro b
          exact MatrixMap.isCompletelyPositive_comp _ _ (common_cp after oracles S (T.erase b.val))
            (oracles (.inr b.val)).completelyPositive
  | node I next ih =>
    apply cp_sum_difference
    intro l
    exact cp_comp_difference _ _ _ (ih l S T) (MatrixMap.ofKraus_completelyPositive _)

end
end ICO.SamplingOrderCore

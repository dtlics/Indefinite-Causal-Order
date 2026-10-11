import ICO.FreshSamplingMaps
import ICO.FirstQueryInstrument

/-! Positivity and complete positivity of adaptive no-collision sampling. -/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.FreshSamplingMaps

namespace ICO.SamplingCP
set_option maxHeartbeats 600000
noncomputable section
variable {H O B : Type} [Fintype H] [Fintype O] [Fintype B]
variable [DecidableEq H] [DecidableEq O] [DecidableEq B]

theorem choi_smul (w : ℂ) (f : MatrixMap B O) :
    MatrixMap.choi (w • f) = w • MatrixMap.choi f := by
  ext i j
  rfl

theorem cp_scale (w : ℝ) (hw : 0 ≤ w) (f : MatrixMap B O)
    (hf : MatrixMap.IsCompletelyPositive f) :
    MatrixMap.IsCompletelyPositive ((w : ℂ) • f) := by
  change (MatrixMap.choi ((w : ℂ) • f)).PosSemidef
  rw [choi_smul]
  exact hf.smul (show (0 : ℂ) ≤ w by exact_mod_cast hw)

theorem cp_inv_nat (n : ℕ) (f : MatrixMap B O)
    (hf : MatrixMap.IsCompletelyPositive f) :
    MatrixMap.IsCompletelyPositive ((n : ℂ)⁻¹ • f) := by
  simpa using cp_scale (n : ℝ)⁻¹ (by positivity) f hf

theorem common_cp {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    MatrixMap.IsCompletelyPositive (commonMap tree oracles S T) := by
  induction tree generalizing S T with
  | stop after => exact after.completelyPositive
  | query second after ih =>
    cases second
    · apply cp_inv_nat
      apply ICO.FirstQueryInstrument.cp_sum
      intro a
      exact MatrixMap.isCompletelyPositive_comp _ _ (ih (S.erase a.val) T)
        (oracles (.inl a.val)).completelyPositive
    · apply cp_inv_nat
      apply ICO.FirstQueryInstrument.cp_sum
      intro b
      exact MatrixMap.isCompletelyPositive_comp _ _ (ih S (T.erase b.val))
        (oracles (.inr b.val)).completelyPositive
  | node I next ih =>
    apply ICO.FirstQueryInstrument.cp_sum
    intro l
    exact MatrixMap.isCompletelyPositive_comp _ _ (ih l S T)
      (MatrixMap.ofKraus_completelyPositive _)

theorem fresh_cp {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    MatrixMap.IsCompletelyPositive (freshMap tree oracles S T) := by
  induction tree generalizing S T with
  | stop after => exact after.completelyPositive
  | query second after ih =>
    cases second
    · apply cp_inv_nat
      apply ICO.FirstQueryInstrument.cp_sum
      intro a
      exact MatrixMap.isCompletelyPositive_comp _ _ (ih (S.erase a.val) T)
        (oracles (.inl a.val)).completelyPositive
    · apply cp_inv_nat
      apply ICO.FirstQueryInstrument.cp_sum
      intro b
      exact MatrixMap.isCompletelyPositive_comp _ _ (ih S (T.erase b.val))
        (oracles (.inr b.val)).completelyPositive
  | node I next ih =>
    apply ICO.FirstQueryInstrument.cp_sum
    intro l
    exact MatrixMap.isCompletelyPositive_comp _ _ (ih l S T)
      (MatrixMap.ofKraus_completelyPositive _)

theorem common_positive {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r))
    {X : CMatrix B} (hX : X.PosSemidef) : (commonMap tree oracles S T X).PosSemidef :=
  MatrixMap.isCompletelyPositive_mapsPositive _ (common_cp tree oracles S T) X hX

end
end ICO.SamplingCP

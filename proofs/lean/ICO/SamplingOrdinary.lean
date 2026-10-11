import ICO.SamplingOrderCore

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.FreshSamplingMaps ICO.SamplingCP ICO.SamplingOrderCore

namespace ICO.SamplingOrdinary
set_option maxHeartbeats 600000
noncomputable section
variable {H O B : Type} [Fintype H] [Fintype O] [Fintype B]
variable [DecidableEq H] [DecidableEq O] [DecidableEq B]

def uniformChannel {r : ℕ} [NeZero r] (oracles : Fin r → Channel H H) : Channel H H :=
  adaptiveChannel (ICO.UniformInstrument.instrument (H := H) (I := Fin r)) oracles

theorem uniformChannel_map {r : ℕ} [NeZero r] (oracles : Fin r → Channel H H) :
    (uniformChannel oracles).map = (r : ℂ)⁻¹ • ∑ a, (oracles a).map := by
  simpa [uniformChannel] using ICO.UniformInstrument.channel_map oracles

def ordinaryChannel {q r : ℕ} [NeZero r] (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) : Channel B O :=
  tree.channel (uniformChannel fun a => oracles (.inl a)) (uniformChannel fun b => oracles (.inr b))

theorem ordinary_query_left {q r : ℕ} [NeZero r] (after : ICO.BudgetQueryTree.Tree H O q H)
    (oracles : Fin r ⊕ Fin r → Channel H H) :
    (ordinaryChannel (.query false after) oracles).map = (r : ℂ)⁻¹ •
      ∑ a, (ordinaryChannel after oracles).map.comp (oracles (.inl a)).map := by
  change (ordinaryChannel after oracles).map.comp (uniformChannel _).map = _
  rw [uniformChannel_map]
  ext X i j
  simp [map_sum, map_smul, Finset.smul_sum]

theorem ordinary_query_right {q r : ℕ} [NeZero r] (after : ICO.BudgetQueryTree.Tree H O q H)
    (oracles : Fin r ⊕ Fin r → Channel H H) :
    (ordinaryChannel (.query true after) oracles).map = (r : ℂ)⁻¹ •
      ∑ b, (ordinaryChannel after oracles).map.comp (oracles (.inr b)).map := by
  change (ordinaryChannel after oracles).map.comp (uniformChannel _).map = _
  rw [uniformChannel_map]
  ext X i j
  simp [map_sum, map_smul, Finset.smul_sum]

theorem cp_full_sub_partial {r : ℕ} (S : Finset (Fin r))
    (f : Fin r → MatrixMap B O) (g : ↥S → MatrixMap B O)
    (hf : ∀ a, MatrixMap.IsCompletelyPositive (f a))
    (hfg : ∀ a, MatrixMap.IsCompletelyPositive (f a.val - g a)) :
    MatrixMap.IsCompletelyPositive ((∑ a, f a) - ∑ a : ↥S, g a) := by
  have hpart : (∑ a : ↥S, f a.val) + (∑ a : ↥(Sᶜ), f a.val) = ∑ a, f a := by
    simp only [Finset.sum_coe_sort]
    exact Finset.sum_add_sum_compl S f
  rw [← hpart]
  have heq : (∑ a : ↥S, f a.val) + (∑ a : ↥(Sᶜ), f a.val) - (∑ a : ↥S, g a) =
      (∑ a : ↥S, (f a.val - g a)) + (∑ a : ↥(Sᶜ), f a.val) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [heq]
  exact cp_add _ _ (ICO.FirstQueryInstrument.cp_sum _ hfg)
    (ICO.FirstQueryInstrument.cp_sum _ fun a => hf a.val)

theorem inv_nat_smul_sub (r : ℕ) (f g : MatrixMap B O) :
    (r : ℂ)⁻¹ • f - (r : ℂ)⁻¹ • g = (r : ℂ)⁻¹ • (f - g) := by
  ext X i j
  simp
  ring

theorem ordinary_sub_common_cp {q r : ℕ} [NeZero r]
    (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    MatrixMap.IsCompletelyPositive ((ordinaryChannel tree oracles).map - commonMap tree oracles S T) := by
  induction tree generalizing S T with
  | stop after => change MatrixMap.IsCompletelyPositive (after.map - after.map); simpa using (cp_zero (B := _) (O := O))
  | query second after ih =>
    cases second
    · rw [ordinary_query_left, common_left]
      rw [inv_nat_smul_sub]
      apply cp_inv_nat
      apply cp_full_sub_partial S
      · intro a
        exact MatrixMap.isCompletelyPositive_comp _ _ (ordinaryChannel after oracles).completelyPositive
          (oracles (.inl a)).completelyPositive
      · intro a
        exact cp_comp_difference _ _ _ (ih (S.erase a.val) T)
          (oracles (.inl a.val)).completelyPositive
    · rw [ordinary_query_right, common_right]
      rw [inv_nat_smul_sub]
      apply cp_inv_nat
      apply cp_full_sub_partial T
      · intro b
        exact MatrixMap.isCompletelyPositive_comp _ _ (ordinaryChannel after oracles).completelyPositive
          (oracles (.inr b)).completelyPositive
      · intro b
        exact cp_comp_difference _ _ _ (ih S (T.erase b.val))
          (oracles (.inr b.val)).completelyPositive
  | node I next ih =>
    apply cp_sum_difference
    intro l
    exact cp_comp_difference _ _ _ (ih l S T) (MatrixMap.ofKraus_completelyPositive _)

end
end ICO.SamplingOrdinary

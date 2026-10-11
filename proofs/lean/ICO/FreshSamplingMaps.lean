import ICO.FreshBudgetCompile

/-! # The ordinary and fresh sampling maps, and their common no-collision part -/

open Matrix QIT ICO.InstrumentCompression

namespace ICO.FreshSamplingMaps
set_option maxHeartbeats 600000
noncomputable section
variable {H O B : Type} [Fintype H] [Fintype O] [Fintype B]
variable [DecidableEq H] [DecidableEq O] [DecidableEq B]

def freshMap {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) : MatrixMap B O := by
  induction tree generalizing S T with
  | stop after => exact after.map
  | query second after ih =>
    cases second
    · exact (S.card : ℂ)⁻¹ • ∑ a : ↥S, (ih (S.erase a.val) T).comp (oracles (.inl a.val)).map
    · exact (T.card : ℂ)⁻¹ • ∑ b : ↥T, (ih S (T.erase b.val)).comp (oracles (.inr b.val)).map
  | node I next ih => exact ∑ l, (ih l S T).comp (branchMap I l)

/-- Every retained branch uses the ordinary label probability `1/r`; repeated
labels contribute zero. This is a physical CP subchannel, not a normalized
conditional output state. -/
def commonMap {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) : MatrixMap B O := by
  induction tree generalizing S T with
  | stop after => exact after.map
  | query second after ih =>
    cases second
    · exact (r : ℂ)⁻¹ • ∑ a : ↥S, (ih (S.erase a.val) T).comp (oracles (.inl a.val)).map
    · exact (r : ℂ)⁻¹ • ∑ b : ↥T, (ih S (T.erase b.val)).comp (oracles (.inr b.val)).map
  | node I next ih => exact ∑ l, (ih l S T).comp (branchMap I l)

theorem fresh_stop {q r : ℕ} (after : Channel B O)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    freshMap (.stop (q := q) after) oracles S T = after.map := rfl

theorem common_stop {q r : ℕ} (after : Channel B O)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    commonMap (.stop (q := q) after) oracles S T = after.map := rfl

theorem fresh_left {q r : ℕ} (after : ICO.BudgetQueryTree.Tree H O q H)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    freshMap (.query false after) oracles S T = (S.card : ℂ)⁻¹ •
      ∑ a : ↥S, (freshMap after oracles (S.erase a.val) T).comp (oracles (.inl a.val)).map := rfl

theorem fresh_right {q r : ℕ} (after : ICO.BudgetQueryTree.Tree H O q H)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    freshMap (.query true after) oracles S T = (T.card : ℂ)⁻¹ •
      ∑ b : ↥T, (freshMap after oracles S (T.erase b.val)).comp (oracles (.inr b.val)).map := rfl

theorem common_left {q r : ℕ} (after : ICO.BudgetQueryTree.Tree H O q H)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    commonMap (.query false after) oracles S T = (r : ℂ)⁻¹ •
      ∑ a : ↥S, (commonMap after oracles (S.erase a.val) T).comp (oracles (.inl a.val)).map := rfl

theorem common_right {q r : ℕ} (after : ICO.BudgetQueryTree.Tree H O q H)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) :
    commonMap (.query true after) oracles S T = (r : ℂ)⁻¹ •
      ∑ b : ↥T, (commonMap after oracles S (T.erase b.val)).comp (oracles (.inr b.val)).map := rfl

theorem channel_cast {r : ℕ} {S T : Finset (Fin r ⊕ Fin r)}
    (h : S = T) (tree : ICO.AtMostLabelledQueryTree.Tree (Fin r ⊕ Fin r) H O S B)
    (oracles : Fin r ⊕ Fin r → Channel H H) :
    ((h ▸ tree).channel oracles).map = (tree.channel oracles).map := by
  subst T
  rfl

theorem fresh_compile_map {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r))
    (hS : q ≤ S.card) (hT : q ≤ T.card) :
    ((ICO.FreshBudgetCompile.fresh tree S T hS hT).channel oracles).map =
      freshMap tree oracles S T := by
  induction tree generalizing S T with
  | stop after => rfl
  | @query q second after ih =>
    cases second
    · letI : Nonempty ↥S := by
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
        exact ⟨⟨a, ha⟩⟩
      rw [ICO.FreshBudgetCompile.fresh, ICO.AtMostLabelledQueryTree.Tree.channel,
        ICO.UniformInstrument.channel_map]
      rw [Fintype.card_coe]
      change (S.card : ℂ)⁻¹ • (∑ a : ↥S,
        (((ICO.FreshBudgetCompile.erase_left S T a.val) ▸
          ICO.FreshBudgetCompile.fresh after (S.erase a.val) T
            (by rw [Finset.card_erase_of_mem a.property]; omega) (by omega)).channel oracles).map.comp
              (oracles (.inl a.val)).map) = _
      simp_rw [channel_cast, ih]
      rfl
    · letI : Nonempty ↥T := by
        obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        exact ⟨⟨b, hb⟩⟩
      rw [ICO.FreshBudgetCompile.fresh, ICO.AtMostLabelledQueryTree.Tree.channel,
        ICO.UniformInstrument.channel_map]
      rw [Fintype.card_coe]
      change (T.card : ℂ)⁻¹ • (∑ b : ↥T,
        (((ICO.FreshBudgetCompile.erase_right S T b.val) ▸
          ICO.FreshBudgetCompile.fresh after S (T.erase b.val)
            (by omega) (by rw [Finset.card_erase_of_mem b.property]; omega)).channel oracles).map.comp
              (oracles (.inr b.val)).map) = _
      simp_rw [channel_cast, ih]
      rfl
  | node I next ih =>
    change (∑ l, ((ICO.FreshBudgetCompile.fresh (next l) S T hS hT).channel oracles).map.comp
      (branchMap I l)) = _
    simp_rw [ih]
    rfl

end
end ICO.FreshSamplingMaps

import ICO.SamplingLoss

/-! The actual no-collision CP branch loses at most the total-query birthday probability. -/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.FreshSamplingMaps ICO.SamplingCP ICO.SamplingLoss

namespace ICO.SamplingTrace
set_option maxHeartbeats 600000
noncomputable section
variable {H O B C L : Type} [Fintype H] [Fintype O] [Fintype B] [Fintype C] [Fintype L]
variable [DecidableEq H] [DecidableEq O] [DecidableEq B] [DecidableEq C] [DecidableEq L]

theorem common_trace_left {q r : ℕ} (after : ICO.BudgetQueryTree.Tree H O q H)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) (X : CMatrix H) :
    (commonMap (.query false after) oracles S T X).trace.re = (r : ℝ)⁻¹ *
      ∑ a : ↥S, (commonMap after oracles (S.erase a.val) T ((oracles (.inl a.val)).map X)).trace.re := by
  rw [common_left]
  simp [Matrix.trace_smul, Matrix.trace_sum, Complex.mul_re]

theorem common_trace_right {q r : ℕ} (after : ICO.BudgetQueryTree.Tree H O q H)
    (oracles : Fin r ⊕ Fin r → Channel H H) (S T : Finset (Fin r)) (X : CMatrix H) :
    (commonMap (.query true after) oracles S T X).trace.re = (r : ℝ)⁻¹ *
      ∑ b : ↥T, (commonMap after oracles S (T.erase b.val) ((oracles (.inr b.val)).map X)).trace.re := by
  rw [common_right]
  simp [Matrix.trace_smul, Matrix.trace_sum, Complex.mul_re]

theorem instrument_trace_sum (I : Instrument B C L) (X : CMatrix B) :
    (∑ l, (branchMap I l X).trace.re) = X.trace.re := by
  have h := adaptiveMap_tp I (fun _ => Channel.idChannel C) X
  simpa [adaptiveMap, Channel.idChannel, MatrixMap.ofKraus, Matrix.trace_sum, Complex.re_sum] using congrArg Complex.re h

theorem common_trace_loss {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (hr : 0 < r)
    (S T : Finset (Fin r)) (t : ℕ) (hS : r - S.card ≤ t) (hT : r - T.card ≤ t)
    {X : CMatrix B} (hX : X.PosSemidef) :
    X.trace.re - (commonMap tree oracles S T X).trace.re ≤ loss r t q * X.trace.re := by
  induction tree generalizing S T t with
  | stop after =>
    rw [common_stop, after.tracePreserving, sub_self]
    exact mul_nonneg (loss_nonneg _ _ _) hX.trace_nonneg.1
  | @query q second after ih =>
    cases second
    · rw [common_trace_left, loss_succ]
      apply step_loss r t hr (I := ↥S)
      · simpa using Finset.card_le_univ S
      · simpa using hS
      · exact hX.trace_nonneg.1
      · exact loss_nonneg _ _ _
      · intro a
        have hSa : r - (S.erase a.val).card ≤ t + 1 := by
          rw [Finset.card_erase_of_mem a.property]
          omega
        have hTa : r - T.card ≤ t + 1 := by omega
        have hh := ih (S.erase a.val) T (t+1) hSa hTa ((oracles (.inl a.val)).mapsPositive X hX)
        have hp := (oracles (.inl a.val)).tracePreserving X
        rw [hp] at hh
        exact hh
    · rw [common_trace_right, loss_succ]
      apply step_loss r t hr (I := ↥T)
      · simpa using Finset.card_le_univ T
      · simpa using hT
      · exact hX.trace_nonneg.1
      · exact loss_nonneg _ _ _
      · intro b
        have hSb : r - S.card ≤ t + 1 := by omega
        have hTb : r - (T.erase b.val).card ≤ t + 1 := by
          rw [Finset.card_erase_of_mem b.property]
          omega
        have hh := ih S (T.erase b.val) (t+1) hSb hTb ((oracles (.inr b.val)).mapsPositive X hX)
        have hp := (oracles (.inr b.val)).tracePreserving X
        rw [hp] at hh
        exact hh
  | node I next ih =>
    change X.trace.re - ((∑ l, (commonMap (next l) oracles S T).comp (branchMap I l)) X).trace.re ≤ _
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.trace_sum, Complex.re_sum]
    rw [← instrument_trace_sum I X, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    exact ih l S T t hS hT (MatrixMap.ofKraus_mapsPositive _ X hX)

theorem initial_trace_loss {q r : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (oracles : Fin r ⊕ Fin r → Channel H H) (hr : 0 < r)
    {X : CMatrix B} (hX : X.PosSemidef) :
    X.trace.re - (commonMap tree oracles Finset.univ Finset.univ X).trace.re ≤
      ((q : ℝ) * (q - 1) / (2 * r)) * X.trace.re := by
  simpa only [loss_initial] using common_trace_loss tree oracles hr Finset.univ Finset.univ 0
    (by simp) (by simp) hX

end
end ICO.SamplingTrace

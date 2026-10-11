import ICO.InstrumentCompression

/-! # A finite first-query decision is an operator-valued instrument

An arbitrary finite oracle-free adaptive decision tree can terminate with a
classical query label. Its Kraus refinement has a proved completeness equation.
The branch weights are consequently allowed to depend on the quantum input;
there is no assumed scalar lottery over causal orders.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression

namespace ICO.FirstQueryInstrument

set_option maxHeartbeats 200000
noncomputable section

universe u
variable {A B C L Q : Type u}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype L] [Fintype Q]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq L] [DecidableEq Q]

theorem cp_sum (maps : L → MatrixMap A C)
    (h : ∀ l, MatrixMap.IsCompletelyPositive (maps l)) :
    MatrixMap.IsCompletelyPositive (∑ l : L, maps l) := by
  have hc : MatrixMap.choi (∑ l : L, maps l) = ∑ l : L, MatrixMap.choi (maps l) := by
    ext i j
    simp [MatrixMap.choi, Matrix.sum_apply]
  rw [MatrixMap.IsCompletelyPositive, hc]
  exact Matrix.posSemidef_sum Finset.univ fun l _ => h l

structure LabelledChannel (A C Q : Type u) [Fintype A] [Fintype C] [Fintype Q]
    [DecidableEq A] [DecidableEq C] where
  map : Q → MatrixMap A C
  cp : ∀ q, MatrixMap.IsCompletelyPositive (map q)
  total_tp : MatrixMap.IsTracePreserving (∑ q : Q, map q)

def terminal (q₀ : Q) (channel : Channel A C) : LabelledChannel A C Q where
  map q := if q = q₀ then channel.map else 0
  cp q := by
    split_ifs
    · exact channel.completelyPositive
    · change (MatrixMap.choi (0 : MatrixMap A C)).PosSemidef
      have hzero : MatrixMap.choi (0 : MatrixMap A C) = 0 := by ext i j; rfl
      rw [hzero]
      exact Matrix.PosSemidef.zero
  total_tp := by
    simpa using channel.tracePreserving

def continueWith (I : Instrument A B L) (next : L → LabelledChannel B C Q) :
    LabelledChannel A C Q where
  map q := ∑ l : L, ((next l).map q).comp (branchMap I l)
  cp q := cp_sum _ fun l => MatrixMap.isCompletelyPositive_comp
    ((next l).map q) (branchMap I l) ((next l).cp q)
      (MatrixMap.ofKraus_completelyPositive _)
  total_tp := by
    intro X
    change ((∑ q : Q, ∑ l : L, ((next l).map q).comp (branchMap I l)) X).trace = X.trace
    rw [Finset.sum_comm]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.trace_sum]
    have hp (l : L) : (∑ q : Q, ((next l).map q (branchMap I l X)).trace) =
        (branchMap I l X).trace := by
      have h := (next l).total_tp (branchMap I l X)
      simpa [LinearMap.sum_apply, Matrix.trace_sum] using h
    simp_rw [hp, branchMap_apply]
    have hI : MatrixMap.krausAdjoint I.op (1 : CMatrix B) = 1 := by
      simpa [MatrixMap.krausAdjoint] using I.complete
    have h := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one I.op hI X
    simpa [MatrixMap.ofKraus, Matrix.trace_sum] using h

inductive DecisionTree (C Q : Type u) [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q] :
    (A : Type u) → [Fintype A] → [DecidableEq A] → Type (u + 1) where
  | stop {A : Type u} [Fintype A] [DecidableEq A]
      (label : Q) (channel : Channel A C) : DecisionTree C Q A
  | node {A B L : Type u} [Fintype A] [Fintype B] [Fintype L]
      [DecidableEq A] [DecidableEq B] [DecidableEq L]
      (instrument : Instrument A B L) (next : L → DecisionTree C Q B) : DecisionTree C Q A

def DecisionTree.compile {C Q : Type u} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]
    {A : Type u} [Fintype A] [DecidableEq A] (tree : DecisionTree C Q A) :
    LabelledChannel A C Q := by
  induction tree with
  | stop label channel => exact terminal label channel
  | node instrument next ih => exact continueWith instrument ih

/-- The first-query labels admit a concrete Kraus refinement with a complete
operator-valued preprocessing instrument. -/
theorem LabelledChannel.exists_complete_refinement (D : LabelledChannel A C Q) :
    ∃ K : Q → (A × C) → Matrix C A ℂ,
      (∀ q, D.map q = MatrixMap.ofKraus (K q)) ∧
        (∑ j : Q × (A × C), (K j.1 j.2).conjTranspose * K j.1 j.2) = 1 := by
  choose K hK using fun q => MatrixMap.exists_kraus_of_choi_psd (D.map q) (D.cp q)
  refine ⟨K, hK, ?_⟩
  let allK : Q × (A × C) → Matrix C A ℂ := fun j => K j.1 j.2
  have hsum : MatrixMap.ofKraus allK = ∑ q : Q, D.map q := by
    simp_rw [hK]
    ext X i j
    simp [MatrixMap.ofKraus, allK, Fintype.sum_prod_type, Matrix.sum_apply]
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus allK) := by
    rw [hsum]
    exact D.total_tp
  have hcomplete := MatrixMap.krausAdjoint_one_of_tracePreserving allK hTP
  simpa [MatrixMap.krausAdjoint, allK] using hcomplete

theorem DecisionTree.first_query_instrument
    {C Q : Type u} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]
    {A : Type u} [Fintype A] [DecidableEq A] (tree : DecisionTree C Q A) :
    ∃ K : Q → (A × C) → Matrix C A ℂ,
      (∀ q, tree.compile.map q = MatrixMap.ofKraus (K q)) ∧
        (∑ j : Q × (A × C), (K j.1 j.2).conjTranspose * K j.1 j.2) = 1 :=
  tree.compile.exists_complete_refinement

/-- Weight of an actual Kraus branch on the maximally mixed input. -/
def krausWeight (K : Matrix C A ℂ) : ℝ :=
  (K.conjTranspose * K).trace.re / (Fintype.card A : ℝ)

theorem krausWeight_nonneg (K : Matrix C A ℂ) : 0 ≤ krausWeight K := by
  unfold krausWeight
  exact div_nonneg (Matrix.posSemidef_conjTranspose_mul_self K).trace_nonneg.1
    (by positivity)

theorem instrument_weights_sum [Nonempty A] (I : Instrument A C L) :
    (∑ l : L, krausWeight (I.op l)) = 1 := by
  have h := congrArg (fun X : CMatrix A => X.trace.re) I.complete
  have hs : (∑ l : L, ((I.op l).conjTranspose * I.op l).trace.re) =
      (Fintype.card A : ℝ) := by
    simpa [Matrix.trace_sum] using h
  simp only [krausWeight, ← Finset.sum_div, hs]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

end
end ICO.FirstQueryInstrument


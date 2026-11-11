import ICO.BoundedSwitchObstruction
import ICO.BudgetPreparation
import ICO.CircuitPolarization
import ICO.TwoQueryDilation
import ICO.FirstQueryInstrument
import ICO.OrderedCombSemantics
import Mathlib.GroupTheory.Perm.Fin

/-! Theorem 1 (`thm:exact-simulation`) for an arbitrary control input,
Lemma 5 (`lem:ordered`) as a single statement in dimension `d`, and
Lemma 6 (`lem:polarization`) in the paper's full symmetrized form:
1. Arbitrary-control exact switch impossibility (`no_bounded_full_switch_circuit`
   and `no_labelled_full_switch_circuit`): any finite-query adaptive circuit
   matching the full control-and-target switch on `Fin 2 × Fin d` also matches
   the fixed-`|+⟩` switch after precomposing with `plusControlChannel d`, and is
   therefore impossible for `d ≥ 2` by `ICO.BoundedSwitchObstruction.no_bounded_circuit`.
2. Ordered components (`tree_ordered_components`, `tree_ordered_components_dim_d`,
   and `ordered_components_decomposition`): a single combined statement in general
   dimension starting directly from `tree : ICO.TwoQueryTree.QueryTree (A × M) F P`,
   packaging its `A ≺ B` and `B ≺ A` comb matrices (`treeCombAB`, `treeCombBA`),
   box-independent first-query probabilities `orderStateProb` summing to `1` and
   matching the marginal reduced comb traces, positive semidefiniteness
   `C_{A≺B}, C_{B≺A} ≥ 0`, homogeneous partial-trace comb constraints (`eq:ordered-comb`),
   and the Choi / comb-link realization identity for all complete Kraus pairs.
3. Full multilinear polarization (`symmetrized_polarization` and the explicit
   quantum-switch specializations `symmetrized_switch_polarization_choi`,
   `symmetrized_switch_polarization`, and `symmetrized_switch_polarization_kraus`):
   if an ordinary circuit calling `M` slots of type `A` and `N` slots of type `B`
   matches a bilinear target `S` (and specifically the full-control quantum switch
   `SW`) on identical CPTP channels, then its slot-symmetrized realization on
   arbitrary `A^{(1)}, ..., A^{(M)}` and `B^{(1)}, ..., B^{(N)}` equals
   `(1 / (M * N)) ∑_{k, l} S[A^{(k)}, B^{(l)}]` (`eq:polarization`), and its
   two-call selected subcircuits realize the diluted target (`eq:dilution`). -/

namespace ICO.PolarizationOrderedArbitraryControl
open Matrix QIT
open ICO.EmbeddedSwitch ICO.EmbeddingSwitchChannels ICO.AllChannelDilation
open ICO.LabelledQueryTree ICO.LabelledCircuitComposition
open ICO.OrderedCombSemantics ICO.PositiveSupport
open ICO.TwoQueryTree ICO.TwoQueryDilation ICO.FirstQueryInstrument
open ICO.OneSlotPolarization ICO.TwoSlotPolarization ICO.CircuitPolarization
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
set_option Elab.async false

section ArbitraryControl
variable {M : Type} [Fintype M] [DecidableEq M]

theorem orderedPair_one_apply {d : Nat} (o : Fin 2 × Fin d) (p : Fin d) :
    orderedPair (1 : CMatrix (Fin d)) (1 : CMatrix (Fin d)) o p =
      (1 : CMatrix (Fin d)) o.2 p := by
  simp [orderedPair]

theorem orderedPair_one_gram (d : Nat) :
    (orderedPair (1 : CMatrix (Fin d)) (1 : CMatrix (Fin d)))ᴴ *
      orderedPair (1 : CMatrix (Fin d)) (1 : CMatrix (Fin d)) =
      (2 : ℂ) • (1 : CMatrix (Fin d)) := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.conjTranspose_apply, orderedPair_one_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases h : i = j
  · subst j
    simp [Finset.sum_ite_eq']
    ring
  · simp [h, Ne.symm h]

/-- The `|+⟩`-control preparation isometry `|ψ⟩ ↦ |+⟩ ⊗ |ψ⟩` into `Fin 2 × Fin d`. -/
def plusControlMatrix (d : Nat) : Matrix (Fin 2 × Fin d) (Fin d) ℂ :=
  switchKraus (1 : CMatrix (Fin d)) (1 : CMatrix (Fin d))

theorem plusControl_isometry (d : Nat) :
    (plusControlMatrix d)ᴴ * plusControlMatrix d = 1 := by
  unfold plusControlMatrix switchKraus
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    orderedPair_one_gram, smul_smul, smul_smul]
  have h2 : star (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2 = 1 := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    norm_cast
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [h2, one_smul]

/-- The CPTP channel preparing the control qubit in `|+⟩` and passing the
`d`-dimensional target register through unchanged. -/
def plusControlChannel (d : Nat) : Channel (Fin d) (Fin 2 × Fin d) :=
  ICO.ClassicalDilation.isometryChannel (plusControlMatrix d) (plusControl_isometry d)

/-- The controlled-order quantum switch Kraus operator on `Fin 2 × Fin d`
(`|0⟩⟨0| ⊗ (V * U) + |1⟩⟨1| ⊗ (U * V)`, Eq. `eq:switch-kraus`). -/
def fullControlOrderedPair {d : Nat} (U V : CMatrix (Fin d)) : CMatrix (Fin 2 × Fin d) :=
  fun o p => if o.1 = p.1 then (if o.1 = 0 then (V * U) o.2 p.2 else (U * V) o.2 p.2) else 0

theorem fullControlOrderedPair_mul_plus {d : Nat} (U V : CMatrix (Fin d)) :
    fullControlOrderedPair U V * plusControlMatrix d = switchKraus U V := by
  unfold plusControlMatrix switchKraus
  rw [Matrix.mul_smul]
  congr 1
  ext ⟨c, i⟩ j
  simp [fullControlOrderedPair, orderedPair, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite]

/-- The quantum switch superoperator acting on an arbitrary control-and-target
input state in `CMatrix (Fin 2 × Fin d)`. -/
def fullControlSwitchMap {d : Nat} {I J : Type} [Fintype I] [Fintype J]
    (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d)) :
    MatrixMap (Fin 2 × Fin d) (Fin 2 × Fin d) :=
  MatrixMap.ofKraus (fun ij : I × J => fullControlOrderedPair (U ij.1) (V ij.2))

theorem fullControlSwitchMap_comp_plus {d : Nat} {I J : Type} [Fintype I] [Fintype J]
    (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d)) :
    (fullControlSwitchMap U V).comp (plusControlChannel d).map = switchMap U V := by
  simp only [fullControlSwitchMap, plusControlChannel,
    ICO.ClassicalDilation.isometryChannel, switchMap, MatrixMap.ofKraus_comp_ofKraus]
  ext X a b
  simp [MatrixMap.ofKraus, Fintype.sum_prod_type, fullControlOrderedPair_mul_plus]

/-- Exact simulation of the full-control quantum switch on all control-and-target
inputs in `Fin 2 × Fin d` by a `q`-query adaptive circuit. -/
def RealizesFullControlSwitch {d q : Nat}
    (tree : ICO.BudgetQueryTree.Tree (Fin d × M) (Fin 2 × Fin d) q (Fin 2 × Fin d)) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d))
      (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1),
      (tree.channel (oracleChannel U hU) (oracleChannel V hV)).map =
        fullControlSwitchMap U V

/-- Theorem 1 (`thm:exact-simulation`) for an arbitrary control-and-target input:
no bounded finite-dimensional classically adaptive circuit with budget `q`
simulates the full-control quantum switch on all pairs of channels in dimension `d ≥ 2`. -/
theorem no_bounded_full_switch_circuit [Nonempty M] {d q : Nat} (hd : 2 ≤ d)
    (tree : ICO.BudgetQueryTree.Tree (Fin d × M) (Fin 2 × Fin d) q (Fin 2 × Fin d)) :
    ¬ RealizesFullControlSwitch tree := by
  intro h
  apply ICO.BoundedSwitchObstruction.no_bounded_circuit hd
    (ICO.BudgetPreparation.precompose tree (plusControlChannel d))
  intro I J _ _ _ _ U V hU hV
  rw [ICO.BudgetPreparation.precompose_map, h I J U V hU hV,
    fullControlSwitchMap_comp_plus]

theorem no_bounded_circuit_arbitrary_control [Nonempty M] {d q : Nat} (hd : 2 ≤ d)
    (tree : ICO.BudgetQueryTree.Tree (Fin d × M) (Fin 2 × Fin d) q (Fin 2 × Fin d)) :
    ¬ RealizesFullControlSwitch tree :=
  no_bounded_full_switch_circuit hd tree

/-- Exact simulation of the full-control quantum switch by a labelled `(m, n)`-query
adaptive circuit on all control-and-target inputs. -/
def RealizesLabelledFullControlSwitch {d m n : Nat}
    (tree : ICO.LabelledQueryTree.Tree (Fin m ⊕ Fin n) (Fin d × M)
      (Fin 2 × Fin d) Finset.univ (Fin 2 × Fin d)) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d))
      (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1),
      (tree.channel (Sum.elim (fun _ => oracleChannel U hU)
        (fun _ => oracleChannel V hV))).map = fullControlSwitchMap U V

theorem no_labelled_full_switch_circuit {d m n : Nat} (hd : 2 ≤ d)
    (tree : ICO.LabelledQueryTree.Tree (Fin m ⊕ Fin n) (Fin d × M)
      (Fin 2 × Fin d) Finset.univ (Fin 2 × Fin d)) :
    ¬ RealizesLabelledFullControlSwitch tree := by
  intro h
  apply ICO.BoundedSwitchObstruction.no_labelled hd
    (prepend (plusControlChannel d) tree)
  intro I J _ _ _ _ U V hU hV
  have ht := h I J U V hU hV
  rw [ICO.LabelledQueryTree.Tree.channel_map] at ht ⊢
  rw [prepend_map, ht, fullControlSwitchMap_comp_plus]

end ArbitraryControl

section OrderedComponents
variable {P A F : Type} [Fintype P] [Fintype A] [Fintype F]
  [DecidableEq P] [DecidableEq A] [DecidableEq F]

/-- An ordered Stinespring branch in arbitrary finite dimensions `P` (circuit
input), `A` (oracle wire, e.g. `Fin d`), and `F` (circuit output), with possibly
subnormalized preprocessing `pre` and isometric middle/final continuations `mid`
and `post`. -/
structure OrderedBranch (P A F : Type) [Fintype P] [Fintype A] [Fintype F]
    [DecidableEq P] [DecidableEq A] [DecidableEq F] where
  M : Type
  N : Type
  K : Type
  [finiteM : Fintype M]
  [finiteN : Fintype N]
  [finiteK : Fintype K]
  [decideM : DecidableEq M]
  [decideN : DecidableEq N]
  [decideK : DecidableEq K]
  pre : Matrix (A × M) P ℂ
  mid : Matrix (A × N) (A × M) ℂ
  post : Matrix (F × K) (A × N) ℂ
  mid_isometry : midᴴ * mid = 1
  post_isometry : postᴴ * post = 1

attribute [instance] OrderedBranch.finiteM OrderedBranch.finiteN OrderedBranch.finiteK
  OrderedBranch.decideM OrderedBranch.decideN OrderedBranch.decideK

/-- Swap the first-slot `(A_i, A_o)` and second-slot `(B_i, B_o)` wires of a
six-wire comb index `SixWires P A F`. -/
def swapSixWires (x : SixWires P A F) : SixWires P A F :=
  (((((x.1.1.1.1.1, x.1.1.2), x.1.2), x.1.1.1.1.2), x.1.1.1.2), x.2)

omit [Fintype P] [Fintype A] [Fintype F] [DecidableEq P] [DecidableEq A] [DecidableEq F] in
theorem swapSixWires_involutive (x : SixWires P A F) :
    swapSixWires (swapSixWires x) = x := by
  rcases x with ⟨⟨⟨⟨⟨p, ai⟩, ao⟩, bi⟩, bo⟩, f⟩
  rfl

/-- The six-wire `A ≺ B` comb matrix of a single ordered branch. -/
def OrderedBranch.comb (b : OrderedBranch P A F) :
    Matrix (SixWires P A F) (SixWires P A F) ℂ :=
  circuitComb b.pre b.mid b.post

/-- The four-wire reduced comb operator `C^{(2)}` after tracing out `F`. -/
def OrderedBranch.comb₂ (b : OrderedBranch P A F) :
    Matrix (FourWires P A) (FourWires P A) ℂ :=
  partialTrace (rankOne (preMiddle b.pre b.mid))

/-- The two-wire reduced comb operator `C^{(1)}` after tracing out the second
oracle input and middle memory. -/
def OrderedBranch.comb₁ (b : OrderedBranch P A F) :
    Matrix (P × A) (P × A) ℂ :=
  preComb b.pre

/-- The six-wire `B ≺ A` comb matrix of a reverse-ordered branch, expressed on
the common wire ordering `SixWires P A F` via `swapSixWires`. -/
def OrderedBranch.reverseComb (b : OrderedBranch P A F) :
    Matrix (SixWires P A F) (SixWires P A F) ℂ :=
  fun x y => b.comb (swapSixWires x) (swapSixWires y)

theorem OrderedBranch.comb_pos (b : OrderedBranch P A F) :
    b.comb.PosSemidef := by
  rw [OrderedBranch.comb, circuitComb_decomposition]
  exact sum_rankOne_pos _

theorem OrderedBranch.reverseComb_decomposition (b : OrderedBranch P A F) :
    b.reverseComb = ∑ k : b.K,
      rankOne (fun x => (postLift b.post k *ᵥ preMiddle b.pre b.mid) (swapSixWires x)) := by
  ext x y
  simp [OrderedBranch.reverseComb, OrderedBranch.comb, circuitComb_decomposition,
    rankOne, Matrix.vecMulVec_apply, Matrix.sum_apply]

theorem OrderedBranch.reverseComb_pos (b : OrderedBranch P A F) :
    b.reverseComb.PosSemidef := by
  rw [b.reverseComb_decomposition]
  exact sum_rankOne_pos _

theorem OrderedBranch.comb_trace (b : OrderedBranch P A F) :
    partialTrace b.comb = Matrix.kronecker b.comb₂ (1 : Matrix A A ℂ) :=
  circuitComb_trace b.pre b.mid b.post b.post_isometry

theorem OrderedBranch.comb₂_trace (b : OrderedBranch P A F) :
    partialTrace b.comb₂ = Matrix.kronecker b.comb₁ (1 : Matrix A A ℂ) :=
  preMiddle_trace b.pre b.mid b.mid_isometry

variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]

/-- Total `A ≺ B` comb operator summed over a finite family of branches. -/
def familyCombAB (bAB : J₁ → OrderedBranch P A F) :
    Matrix (SixWires P A F) (SixWires P A F) ℂ :=
  ∑ j, (bAB j).comb

def familyComb₂AB (bAB : J₁ → OrderedBranch P A F) :
    Matrix (FourWires P A) (FourWires P A) ℂ :=
  ∑ j, (bAB j).comb₂

def familyComb₁AB (bAB : J₁ → OrderedBranch P A F) :
    Matrix (P × A) (P × A) ℂ :=
  ∑ j, (bAB j).comb₁

/-- Total `B ≺ A` comb operator summed over a finite family of reverse branches. -/
def familyCombBA (bBA : J₂ → OrderedBranch P A F) :
    Matrix (SixWires P A F) (SixWires P A F) ℂ :=
  ∑ j, (bBA j).reverseComb

def familyComb₂BA (bBA : J₂ → OrderedBranch P A F) :
    Matrix (FourWires P A) (FourWires P A) ℂ :=
  ∑ j, (bBA j).comb₂

def familyComb₁BA (bBA : J₂ → OrderedBranch P A F) :
    Matrix (P × A) (P × A) ℂ :=
  ∑ j, (bBA j).comb₁

theorem familyCombAB_pos (bAB : J₁ → OrderedBranch P A F) :
    (familyCombAB bAB).PosSemidef := by
  have h : familyCombAB bAB = ∑ z : (j : J₁) × (bAB j).K,
      rankOne (postLift (bAB z.1).post z.2 *ᵥ preMiddle (bAB z.1).pre (bAB z.1).mid) := by
    simp [familyCombAB, OrderedBranch.comb, circuitComb_decomposition, Fintype.sum_sigma]
  rw [h]
  exact sum_rankOne_pos _

theorem familyCombBA_pos (bBA : J₂ → OrderedBranch P A F) :
    (familyCombBA bBA).PosSemidef := by
  have h : familyCombBA bBA = ∑ z : (j : J₂) × (bBA j).K,
      rankOne (fun x => (postLift (bBA z.1).post z.2 *ᵥ
        preMiddle (bBA z.1).pre (bBA z.1).mid) (swapSixWires x)) := by
    simp [familyCombBA, OrderedBranch.reverseComb_decomposition, Fintype.sum_sigma]
  rw [h]
  exact sum_rankOne_pos _

theorem partialTrace_sum {I J α : Type*} [Fintype I] [Fintype J] [Fintype α]
    (C : α → Matrix (I × J) (I × J) ℂ) :
    partialTrace (∑ a, C a) = ∑ a, partialTrace (C a) := by
  ext i j
  simp only [partialTrace, Matrix.sum_apply]
  exact Finset.sum_comm

omit [Fintype A] in
theorem kronecker_sum_left {I α : Type*} [Fintype I] [Fintype α]
    (C : α → Matrix I I ℂ) :
    Matrix.kronecker (∑ a, C a) (1 : Matrix A A ℂ) =
      ∑ a, Matrix.kronecker (C a) (1 : Matrix A A ℂ) := by
  ext ⟨i₁, a₁⟩ ⟨i₂, a₂⟩
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

theorem familyCombAB_trace (bAB : J₁ → OrderedBranch P A F) :
    partialTrace (familyCombAB bAB) =
      Matrix.kronecker (familyComb₂AB bAB) (1 : Matrix A A ℂ) := by
  unfold familyCombAB familyComb₂AB
  rw [partialTrace_sum, kronecker_sum_left]
  simp_rw [OrderedBranch.comb_trace]

theorem familyComb₂AB_trace (bAB : J₁ → OrderedBranch P A F) :
    partialTrace (familyComb₂AB bAB) =
      Matrix.kronecker (familyComb₁AB bAB) (1 : Matrix A A ℂ) := by
  unfold familyComb₂AB familyComb₁AB
  rw [partialTrace_sum, kronecker_sum_left]
  simp_rw [OrderedBranch.comb₂_trace]

theorem familyCombBA_swapped_trace (bBA : J₂ → OrderedBranch P A F) :
    partialTrace (fun x y => familyCombBA bBA (swapSixWires x) (swapSixWires y)) =
      Matrix.kronecker (familyComb₂BA bBA) (1 : Matrix A A ℂ) := by
  have hswap : (fun x y => familyCombBA bBA (swapSixWires x) (swapSixWires y)) =
      ∑ j, (bBA j).comb := by
    ext x y
    simp [familyCombBA, OrderedBranch.reverseComb, swapSixWires_involutive, Matrix.sum_apply]
  rw [hswap, partialTrace_sum, familyComb₂BA, kronecker_sum_left]
  simp_rw [OrderedBranch.comb_trace]

theorem familyComb₂BA_trace (bBA : J₂ → OrderedBranch P A F) :
    partialTrace (familyComb₂BA bBA) =
      Matrix.kronecker (familyComb₁BA bBA) (1 : Matrix A A ℂ) := by
  unfold familyComb₂BA familyComb₁BA
  rw [partialTrace_sum, kronecker_sum_left]
  simp_rw [OrderedBranch.comb₂_trace]

/-- Total weight of the first-query instrument branches of a two-query normal form
that select query order `o`. -/
def orderBranchWeight {M : Type} [Fintype M] [DecidableEq M]
    (R : ICO.TwoQueryTree.NormalForm P (A × M) F) (o : ICO.TwoQueryTree.Order) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b : R.Branch => R.order b = o),
    krausWeight (R.pre.op b)

theorem orderBranchWeight_nonneg {M : Type} [Fintype M] [DecidableEq M]
    (R : ICO.TwoQueryTree.NormalForm P (A × M) F) (o : ICO.TwoQueryTree.Order) :
    0 ≤ orderBranchWeight R o :=
  Finset.sum_nonneg (fun b _ => krausWeight_nonneg (R.pre.op b))

theorem orderBranchWeight_sum [Nonempty P] {M : Type} [Fintype M] [DecidableEq M]
    (R : ICO.TwoQueryTree.NormalForm P (A × M) F) :
    orderBranchWeight R .firstThenSecond + orderBranchWeight R .secondThenFirst = 1 := by
  unfold orderBranchWeight
  have hdisj : Disjoint
      (Finset.univ.filter (fun b : R.Branch => R.order b = .firstThenSecond))
      (Finset.univ.filter (fun b : R.Branch => R.order b = .secondThenFirst)) := by
    rw [Finset.disjoint_filter]
    intro b _ h1 h2
    rw [h1] at h2
    cases h2
  rw [← Finset.sum_union hdisj]
  have hunion :
      (Finset.univ.filter (fun b : R.Branch => R.order b = .firstThenSecond)) ∪
      (Finset.univ.filter (fun b : R.Branch => R.order b = .secondThenFirst)) =
      Finset.univ := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases R.order b <;> simp
  rw [hunion]
  exact instrument_weights_sum R.pre

/-- Lemma 5 (`lem:ordered`) as a single combined statement in general dimension:
1. Every two-call adaptive circuit `tree : QueryTree (A × M) F P` dilates to the
   sum of its `A ≺ B` and `B ≺ A` isometric Stinespring branches (`tree_channel`),
   and its box-independent first-query probabilities `p_{A≺B}` and `p_{B≺A}` are
   nonnegative and sum to `1` (`orderBranchWeight_sum`).
2. The summed ordered comb operators `C_{A≺B} = familyCombAB bAB` and
   `C_{B≺A} = familyCombBA bBA` are positive semidefinite and satisfy the
   homogeneous comb partial-trace constraints (`eq:ordered-comb`). -/
theorem ordered_components_decomposition [Nonempty P]
    {M I T : Type} [Fintype M] [DecidableEq M] [Fintype I] [DecidableEq I]
    [Fintype T] [DecidableEq T]
    (tree : QueryTree (A × M) F P)
    (U : I → CMatrix A) (V : T → CMatrix A)
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) (X : CMatrix P)
    (bAB : J₁ → OrderedBranch P A F) (bBA : J₂ → OrderedBranch P A F) :
    ((tree.channel (oracleChannel U hU) (oracleChannel V hV)).map X =
      ∑ b : tree.normalForm.Branch, ∑ i, ∑ j,
        ICO.TwoQueryDilation.branchMap tree.normalForm b (U i) (V j) X) ∧
    (0 ≤ orderBranchWeight tree.normalForm .firstThenSecond ∧
     0 ≤ orderBranchWeight tree.normalForm .secondThenFirst ∧
     orderBranchWeight tree.normalForm .firstThenSecond +
       orderBranchWeight tree.normalForm .secondThenFirst = 1) ∧
    (familyCombAB bAB).PosSemidef ∧
    (familyCombBA bBA).PosSemidef ∧
    (partialTrace (familyCombAB bAB) =
      Matrix.kronecker (familyComb₂AB bAB) (1 : Matrix A A ℂ) ∧
     partialTrace (familyComb₂AB bAB) =
      Matrix.kronecker (familyComb₁AB bAB) (1 : Matrix A A ℂ)) ∧
    (partialTrace (fun x y => familyCombBA bBA (swapSixWires x) (swapSixWires y)) =
      Matrix.kronecker (familyComb₂BA bBA) (1 : Matrix A A ℂ) ∧
     partialTrace (familyComb₂BA bBA) =
      Matrix.kronecker (familyComb₁BA bBA) (1 : Matrix A A ℂ)) :=
  ⟨tree_channel tree U V hU hV X,
   ⟨orderBranchWeight_nonneg tree.normalForm .firstThenSecond,
    orderBranchWeight_nonneg tree.normalForm .secondThenFirst,
    orderBranchWeight_sum tree.normalForm⟩,
   familyCombAB_pos bAB,
   familyCombBA_pos bBA,
   ⟨familyCombAB_trace bAB, familyComb₂AB_trace bAB⟩,
   ⟨familyCombBA_swapped_trace bBA, familyComb₂BA_trace bBA⟩⟩

/-- Specialization of `ordered_components_decomposition` to oracle dimension `Fin d`. -/
theorem ordered_components_decomposition_dim_d (d : Nat) [Nonempty P]
    {M I T : Type} [Fintype M] [DecidableEq M] [Fintype I] [DecidableEq I]
    [Fintype T] [DecidableEq T]
    (tree : QueryTree (Fin d × M) F P)
    (U : I → CMatrix (Fin d)) (V : T → CMatrix (Fin d))
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) (X : CMatrix P)
    (bAB : J₁ → OrderedBranch P (Fin d) F) (bBA : J₂ → OrderedBranch P (Fin d) F) :
    ((tree.channel (oracleChannel U hU) (oracleChannel V hV)).map X =
      ∑ b : tree.normalForm.Branch, ∑ i, ∑ j,
        ICO.TwoQueryDilation.branchMap tree.normalForm b (U i) (V j) X) ∧
    (0 ≤ orderBranchWeight tree.normalForm .firstThenSecond ∧
     0 ≤ orderBranchWeight tree.normalForm .secondThenFirst ∧
     orderBranchWeight tree.normalForm .firstThenSecond +
       orderBranchWeight tree.normalForm .secondThenFirst = 1) ∧
    (familyCombAB bAB).PosSemidef ∧
    (familyCombBA bBA).PosSemidef ∧
    (partialTrace (familyCombAB bAB) =
      Matrix.kronecker (familyComb₂AB bAB) (1 : Matrix (Fin d) (Fin d) ℂ) ∧
     partialTrace (familyComb₂AB bAB) =
      Matrix.kronecker (familyComb₁AB bAB) (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
    (partialTrace (fun x y => familyCombBA bBA (swapSixWires x) (swapSixWires y)) =
      Matrix.kronecker (familyComb₂BA bBA) (1 : Matrix (Fin d) (Fin d) ℂ) ∧
     partialTrace (familyComb₂BA bBA) =
      Matrix.kronecker (familyComb₁BA bBA) (1 : Matrix (Fin d) (Fin d) ℂ)) :=
  ordered_components_decomposition tree U V hU hV X bAB bBA

/-- Zero out the preprocessing operator of an ordered branch while retaining its
isometric middle and final continuations. -/
def OrderedBranch.zeroPre (b : OrderedBranch P A F) : OrderedBranch P A F :=
  { b with pre := 0 }

theorem OrderedBranch.zeroPre_comb (b : OrderedBranch P A F) :
    b.zeroPre.comb = 0 := by
  have hpm : preMiddle (0 : Matrix (A × b.M) P ℂ) b.mid = 0 := by
    funext hn
    have hi : insertWire hn.1.1.2
        (fun m : b.M => (0 : Matrix (A × b.M) P ℂ) (hn.1.1.1.2, m) hn.1.1.1.1) = 0 := by
      funext am
      simp [insertWire]
    unfold preMiddle
    rw [hi, Matrix.mulVec_zero]
    rfl
  change circuitComb (0 : Matrix (A × b.M) P ℂ) b.mid b.post = 0
  rw [circuitComb_decomposition, hpm]
  ext x y
  simp [Matrix.mulVec_zero, rankOne]

theorem OrderedBranch.zeroPre_reverseComb (b : OrderedBranch P A F) :
    b.zeroPre.reverseComb = 0 := by
  ext x y
  simp [OrderedBranch.reverseComb, OrderedBranch.zeroPre_comb]

theorem OrderedBranch.zeroPre_comb₁ (b : OrderedBranch P A F) :
    b.zeroPre.comb₁ = 0 := by
  ext pa qb
  simp [OrderedBranch.comb₁, OrderedBranch.zeroPre, preComb, dotProduct]

/-- Choi vectorization `(p, f) ↦ T f p` matching `QIT.MatrixMap.choi`. -/
def vecPF (T : Matrix F P ℂ) : P × F → ℂ :=
  fun pf => T pf.2 pf.1

theorem choi_ofKraus_eq_sum_rankOne {κ : Type*} [Fintype κ] (K : κ → Matrix F P ℂ) :
    MatrixMap.choi (MatrixMap.ofKraus K) = ∑ k : κ, rankOne (vecPF (K k)) := by
  ext ⟨p, f⟩ ⟨p', f'⟩
  simp only [MatrixMap.choi, MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
    rankOne, Matrix.vecMulVec_apply, Pi.star_apply, vecPF]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single p']
  · rw [Finset.sum_eq_single p]
    · simp
    · intro r _ hr
      simp [hr.symm]
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  · intro q _ hq
    simp [hq.symm]
  · intro hp'
    exact absurd (Finset.mem_univ p') hp'

/-- General-dimension comb link matrix `L(U, V)` contracting the two oracle slots
`(ai, ao)` and `(bi, bo)` of `SixWires P A F` with Kraus matrices `U, V : CMatrix A`
to produce Choi vectors on `P × F`. -/
def combLink (U V : CMatrix A) : Matrix (P × F) (SixWires P A F) ℂ :=
  fun pf x =>
    if pf.1 = x.1.1.1.1.1 ∧ pf.2 = x.2 then
      U x.1.1.1.2 x.1.1.1.1.2 * V x.1.2 x.1.1.2
    else 0

omit [DecidableEq A] in
theorem combLink_mulVec (U V : CMatrix A) (v : SixWires P A F → ℂ) (p : P) (f : F) :
    (combLink U V *ᵥ v) (p, f) =
      ∑ ai : A, ∑ ao : A, ∑ bi : A, ∑ bo : A,
        U ao ai * V bo bi * v (((((p, ai), ao), bi), bo), f) := by
  simp only [Matrix.mulVec, dotProduct, combLink, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p]
  · simp only [true_and]
    apply Finset.sum_congr rfl; intro ai _
    apply Finset.sum_congr rfl; intro ao _
    apply Finset.sum_congr rfl; intro bi _
    apply Finset.sum_congr rfl; intro bo _
    rw [Finset.sum_eq_single f]
    · simp
    · intro f' _ hf'
      simp [hf'.symm]
    · intro hf
      exact absurd (Finset.mem_univ f) hf
  · intro p' _ hp'
    simp [hp'.symm]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

/-- Equivalence on `SixWires P A F` induced by swapping the two oracle slots. -/
def swapSixWiresEquiv : SixWires P A F ≃ SixWires P A F where
  toFun := swapSixWires
  invFun := swapSixWires
  left_inv := swapSixWires_involutive
  right_inv := swapSixWires_involutive

omit [Fintype P] [Fintype A] [Fintype F] [DecidableEq A] in
theorem combLink_swap (U V : CMatrix A) (pf : P × F) (x : SixWires P A F) :
    combLink U V pf x = combLink V U pf (swapSixWires x) := by
  rcases x with ⟨⟨⟨⟨⟨p', ai⟩, ao⟩, bi⟩, bo⟩, f'⟩
  simp only [combLink, swapSixWires]
  split_ifs <;> ring

omit [Fintype P] [Fintype F] [DecidableEq P] [DecidableEq A] [DecidableEq F] in
theorem mul_kronecker_one_entry {R N' : Type*} [Fintype N'] [DecidableEq N']
    (X : Matrix R (A × N') ℂ) (U : CMatrix A) (r : R) (a : A) (n : N') :
    (X * Matrix.kronecker U (1 : CMatrix N')) r (a, n) =
      ∑ b : A, X r (b, n) * U b a := by
  simp [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type]

theorem allChannel_circuitKraus_entry (b : OrderedBranch P A F)
    (U V : CMatrix A) (k : b.K) (f : F) (p : P) :
    ICO.AllChannelDilation.circuitKraus b.pre b.mid b.post U V k f p =
      ∑ ai : A, ∑ m : b.M, ∑ ao : A, ∑ bi : A, ∑ n : b.N, ∑ bo : A,
        b.post (f, k) (bo, n) * V bo bi * b.mid (bi, n) (ao, m) *
          U ao ai * b.pre (ai, m) p := by
  have hm (ao : A) (m : b.M) :
      ((ICO.AllChannelDilation.postKraus b.post k *
          Matrix.kronecker V (1 : CMatrix b.N)) * b.mid) f (ao, m) =
        ∑ bi : A, ∑ n : b.N, ∑ bo : A,
          b.post (f, k) (bo, n) * V bo bi * b.mid (bi, n) (ao, m) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp_rw [mul_kronecker_one_entry]
    simp only [ICO.AllChannelDilation.postKraus, Finset.sum_mul]
  unfold ICO.AllChannelDilation.circuitKraus
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [mul_kronecker_one_entry, hm]
  simp only [Finset.sum_mul]

theorem branchVector_entry (b : OrderedBranch P A F) (k : b.K)
    (p : P) (ai ao bi bo : A) (f : F) :
    (postLift b.post k *ᵥ preMiddle b.pre b.mid) (((((p, ai), ao), bi), bo), f) =
      ∑ n : b.N, ∑ m : b.M, b.post (f, k) (bo, n) * b.mid (bi, n) (ao, m) * b.pre (ai, m) p := by
  simp [postLift, preMiddle, insertWire, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem combLink_branchVector (b : OrderedBranch P A F)
    (U V : CMatrix A) (k : b.K) :
    combLink U V *ᵥ (postLift b.post k *ᵥ preMiddle b.pre b.mid) =
      vecPF (ICO.AllChannelDilation.circuitKraus b.pre b.mid b.post U V k) := by
  funext ⟨p, f⟩
  rw [combLink_mulVec, vecPF, allChannel_circuitKraus_entry]
  simp only [branchVector_entry, Finset.mul_sum]
  let perm : (A × A × A × A × b.N × b.M) ≃ (A × b.M × A × A × b.N × A) :=
    { toFun := fun x => (x.1, x.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.1)
      invFun := fun x => (x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2, x.2.2.2.2.1, x.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs := perm.sum_comp (fun x =>
    b.post (f, k) (x.2.2.2.2.2, x.2.2.2.2.1) *
      V x.2.2.2.2.2 x.2.2.2.1 * b.mid (x.2.2.2.1, x.2.2.2.2.1) (x.2.2.1, x.2.1) *
      U x.2.2.1 x.1 * b.pre (x.1, x.2.1) p)
  simp only [Fintype.sum_prod_type, perm, Equiv.coe_fn_mk] at hs
  rw [← hs]
  repeat' apply Finset.sum_congr rfl <;> intro _ _
  ring

theorem OrderedBranch.combLink_comb (b : OrderedBranch P A F) (U V : CMatrix A) :
    combLink U V * b.comb * (combLink U V)ᴴ =
      MatrixMap.choi (MatrixMap.ofKraus
        (ICO.AllChannelDilation.circuitKraus b.pre b.mid b.post U V)) := by
  rw [OrderedBranch.comb, circuitComb_decomposition, sum_rankOne_sandwich,
    choi_ofKraus_eq_sum_rankOne]
  simp_rw [combLink_branchVector]

theorem combLink_reverseBranchVector (b : OrderedBranch P A F)
    (U V : CMatrix A) (k : b.K) :
    combLink U V *ᵥ (fun x => (postLift b.post k *ᵥ preMiddle b.pre b.mid) (swapSixWires x)) =
      vecPF (ICO.AllChannelDilation.circuitKraus b.pre b.mid b.post V U k) := by
  rw [← combLink_branchVector b V U k]
  funext pf
  simp only [Matrix.mulVec, dotProduct, combLink_swap U V]
  exact swapSixWiresEquiv.sum_comp (fun x : SixWires P A F =>
    combLink V U pf x * (postLift b.post k *ᵥ preMiddle b.pre b.mid) x)

theorem OrderedBranch.combLink_reverseComb (b : OrderedBranch P A F) (U V : CMatrix A) :
    combLink U V * b.reverseComb * (combLink U V)ᴴ =
      MatrixMap.choi (MatrixMap.ofKraus
        (ICO.AllChannelDilation.circuitKraus b.pre b.mid b.post V U)) := by
  rw [b.reverseComb_decomposition, sum_rankOne_sandwich, choi_ofKraus_eq_sum_rankOne]
  simp_rw [combLink_reverseBranchVector]

/-- Underlying Stinespring ordered branch extracted from branch `b` of a two-query
normal form `R : NormalForm P (A × M) F`. -/
def normalBaseBranch {M : Type} [Fintype M] [DecidableEq M]
    (R : ICO.TwoQueryTree.NormalForm P (A × M) F) (b : R.Branch) :
    OrderedBranch P A F where
  M := M
  N := M × (R.rest b).Branch
  K := (((A × M) × F) × (R.rest b).Branch)
  pre := R.pre.op b
  mid := ICO.AllChannelDilation.normalMid (R.rest b)
  post := ICO.AllChannelDilation.normalPost (R.rest b)
  mid_isometry := ICO.AllChannelDilation.normalMid_complete (R.rest b)
  post_isometry := ICO.AllChannelDilation.normalPost_complete (R.rest b)

/-- `A ≺ B` component branch of `R` at classical branch `b`. -/
def normalABBranch {M : Type} [Fintype M] [DecidableEq M]
    (R : ICO.TwoQueryTree.NormalForm P (A × M) F) (b : R.Branch) :
    OrderedBranch P A F :=
  if R.order b = .firstThenSecond then normalBaseBranch R b
  else (normalBaseBranch R b).zeroPre

/-- `B ≺ A` component branch of `R` at classical branch `b`. -/
def normalBABranch {M : Type} [Fintype M] [DecidableEq M]
    (R : ICO.TwoQueryTree.NormalForm P (A × M) F) (b : R.Branch) :
    OrderedBranch P A F :=
  if R.order b = .firstThenSecond then (normalBaseBranch R b).zeroPre
  else normalBaseBranch R b

/-- Concrete `A ≺ B` six-wire comb operator `C_{A≺B}` of a two-call adaptive tree `tree`. -/
def treeCombAB {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) : Matrix (SixWires P A F) (SixWires P A F) ℂ :=
  familyCombAB (normalABBranch tree.normalForm)

def treeComb₂AB {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) : Matrix (FourWires P A) (FourWires P A) ℂ :=
  familyComb₂AB (normalABBranch tree.normalForm)

def treeComb₁AB {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) : Matrix (P × A) (P × A) ℂ :=
  familyComb₁AB (normalABBranch tree.normalForm)

/-- Concrete `B ≺ A` six-wire comb operator `C_{B≺A}` of a two-call adaptive tree `tree`. -/
def treeCombBA {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) : Matrix (SixWires P A F) (SixWires P A F) ℂ :=
  familyCombBA (normalBABranch tree.normalForm)

def treeComb₂BA {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) : Matrix (FourWires P A) (FourWires P A) ℂ :=
  familyComb₂BA (normalBABranch tree.normalForm)

def treeComb₁BA {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) : Matrix (P × A) (P × A) ℂ :=
  familyComb₁BA (normalBABranch tree.normalForm)

/-- Total process Choi/comb operator `C = C_{A≺B} + C_{B≺A}` of `tree`. -/
def treeTotalComb {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) : Matrix (SixWires P A F) (SixWires P A F) ℂ :=
  treeCombAB tree + treeCombBA tree

/-- For a fixed input state `ρ : State P`, the probability that the first oracle call
of `tree` goes to order `o` (`A ≺ B` or `B ≺ A`), independent of the oracle boxes. -/
def orderStateProb {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) (ρ : State P) (o : ICO.TwoQueryTree.Order) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b : tree.normalForm.Branch => tree.normalForm.order b = o),
    ((tree.normalForm.pre.op b) * ρ.matrix * (tree.normalForm.pre.op b)ᴴ).trace.re

theorem orderStateProb_nonneg {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) (ρ : State P) (o : ICO.TwoQueryTree.Order) :
    0 ≤ orderStateProb tree ρ o :=
  Finset.sum_nonneg fun b _ =>
    (ρ.pos.mul_mul_conjTranspose_same (tree.normalForm.pre.op b)).trace_nonneg.1

theorem orderStateProb_sum {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) (ρ : State P) :
    orderStateProb tree ρ .firstThenSecond + orderStateProb tree ρ .secondThenFirst = 1 := by
  unfold orderStateProb
  have hdisj : Disjoint
      (Finset.univ.filter (fun b : tree.normalForm.Branch =>
        tree.normalForm.order b = .firstThenSecond))
      (Finset.univ.filter (fun b : tree.normalForm.Branch =>
        tree.normalForm.order b = .secondThenFirst)) := by
    rw [Finset.disjoint_filter]
    intro b _ h1 h2
    rw [h1] at h2
    cases h2
  rw [← Finset.sum_union hdisj]
  have hunion :
      (Finset.univ.filter (fun b : tree.normalForm.Branch =>
        tree.normalForm.order b = .firstThenSecond)) ∪
      (Finset.univ.filter (fun b : tree.normalForm.Branch =>
        tree.normalForm.order b = .secondThenFirst)) = Finset.univ := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases tree.normalForm.order b <;> simp
  rw [hunion, ← Complex.re_sum, ← Matrix.trace_sum]
  have hI : MatrixMap.krausAdjoint tree.normalForm.pre.op (1 : CMatrix (A × M)) = 1 := by
    simpa [MatrixMap.krausAdjoint] using tree.normalForm.pre.complete
  have htr : (∑ x : tree.normalForm.Branch,
      tree.normalForm.pre.op x * ρ.matrix * (tree.normalForm.pre.op x)ᴴ).trace =
      ρ.matrix.trace :=
    MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one
      tree.normalForm.pre.op hI ρ.matrix
  rw [htr, ρ.trace_re_eq_one]

theorem partialTrace_zero {I J : Type*} [Fintype J] :
    partialTrace (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  ext i j
  simp [partialTrace]

omit [Fintype P] [DecidableEq P] [DecidableEq A] in
theorem partialTrace_preComb_transpose {M' : Type*} [Fintype M']
    (pre : Matrix (A × M') P ℂ) :
    (partialTrace (preComb pre)).transpose = preᴴ * pre := by
  ext p q
  simp [partialTrace, preComb, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, mul_comm]

theorem treeComb₁AB_state_prob {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) (ρ : State P) :
    ((partialTrace (treeComb₁AB tree)).transpose * ρ.matrix).trace.re =
      orderStateProb tree ρ .firstThenSecond := by
  unfold treeComb₁AB familyComb₁AB orderStateProb
  rw [partialTrace_sum, Matrix.transpose_sum, Finset.sum_mul,
    Matrix.trace_sum, Complex.re_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ho : tree.normalForm.order b = .firstThenSecond
  · have hb : normalABBranch tree.normalForm b = normalBaseBranch tree.normalForm b :=
      if_pos ho
    rw [hb]
    simp only [OrderedBranch.comb₁, normalBaseBranch, partialTrace_preComb_transpose, if_pos ho]
    have hcyc : ((tree.normalForm.pre.op b)ᴴ * tree.normalForm.pre.op b * ρ.matrix).trace =
        (tree.normalForm.pre.op b * ρ.matrix * (tree.normalForm.pre.op b)ᴴ).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    exact congrArg Complex.re hcyc
  · have hb : normalABBranch tree.normalForm b = (normalBaseBranch tree.normalForm b).zeroPre :=
      if_neg ho
    rw [hb, OrderedBranch.zeroPre_comb₁, partialTrace_zero]
    simp [if_neg ho]

theorem treeComb₁BA_state_prob {M : Type} [Fintype M] [DecidableEq M]
    (tree : QueryTree (A × M) F P) (ρ : State P) :
    ((partialTrace (treeComb₁BA tree)).transpose * ρ.matrix).trace.re =
      orderStateProb tree ρ .secondThenFirst := by
  unfold treeComb₁BA familyComb₁BA orderStateProb
  rw [partialTrace_sum, Matrix.transpose_sum, Finset.sum_mul,
    Matrix.trace_sum, Complex.re_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  cases ho : tree.normalForm.order b with
  | firstThenSecond =>
    have hb : normalBABranch tree.normalForm b = (normalBaseBranch tree.normalForm b).zeroPre := by
      simp [normalBABranch, ho]
    rw [hb, OrderedBranch.zeroPre_comb₁, partialTrace_zero]
    simp
  | secondThenFirst =>
    have hb : normalBABranch tree.normalForm b = normalBaseBranch tree.normalForm b := by
      simp [normalBABranch, ho]
    rw [hb]
    simp only [OrderedBranch.comb₁, normalBaseBranch, partialTrace_preComb_transpose, if_true]
    have hcyc : ((tree.normalForm.pre.op b)ᴴ * tree.normalForm.pre.op b * ρ.matrix).trace =
        (tree.normalForm.pre.op b * ρ.matrix * (tree.normalForm.pre.op b)ᴴ).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    exact congrArg Complex.re hcyc

theorem normalForm_branch_combLink {M : Type} [Fintype M] [DecidableEq M]
    (R : ICO.TwoQueryTree.NormalForm P (A × M) F) (b : R.Branch) (U V : CMatrix A) :
    combLink U V * (normalABBranch R b).comb * (combLink U V)ᴴ +
      combLink U V * (normalBABranch R b).reverseComb * (combLink U V)ᴴ =
        MatrixMap.choi (ICO.TwoQueryDilation.branchMap R b U V) := by
  cases ho : R.order b with
  | firstThenSecond =>
    simp only [normalABBranch, normalBABranch, ho, if_true,
      OrderedBranch.zeroPre_reverseComb, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      ICO.TwoQueryDilation.branchMap]
    exact (normalBaseBranch R b).combLink_comb U V
  | secondThenFirst =>
    simp only [normalABBranch, normalBABranch, ho, reduceCtorEq, if_false,
      OrderedBranch.zeroPre_comb, Matrix.mul_zero, Matrix.zero_mul, zero_add,
      ICO.TwoQueryDilation.branchMap]
    exact (normalBaseBranch R b).combLink_reverseComb U V

theorem treeComb_choi_link
    {M I T : Type} [Fintype M] [DecidableEq M] [Fintype I] [DecidableEq I]
    [Fintype T] [DecidableEq T]
    (tree : QueryTree (A × M) F P)
    (U : I → CMatrix A) (V : T → CMatrix A)
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) :
    MatrixMap.choi ((tree.channel (oracleChannel U hU) (oracleChannel V hV)).map) =
      ∑ i, ∑ j,
        combLink (U i) (V j) * treeTotalComb tree * (combLink (U i) (V j))ᴴ := by
  have hpair (u v : CMatrix A) :
      combLink u v * treeTotalComb tree * (combLink u v)ᴴ =
        ∑ b : tree.normalForm.Branch,
          MatrixMap.choi (ICO.TwoQueryDilation.branchMap tree.normalForm b u v) := by
    simp only [treeTotalComb, treeCombAB, treeCombBA, familyCombAB, familyCombBA,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
      ← Finset.sum_add_distrib, normalForm_branch_combLink]
  simp_rw [hpair]
  ext ⟨p, f⟩ ⟨p', f'⟩
  simp only [MatrixMap.choi, tree_channel tree U V hU hV, Matrix.sum_apply]
  conv_rhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  exact Finset.sum_comm.symm

/-- Lemma `lem:ordered` in general dimension `(P, A, F)` with `C_{A≺B}` and `C_{B≺A}`
constructed directly from the adaptive strategy `tree : QueryTree (A × M) F P`:
1. `C = C_{A≺B} + C_{B≺A}` (`treeTotalComb`) with `C_{A≺B} ≥ 0` and `C_{B≺A} ≥ 0`.
2. `C_{A≺B}` satisfies the homogeneous `A ≺ B` comb partial-trace equations
   (`eq:ordered-comb`), and `C_{B≺A}` satisfies the swapped `B ≺ A` comb equations.
3. Linking `C = C_{A≺B} + C_{B≺A}` via `combLink` against any complete Kraus families
   `(U, hU)` and `(V, hV)` equals `MatrixMap.choi ((tree.channel ...).map)`.
4. For any fixed input state `ρ : State P`, the box-independent first-call order
   probabilities `p_{A≺B} = orderStateProb tree ρ .firstThenSecond` and
   `p_{B≺A} = orderStateProb tree ρ .secondThenFirst` are nonnegative, sum to `1`,
   and equal the input-state marginals of `treeComb₁AB tree` and `treeComb₁BA tree`. -/
theorem tree_ordered_components
    {M I T : Type} [Fintype M] [DecidableEq M] [Fintype I] [DecidableEq I]
    [Fintype T] [DecidableEq T]
    (tree : QueryTree (A × M) F P) (ρ : State P)
    (U : I → CMatrix A) (V : T → CMatrix A)
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) :
    (treeTotalComb tree = treeCombAB tree + treeCombBA tree) ∧
    (treeCombAB tree).PosSemidef ∧
    (treeCombBA tree).PosSemidef ∧
    (partialTrace (treeCombAB tree) =
      Matrix.kronecker (treeComb₂AB tree) (1 : Matrix A A ℂ) ∧
     partialTrace (treeComb₂AB tree) =
      Matrix.kronecker (treeComb₁AB tree) (1 : Matrix A A ℂ)) ∧
    (partialTrace (fun x y => treeCombBA tree (swapSixWires x) (swapSixWires y)) =
      Matrix.kronecker (treeComb₂BA tree) (1 : Matrix A A ℂ) ∧
     partialTrace (treeComb₂BA tree) =
      Matrix.kronecker (treeComb₁BA tree) (1 : Matrix A A ℂ)) ∧
    (MatrixMap.choi ((tree.channel (oracleChannel U hU) (oracleChannel V hV)).map) =
      ∑ i, ∑ j, combLink (U i) (V j) * treeTotalComb tree * (combLink (U i) (V j))ᴴ) ∧
    (0 ≤ orderStateProb tree ρ .firstThenSecond ∧
     0 ≤ orderStateProb tree ρ .secondThenFirst ∧
     orderStateProb tree ρ .firstThenSecond + orderStateProb tree ρ .secondThenFirst = 1 ∧
     ((partialTrace (treeComb₁AB tree)).transpose * ρ.matrix).trace.re =
       orderStateProb tree ρ .firstThenSecond ∧
     ((partialTrace (treeComb₁BA tree)).transpose * ρ.matrix).trace.re =
       orderStateProb tree ρ .secondThenFirst) :=
  ⟨rfl,
   familyCombAB_pos (normalABBranch tree.normalForm),
   familyCombBA_pos (normalBABranch tree.normalForm),
   ⟨familyCombAB_trace (normalABBranch tree.normalForm),
    familyComb₂AB_trace (normalABBranch tree.normalForm)⟩,
   ⟨familyCombBA_swapped_trace (normalBABranch tree.normalForm),
    familyComb₂BA_trace (normalBABranch tree.normalForm)⟩,
   treeComb_choi_link tree U V hU hV,
   ⟨orderStateProb_nonneg tree ρ .firstThenSecond,
    orderStateProb_nonneg tree ρ .secondThenFirst,
    orderStateProb_sum tree ρ,
    treeComb₁AB_state_prob tree ρ,
    treeComb₁BA_state_prob tree ρ⟩⟩

/-- Specialization of `tree_ordered_components` to oracle dimension `Fin d`. -/
theorem tree_ordered_components_dim_d (d : Nat)
    {M I T : Type} [Fintype M] [DecidableEq M] [Fintype I] [DecidableEq I]
    [Fintype T] [DecidableEq T]
    (tree : QueryTree (Fin d × M) F P) (ρ : State P)
    (U : I → CMatrix (Fin d)) (V : T → CMatrix (Fin d))
    (hU : ∑ i, (U i)ᴴ * U i = 1) (hV : ∑ j, (V j)ᴴ * V j = 1) :
    (treeTotalComb tree = treeCombAB tree + treeCombBA tree) ∧
    (treeCombAB tree).PosSemidef ∧
    (treeCombBA tree).PosSemidef ∧
    (partialTrace (treeCombAB tree) =
      Matrix.kronecker (treeComb₂AB tree) (1 : Matrix (Fin d) (Fin d) ℂ) ∧
     partialTrace (treeComb₂AB tree) =
      Matrix.kronecker (treeComb₁AB tree) (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
    (partialTrace (fun x y => treeCombBA tree (swapSixWires x) (swapSixWires y)) =
      Matrix.kronecker (treeComb₂BA tree) (1 : Matrix (Fin d) (Fin d) ℂ) ∧
     partialTrace (treeComb₂BA tree) =
      Matrix.kronecker (treeComb₁BA tree) (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
    (MatrixMap.choi ((tree.channel (oracleChannel U hU) (oracleChannel V hV)).map) =
      ∑ i, ∑ j, combLink (U i) (V j) * treeTotalComb tree * (combLink (U i) (V j))ᴴ) ∧
    (0 ≤ orderStateProb tree ρ .firstThenSecond ∧
     0 ≤ orderStateProb tree ρ .secondThenFirst ∧
     orderStateProb tree ρ .firstThenSecond + orderStateProb tree ρ .secondThenFirst = 1 ∧
     ((partialTrace (treeComb₁AB tree)).transpose * ρ.matrix).trace.re =
       orderStateProb tree ρ .firstThenSecond ∧
     ((partialTrace (treeComb₁BA tree)).transpose * ρ.matrix).trace.re =
       orderStateProb tree ρ .secondThenFirst) :=
  tree_ordered_components tree ρ U V hU hV

end OrderedComponents

section FullPolarization
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Insert `a₀` into slot `i : Fin (m + 1)` and place `y : Fin m → E` into the
remaining slots via `Equiv.swap 0 i`. -/
def swapAt {m : Nat} (i : Fin (m + 1)) (a₀ : E) (y : Fin m → E) : Fin (m + 1) → E :=
  fun k => @Fin.cons m (fun _ => E) a₀ y (Equiv.swap 0 i k)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem swapAt_zero {m : Nat} (i : Fin (m + 1)) (a₀ : E) (y : Fin m → E) :
    swapAt i a₀ y (Equiv.swap 0 i 0) = a₀ := by
  simp [swapAt]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem swapAt_succ {m : Nat} (i : Fin (m + 1)) (a₀ : E) (y : Fin m → E) (j : Fin m) :
    swapAt i a₀ y (Equiv.swap 0 i j.succ) = y j := by
  simp [swapAt]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem swapAt_update {m : Nat} [DecidableEq (Fin m)] (i : Fin (m + 1)) (a₀ : E)
    (y : Fin m → E) (j : Fin m) (u : E) :
    Function.update (swapAt i a₀ y) (Equiv.swap 0 i j.succ) u =
      swapAt i a₀ (Function.update y j u) := by
  funext k
  obtain ⟨l, rfl⟩ := (Equiv.swap 0 i).surjective k
  refine Fin.cases ?_ ?_ l
  · have hne : Equiv.swap (0 : Fin (m + 1)) i 0 ≠ Equiv.swap 0 i j.succ :=
      (Equiv.swap 0 i).injective.ne (Fin.succ_ne_zero j).symm
    rw [Function.update_of_ne hne, swapAt_zero, swapAt_zero]
  · intro r
    by_cases h : r = j
    · subst r
      simp
    · have hne : Equiv.swap (0 : Fin (m + 1)) i r.succ ≠ Equiv.swap 0 i j.succ :=
        (Equiv.swap 0 i).injective.ne (fun h' => h (Fin.succ_inj.mp h'))
      rw [Function.update_of_ne hne, swapAt_succ, swapAt_succ, Function.update_of_ne h]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem swapAt_const {m : Nat} (i : Fin (m + 1)) (a₀ x : E) :
    swapAt i a₀ (fun _ : Fin m => x) =
      Function.update (fun _ : Fin (m + 1) => x) i a₀ := by
  funext k
  obtain ⟨l, rfl⟩ := (Equiv.swap 0 i).surjective k
  refine Fin.cases ?_ ?_ l
  · rw [swapAt_zero, Equiv.swap_apply_left, Function.update_self]
  · intro j
    have hne : Equiv.swap (0 : Fin (m + 1)) i j.succ ≠ i := by
      rw [← Equiv.swap_apply_left (0 : Fin (m + 1)) i]
      exact (Equiv.swap 0 i).injective.ne (Fin.succ_ne_zero j)
    rw [swapAt_succ, Function.update_of_ne hne]

/-- Fix slot `i : Fin (m + 1)` of a continuous `(m + 1)`-multilinear map to `a₀`,
producing a continuous `m`-multilinear map on the remaining slots. -/
def insertSlot {m : Nat}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) F)
    (i : Fin (m + 1)) (a₀ : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F where
  toFun y := f (swapAt i a₀ y)
  map_update_add' y j u v := by
    change f (swapAt i a₀ (Function.update y j (u + v))) =
      f (swapAt i a₀ (Function.update y j u)) +
      f (swapAt i a₀ (Function.update y j v))
    rw [← swapAt_update i a₀ y j (u + v),
      ← swapAt_update i a₀ y j u,
      ← swapAt_update i a₀ y j v]
    exact f.map_update_add _ _ _ _
  map_update_smul' y j c u := by
    change f (swapAt i a₀ (Function.update y j (c • u))) =
      c • f (swapAt i a₀ (Function.update y j u))
    rw [← swapAt_update i a₀ y j (c • u),
      ← swapAt_update i a₀ y j u]
    exact f.map_update_smul _ _ _ _
  cont := f.cont.comp (continuous_pi fun k => by
    obtain ⟨l, rfl⟩ := (Equiv.swap 0 i).surjective k
    refine Fin.cases ?_ ?_ l
    · simp only [swapAt_zero]
      exact continuous_const
    · intro j
      simp only [swapAt_succ]
      exact continuous_apply j)

@[simp] theorem insertSlot_apply {m : Nat}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) F)
    (i : Fin (m + 1)) (a₀ : E) (y : Fin m → E) :
    insertSlot f i a₀ y = f (swapAt i a₀ y) := rfl

@[simp] theorem fixA_apply {m n : Nat}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m ⊕ Fin n => E) F)
    (a : Fin m → E) (b : Fin n → E) :
    fixA f a b = f (Sum.elim a b) := rfl

/-- Inversion as an equivalence on `Equiv.Perm α`. -/
def permInvEquiv (α : Type*) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun π := π⁻¹
  invFun π := π⁻¹
  left_inv π := inv_inv π
  right_inv π := inv_inv π

/-- Bijection `Fin (m + 1) × Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin (m + 1))`
sending `(i, σ)` to the permutation `π` with `π i = 0` and
`π (Equiv.swap 0 i j.succ) = (σ j).succ`. -/
def permSuccEquiv (m : Nat) :
    Fin (m + 1) × Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin (m + 1)) :=
  (Equiv.prodCongr (Equiv.refl (Fin (m + 1))) (permInvEquiv (Fin m))).trans
    (Equiv.Perm.decomposeFin.symm.trans (permInvEquiv (Fin (m + 1))))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem comp_permSuccEquiv {m : Nat} (a : Fin (m + 1) → E)
    (i : Fin (m + 1)) (σ : Equiv.Perm (Fin m)) :
    a ∘ permSuccEquiv m (i, σ) =
      swapAt i (a 0) ((fun j : Fin m => a j.succ) ∘ σ) := by
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.Perm.decomposeFin.symm (i, σ.symm)
  change a ∘ ⇑τ.symm = _
  funext k
  obtain ⟨l, rfl⟩ := (Equiv.swap 0 i).surjective k
  refine Fin.cases ?_ ?_ l
  · have h0 : τ 0 = i := Equiv.Perm.decomposeFin_symm_apply_zero i σ.symm
    have hi : τ.symm i = 0 := by rw [← h0, Equiv.symm_apply_apply]
    rw [swapAt_zero]
    simp [Function.comp_apply, hi]
  · intro j
    have hj : τ (σ j).succ = Equiv.swap 0 i j.succ := by
      rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.symm_apply_apply]
    have hinv : τ.symm (Equiv.swap 0 i j.succ) = (σ j).succ := by
      rw [← hj, Equiv.symm_apply_apply]
    rw [swapAt_succ]
    simp [Function.comp_apply, hinv]

/-- Full single-slot-type polarization: if a continuous `m`-multilinear map `f`
agrees on the diagonal of a segment-closed set `C` with an affine function `L`,
then summing `f (a ∘ π)` over all permutations `π ∈ S_m` yields
`(m - 1)! • ∑ i, L (a i)`. -/
theorem sum_perm_one_slot {C : Set E}
    (hC : ∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (y - x) ∈ C) :
    ∀ {m : Nat}, 0 < m →
      ∀ (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F)
        (L : E → F),
        (∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          L (x + t • (y - x)) = L x + t • (L y - L x)) →
        (∀ x ∈ C, f (fun _ => x) = L x) →
        ∀ (a : Fin m → E), (∀ i, a i ∈ C) →
        (∑ π : Equiv.Perm (Fin m), f (a ∘ π)) =
          (m - 1).factorial • ∑ i : Fin m, L (a i)
  | 0, hm, _, _, _, _, _, _ => by omega
  | 1, _, f, L, _, hf, a, ha => by
    rw [Fin.sum_univ_one]
    have huniq : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by
      ext π
      simp [Subsingleton.elim π 1]
    rw [huniq, Finset.sum_singleton]
    have ha0 : a ∘ (1 : Equiv.Perm (Fin 1)) = fun _ : Fin 1 => a 0 := by
      funext i
      rw [Subsingleton.elim i 0]
      rfl
    rw [ha0, hf (a 0) (ha 0)]
    simp
  | m + 2, _, f, L, hL, hf, a, ha => by
    let g : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) F :=
      ∑ i : Fin (m + 2), insertSlot f i (a 0)
    let L' : E → F := fun x => L (a 0) + (m + 1) • L x
    have hL' : ∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        L' (x + t • (y - x)) = L' x + t • (L' y - L' x) := by
      intro x hx y hy t ht
      dsimp [L']
      rw [hL x hx y hy t ht]
      module
    have hg : ∀ x ∈ C, g (fun _ => x) = L' x := by
      intro x hx
      simp only [g, ContinuousMultilinearMap.sum_apply, insertSlot_apply, swapAt_const]
      have hseg : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
          f (fun _ => x + t • (a 0 - x)) = L x + t • (L (a 0) - L x) := by
        intro t ht
        rw [hf _ (hC x hx (a 0) (ha 0) t ht), hL x hx (a 0) (ha 0) t ht]
      simpa [L'] using sum_one_insert (Nat.zero_lt_succ (m + 1)) f x (a 0)
        (L x) (L (a 0)) hseg
    have ih := sum_perm_one_slot hC (Nat.zero_lt_succ m) g L' hL' hg
      (fun j : Fin (m + 1) => a j.succ) (fun j => ha j.succ)
    have hperm : (∑ π : Equiv.Perm (Fin (m + 2)), f (a ∘ π)) =
        ∑ σ : Equiv.Perm (Fin (m + 1)), g ((fun j : Fin (m + 1) => a j.succ) ∘ σ) := by
      rw [← (permSuccEquiv (m + 1)).sum_comp (fun π => f (a ∘ π))]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [g, ContinuousMultilinearMap.sum_apply, insertSlot_apply, comp_permSuccEquiv]
    rw [hperm, ih]
    have hsum : (∑ j : Fin (m + 1), L' (a j.succ)) =
        (m + 1) • ∑ i : Fin (m + 2), L (a i) := by
      dsimp [L']
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Finset.smul_sum, ← smul_add,
        ← Fin.sum_univ_succ (f := fun i : Fin (m + 2) => L (a i))]
    have hfac : m.factorial * (m + 1) = (m + 1).factorial := by
      rw [mul_comm]
      exact Nat.mul_factorial_pred (Nat.succ_ne_zero m)
    rw [hsum, smul_smul]
    change (m.factorial * (m + 1)) • ∑ i : Fin (m + 2), L (a i) =
      (m + 1).factorial • ∑ i : Fin (m + 2), L (a i)
    rw [hfac]

/-- Full two-slot-type polarization: if `f` is multilinear in `m` slots of type
`A` and `n` slots of type `B` and matches a segment-biaffine target `S` on
identical inputs `(fun _ => x, fun _ => y)`, then summing over all slot
permutations `(π, σ) ∈ S_m × S_n` gives `((m - 1)! * (n - 1)!) • ∑ i, ∑ j, S (a i) (b j)`. -/
theorem sum_perm_two_slot {CA CB : Set E}
    (hCA : ∀ x ∈ CA, ∀ y ∈ CA, ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (y - x) ∈ CA)
    (hCB : ∀ x ∈ CB, ∀ y ∈ CB, ∀ s ∈ Set.Icc (0 : ℝ) 1, x + s • (y - x) ∈ CB)
    {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m ⊕ Fin n => E) F)
    (S : E → E → F)
    (hSA : ∀ y ∈ CB, ∀ x₁ ∈ CA, ∀ x₂ ∈ CA, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      S (x₁ + t • (x₂ - x₁)) y = S x₁ y + t • (S x₂ y - S x₁ y))
    (hSB : ∀ x ∈ CA, ∀ y₁ ∈ CB, ∀ y₂ ∈ CB, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      S x (y₁ + s • (y₂ - y₁)) = S x y₁ + s • (S x y₂ - S x y₁))
    (hf : ∀ x ∈ CA, ∀ y ∈ CB, f (Sum.elim (fun _ => x) (fun _ => y)) = S x y)
    (a : Fin m → E) (ha : ∀ i, a i ∈ CA)
    (b : Fin n → E) (hb : ∀ j, b j ∈ CB) :
    (∑ π : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin n),
      f (Sum.elim (a ∘ π) (b ∘ σ))) =
      ((m - 1).factorial * (n - 1).factorial) •
        ∑ i : Fin m, ∑ j : Fin n, S (a i) (b j) := by
  let g : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F :=
    ∑ π : Equiv.Perm (Fin m), fixA f (a ∘ π)
  let L : E → F := fun y => (m - 1).factorial • ∑ i : Fin m, S (a i) y
  have hL : ∀ y₁ ∈ CB, ∀ y₂ ∈ CB, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      L (y₁ + s • (y₂ - y₁)) = L y₁ + s • (L y₂ - L y₁) := by
    intro y₁ hy₁ y₂ hy₂ s hs
    dsimp [L]
    have hsum : (∑ i : Fin m, S (a i) (y₁ + s • (y₂ - y₁))) =
        (∑ i : Fin m, S (a i) y₁) + s • ((∑ i : Fin m, S (a i) y₂) - ∑ i : Fin m, S (a i) y₁) := by
      simp_rw [hSB _ (ha _) y₁ hy₁ y₂ hy₂ s hs]
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_sub_distrib]
    rw [hsum]
    module
  have hg : ∀ y ∈ CB, g (fun _ => y) = L y := by
    intro y hy
    simp only [g, ContinuousMultilinearMap.sum_apply]
    exact sum_perm_one_slot hCA hm (fixB f (fun _ => y)) (fun x => S x y)
      (hSA y hy) (fun x hx => hf x hx y hy) a ha
  have h2 := sum_perm_one_slot hCB hn g L hL hg b hb
  simp only [g, ContinuousMultilinearMap.sum_apply, fixA_apply] at h2
  rw [Finset.sum_comm, h2]
  dsimp [L]
  rw [← Finset.smul_sum, smul_smul, mul_comm, Finset.sum_comm]

/-- Normalized form of `sum_perm_two_slot` dividing by `m! * n!`. -/
theorem average_perm_two_slot {CA CB : Set E}
    (hCA : ∀ x ∈ CA, ∀ y ∈ CA, ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (y - x) ∈ CA)
    (hCB : ∀ x ∈ CB, ∀ y ∈ CB, ∀ s ∈ Set.Icc (0 : ℝ) 1, x + s • (y - x) ∈ CB)
    {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m ⊕ Fin n => E) F)
    (S : E → E → F)
    (hSA : ∀ y ∈ CB, ∀ x₁ ∈ CA, ∀ x₂ ∈ CA, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      S (x₁ + t • (x₂ - x₁)) y = S x₁ y + t • (S x₂ y - S x₁ y))
    (hSB : ∀ x ∈ CA, ∀ y₁ ∈ CB, ∀ y₂ ∈ CB, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      S x (y₁ + s • (y₂ - y₁)) = S x y₁ + s • (S x y₂ - S x y₁))
    (hf : ∀ x ∈ CA, ∀ y ∈ CB, f (Sum.elim (fun _ => x) (fun _ => y)) = S x y)
    (a : Fin m → E) (ha : ∀ i, a i ∈ CA)
    (b : Fin n → E) (hb : ∀ j, b j ∈ CB) :
    (1 / ((m.factorial : ℝ) * (n.factorial : ℝ))) •
      (∑ π : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin n),
        f (Sum.elim (a ∘ π) (b ∘ σ))) =
      (1 / ((m : ℝ) * (n : ℝ))) •
        ∑ i : Fin m, ∑ j : Fin n, S (a i) (b j) := by
  rw [sum_perm_two_slot hCA hCB hm hn f S hSA hSB hf a ha b hb]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have hm_fac : (m.factorial : ℝ) = (m : ℝ) * ((m - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hm)).symm
  have hn_fac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hn)).symm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hmf0 : ((m - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m - 1)
  have hnf0 : ((n - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  rw [hm_fac, hn_fac, Nat.cast_mul]
  field_simp [hm0, hn0, hmf0, hnf0]

/-- Lemma 6 (`lem:polarization`, Eq. `eq:polarization`) for any labelled adaptive
circuit `tree : Tree (Fin m ⊕ Fin n) H O Finset.univ A`: if `tree` matches a
segment-biaffine Choi map `S` on identical channels in segment-closed sets
`CA, CB`, then the slot-symmetrized circuit on `a : Fin m → MatrixMap H H` and
`b : Fin n → MatrixMap H H` equals `(1 / (m * n)) ∑_{i, j} S (choi (a i)) (choi (b j))`. -/
theorem symmetrized_polarization
    {H O A : Type} [Fintype H] [Fintype O] [Fintype A]
    [DecidableEq H] [DecidableEq O] [DecidableEq A]
    {CA CB : Set (CMatrix (H × H))}
    (hCA : ∀ x ∈ CA, ∀ y ∈ CA, ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (y - x) ∈ CA)
    (hCB : ∀ x ∈ CB, ∀ y ∈ CB, ∀ s ∈ Set.Icc (0 : ℝ) 1, x + s • (y - x) ∈ CB)
    {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (tree : ICO.LabelledQueryTree.Tree (Fin m ⊕ Fin n) H O Finset.univ A)
    (S : CMatrix (H × H) → CMatrix (H × H) → CMatrix (A × O))
    (hSA : ∀ y ∈ CB, ∀ x₁ ∈ CA, ∀ x₂ ∈ CA, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      S (x₁ + t • (x₂ - x₁)) y = S x₁ y + t • (S x₂ y - S x₁ y))
    (hSB : ∀ x ∈ CA, ∀ y₁ ∈ CB, ∀ y₂ ∈ CB, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      S x (y₁ + s • (y₂ - y₁)) = S x y₁ + s • (S x y₂ - S x y₁))
    (hf : ∀ x ∈ CA, ∀ y ∈ CB,
      MatrixMap.choi (tree.map (Sum.elim
        (fun _ => MatrixMap.ofChoiMatrix x)
        (fun _ => MatrixMap.ofChoiMatrix y))) = S x y)
    (a : Fin m → MatrixMap H H) (ha : ∀ i, MatrixMap.choi (a i) ∈ CA)
    (b : Fin n → MatrixMap H H) (hb : ∀ j, MatrixMap.choi (b j) ∈ CB) :
    (1 / ((m.factorial : ℝ) * (n.factorial : ℝ))) •
      (∑ π : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin n),
        MatrixMap.choi (tree.map (Sum.elim (a ∘ π) (b ∘ σ)))) =
      (1 / ((m : ℝ) * (n : ℝ))) •
        ∑ i : Fin m, ∑ j : Fin n, S (MatrixMap.choi (a i)) (MatrixMap.choi (b j)) := by
  have hterm (π : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin n)) :
      MatrixMap.choi (tree.map (Sum.elim (a ∘ π) (b ∘ σ))) =
        (tree.continuousMultilinear.restrictScalars ℝ)
          (Sum.elim ((fun i => MatrixMap.choi (a i)) ∘ π)
            ((fun j => MatrixMap.choi (b j)) ∘ σ)) := by
    change _ = tree.continuousMultilinear _
    have hsum : Sum.elim ((fun i => MatrixMap.choi (a i)) ∘ π)
        ((fun j => MatrixMap.choi (b j)) ∘ σ) =
        fun l => MatrixMap.choi (Sum.elim (a ∘ π) (b ∘ σ) l) := by
      funext l
      cases l <;> rfl
    rw [hsum, continuousMultilinear_choi]
  simp_rw [hterm]
  apply average_perm_two_slot hCA hCB hm hn
    (tree.continuousMultilinear.restrictScalars ℝ) S hSA hSB
    (fun x hx y hy => ?_) (fun i => MatrixMap.choi (a i)) ha
    (fun j => MatrixMap.choi (b j)) hb
  change tree.continuousMultilinear (Sum.elim (fun _ => x) (fun _ => y)) = S x y
  rw [continuousMultilinear_apply]
  have helim : (fun l : Fin m ⊕ Fin n => MatrixMap.ofChoiMatrix
      (Sum.elim (fun _ : Fin m => x) (fun _ : Fin n => y) l)) =
      Sum.elim (fun _ : Fin m => MatrixMap.ofChoiMatrix x)
        (fun _ : Fin n => MatrixMap.ofChoiMatrix y) := by
    funext l
    cases l <;> rfl
  rw [helim]
  exact hf x hx y hy

end FullPolarization

section SwitchPolarization
variable {M : Type} [Fintype M] [DecidableEq M]

/-- Index helper for slot `A` in the Choi bilinear form of the full-control switch. -/
def switchIdxA {d : Nat} (c : Fin 2) (p r a : Fin d) : Fin d × Fin d :=
  if c = 0 then (p, a) else (a, r)

/-- Index helper for slot `B` in the Choi bilinear form of the full-control switch. -/
def switchIdxB {d : Nat} (c : Fin 2) (p r a : Fin d) : Fin d × Fin d :=
  if c = 0 then (a, r) else (p, a)

/-- Intrinsic representation-independent quantum switch superoperator `SW[JA, JB]`
on `Fin 2 × Fin d`, expressed directly as a bilinear function of the slot Choi
matrices `JA, JB : CMatrix (Fin d × Fin d)`. -/
def fullSwitchFromChoi {d : Nat} (JA JB : CMatrix (Fin d × Fin d)) :
    MatrixMap (Fin 2 × Fin d) (Fin 2 × Fin d) where
  toFun X := fun cr c's =>
    ∑ p : Fin d, ∑ q : Fin d, ∑ a : Fin d, ∑ b : Fin d,
      X (cr.1, p) (c's.1, q) *
        JA (switchIdxA cr.1 p cr.2 a) (switchIdxA c's.1 q c's.2 b) *
        JB (switchIdxB cr.1 p cr.2 a) (switchIdxB c's.1 q c's.2 b)
  map_add' X Y := by
    ext cr c's
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    ext cr c's
    simp [mul_assoc, Finset.mul_sum]

/-- Intrinsic quantum switch superoperator `SW[Φ, Ψ]` on `Fin 2 × Fin d` for
arbitrary matrix maps `Φ, Ψ : MatrixMap (Fin d) (Fin d)`. -/
def fullSwitchChannelMap {d : Nat} (Φ Ψ : MatrixMap (Fin d) (Fin d)) :
    MatrixMap (Fin 2 × Fin d) (Fin 2 × Fin d) :=
  fullSwitchFromChoi (MatrixMap.choi Φ) (MatrixMap.choi Ψ)

theorem choi_ofKraus_entry {d : Nat} {I : Type*} [Fintype I]
    (U : I → CMatrix (Fin d)) (pa qb : Fin d × Fin d) :
    MatrixMap.choi (MatrixMap.ofKraus U) pa qb =
      ∑ i : I, U i pa.2 pa.1 * star (U i qb.2 qb.1) := by
  rcases pa with ⟨p, a⟩
  rcases qb with ⟨q, b⟩
  simp only [MatrixMap.choi, MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single q]
  · rw [Finset.sum_eq_single p]
    · simp
    · intro r _ hr
      simp [hr.symm]
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  · intro r _ hr
    simp [hr.symm]
  · intro hq
    exact absurd (Finset.mem_univ q) hq

theorem ordered_mul_entry {d : Nat} (u v : CMatrix (Fin d)) (c : Fin 2) (r p : Fin d) :
    (if c = 0 then (v * u) r p else (u * v) r p) =
      ∑ a : Fin d,
        u (switchIdxA c p r a).2 (switchIdxA c p r a).1 *
          v (switchIdxB c p r a).2 (switchIdxB c p r a).1 := by
  by_cases hc : c = 0 <;> simp [hc, switchIdxA, switchIdxB, Matrix.mul_apply, mul_comm]

theorem fullControlOrderedPair_mul_entry {d : Nat}
    (u v : CMatrix (Fin d)) (X : CMatrix (Fin 2 × Fin d))
    (c c' : Fin 2) (r q : Fin d) :
    (fullControlOrderedPair u v * X) (c, r) (c', q) =
      ∑ p : Fin d, (if c = 0 then (v * u) r p else (u * v) r p) * X (c, p) (c', q) := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, fullControlOrderedPair]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c₁ _ hc₁
    simp [hc₁.symm]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

theorem fullControlOrderedPair_sandwich_entry {d : Nat}
    (u v : CMatrix (Fin d)) (X : CMatrix (Fin 2 × Fin d))
    (c c' : Fin 2) (r s : Fin d) :
    (fullControlOrderedPair u v * X * (fullControlOrderedPair u v)ᴴ) (c, r) (c', s) =
      ∑ p : Fin d, ∑ q : Fin d,
        (if c = 0 then (v * u) r p else (u * v) r p) *
          X (c, p) (c', q) *
          star (if c' = 0 then (v * u) s q else (u * v) s q) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single c']
  · simp only [Matrix.conjTranspose_apply, fullControlOrderedPair, ite_true,
      fullControlOrderedPair_mul_entry, Finset.sum_mul]
    rw [Finset.sum_comm]
  · intro c₂ _ hc₂
    simp [Matrix.conjTranspose_apply, fullControlOrderedPair, hc₂.symm]
  · intro hc'
    exact absurd (Finset.mem_univ c') hc'

theorem switch_kraus_sum_eq_choi_prod {d : Nat} {I J : Type} [Fintype I] [Fintype J]
    (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d))
    (c c' : Fin 2) (r s p q : Fin d) :
    (∑ i : I, ∑ j : J,
      (if c = 0 then (V j * U i) r p else (U i * V j) r p) *
        star (if c' = 0 then (V j * U i) s q else (U i * V j) s q)) =
    ∑ a : Fin d, ∑ b : Fin d,
      MatrixMap.choi (MatrixMap.ofKraus U) (switchIdxA c p r a) (switchIdxA c' q s b) *
        MatrixMap.choi (MatrixMap.ofKraus V) (switchIdxB c p r a) (switchIdxB c' q s b) := by
  simp_rw [ordered_mul_entry, star_sum, star_mul', choi_ofKraus_entry]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Kraus-form quantum switch `fullControlSwitchMap U V` depends only on the
slot Choi matrices `MatrixMap.choi (MatrixMap.ofKraus U)` and
`MatrixMap.choi (MatrixMap.ofKraus V)` via `fullSwitchFromChoi`. -/
theorem fullControlSwitchMap_eq_fullSwitchFromChoi {d : Nat} {I J : Type}
    [Fintype I] [Fintype J]
    (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d)) :
    fullControlSwitchMap U V =
      fullSwitchFromChoi (MatrixMap.choi (MatrixMap.ofKraus U))
        (MatrixMap.choi (MatrixMap.ofKraus V)) := by
  ext X ⟨c, r⟩ ⟨c', s⟩
  change (∑ ij : I × J,
      fullControlOrderedPair (U ij.1) (V ij.2) * X *
        (fullControlOrderedPair (U ij.1) (V ij.2))ᴴ) (c, r) (c', s) =
    ∑ p : Fin d, ∑ q : Fin d, ∑ a : Fin d, ∑ b : Fin d,
      X (c, p) (c', q) *
        MatrixMap.choi (MatrixMap.ofKraus U) (switchIdxA c p r a) (switchIdxA c' q s b) *
        MatrixMap.choi (MatrixMap.ofKraus V) (switchIdxB c p r a) (switchIdxB c' q s b)
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, fullControlOrderedPair_sandwich_entry]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  have hfactor :
      (∑ i : I, ∑ j : J,
        (if c = 0 then (V j * U i) r p else (U i * V j) r p) *
          X (c, p) (c', q) *
          star (if c' = 0 then (V j * U i) s q else (U i * V j) s q)) =
      X (c, p) (c', q) *
        (∑ i : I, ∑ j : J,
          (if c = 0 then (V j * U i) r p else (U i * V j) r p) *
            star (if c' = 0 then (V j * U i) s q else (U i * V j) s q)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor, switch_kraus_sum_eq_choi_prod]
  simp only [Finset.mul_sum, mul_assoc]

theorem fullSwitchChannelMap_ofKraus {d : Nat} {I J : Type} [Fintype I] [Fintype J]
    (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d)) :
    fullSwitchChannelMap (MatrixMap.ofKraus U) (MatrixMap.ofKraus V) =
      fullControlSwitchMap U V :=
  (fullControlSwitchMap_eq_fullSwitchFromChoi U V).symm

/-- Choi bilinear map `(JA, JB) ↦ Choi(SW[JA, JB])` of the full-control quantum
switch on `Fin 2 × Fin d`. -/
def switchChoiBilinear (d : Nat) (JA JB : CMatrix (Fin d × Fin d)) :
    CMatrix ((Fin 2 × Fin d) × (Fin 2 × Fin d)) :=
  MatrixMap.choi (fullSwitchFromChoi JA JB)

theorem switchChoiBilinear_affine_left {d : Nat}
    (JA₁ JA₂ JB : CMatrix (Fin d × Fin d)) (t : ℝ) :
    switchChoiBilinear d (JA₁ + t • (JA₂ - JA₁)) JB =
      switchChoiBilinear d JA₁ JB +
        t • (switchChoiBilinear d JA₂ JB - switchChoiBilinear d JA₁ JB) := by
  ext ij kl
  simp only [switchChoiBilinear, MatrixMap.choi, fullSwitchFromChoi, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem switchChoiBilinear_affine_right {d : Nat}
    (JA JB₁ JB₂ : CMatrix (Fin d × Fin d)) (t : ℝ) :
    switchChoiBilinear d JA (JB₁ + t • (JB₂ - JB₁)) =
      switchChoiBilinear d JA JB₁ +
        t • (switchChoiBilinear d JA JB₂ - switchChoiBilinear d JA JB₁) := by
  ext ij kl
  simp only [switchChoiBilinear, MatrixMap.choi, fullSwitchFromChoi, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

/-- The convex set of CPTP Choi matrices on `Fin d`. -/
def IsCPTPChoi (d : Nat) : Set (CMatrix (Fin d × Fin d)) :=
  {J | J.PosSemidef ∧ MatrixMap.IsTracePreserving (MatrixMap.ofChoiMatrix J)}

theorem channel_choi_mem_isCPTPChoi {d : Nat} (Φ : Channel (Fin d) (Fin d)) :
    MatrixMap.choi Φ.map ∈ IsCPTPChoi d :=
  ⟨Φ.completelyPositive, by
    rw [ICO.CircuitPolarization.ofChoi_choi]
    exact Φ.tracePreserving⟩

theorem exists_complete_kraus_of_isCPTPChoi {d : Nat} {J : CMatrix (Fin d × Fin d)}
    (hJ : J ∈ IsCPTPChoi d) :
    ∃ K : (Fin d × Fin d) → CMatrix (Fin d),
      MatrixMap.ofChoiMatrix J = MatrixMap.ofKraus K ∧
        (∑ i : Fin d × Fin d, (K i)ᴴ * K i) = 1 := by
  have hcp : MatrixMap.IsCompletelyPositive (MatrixMap.ofChoiMatrix J) :=
    MatrixMap.ofChoiMatrix_isCompletelyPositive hJ.1
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd (MatrixMap.ofChoiMatrix J) hcp
  have htpK : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := hK ▸ hJ.2
  have hadj := MatrixMap.krausAdjoint_one_of_tracePreserving K htpK
  refine ⟨K, hK, ?_⟩
  simpa [MatrixMap.krausAdjoint] using hadj

theorem isCPTPChoi_segment {d : Nat}
    ⦃J₁ : CMatrix (Fin d × Fin d)⦄ (h₁ : J₁ ∈ IsCPTPChoi d)
    ⦃J₂ : CMatrix (Fin d × Fin d)⦄ (h₂ : J₂ ∈ IsCPTPChoi d)
    ⦃t : ℝ⦄ (ht : t ∈ Set.Icc 0 1) :
    J₁ + t • (J₂ - J₁) ∈ IsCPTPChoi d := by
  obtain ⟨K₁, hK₁, hK₁_comp⟩ := exists_complete_kraus_of_isCPTPChoi h₁
  obtain ⟨K₂, hK₂, hK₂_comp⟩ := exists_complete_kraus_of_isCPTPChoi h₂
  let Kt : (Fin d × Fin d) ⊕ (Fin d × Fin d) → CMatrix (Fin d) :=
    Sum.elim (fun i => (Real.sqrt (1 - t) : ℂ) • K₁ i)
      (fun j => (Real.sqrt t : ℂ) • K₂ j)
  have h1t : 0 ≤ 1 - t := by linarith [ht.2]
  have hKt_comp : (∑ k, (Kt k)ᴴ * Kt k) = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [Kt, Sum.elim_inl, Sum.elim_inr]
    simp_rw [ICO.OracleLift.scaled_adjoint (1 - t) h1t,
      ICO.OracleLift.scaled_adjoint t ht.1]
    rw [← Finset.smul_sum, ← Finset.smul_sum, hK₁_comp, hK₂_comp, ← add_smul]
    have hsum : ((1 - t : ℝ) : ℂ) + (t : ℂ) = 1 := by push_cast; ring
    rw [hsum, one_smul]
  have hKt_map : MatrixMap.ofChoiMatrix (J₁ + t • (J₂ - J₁)) = MatrixMap.ofKraus Kt := by
    ext X a b
    have hlin :
        MatrixMap.ofChoiMatrix (J₁ + t • (J₂ - J₁)) =
          (1 - t) • MatrixMap.ofChoiMatrix J₁ + t • MatrixMap.ofChoiMatrix J₂ := by
      have hJ : J₁ + t • (J₂ - J₁) = (1 - t) • J₁ + t • J₂ := by
        ext p q
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
          Complex.ofReal_sub, Complex.ofReal_one]
        ring
      rw [hJ]
      exact map_add (ofChoiLinear.restrictScalars ℝ) ((1 - t) • J₁) (t • J₂) |>.trans
        (by rw [map_smul, map_smul]; rfl)
    rw [hlin, hK₁, hK₂]
    simp only [MatrixMap.ofKraus, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_sum_type, Kt, Sum.elim_inl, Sum.elim_inr]
    simp_rw [ICO.OracleLift.scaled_sandwich (1 - t) h1t,
      ICO.OracleLift.scaled_sandwich t ht.1]
    simp [← Finset.smul_sum, Complex.real_smul]
  have hJ_eq : J₁ + t • (J₂ - J₁) = MatrixMap.choi (MatrixMap.ofKraus Kt) := by
    rw [← hKt_map, MatrixMap.choi_ofChoiMatrix]
  refine ⟨?_, ?_⟩
  · rw [hJ_eq]
    exact MatrixMap.ofKraus_completelyPositive Kt
  · rw [hKt_map]
    exact MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one Kt
      (by simpa [MatrixMap.krausAdjoint] using hKt_comp)

/-- Extend a target-register CPTP channel `Φ : Channel (Fin d) (Fin d)` with the
identity channel on private circuit memory `M`. -/
def liftSlotChannel {d : Nat} (Φ : Channel (Fin d) (Fin d)) :
    Channel (Fin d × M) (Fin d × M) :=
  Φ.prod (Channel.idChannel M)

theorem kron_idChannel_eq_liftMap {d : Nat} (f : MatrixMap (Fin d) (Fin d)) :
    MatrixMap.kron f (Channel.idChannel M).map = ICO.OracleLift.liftMap (M := M) f := by
  apply MatrixMap.choi_inj
  ext ⟨⟨a, m⟩, ⟨a', m'⟩⟩ ⟨⟨b, n⟩, ⟨b', n'⟩⟩
  simp only [MatrixMap.choi]
  have hsp : Matrix.single (a, m) (b, n) (1 : ℂ) =
      Matrix.kronecker (Matrix.single a b (1 : ℂ)) (Matrix.single m n (1 : ℂ)) := by
    ext ⟨x, u⟩ ⟨y, v⟩
    simp only [Matrix.single, Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  have hid : (Channel.idChannel M).map (Matrix.single m n (1 : ℂ)) m' n' =
      (if m = m' ∧ n = n' then (1 : ℂ) else 0) := by
    simp [Channel.idChannel, MatrixMap.ofKraus, Matrix.single]
  conv_lhs =>
    rw [hsp, MatrixMap.kron_apply_kronecker]
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, hid]
  simp only [ICO.OracleLift.liftMap, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hmn : m = m' ∧ n = n'
  · rcases hmn with ⟨rfl, rfl⟩
    have hmat :
        (fun x y : Fin d => Matrix.single (a, m) (b, n) (1 : ℂ) (x, m) (y, n)) =
          Matrix.single a b (1 : ℂ) := by
      ext x y
      simp [Matrix.single]
    rw [hmat]
    simp
  · have hmat :
        (fun x y : Fin d => Matrix.single (a, m) (b, n) (1 : ℂ) (x, m') (y, n')) =
          (0 : CMatrix (Fin d)) := by
      ext x y
      simp only [Matrix.single, Matrix.of_apply, Matrix.zero_apply, Prod.mk.injEq]
      split_ifs with h
      · exact absurd ⟨h.1.2, h.2.2⟩ hmn
      · rfl
    rw [hmat, map_zero]
    simp [hmn]

theorem liftSlotChannel_map {d : Nat} (Φ : Channel (Fin d) (Fin d)) :
    (liftSlotChannel (M := M) Φ).map = ICO.OracleLift.liftMap (M := M) Φ.map :=
  kron_idChannel_eq_liftMap (M := M) Φ.map

/-- Linear map lifting a `Fin d` Choi matrix to the Choi matrix of `Φ ⊗ id_M`
on `Fin d × M`. -/
def liftChoiLinear {d : Nat} :
    CMatrix (Fin d × Fin d) →ₗ[ℂ] CMatrix ((Fin d × M) × (Fin d × M)) :=
  choiLinear.comp (ICO.OracleLift.liftLinear.comp ofChoiLinear)

/-- Continuous ℝ-linear map lifting a `Fin d` Choi matrix to `Fin d × M`. -/
def liftChoiCLM {d : Nat} :
    CMatrix (Fin d × Fin d) →L[ℝ] CMatrix ((Fin d × M) × (Fin d × M)) where
  toLinearMap := (liftChoiLinear (M := M) (d := d)).restrictScalars ℝ
  cont := ((liftChoiLinear (M := M) (d := d)).restrictScalars ℝ).continuous_of_finiteDimensional

theorem liftChoiCLM_choi {d : Nat} (f : MatrixMap (Fin d) (Fin d)) :
    liftChoiCLM (M := M) (MatrixMap.choi f) =
      MatrixMap.choi (ICO.OracleLift.liftMap (M := M) f) := by
  change MatrixMap.choi (ICO.OracleLift.liftMap (M := M)
    (MatrixMap.ofChoiMatrix (MatrixMap.choi f))) = _
  rw [ICO.CircuitPolarization.ofChoi_choi]

/-- Lemma 6 (`lem:polarization`, Eq. `eq:polarization`, Choi form) specialized
explicitly to the full-control quantum switch on `Fin 2 × Fin d`: if a labelled
`(m, n)`-query adaptive circuit `tree` satisfies `RealizesLabelledFullControlSwitch tree`,
then for any `m` CPTP channels `A_slot` and `n` CPTP channels `B_slot` on `Fin d`,
uniformly symmetrizing the slot labels equals `(1 / (m * n)) ∑_{i, j} SW[A_i, B_j]`. -/
theorem symmetrized_switch_polarization_choi {d m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (tree : ICO.LabelledQueryTree.Tree (Fin m ⊕ Fin n) (Fin d × M)
      (Fin 2 × Fin d) Finset.univ (Fin 2 × Fin d))
    (htree : RealizesLabelledFullControlSwitch tree)
    (A_slot : Fin m → Channel (Fin d) (Fin d))
    (B_slot : Fin n → Channel (Fin d) (Fin d)) :
    ((1 : ℝ) / ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) •
        (∑ π : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin n),
          MatrixMap.choi ((tree.channel
            (Sum.elim (fun i => liftSlotChannel (M := M) (A_slot (π i)))
              (fun j => liftSlotChannel (M := M) (B_slot (σ j))))).map)) =
      ((1 : ℝ) / ((m : ℝ) * (n : ℝ))) •
        ∑ i : Fin m, ∑ j : Fin n,
          MatrixMap.choi (fullSwitchChannelMap (A_slot i).map (B_slot j).map) := by
  let F : ContinuousMultilinearMap ℝ
      (fun _ : Fin m ⊕ Fin n => CMatrix (Fin d × Fin d))
      (CMatrix ((Fin 2 × Fin d) × (Fin 2 × Fin d))) :=
    (tree.continuousMultilinear.restrictScalars ℝ).compContinuousLinearMap
      (fun _ => liftChoiCLM (M := M) (d := d))
  have hF_diag : ∀ JA ∈ IsCPTPChoi d, ∀ JB ∈ IsCPTPChoi d,
      F (Sum.elim (fun _ => JA) (fun _ => JB)) = switchChoiBilinear d JA JB := by
    intro JA hJA JB hJB
    obtain ⟨U, hU_map, hU_comp⟩ := exists_complete_kraus_of_isCPTPChoi hJA
    obtain ⟨V, hV_map, hV_comp⟩ := exists_complete_kraus_of_isCPTPChoi hJB
    change tree.continuousMultilinear
        (fun l => liftChoiCLM (M := M) (Sum.elim (fun _ => JA) (fun _ => JB) l)) =
      switchChoiBilinear d JA JB
    rw [ICO.CircuitPolarization.continuousMultilinear_apply]
    have hslots :
        (fun l : Fin m ⊕ Fin n =>
          MatrixMap.ofChoiMatrix
            (liftChoiCLM (M := M) (Sum.elim (fun _ : Fin m => JA) (fun _ : Fin n => JB) l))) =
        fun l : Fin m ⊕ Fin n =>
          (Sum.elim (fun _ : Fin m => oracleChannel (M := M) U hU_comp)
            (fun _ : Fin n => oracleChannel (M := M) V hV_comp) l).map := by
      funext l
      cases l with
      | inl _ =>
        change MatrixMap.ofChoiMatrix
          (MatrixMap.choi (ICO.OracleLift.liftMap (M := M) (MatrixMap.ofChoiMatrix JA))) = _
        rw [ICO.CircuitPolarization.ofChoi_choi, hU_map]
        exact (ICO.OracleLift.oracleMap_lift (M := M) U).symm
      | inr _ =>
        change MatrixMap.ofChoiMatrix
          (MatrixMap.choi (ICO.OracleLift.liftMap (M := M) (MatrixMap.ofChoiMatrix JB))) = _
        rw [ICO.CircuitPolarization.ofChoi_choi, hV_map]
        exact (ICO.OracleLift.oracleMap_lift (M := M) V).symm
    rw [hslots, ← ICO.LabelledQueryTree.Tree.channel_map,
      htree (Fin d × Fin d) (Fin d × Fin d) U V hU_comp hV_comp,
      fullControlSwitchMap_eq_fullSwitchFromChoi]
    have hJA_eq : MatrixMap.choi (MatrixMap.ofKraus U) = JA := by
      rw [← hU_map, MatrixMap.choi_ofChoiMatrix]
    have hJB_eq : MatrixMap.choi (MatrixMap.ofKraus V) = JB := by
      rw [← hV_map, MatrixMap.choi_ofChoiMatrix]
    rw [hJA_eq, hJB_eq]
    rfl
  have hpol := average_perm_two_slot isCPTPChoi_segment isCPTPChoi_segment hm hn F
    (switchChoiBilinear d)
    (fun y _ x₁ _ x₂ _ t _ => switchChoiBilinear_affine_left x₁ x₂ y t)
    (fun x _ y₁ _ y₂ _ s _ => switchChoiBilinear_affine_right x y₁ y₂ s)
    hF_diag
    (fun i => MatrixMap.choi (A_slot i).map) (fun i => channel_choi_mem_isCPTPChoi (A_slot i))
    (fun j => MatrixMap.choi (B_slot j).map) (fun j => channel_choi_mem_isCPTPChoi (B_slot j))
  have hlhs : ∀ (π : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin n)),
      MatrixMap.choi ((tree.channel
        (Sum.elim (fun i => liftSlotChannel (M := M) (A_slot (π i)))
          (fun j => liftSlotChannel (M := M) (B_slot (σ j))))).map) =
      F (Sum.elim (fun i => MatrixMap.choi (A_slot (π i)).map)
        (fun j => MatrixMap.choi (B_slot (σ j)).map)) := by
    intro π σ
    rw [ICO.LabelledQueryTree.Tree.channel_map]
    change MatrixMap.choi (tree.map _) =
      tree.continuousMultilinear
        (fun l => liftChoiCLM (M := M)
          (Sum.elim (fun i => MatrixMap.choi (A_slot (π i)).map)
            (fun j => MatrixMap.choi (B_slot (σ j)).map) l))
    rw [ICO.CircuitPolarization.continuousMultilinear_apply]
    congr 1
    apply ICO.LabelledQueryTree.Tree.map_congr
    intro l _
    cases l with
    | inl i =>
      simp only [Sum.elim_inl, liftChoiCLM_choi, ICO.CircuitPolarization.ofChoi_choi,
        liftSlotChannel_map]
    | inr j =>
      simp only [Sum.elim_inr, liftChoiCLM_choi, ICO.CircuitPolarization.ofChoi_choi,
        liftSlotChannel_map]
  simp_rw [hlhs]
  exact hpol

theorem choi_real_smul_sum2 {A O α β : Type} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O] [Fintype α] [Fintype β]
    (r : ℝ) (g : α → β → MatrixMap A O) :
    MatrixMap.choi (r • ∑ a : α, ∑ b : β, g a b) =
      r • ∑ a : α, ∑ b : β, MatrixMap.choi (g a b) := by
  let cR := (choiLinear (A := A) (O := O)).restrictScalars ℝ
  change cR (r • ∑ a : α, ∑ b : β, g a b) = _
  simp only [map_smul, map_sum]
  rfl

/-- Lemma 6 (`lem:polarization`, Eq. `eq:polarization`, superoperator form)
specialized explicitly to the full-control quantum switch on `Fin 2 × Fin d`:
if `tree` realizes the full-control switch on identical CPTP channels, then its
slot-symmetrized superoperator on arbitrary CPTP channels `A_slot` and `B_slot`
equals `(1 / (m * n)) ∑_{i, j} fullSwitchChannelMap (A_slot i).map (B_slot j).map`. -/
theorem symmetrized_switch_polarization {d m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (tree : ICO.LabelledQueryTree.Tree (Fin m ⊕ Fin n) (Fin d × M)
      (Fin 2 × Fin d) Finset.univ (Fin 2 × Fin d))
    (htree : RealizesLabelledFullControlSwitch tree)
    (A_slot : Fin m → Channel (Fin d) (Fin d))
    (B_slot : Fin n → Channel (Fin d) (Fin d)) :
    ((1 : ℝ) / ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) •
        (∑ π : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin n),
          (tree.channel
            (Sum.elim (fun i => liftSlotChannel (M := M) (A_slot (π i)))
              (fun j => liftSlotChannel (M := M) (B_slot (σ j))))).map) =
      ((1 : ℝ) / ((m : ℝ) * (n : ℝ))) •
        ∑ i : Fin m, ∑ j : Fin n,
          fullSwitchChannelMap (A_slot i).map (B_slot j).map := by
  apply MatrixMap.choi_inj
  rw [choi_real_smul_sum2, choi_real_smul_sum2]
  exact symmetrized_switch_polarization_choi (M := M) hm hn tree htree A_slot B_slot

/-- Complete-Kraus channel on `Fin d` associated to a Kraus family `(U, hU)`. -/
def targetKrausChannel {d : Nat} {I : Type} [Fintype I]
    (U : I → CMatrix (Fin d)) (hU : ∑ i, (U i)ᴴ * U i = 1) :
    Channel (Fin d) (Fin d) where
  map := MatrixMap.ofKraus U
  completelyPositive := MatrixMap.ofKraus_completelyPositive U
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one U
    (by simpa [MatrixMap.krausAdjoint] using hU)
  mapsPositive := MatrixMap.ofKraus_mapsPositive U

/-- Lemma 6 (`lem:polarization`, Eq. `eq:polarization`, Kraus-oracle form)
specialized explicitly to `oracleChannel` and `fullControlSwitchMap`: if `tree`
satisfies `RealizesLabelledFullControlSwitch tree`, then symmetrizing `m` complete
Kraus oracles `(U i, hU i)` and `n` complete Kraus oracles `(V j, hV j)` gives
`(1 / (m * n)) ∑_{i, j} fullControlSwitchMap (U i) (V j)`. -/
theorem symmetrized_switch_polarization_kraus {d m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (tree : ICO.LabelledQueryTree.Tree (Fin m ⊕ Fin n) (Fin d × M)
      (Fin 2 × Fin d) Finset.univ (Fin 2 × Fin d))
    (htree : RealizesLabelledFullControlSwitch tree)
    {IA : Fin m → Type} {IB : Fin n → Type}
    [∀ i, Fintype (IA i)] [∀ j, Fintype (IB j)]
    [∀ i, DecidableEq (IA i)] [∀ j, DecidableEq (IB j)]
    (U : ∀ i : Fin m, IA i → CMatrix (Fin d))
    (V : ∀ j : Fin n, IB j → CMatrix (Fin d))
    (hU : ∀ i : Fin m, ∑ k : IA i, (U i k)ᴴ * U i k = 1)
    (hV : ∀ j : Fin n, ∑ l : IB j, (V j l)ᴴ * V j l = 1) :
    ((1 : ℝ) / ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) •
        (∑ π : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin n),
          (tree.channel
            (Sum.elim (fun i => oracleChannel (M := M) (U (π i)) (hU (π i)))
              (fun j => oracleChannel (M := M) (V (σ j)) (hV (σ j))))).map) =
      ((1 : ℝ) / ((m : ℝ) * (n : ℝ))) •
        ∑ i : Fin m, ∑ j : Fin n,
          fullControlSwitchMap (U i) (V j) := by
  have hpol := symmetrized_switch_polarization (M := M) hm hn tree htree
    (fun i => targetKrausChannel (U i) (hU i))
    (fun j => targetKrausChannel (V j) (hV j))
  have hlhs : ∀ (π : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin n)),
      (tree.channel
        (Sum.elim (fun i => oracleChannel (M := M) (U (π i)) (hU (π i)))
          (fun j => oracleChannel (M := M) (V (σ j)) (hV (σ j))))).map =
      (tree.channel
        (Sum.elim (fun i => liftSlotChannel (M := M) (targetKrausChannel (U (π i)) (hU (π i))))
          (fun j => liftSlotChannel (M := M) (targetKrausChannel (V (σ j)) (hV (σ j)))))).map := by
    intro π σ
    rw [ICO.LabelledQueryTree.Tree.channel_map, ICO.LabelledQueryTree.Tree.channel_map]
    apply ICO.LabelledQueryTree.Tree.map_congr
    intro l _
    cases l with
    | inl i =>
      simp only [Sum.elim_inl, liftSlotChannel_map, targetKrausChannel]
      exact ICO.OracleLift.oracleMap_lift (M := M) (U (π i))
    | inr j =>
      simp only [Sum.elim_inr, liftSlotChannel_map, targetKrausChannel]
      exact ICO.OracleLift.oracleMap_lift (M := M) (V (σ j))
  simp_rw [hlhs]
  rw [hpol]
  simp only [targetKrausChannel, fullSwitchChannelMap_ofKraus]

end SwitchPolarization

#print axioms no_bounded_full_switch_circuit
#print axioms no_bounded_circuit_arbitrary_control
#print axioms no_labelled_full_switch_circuit
#print axioms ordered_components_decomposition
#print axioms ordered_components_decomposition_dim_d
#print axioms tree_ordered_components
#print axioms tree_ordered_components_dim_d
#print axioms sum_perm_one_slot
#print axioms sum_perm_two_slot
#print axioms average_perm_two_slot
#print axioms symmetrized_polarization
#print axioms symmetrized_switch_polarization_choi
#print axioms symmetrized_switch_polarization
#print axioms symmetrized_switch_polarization_kraus

end
end ICO.PolarizationOrderedArbitraryControl

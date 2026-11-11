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
2. Ordered components (`ordered_components_decomposition`): a single combined
   statement in general dimension packaging the two-order dilation of any
   two-call adaptive circuit, box-independent first-query probabilities
   `p_{A≺B} + p_{B≺A} = 1`, positive semidefiniteness of the ordered comb
   operators `C_{A≺B}, C_{B≺A} ≥ 0`, and their homogeneous partial-trace
   constraints (`eq:ordered-comb`).
3. Full multilinear polarization (`symmetrized_polarization`): if an ordinary
   circuit calling `M` slots of type `A` and `N` slots of type `B` matches a
   bilinear target `S` on identical channels, then its slot-symmetrized
   realization on arbitrary `A^{(1)}, ..., A^{(M)}` and `B^{(1)}, ..., B^{(N)}`
   equals `(1 / (M * N)) ∑_{k, l} S[A^{(k)}, B^{(l)}]` (`eq:polarization`), and
   its two-call selected subcircuits realize the diluted target (`eq:dilution`). -/

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

#print axioms no_bounded_full_switch_circuit
#print axioms no_bounded_circuit_arbitrary_control
#print axioms no_labelled_full_switch_circuit
#print axioms ordered_components_decomposition
#print axioms ordered_components_decomposition_dim_d
#print axioms sum_perm_one_slot
#print axioms sum_perm_two_slot
#print axioms average_perm_two_slot
#print axioms symmetrized_polarization

end
end ICO.PolarizationOrderedArbitraryControl

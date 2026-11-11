import ICO.C4FullSwitchTheorem
import ICO.C6OperationalDecision
import ICO.PolarizationOrderedArbitraryControl

/-!
# Remark `rem:unitary` ("One unitary box is easy") and Numerical Remarks `rem:approx-content` and `rem:crossover`

1. **Remark `rem:unitary` ("One unitary box is easy")**:
   - The diluted box `x A + (1 - x) id` is not a unitary channel for `0 < x < 1`, confirming
     that the set of unitary channels is not convex (`diluted_unitary_not_unitary`).
   - If box `A` is known to be unitary (`U ∈ U(A)`), the 3-call circuit `unitaryThreeCallTree a₀`
     of Figure `fig:unitary` (prepare dummy in `|a₀⟩`, swap on `|1⟩`, call `A`, undo swap; call `B`
     on target; swap on `|0⟩`, call `A` a second time, undo swap, discard dummy) reproduces the
     exact quantum switch `SW[A, B]` on control and target for **every** CPTP channel `B`
     (`unitaryThreeCallTree_unitary_kraus_eq`, `unitaryThreeCallTree_unitary_left_channel_eq`,
     and `Fin 2 × Fin d` bridge `unitaryThreeCallTree_fullSwitchChannelMap_eq`), specializing
     to two unitary gates (`unitaryThreeCallTree_channel_eq`, `unitaryThreeCallTree_fullChannel_eq`,
     `unitaryThreeCallTree_allChannel_eq`, `unitaryThreeCallTree_diamond_zero`).
   - Symmetrically, when box `B` is unitary (`V ∈ U(A)`) and `A` is an arbitrary CPTP channel,
     exchanging the roles of `A` and `B` (`unitarySecondThreeCallTree a₀`) reproduces `SW[A, B]`
     in 3 calls (`unitarySecondThreeCallTree_unitary_kraus_eq` and
     `unitarySecondThreeCallTree_unitary_right_channel_eq`).
   - When the box called twice (`A`) is not unitary (e.g. computational-basis dephasing `Δ_I` on
     `Fin 2` with `B = id`), the dummy becomes correlated with the control, control coherence is
     reduced, and `unitaryThreeCallTree a₀` fails to implement `SW[A, B]` for every initial dummy
     basis state `a₀` (`unitaryThreeCallTree_fails_nonunitary` and
     `exists_nonunitary_unitaryThreeCallTree_ne_channelSwitch`).
2. **Remark `rem:approx-content` (Where the bound of Theorem `thm:simulation-summary` has content)**:
   At `q = 2`, the tradeoff bound `1/2 - 13(r+1)²/(3d) - q(q-1)/(2(r+1))` is
   strictly positive at `r + 1 = 3` (`r = 2`) for all `d ≥ 235` (giving error
   `≥ 1/6 - 39/d ≥ 1/1410 > 0`), and is nonpositive for all `r` when `1 ≤ d ≤ 234`.
   Furthermore, the constant-error consequence `d < 4096 q⁴` at `ε = 1/48` forces
   `q ≥ 3` whenever `d ≥ 65536`. Finally, for `r ≥ 2` and `d ≥ 2`, the uniform
   mixture of `r` independent Haar-random unitary channels is almost surely not a
   unitary channel (`uniform_haar_mixture_ae_not_unitary` and
   `uniform_haar_mixture_ae_not_ambient_unitary`).
3. **Archival `SAME`/`MUB` crossover thresholds (`n = 107` and `n = 155`, outside the Round-7 manuscript)**:
   For `d = 2^n`, the unattenuated `SAME`/`MUB` bound `d^(1/16)/100 = 2^(n/16)/100`
   crosses `1` at `n = 107` (`< 1` for `n ≤ 106`, `> 1` for `n ≥ 107`) and crosses `8`
   at `n = 155` (`< 8` for `n ≤ 154`, `> 8` for `n ≥ 155`). These six endpoints are
   preserved as audited supplementary results outside the manuscript.
4. **Remark `rem:crossover` (Crossover thresholds `n ≥ 142` and `n ≥ 238`, switch-test call bound, and trivial `1/(3p)` bound)**:
   Every adaptive `Q`-query strategy distinguishing two channels of diamond trace
   distance at most `p` (`0 < p`) with `(2/3, 1/3)` advantage (or balanced-prior
   success `≥ 2/3`) requires `Q ≥ 1 / (3p)` (`trivial_query_lower_bound_of_diamond_le`).
   For `d = 2^n`, the Theorem 3 (`thm:c6`) lower bound `d^(1/16) / (1400 p)` exceeds
   `1 / (3p)` if and only if `n ≥ 142` (`one_div_three_p_lt_validation_bound_iff`),
   and exceeds `21 / p` — a lower bound on the `14 ⌈3 / (2p)⌉` device uses of the
   switch test (`switch_test_calls_ge_twenty_one_div_p`) — if and only if `n ≥ 238`
   (`twenty_one_div_p_lt_validation_bound_iff`).
-/

namespace ICO.RemarksUnitaryNumerical

open Matrix QIT ICO.InstrumentCompression ICO.BudgetQueryTree
open ICO.AllChannelDilation ICO.FullSwitchChannel ICO.BudgetHaarBound
open ICO.C4PhysicalEnsemble ICO.C6OperationalDecision ICO.SwitchObservable
open ICO.BudgetContinuity ICO.BudgetTesting ICO.C6Decision ICO.C6SwitchTest ICO.SwitchChoiWitness
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

variable {A M O B : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]

instance : Nonempty A := Nontrivial.to_nonempty

/-! ## 1. Remark `rem:unitary`: One Unitary Box Is Easy -/

/-- Prepare the dummy register in `a₀ : A` and swap target and dummy when the
control qubit is `true` (`|1⟩`). -/
def preIsometry (a₀ : A) : Matrix (A × (A × Bool)) (A × Bool) ℂ :=
  fun tdc ac =>
    if tdc.2.2 = ac.2 then
      if ac.2 then
        if tdc.1 = a₀ ∧ tdc.2.1 = ac.1 then 1 else 0
      else
        if tdc.1 = ac.1 ∧ tdc.2.1 = a₀ then 1 else 0
    else 0

theorem preIsometry_complete (a₀ : A) :
    (preIsometry a₀)ᴴ * preIsometry a₀ = 1 := by
  ext ac₁ ac₂
  rcases ac₁ with ⟨a₁, c₁⟩
  rcases ac₂ with ⟨a₂, c₂⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, preIsometry, Matrix.one_apply]
  by_cases hc : c₁ = c₂
  · subst hc
    cases c₁
    · rw [Finset.sum_eq_single (a₁, (a₀, false))]
      · by_cases ha : a₁ = a₂ <;> simp [Prod.ext_iff, ha]
      · intro x _ hx
        have hne : ¬(x.1 = a₁ ∧ x.2.1 = a₀ ∧ x.2.2 = false) := by
          intro h
          exact hx (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
        by_cases h1 : x.2.2 = false
        · by_cases h2 : x.1 = a₁ ∧ x.2.1 = a₀
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · rw [Finset.sum_eq_single (a₀, (a₁, true))]
      · by_cases ha : a₁ = a₂ <;> simp [Prod.ext_iff, ha]
      · intro x _ hx
        have hne : ¬(x.1 = a₀ ∧ x.2.1 = a₁ ∧ x.2.2 = true) := by
          intro h
          exact hx (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
        by_cases h1 : x.2.2 = true
        · by_cases h2 : x.1 = a₀ ∧ x.2.1 = a₁
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  · simp only [Prod.ext_iff, hc, and_false, ite_false]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : x.2.2 = c₁
    · simp [h1, hc]
    · simp [h1]

def preInstrument (a₀ : A) : Instrument (A × Bool) (A × (A × Bool)) PUnit where
  op _ := preIsometry a₀
  complete := by simpa using preIsometry_complete a₀

/-- Controlled swap between target `A` and dummy `A` active when control is `true` (`|1⟩`). -/
def cswapTrue : CMatrix (A × (A × Bool)) :=
  fun tdc' tdc =>
    if tdc'.2.2 = tdc.2.2 then
      if tdc.2.2 then
        if tdc'.1 = tdc.2.1 ∧ tdc'.2.1 = tdc.1 then 1 else 0
      else
        if tdc'.1 = tdc.1 ∧ tdc'.2.1 = tdc.2.1 then 1 else 0
    else 0

theorem cswapTrue_complete :
    (cswapTrue (A := A))ᴴ * cswapTrue (A := A) = 1 := by
  ext x y
  rcases x with ⟨t₁, d₁, c₁⟩
  rcases y with ⟨t₂, d₂, c₂⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cswapTrue, Matrix.one_apply]
  by_cases hc : c₁ = c₂
  · subst hc
    cases c₁
    · rw [Finset.sum_eq_single (t₁, (d₁, false))]
      · by_cases ht : t₁ = t₂ <;> by_cases hd : d₁ = d₂ <;> simp [Prod.ext_iff, ht, hd]
      · intro z _ hz
        have hne : ¬(z.1 = t₁ ∧ z.2.1 = d₁ ∧ z.2.2 = false) := by
          intro h
          exact hz (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
        by_cases h1 : z.2.2 = false
        · by_cases h2 : z.1 = t₁ ∧ z.2.1 = d₁
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · rw [Finset.sum_eq_single (d₁, (t₁, true))]
      · by_cases ht : t₁ = t₂ <;> by_cases hd : d₁ = d₂ <;> simp [Prod.ext_iff, ht, hd]
      · intro z _ hz
        have hne : ¬(z.1 = d₁ ∧ z.2.1 = t₁ ∧ z.2.2 = true) := by
          intro h
          exact hz (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
        by_cases h1 : z.2.2 = true
        · by_cases h2 : z.1 = d₁ ∧ z.2.1 = t₁
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  · simp only [Prod.ext_iff, hc, and_false, ite_false]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : z.2.2 = c₁
    · simp [h1, hc]
    · simp [h1]

def cswapTrueInstrument : Instrument (A × (A × Bool)) (A × (A × Bool)) PUnit where
  op _ := cswapTrue (A := A)
  complete := by simpa using cswapTrue_complete (A := A)

/-- Controlled swap between target `A` and dummy `A` active when control is `false` (`|0⟩`). -/
def cswapFalse : CMatrix (A × (A × Bool)) :=
  fun tdc' tdc =>
    if tdc'.2.2 = tdc.2.2 then
      if tdc.2.2 then
        if tdc'.1 = tdc.1 ∧ tdc'.2.1 = tdc.2.1 then 1 else 0
      else
        if tdc'.1 = tdc.2.1 ∧ tdc'.2.1 = tdc.1 then 1 else 0
    else 0

theorem cswapFalse_complete :
    (cswapFalse (A := A))ᴴ * cswapFalse (A := A) = 1 := by
  ext x y
  rcases x with ⟨t₁, d₁, c₁⟩
  rcases y with ⟨t₂, d₂, c₂⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cswapFalse, Matrix.one_apply]
  by_cases hc : c₁ = c₂
  · subst hc
    cases c₁
    · rw [Finset.sum_eq_single (d₁, (t₁, false))]
      · by_cases ht : t₁ = t₂ <;> by_cases hd : d₁ = d₂ <;> simp [Prod.ext_iff, ht, hd]
      · intro z _ hz
        have hne : ¬(z.1 = d₁ ∧ z.2.1 = t₁ ∧ z.2.2 = false) := by
          intro h
          exact hz (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
        by_cases h1 : z.2.2 = false
        · by_cases h2 : z.1 = d₁ ∧ z.2.1 = t₁
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · rw [Finset.sum_eq_single (t₁, (d₁, true))]
      · by_cases ht : t₁ = t₂ <;> by_cases hd : d₁ = d₂ <;> simp [Prod.ext_iff, ht, hd]
      · intro z _ hz
        have hne : ¬(z.1 = t₁ ∧ z.2.1 = d₁ ∧ z.2.2 = true) := by
          intro h
          exact hz (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
        by_cases h1 : z.2.2 = true
        · by_cases h2 : z.1 = t₁ ∧ z.2.1 = d₁
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  · simp only [Prod.ext_iff, hc, and_false, ite_false]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : z.2.2 = c₁
    · simp [h1, hc]
    · simp [h1]

def cswapFalseInstrument : Instrument (A × (A × Bool)) (A × (A × Bool)) PUnit where
  op _ := cswapFalse (A := A)
  complete := by simpa using cswapFalse_complete (A := A)

/-- Final Kraus operators applying the restoring controlled swap on `false` (`|0⟩`)
and tracing out the dummy register `d : A`. -/
def postKraus (d : A) : Matrix (A × Bool) (A × (A × Bool)) ℂ :=
  fun ac tdc =>
    if ac.2 = tdc.2.2 then
      if tdc.2.2 then
        if ac.1 = tdc.1 ∧ d = tdc.2.1 then 1 else 0
      else
        if ac.1 = tdc.2.1 ∧ d = tdc.1 then 1 else 0
    else 0

theorem postKraus_complete :
    ∑ d : A, (postKraus (A := A) d)ᴴ * postKraus (A := A) d = 1 := by
  ext x y
  rcases x with ⟨t₁, d₁, c₁⟩
  rcases y with ⟨t₂, d₂, c₂⟩
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    postKraus, Matrix.one_apply]
  by_cases hc : c₁ = c₂
  · subst hc
    cases c₁
    · rw [Finset.sum_eq_single t₁]
      · rw [Finset.sum_eq_single (d₁, false)]
        · by_cases ht : t₁ = t₂ <;> by_cases hd : d₁ = d₂ <;> simp [Prod.ext_iff, ht, hd]
        · intro ac _ hac
          have hne : ¬(ac.1 = d₁ ∧ ac.2 = false) := by
            intro h
            exact hac (Prod.ext h.1 h.2)
          by_cases h1 : ac.2 = false
          · by_cases h2 : ac.1 = d₁
            · exact False.elim (hne ⟨h2, h1⟩)
            · simp [h1, h2]
          · simp [h1]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
      · intro d _ hd
        refine Finset.sum_eq_zero fun ac _ => ?_
        have hne : d ≠ t₁ := hd
        by_cases h1 : ac.2 = false
        · simp [h1, hne]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · rw [Finset.sum_eq_single d₁]
      · rw [Finset.sum_eq_single (t₁, true)]
        · by_cases ht : t₁ = t₂ <;> by_cases hd : d₁ = d₂ <;> simp [Prod.ext_iff, ht, hd]
        · intro ac _ hac
          have hne : ¬(ac.1 = t₁ ∧ ac.2 = true) := by
            intro h
            exact hac (Prod.ext h.1 h.2)
          by_cases h1 : ac.2 = true
          · by_cases h2 : ac.1 = t₁
            · exact False.elim (hne ⟨h2, h1⟩)
            · simp [h1, h2]
          · simp [h1]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
      · intro d _ hd
        refine Finset.sum_eq_zero fun ac _ => ?_
        have hne : d ≠ d₁ := hd
        by_cases h1 : ac.2 = true
        · simp [h1, hne]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  · simp only [Prod.ext_iff, hc, and_false, ite_false]
    refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun ac _ => ?_
    by_cases h1 : ac.2 = c₁
    · simp [h1, hc]
    · simp [h1]

def postChannel : Channel (A × (A × Bool)) (A × Bool) where
  map := MatrixMap.ofKraus (postKraus (A := A))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using postKraus_complete (A := A))
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

/-- **Remark `rem:unitary` 3-call query tree**:
Calls `first` (`U`), `second` (`V`), and `first` (`U`) with controlled swaps
between the target `A` and dummy `A` registers around the queries. -/
def unitaryThreeCallTree (a₀ : A) :
    Tree (A × (A × Bool)) (A × Bool) 3 (A × Bool) :=
  .node (preInstrument a₀) (fun _ =>
    .query false (.node (cswapTrueInstrument (A := A)) (fun _ =>
      .query true (.node (cswapFalseInstrument (A := A)) (fun _ =>
        .query false (.stop (postChannel (A := A))))))))

theorem kronecker_identity_mul_entry {N R : Type} [Fintype N] [DecidableEq N]
    (U : CMatrix A) (X : Matrix (A × N) R ℂ) (a : A) (n : N) (r : R) :
    (Matrix.kronecker U (1 : CMatrix N) * X) (a, n) r =
      ∑ b : A, U a b * X (b, n) r := by
  simp [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type]

def stage1Matrix (a₀ : A) (U : CMatrix A) : Matrix (A × (A × Bool)) (A × Bool) ℂ :=
  fun tdc ac =>
    if tdc.2.2 = ac.2 then
      if ac.2 then
        if tdc.2.1 = ac.1 then U tdc.1 a₀ else 0
      else
        if tdc.2.1 = a₀ then U tdc.1 ac.1 else 0
    else 0

theorem stage1Matrix_eq (a₀ : A) (U : CMatrix A) :
    Matrix.kronecker U (1 : CMatrix (A × Bool)) * preIsometry a₀ = stage1Matrix a₀ U := by
  ext tdc ac
  rcases tdc with ⟨t, d, c'⟩
  rcases ac with ⟨a, c⟩
  rw [kronecker_identity_mul_entry]
  simp only [preIsometry, stage1Matrix]
  by_cases hc : c' = c
  · subst hc
    cases c'
    · rw [Finset.sum_eq_single a]
      · by_cases hd : d = a₀ <;> simp [hd]
      · intro b _ hb
        have hne : b ≠ a := hb
        simp [hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · rw [Finset.sum_eq_single a₀]
      · by_cases hd : d = a <;> simp [hd]
      · intro b _ hb
        have hne : b ≠ a₀ := hb
        simp [hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  · simp [hc]

def stage2Matrix (a₀ : A) (U : CMatrix A) : Matrix (A × (A × Bool)) (A × Bool) ℂ :=
  fun tdc ac =>
    if tdc.2.2 = ac.2 then
      if ac.2 then
        if tdc.1 = ac.1 then U tdc.2.1 a₀ else 0
      else
        if tdc.2.1 = a₀ then U tdc.1 ac.1 else 0
    else 0

theorem stage2Matrix_eq (a₀ : A) (U : CMatrix A) :
    cswapTrue (A := A) * stage1Matrix a₀ U = stage2Matrix a₀ U := by
  ext tdc ac
  rcases tdc with ⟨t, d, c'⟩
  rcases ac with ⟨a, c⟩
  simp only [Matrix.mul_apply, cswapTrue, stage1Matrix, stage2Matrix]
  by_cases hc : c' = c
  · subst hc
    cases c'
    · rw [Finset.sum_eq_single (t, (d, false))]
      · simp
      · intro z _ hz
        have hne : ¬(t = z.1 ∧ d = z.2.1 ∧ z.2.2 = false) := by
          intro h
          exact hz (Prod.ext h.1.symm (Prod.ext h.2.1.symm h.2.2))
        by_cases h1 : z.2.2 = false
        · by_cases h2 : t = z.1 ∧ d = z.2.1
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · rw [Finset.sum_eq_single (d, (t, true))]
      · simp
      · intro z _ hz
        have hne : ¬(t = z.2.1 ∧ d = z.1 ∧ z.2.2 = true) := by
          intro h
          exact hz (Prod.ext h.2.1.symm (Prod.ext h.1.symm h.2.2))
        by_cases h1 : z.2.2 = true
        · by_cases h2 : t = z.2.1 ∧ d = z.1
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  · simp only [hc, ite_false]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : z.2.2 = c
    · simp [h1, hc]
    · simp [h1]

def stage3Matrix (a₀ : A) (U V : CMatrix A) : Matrix (A × (A × Bool)) (A × Bool) ℂ :=
  fun tdc ac =>
    if tdc.2.2 = ac.2 then
      if ac.2 then
        V tdc.1 ac.1 * U tdc.2.1 a₀
      else
        if tdc.2.1 = a₀ then (V * U) tdc.1 ac.1 else 0
    else 0

theorem stage3Matrix_eq (a₀ : A) (U V : CMatrix A) :
    Matrix.kronecker V (1 : CMatrix (A × Bool)) * stage2Matrix a₀ U = stage3Matrix a₀ U V := by
  ext tdc ac
  rcases tdc with ⟨t, d, c'⟩
  rcases ac with ⟨a, c⟩
  rw [kronecker_identity_mul_entry]
  simp only [stage2Matrix, stage3Matrix]
  by_cases hc : c' = c
  · subst hc
    cases c'
    · by_cases hd : d = a₀
      · simp [hd, Matrix.mul_apply]
      · simp [hd]
    · rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        have hne : b ≠ a := hb
        simp [hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  · simp [hc]

def stage4Matrix (a₀ : A) (U V : CMatrix A) : Matrix (A × (A × Bool)) (A × Bool) ℂ :=
  fun tdc ac =>
    if tdc.2.2 = ac.2 then
      if ac.2 then
        V tdc.1 ac.1 * U tdc.2.1 a₀
      else
        if tdc.1 = a₀ then (V * U) tdc.2.1 ac.1 else 0
    else 0

theorem stage4Matrix_eq (a₀ : A) (U V : CMatrix A) :
    cswapFalse (A := A) * stage3Matrix a₀ U V = stage4Matrix a₀ U V := by
  ext tdc ac
  rcases tdc with ⟨t, d, c'⟩
  rcases ac with ⟨a, c⟩
  simp only [Matrix.mul_apply, cswapFalse, stage3Matrix, stage4Matrix]
  by_cases hc : c' = c
  · subst hc
    cases c'
    · rw [Finset.sum_eq_single (d, (t, false))]
      · simp
      · intro z _ hz
        have hne : ¬(t = z.2.1 ∧ d = z.1 ∧ z.2.2 = false) := by
          intro h
          exact hz (Prod.ext h.2.1.symm (Prod.ext h.1.symm h.2.2))
        by_cases h1 : z.2.2 = false
        · by_cases h2 : t = z.2.1 ∧ d = z.1
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · rw [Finset.sum_eq_single (t, (d, true))]
      · simp
      · intro z _ hz
        have hne : ¬(t = z.1 ∧ d = z.2.1 ∧ z.2.2 = true) := by
          intro h
          exact hz (Prod.ext h.1.symm (Prod.ext h.2.1.symm h.2.2))
        by_cases h1 : z.2.2 = true
        · by_cases h2 : t = z.1 ∧ d = z.2.1
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  · simp only [hc, ite_false]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : z.2.2 = c
    · simp [h1, hc]
    · simp [h1]

def stage5Matrix (a₀ : A) (U V : CMatrix A) : Matrix (A × (A × Bool)) (A × Bool) ℂ :=
  fun tdc ac =>
    if tdc.2.2 = ac.2 then
      if ac.2 then
        (U * V) tdc.1 ac.1 * U tdc.2.1 a₀
      else
        U tdc.1 a₀ * (V * U) tdc.2.1 ac.1
    else 0

theorem stage5Matrix_eq (a₀ : A) (U V : CMatrix A) :
    Matrix.kronecker U (1 : CMatrix (A × Bool)) * stage4Matrix a₀ U V = stage5Matrix a₀ U V := by
  ext tdc ac
  rcases tdc with ⟨t, d, c'⟩
  rcases ac with ⟨a, c⟩
  rw [kronecker_identity_mul_entry]
  simp only [stage4Matrix, stage5Matrix]
  by_cases hc : c' = c
  · subst hc
    cases c'
    · rw [Finset.sum_eq_single a₀]
      · simp
      · intro b _ hb
        have hne : b ≠ a₀ := hb
        simp [hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · simp [Matrix.mul_apply, Finset.sum_mul, mul_assoc]
  · simp [hc]

theorem postKraus_mul_stage5Matrix (a₀ d : A) (U V : CMatrix A) :
    postKraus (A := A) d * stage5Matrix a₀ U V =
      U d a₀ • controlled (V * U) (U * V) := by
  ext ac' ac
  rcases ac' with ⟨a', c'⟩
  rcases ac with ⟨a, c⟩
  simp only [Matrix.mul_apply, postKraus, stage5Matrix, Matrix.smul_apply,
    smul_eq_mul, controlled]
  by_cases hc : c' = c
  · subst hc
    cases c'
    · rw [Finset.sum_eq_single (d, (a', false))]
      · simp
      · intro z _ hz
        have hne : ¬(a' = z.2.1 ∧ d = z.1 ∧ z.2.2 = false) := by
          intro h
          exact hz (Prod.ext h.2.1.symm (Prod.ext h.1.symm h.2.2))
        by_cases h1 : z.2.2 = false
        · by_cases h2 : a' = z.2.1 ∧ d = z.1
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · rw [Finset.sum_eq_single (a', (d, true))]
      · simp [mul_comm]
      · intro z _ hz
        have hne : ¬(a' = z.1 ∧ d = z.2.1 ∧ z.2.2 = true) := by
          intro h
          exact hz (Prod.ext h.1.symm (Prod.ext h.2.1.symm h.2.2))
        by_cases h1 : z.2.2 = true
        · by_cases h2 : a' = z.1 ∧ d = z.2.1
          · exact False.elim (hne ⟨h2.1, h2.2, h1⟩)
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  · simp only [hc, ite_false, mul_zero]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h1 : z.2.2 = c
    · simp [h1, hc]
    · simp [h1]

theorem conj_step_assoc {B₁ B₂ B₃ : Type} [Fintype B₁] [Fintype B₂] [Fintype B₃]
    [DecidableEq B₁] [DecidableEq B₂] [DecidableEq B₃]
    (L : Matrix B₃ B₂ ℂ) (K : Matrix B₂ B₁ ℂ) (X : CMatrix B₁) :
    L * (K * X * Kᴴ) * Lᴴ = (L * K) * X * (L * K)ᴴ := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem single_unitary_kraus_complete (U : Matrix.unitaryGroup A ℂ) :
    ∑ _ : Fin 1, ((U : CMatrix A))ᴴ * (U : CMatrix A) = 1 := by
  rw [Finset.univ_unique, Finset.sum_singleton]
  exact Matrix.UnitaryGroup.star_mul_self U

/-- Unitary quantum switch channel on `A × Bool` for unitary pair `U, V ∈ U(A)`. -/
def unitarySwitchChannel (U V : Matrix.unitaryGroup A ℂ) : Channel (A × Bool) (A × Bool) :=
  ICO.ClassicalDilation.isometryChannel (pair U V) (pair_complete U V)

theorem unitarySwitchChannel_eq_fullChannel (U V : Matrix.unitaryGroup A ℂ) :
    unitarySwitchChannel U V =
      fullChannel (by decide : 0 < 1) (by decide : 0 < 1) (fun _ => U) (fun _ => V) := by
  apply channel_eq_of_map_eq
  ext X ij kl
  simp [unitarySwitchChannel, ICO.ClassicalDilation.isometryChannel,
    fullChannel, fullKraus, uniformCoefficient, MatrixMap.ofKraus]

theorem tree_node_map_apply {H O B C L : Type} [Fintype H] [Fintype O] [Fintype B]
    [Fintype C] [Fintype L] [DecidableEq H] [DecidableEq O] [DecidableEq B]
    [DecidableEq C] [DecidableEq L] {q : ℕ}
    (I : Instrument B C L) (next : L → BudgetQueryTree.Tree H O q C) (first second : Channel H H)
    (X : CMatrix B) :
    ((BudgetQueryTree.Tree.node I next).channel first second).map X =
      ∑ l : L, ((next l).channel first second).map (I.op l * X * (I.op l)ᴴ) :=
  adaptiveMap_apply I (fun l => (next l).channel first second) X

theorem tree_query_map_apply {H O : Type} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O] {q : ℕ}
    (b : Bool) (after : BudgetQueryTree.Tree H O q H) (first second : Channel H H) (X : CMatrix H) :
    ((BudgetQueryTree.Tree.query b after).channel first second).map X =
      (after.channel first second).map ((if b then second else first).map X) := rfl

theorem tree_stop_map_apply {H O B : Type} [Fintype H] [Fintype O] [Fintype B]
    [DecidableEq H] [DecidableEq O] [DecidableEq B] {q : ℕ}
    (after : Channel B O) (first second : Channel H H) (X : CMatrix B) :
    ((BudgetQueryTree.Tree.stop after : BudgetQueryTree.Tree H O q B).channel first second).map X =
      after.map X := rfl

/-- **Remark `rem:unitary` (Three calls simulate the switch on unitary boxes)**:
For any unitary boxes `U, V ∈ U(A)`, the 3-call tree `unitaryThreeCallTree a₀`
implements the exact unitary switch channel `unitarySwitchChannel U V`
(and equivalently `fullChannel _ _ (fun _ => U) (fun _ => V)`) on `A × Bool`. -/
theorem unitaryThreeCallTree_channel_eq (a₀ : A) (U V : Matrix.unitaryGroup A ℂ) :
    (unitaryThreeCallTree a₀).channel
      (ICO.ClassicalDilation.oracleChannel U)
      (ICO.ClassicalDilation.oracleChannel V) =
    unitarySwitchChannel U V := by
  apply channel_eq_of_map_eq
  ext X ij kl
  have hmap :
      ((unitaryThreeCallTree a₀).channel
        (ICO.ClassicalDilation.oracleChannel U)
        (ICO.ClassicalDilation.oracleChannel V)).map X =
      (unitarySwitchChannel U V).map X := by
    unfold unitaryThreeCallTree
    simp only [tree_node_map_apply, Fintype.sum_unique,
      preInstrument, cswapTrueInstrument, cswapFalseInstrument,
      tree_query_map_apply, tree_stop_map_apply, Bool.false_eq_true, ite_false, ite_true]
    simp_rw [ICO.ClassicalDilation.oracleChannel_apply, conj_step_assoc,
      stage1Matrix_eq, stage2Matrix_eq, stage3Matrix_eq, stage4Matrix_eq, stage5Matrix_eq]
    rw [unitarySwitchChannel, ICO.ClassicalDilation.isometryChannel_apply]
    change (∑ d : A, postKraus d *
        (stage5Matrix a₀ (U : CMatrix A) (V : CMatrix A) * X *
          (stage5Matrix a₀ (U : CMatrix A) (V : CMatrix A))ᴴ) *
        (postKraus d)ᴴ) =
      pair U V * X * (pair U V)ᴴ
    simp_rw [conj_step_assoc, postKraus_mul_stage5Matrix]
    have hcol : ∑ d : A, (U : CMatrix A) d a₀ * star ((U : CMatrix A) d a₀) = 1 := by
      have hU := congrFun (congrFun (Matrix.UnitaryGroup.star_mul_self U) a₀) a₀
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, ite_true] at hU
      refine (Finset.sum_congr rfl fun d _ => ?_).trans hU
      ring
    have hterm (d : A) :
        ((U : CMatrix A) d a₀ • pair U V) * X *
          ((U : CMatrix A) d a₀ • pair U V)ᴴ =
        ((U : CMatrix A) d a₀ * star ((U : CMatrix A) d a₀)) •
          (pair U V * X * (pair U V)ᴴ) := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_smul, mul_comm]
    change (∑ d : A, ((U : CMatrix A) d a₀ • pair U V) * X *
      ((U : CMatrix A) d a₀ • pair U V)ᴴ) = _
    simp_rw [hterm]
    rw [← Finset.sum_smul, hcol, one_smul]
  exact congrFun (congrFun hmap ij) kl

/-- Same 3-call exact simulation stated with `fullChannel` on single-Kraus unitaries. -/
theorem unitaryThreeCallTree_fullChannel_eq (a₀ : A) (U V : Matrix.unitaryGroup A ℂ) :
    (unitaryThreeCallTree a₀).channel
      (ICO.ClassicalDilation.oracleChannel U)
      (ICO.ClassicalDilation.oracleChannel V) =
    fullChannel (by decide : 0 < 1) (by decide : 0 < 1) (fun _ => U) (fun _ => V) := by
  rw [unitaryThreeCallTree_channel_eq a₀ U V, unitarySwitchChannel_eq_fullChannel U V]

/-- Same 3-call exact simulation stated with `ICO.AllChannelDilation.oracleChannel`. -/
theorem unitaryThreeCallTree_allChannel_eq (a₀ : A) (U V : Matrix.unitaryGroup A ℂ) :
    (unitaryThreeCallTree a₀).channel
      (oracleChannel (M := A × Bool) (fun _ : Fin 1 => (U : CMatrix A))
        (single_unitary_kraus_complete U))
      (oracleChannel (M := A × Bool) (fun _ : Fin 1 => (V : CMatrix A))
        (single_unitary_kraus_complete V)) =
    unitarySwitchChannel U V := by
  have hU :
      oracleChannel (M := A × Bool) (fun _ : Fin 1 => (U : CMatrix A))
        (single_unitary_kraus_complete U) =
      ICO.ClassicalDilation.oracleChannel U := by
    apply channel_eq_of_map_eq
    ext X i j
    simp [oracleChannel, oracleMap, ICO.ClassicalDilation.oracleChannel,
      ICO.ClassicalDilation.isometryChannel, MatrixMap.ofKraus]
  have hV :
      oracleChannel (M := A × Bool) (fun _ : Fin 1 => (V : CMatrix A))
        (single_unitary_kraus_complete V) =
      ICO.ClassicalDilation.oracleChannel V := by
    apply channel_eq_of_map_eq
    ext X i j
    simp [oracleChannel, oracleMap, ICO.ClassicalDilation.oracleChannel,
      ICO.ClassicalDilation.isometryChannel, MatrixMap.ofKraus]
  rw [hU, hV]
  exact unitaryThreeCallTree_channel_eq a₀ U V

/-- The 3-call unitary simulation achieves zero diamond trace distance on all
unitary box pairs. -/
theorem unitaryThreeCallTree_diamond_zero (a₀ : A) (U V : Matrix.unitaryGroup A ℂ) :
    Channel.diamondTraceDistance
      ((unitaryThreeCallTree a₀).channel
        (ICO.ClassicalDilation.oracleChannel U)
        (ICO.ClassicalDilation.oracleChannel V))
      (unitarySwitchChannel U V) ≤ 0 := by
  rw [unitaryThreeCallTree_channel_eq a₀ U V]
  apply Channel.diamondTraceDistance_le_of_inputReferenceBound
  intro ω
  change (1 / 2 : ℝ) * traceNorm (_ - _) ≤ 0
  simp [traceNorm_zero]

/-! ### 1.1 One Unitary Box and One Arbitrary CPTP Channel (`rem:unitary`, R9) -/

theorem postChannel_stage5Matrix_unitary (a₀ : A) (U : Matrix.unitaryGroup A ℂ)
    (V : CMatrix A) (X : CMatrix (A × Bool)) :
    (postChannel (A := A)).map
      (stage5Matrix a₀ (U : CMatrix A) V * X * (stage5Matrix a₀ (U : CMatrix A) V)ᴴ) =
    controlled (V * (U : CMatrix A)) ((U : CMatrix A) * V) * X *
      (controlled (V * (U : CMatrix A)) ((U : CMatrix A) * V))ᴴ := by
  let K := controlled (V * (U : CMatrix A)) ((U : CMatrix A) * V)
  change (∑ d : A, postKraus d *
      (stage5Matrix a₀ (U : CMatrix A) V * X *
        (stage5Matrix a₀ (U : CMatrix A) V)ᴴ) *
      (postKraus d)ᴴ) =
    K * X * Kᴴ
  simp_rw [conj_step_assoc, postKraus_mul_stage5Matrix]
  have hcol : ∑ d : A, (U : CMatrix A) d a₀ * star ((U : CMatrix A) d a₀) = 1 := by
    have hU := congrFun (congrFun (Matrix.UnitaryGroup.star_mul_self U) a₀) a₀
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, ite_true] at hU
    refine (Finset.sum_congr rfl fun d _ => ?_).trans hU
    ring
  have hterm (d : A) :
      ((U : CMatrix A) d a₀ • K) * X * ((U : CMatrix A) d a₀ • K)ᴴ =
      ((U : CMatrix A) d a₀ * star ((U : CMatrix A) d a₀)) • (K * X * Kᴴ) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, mul_comm]
  change (∑ d : A, ((U : CMatrix A) d a₀ • K) * X * ((U : CMatrix A) d a₀ • K)ᴴ) = _
  simp_rw [hterm]
  rw [← Finset.sum_smul, hcol, one_smul]

/-- **Remark `rem:unitary` ("One unitary box is easy", Kraus-family form)**:
For any unitary gate `U ∈ U(A)` and any complete Kraus family `V : J → CMatrix A`
(`∑ j, (V j)ᴴ * V j = 1`), the 3-call circuit `unitaryThreeCallTree a₀` of
Figure `fig:unitary` implements the exact quantum switch superoperator with Kraus
operators `j ↦ controlled (V j * U) (U * V j)` on `A × Bool`. -/
theorem unitaryThreeCallTree_unitary_kraus_eq {J : Type} [Fintype J] [DecidableEq J]
    (a₀ : A) (U : Matrix.unitaryGroup A ℂ)
    (V : J → CMatrix A) (hV : ∑ j : J, (V j)ᴴ * V j = 1) :
    ((unitaryThreeCallTree a₀).channel
      (ICO.ClassicalDilation.oracleChannel U)
      (ICO.AllChannelDilation.oracleChannel (M := A × Bool) V hV)).map =
    MatrixMap.ofKraus
      (fun j : J => controlled (V j * (U : CMatrix A)) ((U : CMatrix A) * V j)) := by
  ext X ij kl
  have hmap :
      ((unitaryThreeCallTree a₀).channel
        (ICO.ClassicalDilation.oracleChannel U)
        (ICO.AllChannelDilation.oracleChannel (M := A × Bool) V hV)).map X =
      MatrixMap.ofKraus
        (fun j : J => controlled (V j * (U : CMatrix A)) ((U : CMatrix A) * V j)) X := by
    unfold unitaryThreeCallTree
    simp only [tree_node_map_apply, Fintype.sum_unique,
      preInstrument, cswapTrueInstrument, cswapFalseInstrument,
      tree_query_map_apply, tree_stop_map_apply, Bool.false_eq_true, ite_false, ite_true]
    simp_rw [ICO.ClassicalDilation.oracleChannel_apply, conj_step_assoc,
      stage1Matrix_eq, stage2Matrix_eq]
    have horacle :
        (ICO.AllChannelDilation.oracleChannel (M := A × Bool) V hV).map
          (stage2Matrix a₀ (U : CMatrix A) * X * (stage2Matrix a₀ (U : CMatrix A))ᴴ) =
        ∑ j : J,
          stage3Matrix a₀ (U : CMatrix A) (V j) * X *
            (stage3Matrix a₀ (U : CMatrix A) (V j))ᴴ := by
      change (∑ j : J,
          Matrix.kronecker (V j) (1 : CMatrix (A × Bool)) *
            (stage2Matrix a₀ (U : CMatrix A) * X * (stage2Matrix a₀ (U : CMatrix A))ᴴ) *
            (Matrix.kronecker (V j) (1 : CMatrix (A × Bool)))ᴴ) = _
      simp_rw [conj_step_assoc, stage3Matrix_eq]
    rw [horacle]
    have hstep45 :
        (Matrix.kronecker (U : CMatrix A) (1 : CMatrix (A × Bool)) * cswapFalse) *
          (∑ j : J, stage3Matrix a₀ (U : CMatrix A) (V j) * X *
            (stage3Matrix a₀ (U : CMatrix A) (V j))ᴴ) *
          (Matrix.kronecker (U : CMatrix A) (1 : CMatrix (A × Bool)) * cswapFalse)ᴴ =
        ∑ j : J,
          stage5Matrix a₀ (U : CMatrix A) (V j) * X *
            (stage5Matrix a₀ (U : CMatrix A) (V j))ᴴ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hmat :
          Matrix.kronecker (U : CMatrix A) (1 : CMatrix (A × Bool)) * cswapFalse *
            stage3Matrix a₀ (U : CMatrix A) (V j) =
          stage5Matrix a₀ (U : CMatrix A) (V j) := by
        rw [Matrix.mul_assoc, stage4Matrix_eq, stage5Matrix_eq]
      rw [conj_step_assoc, hmat]
    rw [hstep45, map_sum]
    simp_rw [postChannel_stage5Matrix_unitary]
    rfl
  exact congrFun (congrFun hmap ij) kl

/-- Target-register CPTP channel `X ↦ U X Uᴴ` associated to `U ∈ U(A)`. -/
def unitaryTargetChannel (U : Matrix.unitaryGroup A ℂ) : Channel A A :=
  ICO.ClassicalDilation.isometryChannel (U : CMatrix A) (Matrix.UnitaryGroup.star_mul_self U)

theorem channelKraus_complete (Φ : Channel A A) :
    ∑ k : A × A, (ICO.ClassicalDilation.channelKraus Φ k)ᴴ *
      ICO.ClassicalDilation.channelKraus Φ k = 1 := by
  have hadj : MatrixMap.krausAdjoint (ICO.ClassicalDilation.channelKraus Φ) 1 = 1 := by
    apply MatrixMap.krausAdjoint_one_of_tracePreserving
    rw [← ICO.ClassicalDilation.channelKraus_map Φ]
    exact Φ.tracePreserving
  simpa [MatrixMap.krausAdjoint] using hadj

theorem controlledSwitchKraus_complete {I J : Type*} [Fintype I] [Fintype J]
    (U : I → CMatrix A) (V : J → CMatrix A)
    (hU : ∑ i : I, (U i)ᴴ * U i = 1) (hV : ∑ j : J, (V j)ᴴ * V j = 1) :
    ∑ ij : I × J,
      (controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2))ᴴ *
        controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2) = 1 := by
  have hsum_controlled (T S : I × J → CMatrix A) :
      (∑ ij : I × J, controlled (T ij) (S ij)) =
        controlled (∑ ij : I × J, T ij) (∑ ij : I × J, S ij) := by
    ext ⟨x, b⟩ ⟨y, c⟩
    cases b <;> cases c <;> simp [controlled, Matrix.sum_apply]
  have hterm (ij : I × J) :
      (controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2))ᴴ *
        controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2) =
      controlled ((U ij.1)ᴴ * ((V ij.2)ᴴ * V ij.2) * U ij.1)
        ((V ij.2)ᴴ * ((U ij.1)ᴴ * U ij.1) * V ij.2) := by
    rw [controlled_star, controlled_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp_rw [hterm]
  rw [hsum_controlled]
  have hleft :
      (∑ ij : I × J, (U ij.1)ᴴ * ((V ij.2)ᴴ * V ij.2) * U ij.1) = 1 := by
    rw [Fintype.sum_prod_type]
    have hi (i : I) :
        (∑ j : J, (U i)ᴴ * ((V j)ᴴ * V j) * U i) = (U i)ᴴ * U i := by
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, hV, Matrix.mul_one]
    simp_rw [hi]
    exact hU
  have hright :
      (∑ ij : I × J, (V ij.2)ᴴ * ((U ij.1)ᴴ * U ij.1) * V ij.2) = 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hj (j : J) :
        (∑ i : I, (V j)ᴴ * ((U i)ᴴ * U i) * V j) = (V j)ᴴ * V j := by
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, hU, Matrix.mul_one]
    simp_rw [hj]
    exact hV
  rw [hleft, hright, controlled_one]

/-- Slot-`A` index helper for the intrinsic Choi-bilinear quantum switch on `A × Bool`. -/
def switchPairA (c : Bool) (p r a : A) : A × A :=
  if c then (a, r) else (p, a)

/-- Slot-`B` index helper for the intrinsic Choi-bilinear quantum switch on `A × Bool`. -/
def switchPairB (c : Bool) (p r a : A) : A × A :=
  if c then (p, a) else (a, r)

/-- Intrinsic representation-independent quantum switch superoperator `SW[JA, JB]`
on `A × Bool`, expressed directly as a bilinear function of the slot Choi matrices
`JA, JB : CMatrix (A × A)`. -/
def channelSwitchFromChoi (JA JB : CMatrix (A × A)) : MatrixMap (A × Bool) (A × Bool) where
  toFun X := fun rc sc' =>
    ∑ p : A, ∑ q : A, ∑ a : A, ∑ b : A,
      X (p, rc.2) (q, sc'.2) *
        JA (switchPairA rc.2 p rc.1 a) (switchPairA sc'.2 q sc'.1 b) *
        JB (switchPairB rc.2 p rc.1 a) (switchPairB sc'.2 q sc'.1 b)
  map_add' X Y := by
    ext rc sc'
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    ext rc sc'
    simp [mul_assoc, Finset.mul_sum]

theorem choi_ofKraus_entry_gen {I : Type*} [Fintype I]
    (U : I → CMatrix A) (pa qb : A × A) :
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

theorem ordered_mul_entry_bool (u v : CMatrix A) (c : Bool) (r p : A) :
    (if c then (u * v) r p else (v * u) r p) =
      ∑ a : A,
        u (switchPairA c p r a).2 (switchPairA c p r a).1 *
          v (switchPairB c p r a).2 (switchPairB c p r a).1 := by
  cases c <;> simp [switchPairA, switchPairB, Matrix.mul_apply, mul_comm]

theorem controlled_mul_left_entry (T S : CMatrix A) (X : CMatrix (A × Bool))
    (r q : A) (c c' : Bool) :
    (controlled T S * X) (r, c) (q, c') =
      ∑ p : A, (if c then S r p else T r p) * X (p, c) (q, c') := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, controlled]
  rw [Finset.sum_comm, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

theorem controlled_sandwich_entry (u v : CMatrix A) (X : CMatrix (A × Bool))
    (r s : A) (c c' : Bool) :
    (controlled (v * u) (u * v) * X * (controlled (v * u) (u * v))ᴴ) (r, c) (s, c') =
      ∑ p : A, ∑ q : A,
        (if c then (u * v) r p else (v * u) r p) *
          X (p, c) (q, c') *
          star (if c' then (u * v) s q else (v * u) s q) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single c']
  · simp only [Matrix.conjTranspose_apply, controlled, ite_true,
      controlled_mul_left_entry, Finset.sum_mul]
    rw [Finset.sum_comm]
  · intro b _ hb
    simp [Matrix.conjTranspose_apply, controlled, hb.symm]
  · intro hc'
    exact absurd (Finset.mem_univ c') hc'

theorem controlled_kraus_sum_eq_choi_prod {I J : Type*} [Fintype I] [Fintype J]
    (U : I → CMatrix A) (V : J → CMatrix A)
    (c c' : Bool) (r s p q : A) :
    (∑ i : I, ∑ j : J,
      (if c then (U i * V j) r p else (V j * U i) r p) *
        star (if c' then (U i * V j) s q else (V j * U i) s q)) =
    ∑ a : A, ∑ b : A,
      MatrixMap.choi (MatrixMap.ofKraus U) (switchPairA c p r a) (switchPairA c' q s b) *
        MatrixMap.choi (MatrixMap.ofKraus V) (switchPairB c p r a) (switchPairB c' q s b) := by
  simp_rw [ordered_mul_entry_bool, star_sum, star_mul', choi_ofKraus_entry_gen]
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

theorem channelSwitchFromChoi_ofKraus {I J : Type*} [Fintype I] [Fintype J]
    (U : I → CMatrix A) (V : J → CMatrix A) :
    MatrixMap.ofKraus (fun ij : I × J => controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2)) =
      channelSwitchFromChoi (MatrixMap.choi (MatrixMap.ofKraus U))
        (MatrixMap.choi (MatrixMap.ofKraus V)) := by
  ext X ⟨r, c⟩ ⟨s, c'⟩
  change (∑ ij : I × J,
      controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2) * X *
        (controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2))ᴴ) (r, c) (s, c') =
    ∑ p : A, ∑ q : A, ∑ a : A, ∑ b : A,
      X (p, c) (q, c') *
        MatrixMap.choi (MatrixMap.ofKraus U) (switchPairA c p r a) (switchPairA c' q s b) *
        MatrixMap.choi (MatrixMap.ofKraus V) (switchPairB c p r a) (switchPairB c' q s b)
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, controlled_sandwich_entry]
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
        (if c then (U i * V j) r p else (V j * U i) r p) *
          X (p, c) (q, c') *
          star (if c' then (U i * V j) s q else (V j * U i) s q)) =
      X (p, c) (q, c') *
        (∑ i : I, ∑ j : J,
          (if c then (U i * V j) r p else (V j * U i) r p) *
            star (if c' then (U i * V j) s q else (V j * U i) s q)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor, controlled_kraus_sum_eq_choi_prod]
  simp only [Finset.mul_sum, mul_assoc]

/-- Intrinsic CPTP quantum switch channel `SW[Φ, Ψ]` on `A × Bool` for arbitrary
CPTP channels `Φ, Ψ : Channel A A`, defined directly from the slot Choi matrices
`MatrixMap.choi Φ.map` and `MatrixMap.choi Ψ.map`. -/
def channelSwitch (Φ Ψ : Channel A A) : Channel (A × Bool) (A × Bool) where
  map := channelSwitchFromChoi (MatrixMap.choi Φ.map) (MatrixMap.choi Ψ.map)
  completelyPositive := by
    rw [ICO.ClassicalDilation.channelKraus_map Φ,
      ICO.ClassicalDilation.channelKraus_map Ψ, ← channelSwitchFromChoi_ofKraus]
    exact MatrixMap.ofKraus_completelyPositive _
  tracePreserving := by
    rw [ICO.ClassicalDilation.channelKraus_map Φ,
      ICO.ClassicalDilation.channelKraus_map Ψ, ← channelSwitchFromChoi_ofKraus]
    apply MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one
    have hc := controlledSwitchKraus_complete
      (ICO.ClassicalDilation.channelKraus Φ)
      (ICO.ClassicalDilation.channelKraus Ψ)
      (channelKraus_complete Φ) (channelKraus_complete Ψ)
    simpa [MatrixMap.krausAdjoint] using hc
  mapsPositive := by
    rw [ICO.ClassicalDilation.channelKraus_map Φ,
      ICO.ClassicalDilation.channelKraus_map Ψ, ← channelSwitchFromChoi_ofKraus]
    exact MatrixMap.ofKraus_mapsPositive _

theorem channelSwitch_map_ofKraus {I J : Type*} [Fintype I] [Fintype J]
    (Φ Ψ : Channel A A) (U : I → CMatrix A) (V : J → CMatrix A)
    (hΦ : Φ.map = MatrixMap.ofKraus U) (hΨ : Ψ.map = MatrixMap.ofKraus V) :
    (channelSwitch Φ Ψ).map =
      MatrixMap.ofKraus (fun ij : I × J => controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2)) := by
  change channelSwitchFromChoi (MatrixMap.choi Φ.map) (MatrixMap.choi Ψ.map) = _
  rw [hΦ, hΨ, ← channelSwitchFromChoi_ofKraus]

theorem kron_idChannel_eq_liftMap_gen (f : MatrixMap A A) :
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
        (fun x y : A => Matrix.single (a, m) (b, n) (1 : ℂ) (x, m) (y, n)) =
          Matrix.single a b (1 : ℂ) := by
      ext x y
      simp [Matrix.single]
    rw [hmat]
    simp
  · have hmat :
        (fun x y : A => Matrix.single (a, m) (b, n) (1 : ℂ) (x, m') (y, n')) =
          (0 : CMatrix A) := by
      ext x y
      simp only [Matrix.single, Matrix.of_apply, Matrix.zero_apply, Prod.mk.injEq]
      split_ifs with h
      · exact absurd ⟨h.1.2, h.2.2⟩ hmn
      · rfl
    rw [hmat, map_zero]
    simp [hmn]

theorem prod_idChannel_eq_allChannelOracle (Φ : Channel A A) :
    Φ.prod (Channel.idChannel M) =
      ICO.AllChannelDilation.oracleChannel (M := M)
        (ICO.ClassicalDilation.channelKraus Φ) (channelKraus_complete Φ) := by
  apply channel_eq_of_map_eq
  change MatrixMap.kron Φ.map (Channel.idChannel M).map =
    ICO.AllChannelDilation.oracleMap (M := M) (ICO.ClassicalDilation.channelKraus Φ)
  rw [kron_idChannel_eq_liftMap_gen, ICO.OracleLift.oracleMap_lift,
    ICO.ClassicalDilation.channelKraus_map]

/-- **Remark `rem:unitary` ("One unitary box is easy", intrinsic `Channel` form)**:
When the first box `A` is known to be unitary (`U ∈ U(A)`), the 3-call circuit
`unitaryThreeCallTree a₀` of Figure `fig:unitary` implements the exact quantum switch
channel `channelSwitch (unitaryTargetChannel U) B_ch` on `A × Bool` for **every**
CPTP channel `B_ch : Channel A A`. -/
theorem unitaryThreeCallTree_unitary_left_channel_eq
    (a₀ : A) (U : Matrix.unitaryGroup A ℂ) (B_ch : Channel A A) :
    (unitaryThreeCallTree a₀).channel
      (ICO.ClassicalDilation.oracleChannel U)
      (B_ch.prod (Channel.idChannel (A × Bool))) =
    channelSwitch (unitaryTargetChannel U) B_ch := by
  apply channel_eq_of_map_eq
  rw [prod_idChannel_eq_allChannelOracle (M := A × Bool) B_ch,
    unitaryThreeCallTree_unitary_kraus_eq a₀ U
      (ICO.ClassicalDilation.channelKraus B_ch) (channelKraus_complete B_ch),
    channelSwitch_map_ofKraus (unitaryTargetChannel U) B_ch
      (fun _ : PUnit.{1} => (U : CMatrix A))
      (ICO.ClassicalDilation.channelKraus B_ch)
      rfl (ICO.ClassicalDilation.channelKraus_map B_ch)]
  ext X ij kl
  simp [MatrixMap.ofKraus, Fintype.sum_prod_type]

theorem channel_comp_map_apply {X₁ X₂ X₃ : Type*} [Fintype X₁] [Fintype X₂] [Fintype X₃]
    [DecidableEq X₁] [DecidableEq X₂] [DecidableEq X₃]
    (Φ : Channel X₂ X₃) (Ψ : Channel X₁ X₂) (X : CMatrix X₁) :
    (Φ.comp Ψ).map X = Φ.map (Ψ.map X) := rfl

theorem ofKraus_apply {X₁ X₂ κ : Type*} [Fintype X₁] [Fintype X₂] [Fintype κ]
    [DecidableEq X₁] [DecidableEq X₂]
    (K : κ → Matrix X₂ X₁ ℂ) (X : CMatrix X₁) :
    MatrixMap.ofKraus K X = ∑ k : κ, K k * X * (K k)ᴴ := rfl

/-- Canonical wire-reordering equivalence `(a, false) ↦ (0, a)`, `(a, true) ↦ (1, a)`
between target-and-`Bool`-control `Fin d × Bool` and `Fin 2`-control-and-target `Fin 2 × Fin d`. -/
def targetBoolEquivControlFin2 (d : ℕ) : (Fin d × Bool) ≃ (Fin 2 × Fin d) where
  toFun ab := (if ab.2 then 1 else 0, ab.1)
  invFun ca := (ca.2, if ca.1 = 0 then false else true)
  left_inv := by
    rintro ⟨a, b⟩
    cases b <;> simp
  right_inv := by
    rintro ⟨c, a⟩
    fin_cases c <;> simp

/-- Permutation matrix swapping `Fin d × Bool` into `Fin 2 × Fin d`. -/
def toFin2ControlMatrix (d : ℕ) : Matrix (Fin 2 × Fin d) (Fin d × Bool) ℂ :=
  fun ca ab => if ca = targetBoolEquivControlFin2 d ab then 1 else 0

/-- Inverse permutation matrix swapping `Fin 2 × Fin d` into `Fin d × Bool`. -/
def fromFin2ControlMatrix (d : ℕ) : Matrix (Fin d × Bool) (Fin 2 × Fin d) ℂ :=
  (toFin2ControlMatrix d)ᴴ

theorem toFin2ControlMatrix_isometry (d : ℕ) :
    (toFin2ControlMatrix d)ᴴ * toFin2ControlMatrix d = 1 := by
  ext ab₁ ab₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, toFin2ControlMatrix, Matrix.one_apply]
  rw [Finset.sum_eq_single (targetBoolEquivControlFin2 d ab₁)]
  · by_cases h : ab₁ = ab₂
    · subst h; simp
    · have hne : targetBoolEquivControlFin2 d ab₁ ≠ targetBoolEquivControlFin2 d ab₂ :=
        fun heq => h ((targetBoolEquivControlFin2 d).injective heq)
      simp [h, hne]
  · intro ca _ hca
    simp [hca]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

theorem fromFin2ControlMatrix_isometry (d : ℕ) :
    (fromFin2ControlMatrix d)ᴴ * fromFin2ControlMatrix d = 1 := by
  unfold fromFin2ControlMatrix
  rw [Matrix.conjTranspose_conjTranspose]
  ext ca₁ ca₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, toFin2ControlMatrix, Matrix.one_apply]
  rw [Finset.sum_eq_single ((targetBoolEquivControlFin2 d).symm ca₁)]
  · by_cases h : ca₁ = ca₂
    · subst h; simp
    · have hne : ca₂ ≠ ca₁ := Ne.symm h
      simp [Equiv.apply_symm_apply, h, hne]
  · intro ab _ hab
    have hne : ca₁ ≠ targetBoolEquivControlFin2 d ab := by
      intro heq
      apply hab
      rw [heq, Equiv.symm_apply_apply]
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- Unitary CPTP wire-swap channel from `Fin d × Bool` to `Fin 2 × Fin d`. -/
def toFin2ControlChannel (d : ℕ) : Channel (Fin d × Bool) (Fin 2 × Fin d) :=
  ICO.ClassicalDilation.isometryChannel (toFin2ControlMatrix d) (toFin2ControlMatrix_isometry d)

/-- Inverse unitary CPTP wire-swap channel from `Fin 2 × Fin d` to `Fin d × Bool`. -/
def fromFin2ControlChannel (d : ℕ) : Channel (Fin 2 × Fin d) (Fin d × Bool) :=
  ICO.ClassicalDilation.isometryChannel (fromFin2ControlMatrix d) (fromFin2ControlMatrix_isometry d)

theorem toFin2ControlMatrix_controlled_mul {d : ℕ} (U V : CMatrix (Fin d)) :
    toFin2ControlMatrix d * controlled (V * U) (U * V) * fromFin2ControlMatrix d =
      ICO.PolarizationOrderedArbitraryControl.fullControlOrderedPair U V := by
  ext ca₁ ca₂
  simp only [Matrix.mul_apply, fromFin2ControlMatrix, Matrix.conjTranspose_apply,
    toFin2ControlMatrix]
  rw [Finset.sum_eq_single ((targetBoolEquivControlFin2 d).symm ca₂)]
  · rw [Finset.sum_eq_single ((targetBoolEquivControlFin2 d).symm ca₁)]
    · rcases ca₁ with ⟨c₁, a₁⟩
      rcases ca₂ with ⟨c₂, a₂⟩
      fin_cases c₁ <;> fin_cases c₂ <;>
        simp [targetBoolEquivControlFin2, controlled,
          ICO.PolarizationOrderedArbitraryControl.fullControlOrderedPair]
    · intro ab₁ _ hab₁
      have hne : ca₁ ≠ targetBoolEquivControlFin2 d ab₁ := by
        intro heq; exact hab₁ (by rw [heq, Equiv.symm_apply_apply])
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · intro ab₂ _ hab₂
    have hne : ca₂ ≠ targetBoolEquivControlFin2 d ab₂ := by
      intro heq; exact hab₂ (by rw [heq, Equiv.symm_apply_apply])
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

theorem ofKraus_conj_fin2Control_eq_fullControlSwitchMap {d : ℕ}
    {I J : Type} [Fintype I] [Fintype J]
    (U : I → CMatrix (Fin d)) (V : J → CMatrix (Fin d)) (X : CMatrix (Fin 2 × Fin d)) :
    toFin2ControlMatrix d *
      (MatrixMap.ofKraus
        (fun ij : I × J => controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2))
        (fromFin2ControlMatrix d * X * (fromFin2ControlMatrix d)ᴴ)) *
      (toFin2ControlMatrix d)ᴴ =
    ICO.PolarizationOrderedArbitraryControl.fullControlSwitchMap U V X := by
  rw [ofKraus_apply, ICO.PolarizationOrderedArbitraryControl.fullControlSwitchMap,
    ofKraus_apply, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [conj_step_assoc (controlled (V ij.2 * U ij.1) (U ij.1 * V ij.2))
        (fromFin2ControlMatrix d) X,
      conj_step_assoc (toFin2ControlMatrix d) _ X,
      ← Matrix.mul_assoc,
      toFin2ControlMatrix_controlled_mul]

theorem channelSwitch_conj_fin2Control_eq_fullSwitchChannelMap {d : ℕ} [Nontrivial (Fin d)]
    (A_ch B_ch : Channel (Fin d) (Fin d)) :
    ((toFin2ControlChannel d).comp
        ((channelSwitch A_ch B_ch).comp (fromFin2ControlChannel d))).map =
      ICO.PolarizationOrderedArbitraryControl.fullSwitchChannelMap A_ch.map B_ch.map := by
  ext X ca₁ ca₂
  have hmap :
      ((toFin2ControlChannel d).comp
          ((channelSwitch A_ch B_ch).comp (fromFin2ControlChannel d))).map X =
        ICO.PolarizationOrderedArbitraryControl.fullSwitchChannelMap A_ch.map B_ch.map X := by
    rw [channel_comp_map_apply, channel_comp_map_apply,
      toFin2ControlChannel, fromFin2ControlChannel,
      ICO.ClassicalDilation.isometryChannel_apply,
      ICO.ClassicalDilation.isometryChannel_apply,
      channelSwitch_map_ofKraus A_ch B_ch
        (ICO.ClassicalDilation.channelKraus A_ch)
        (ICO.ClassicalDilation.channelKraus B_ch)
        (ICO.ClassicalDilation.channelKraus_map A_ch)
        (ICO.ClassicalDilation.channelKraus_map B_ch)]
    conv_rhs =>
      rw [ICO.ClassicalDilation.channelKraus_map A_ch,
        ICO.ClassicalDilation.channelKraus_map B_ch,
        ICO.PolarizationOrderedArbitraryControl.fullSwitchChannelMap_ofKraus]
    exact ofKraus_conj_fin2Control_eq_fullControlSwitchMap
      (ICO.ClassicalDilation.channelKraus A_ch)
      (ICO.ClassicalDilation.channelKraus B_ch) X
  exact congrFun (congrFun hmap ca₁) ca₂

/-- **Remark `rem:unitary` (`Fin 2 × Fin d` bridge to `fullSwitchChannelMap`)**:
For any `d ≥ 2` (`[Nontrivial (Fin d)]`), dummy basis state `a₀ : Fin d`, unitary
gate `U ∈ U(Fin d)`, and arbitrary CPTP channel `B_ch : Channel (Fin d) (Fin d)`,
conjugating the 3-call circuit channel on `Fin d × Bool` by the canonical
control-target wire swap into `Fin 2 × Fin d` reproduces
`ICO.PolarizationOrderedArbitraryControl.fullSwitchChannelMap` on
`(unitaryTargetChannel U).map` and `B_ch.map`. -/
theorem unitaryThreeCallTree_fullSwitchChannelMap_eq {d : ℕ} [Nontrivial (Fin d)]
    (a₀ : Fin d) (U : Matrix.unitaryGroup (Fin d) ℂ) (B_ch : Channel (Fin d) (Fin d)) :
    ((toFin2ControlChannel d).comp
        (((unitaryThreeCallTree a₀).channel
          (ICO.ClassicalDilation.oracleChannel U)
          (B_ch.prod (Channel.idChannel (Fin d × Bool)))).comp
        (fromFin2ControlChannel d))).map =
      ICO.PolarizationOrderedArbitraryControl.fullSwitchChannelMap
        (unitaryTargetChannel U).map B_ch.map := by
  rw [unitaryThreeCallTree_unitary_left_channel_eq a₀ U B_ch]
  exact channelSwitch_conj_fin2Control_eq_fullSwitchChannelMap (unitaryTargetChannel U) B_ch

/-! ### 1.2 Symmetric Right-Unitary 3-Call Simulation (`B` Unitary, `A` Arbitrary CPTP) -/

/-- Unitary Pauli-`X` flip `(a, c) ↦ (a, !c)` on the `Bool` control qubit of `A × Bool`. -/
def controlFlip : CMatrix (A × Bool) :=
  fun x y => if x.1 = y.1 ∧ x.2 = !y.2 then 1 else 0

theorem controlFlip_conjTranspose : (controlFlip (A := A))ᴴ = controlFlip (A := A) := by
  ext ⟨a₁, c₁⟩ ⟨a₂, c₂⟩
  by_cases ha : a₁ = a₂
  · subst ha
    cases c₁ <;> cases c₂ <;> simp [controlFlip, Matrix.conjTranspose_apply]
  · have ha' : a₂ ≠ a₁ := Ne.symm ha
    simp [controlFlip, Matrix.conjTranspose_apply, ha, ha']

theorem controlFlip_mul_self : controlFlip (A := A) * controlFlip (A := A) = 1 := by
  ext ⟨a₁, c₁⟩ ⟨a₂, c₂⟩
  simp only [Matrix.mul_apply, controlFlip, Matrix.one_apply]
  rw [Finset.sum_eq_single (a₁, !c₁)]
  · cases c₁ <;> cases c₂ <;> by_cases ha : a₁ = a₂ <;> simp [Prod.ext_iff, ha]
  · intro z _ hz
    have hne : ¬(a₁ = z.1 ∧ c₁ = !z.2) := by
      intro h
      apply hz
      rcases z with ⟨za, zc⟩
      have hc : zc = !c₁ := by cases c₁ <;> cases zc <;> cases h.2 <;> rfl
      exact Prod.ext h.1.symm hc
    by_cases h : a₁ = z.1 ∧ c₁ = !z.2
    · exact False.elim (hne h)
    · simp [h]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

theorem controlFlip_complete : (controlFlip (A := A))ᴴ * controlFlip (A := A) = 1 := by
  rw [controlFlip_conjTranspose]
  exact controlFlip_mul_self

def controlFlipChannel : Channel (A × Bool) (A × Bool) :=
  ICO.ClassicalDilation.isometryChannel (controlFlip (A := A)) (controlFlip_complete (A := A))

def preSecondIsometry (a₀ : A) : Matrix (A × (A × Bool)) (A × Bool) ℂ :=
  preIsometry a₀ * controlFlip (A := A)

theorem preSecondIsometry_complete (a₀ : A) :
    (preSecondIsometry a₀)ᴴ * preSecondIsometry a₀ = 1 := by
  unfold preSecondIsometry
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (preIsometry a₀)ᴴ,
    preIsometry_complete, Matrix.one_mul, controlFlip_complete]

def preSecondInstrument (a₀ : A) : Instrument (A × Bool) (A × (A × Bool)) PUnit where
  op _ := preSecondIsometry a₀
  complete := by simpa using preSecondIsometry_complete a₀

/-- **Remark `rem:unitary` symmetric 3-call query tree (when box `B` is unitary)**:
Exchanges the roles of `A` and `B` relative to `unitaryThreeCallTree a₀`, calling
`second` (`B`), `first` (`A`), and `second` (`B`). -/
def unitarySecondThreeCallTree (a₀ : A) :
    Tree (A × (A × Bool)) (A × Bool) 3 (A × Bool) :=
  .node (preSecondInstrument a₀) (fun _ =>
    .query true (.node (cswapTrueInstrument (A := A)) (fun _ =>
      .query false (.node (cswapFalseInstrument (A := A)) (fun _ =>
        .query true (.stop ((controlFlipChannel (A := A)).comp (postChannel (A := A)))))))))

theorem unitarySecondThreeCallTree_map_eq (a₀ : A)
    (first second : Channel (A × (A × Bool)) (A × (A × Bool)))
    (X : CMatrix (A × Bool)) :
    ((unitarySecondThreeCallTree a₀).channel first second).map X =
      controlFlip *
        (((unitaryThreeCallTree a₀).channel second first).map
          (controlFlip * X * (controlFlip (A := A))ᴴ)) *
        (controlFlip (A := A))ᴴ := by
  unfold unitarySecondThreeCallTree unitaryThreeCallTree
  simp only [tree_node_map_apply, Fintype.sum_unique,
    preSecondInstrument, preInstrument, cswapTrueInstrument, cswapFalseInstrument,
    tree_query_map_apply, tree_stop_map_apply, Bool.false_eq_true, ite_false, ite_true]
  rw [preSecondIsometry, ← conj_step_assoc (preIsometry a₀) (controlFlip (A := A)) X,
    channel_comp_map_apply, controlFlipChannel, ICO.ClassicalDilation.isometryChannel_apply]

theorem controlFlip_controlled_mul (T S : CMatrix A) :
    controlFlip (A := A) * controlled T S * (controlFlip (A := A))ᴴ = controlled S T := by
  rw [controlFlip_conjTranspose]
  ext ⟨a₁, c₁⟩ ⟨a₂, c₂⟩
  simp only [Matrix.mul_apply, controlFlip]
  rw [Finset.sum_eq_single (a₂, !c₂)]
  · rw [Finset.sum_eq_single (a₁, !c₁)]
    · cases c₁ <;> cases c₂ <;> simp [controlled]
    · intro z₁ _ hz₁
      have hne : ¬(a₁ = z₁.1 ∧ c₁ = !z₁.2) := by
        intro h
        apply hz₁
        rcases z₁ with ⟨za, zc⟩
        have hc : zc = !c₁ := by cases c₁ <;> cases zc <;> cases h.2 <;> rfl
        exact Prod.ext h.1.symm hc
      by_cases h : a₁ = z₁.1 ∧ c₁ = !z₁.2
      · exact False.elim (hne h)
      · simp [h]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · intro z₂ _ hz₂
    have hne : ¬(z₂.1 = a₂ ∧ z₂.2 = !c₂) := by
      intro h; exact hz₂ (Prod.ext h.1 h.2)
    by_cases h : z₂.1 = a₂ ∧ z₂.2 = !c₂
    · exact False.elim (hne h)
    · simp [h]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- **Remark `rem:unitary` (Symmetric Kraus-family form when box `B` is unitary)**:
For any complete Kraus family `U : I → CMatrix A` (`∑ i, (U i)ᴴ * U i = 1`) and any
unitary gate `V ∈ U(A)`, the 3-call circuit `unitarySecondThreeCallTree a₀` implements
the exact quantum switch superoperator with Kraus operators
`i ↦ controlled (V * U i) (U i * V)` on `A × Bool`. -/
theorem unitarySecondThreeCallTree_unitary_kraus_eq {I : Type} [Fintype I] [DecidableEq I]
    (a₀ : A) (U : I → CMatrix A) (hU : ∑ i : I, (U i)ᴴ * U i = 1)
    (V : Matrix.unitaryGroup A ℂ) :
    ((unitarySecondThreeCallTree a₀).channel
      (ICO.AllChannelDilation.oracleChannel (M := A × Bool) U hU)
      (ICO.ClassicalDilation.oracleChannel V)).map =
    MatrixMap.ofKraus
      (fun i : I => controlled ((V : CMatrix A) * U i) (U i * (V : CMatrix A))) := by
  ext X ij kl
  have hmap :
      ((unitarySecondThreeCallTree a₀).channel
        (ICO.AllChannelDilation.oracleChannel (M := A × Bool) U hU)
        (ICO.ClassicalDilation.oracleChannel V)).map X =
      MatrixMap.ofKraus
        (fun i : I => controlled ((V : CMatrix A) * U i) (U i * (V : CMatrix A))) X := by
    rw [unitarySecondThreeCallTree_map_eq,
      unitaryThreeCallTree_unitary_kraus_eq a₀ V U hU,
      ofKraus_apply, ofKraus_apply, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcf :
        controlFlip (A := A) *
          (controlled (U i * (V : CMatrix A)) ((V : CMatrix A) * U i) * controlFlip (A := A)) =
        controlled ((V : CMatrix A) * U i) (U i * (V : CMatrix A)) := by
      have h := controlFlip_controlled_mul (A := A)
        (U i * (V : CMatrix A)) ((V : CMatrix A) * U i)
      rw [controlFlip_conjTranspose] at h
      rw [← Matrix.mul_assoc, h]
    rw [conj_step_assoc (controlled (U i * (V : CMatrix A)) ((V : CMatrix A) * U i))
          (controlFlip (A := A)) X,
        conj_step_assoc (controlFlip (A := A)) _ X,
        hcf]
  exact congrFun (congrFun hmap ij) kl

/-- **Remark `rem:unitary` (Symmetric intrinsic `Channel` form when box `B` is unitary)**:
When the second box `B` is known to be unitary (`V ∈ U(A)`), the role-exchanged 3-call
circuit `unitarySecondThreeCallTree a₀` implements the exact quantum switch channel
`channelSwitch A_ch (unitaryTargetChannel V)` on `A × Bool` for **every** CPTP channel
`A_ch : Channel A A`. -/
theorem unitarySecondThreeCallTree_unitary_right_channel_eq
    (a₀ : A) (A_ch : Channel A A) (V : Matrix.unitaryGroup A ℂ) :
    (unitarySecondThreeCallTree a₀).channel
      (A_ch.prod (Channel.idChannel (A × Bool)))
      (ICO.ClassicalDilation.oracleChannel V) =
    channelSwitch A_ch (unitaryTargetChannel V) := by
  apply channel_eq_of_map_eq
  rw [prod_idChannel_eq_allChannelOracle (M := A × Bool) A_ch,
    unitarySecondThreeCallTree_unitary_kraus_eq a₀
      (ICO.ClassicalDilation.channelKraus A_ch) (channelKraus_complete A_ch) V,
    channelSwitch_map_ofKraus A_ch (unitaryTargetChannel V)
      (ICO.ClassicalDilation.channelKraus A_ch)
      (fun _ : PUnit.{1} => (V : CMatrix A))
      (ICO.ClassicalDilation.channelKraus_map A_ch) rfl]
  ext X ij kl
  simp [MatrixMap.ofKraus, Fintype.sum_prod_type]

/-! ### 1.3 Non-Convexity of Unitary Channels and Failure When `A` Is Non-Unitary -/

/-- Kraus operators `i ↦ |i⟩⟨i|` of the computational-basis dephasing channel `Δ_I` on `Fin 2`. -/
def qubitDephasingKraus (i : Fin 2) : CMatrix (Fin 2) :=
  Matrix.single i i 1

theorem qubitDephasingKraus_complete :
    ∑ i : Fin 2, (qubitDephasingKraus i)ᴴ * qubitDephasingKraus i = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qubitDephasingKraus, Fin.sum_univ_two, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.single]

/-- Computational-basis completely dephasing qubit channel `Δ_I(ρ) = ∑_{i ∈ {0,1}} |i⟩⟨i| ρ |i⟩⟨i|`
(`eq:conjugation` in Section 2.5). -/
def qubitDephasing : Channel (Fin 2) (Fin 2) where
  map := MatrixMap.ofKraus qubitDephasingKraus
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using qubitDephasingKraus_complete)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem qubitDephasing_not_unitary :
    ¬ ∃ U : Matrix.unitaryGroup (Fin 2) ℂ, qubitDephasing = unitaryTargetChannel U := by
  rintro ⟨U, hU⟩
  let X₀ : CMatrix (Fin 2) := Matrix.single 0 1 1
  have hmap := congrArg (fun Φ => Φ.map X₀) hU
  dsimp only at hmap
  have hlhs : qubitDephasing.map X₀ = 0 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [qubitDephasing, qubitDephasingKraus, X₀, MatrixMap.ofKraus,
        Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single]
  rw [hlhs, unitaryTargetChannel, ICO.ClassicalDilation.isometryChannel_apply] at hmap
  have hU_id : (U : CMatrix (Fin 2))ᴴ * (U : CMatrix (Fin 2)) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have hrecover :
      (U : CMatrix (Fin 2))ᴴ * ((U : CMatrix (Fin 2)) * X₀ * (U : CMatrix (Fin 2))ᴴ) *
        (U : CMatrix (Fin 2)) = X₀ := by
    calc
      (U : CMatrix (Fin 2))ᴴ * ((U : CMatrix (Fin 2)) * X₀ * (U : CMatrix (Fin 2))ᴴ) *
          (U : CMatrix (Fin 2)) =
        ((U : CMatrix (Fin 2))ᴴ * (U : CMatrix (Fin 2))) * X₀ *
          ((U : CMatrix (Fin 2))ᴴ * (U : CMatrix (Fin 2))) := by
        simp only [Matrix.mul_assoc]
      _ = X₀ := by
        rw [hU_id, Matrix.one_mul, Matrix.mul_one]
  rw [← hmap, Matrix.mul_zero, Matrix.zero_mul] at hrecover
  have h01 := congrFun (congrFun hrecover 0) 1
  simp [X₀, Matrix.single] at h01

/-- **Remark `rem:unitary` (Failure of the 3-call circuit when `A` is not unitary)**:
For `A = qubitDephasing` (`Δ_I`) and `B = Channel.idChannel (Fin 2)` on `Fin 2`,
the 3-call circuit `unitaryThreeCallTree a₀` correlates the dummy register with the
control qubit, annihilates the off-diagonal control coherence on orthogonal target
state `|1 - a₀⟩`, and fails to reproduce `channelSwitch qubitDephasing (Channel.idChannel (Fin 2))`
for every initial dummy basis state `a₀ : Fin 2` (in particular `a₀ = 0`). -/
theorem unitaryThreeCallTree_fails_nonunitary (a₀ : Fin 2) :
    (unitaryThreeCallTree a₀).channel
      (qubitDephasing.prod (Channel.idChannel (Fin 2 × Bool)))
      ((Channel.idChannel (Fin 2)).prod (Channel.idChannel (Fin 2 × Bool))) ≠
    channelSwitch qubitDephasing (Channel.idChannel (Fin 2)) := by
  intro heq
  let a₁ : Fin 2 := if a₀ = 0 then 1 else 0
  have ha : a₁ ≠ a₀ := by
    fin_cases a₀ <;> decide
  let X_coh : CMatrix (Fin 2 × Bool) := Matrix.single (a₁, false) (a₁, true) 1
  have hpre :
      preIsometry a₀ * X_coh * (preIsometry a₀)ᴴ =
        Matrix.single (a₁, (a₀, false)) (a₀, (a₁, true)) 1 := by
    ext x y
    simp only [X_coh, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_eq_single (a₁, true)]
    · rw [Finset.sum_eq_single (a₁, false)]
      · rcases x with ⟨t₁, d₁, c₁⟩
        rcases y with ⟨t₂, d₂, c₂⟩
        cases c₁ <;> cases c₂
        · simp [preIsometry, Matrix.single]
        · fin_cases a₀ <;> fin_cases t₁ <;> fin_cases d₁ <;>
            fin_cases t₂ <;> fin_cases d₂ <;>
            simp [a₁, preIsometry, Matrix.single]
        · simp [preIsometry, Matrix.single]
        · simp [preIsometry, Matrix.single]
      · intro z _ hz
        simp [Matrix.single, hz.symm]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · intro w _ hw
      rw [Finset.sum_eq_single (a₁, false)]
      · simp [Matrix.single, hw.symm]
      · intro z _ hz
        simp [Matrix.single, hz.symm]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  have hcall1 :
      (qubitDephasing.prod (Channel.idChannel (Fin 2 × Bool))).map
        (Matrix.single (a₁, (a₀, false)) (a₀, (a₁, true)) 1) = 0 := by
    change MatrixMap.kron qubitDephasing.map (Channel.idChannel (Fin 2 × Bool)).map _ = 0
    rw [kron_idChannel_eq_liftMap_gen]
    ext ⟨t₁, m₁⟩ ⟨t₂, m₂⟩
    simp only [ICO.OracleLift.liftMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.zero_apply,
      qubitDephasing, MatrixMap.ofKraus, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, qubitDephasingKraus]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun y _ => ?_
    have hinner :
        (∑ x : Fin 2,
          Matrix.single i i (1 : ℂ) t₁ x *
            Matrix.single (a₁, (a₀, false)) (a₀, (a₁, true)) (1 : ℂ) (x, m₁) (y, m₂)) *
          star (Matrix.single i i (1 : ℂ) t₂ y) = 0 := by
      by_cases hy : i = y
      · subst hy
        refine mul_eq_zero_of_left (Finset.sum_eq_zero fun x _ => ?_) _
        by_cases hx : i = x
        · subst hx
          by_cases hia₀ : i = a₀
          · subst hia₀
            simp [Matrix.single, ha]
          · have hne0 : a₀ ≠ i := Ne.symm hia₀
            simp [Matrix.single, hne0]
        · simp [Matrix.single, hx]
      · simp [Matrix.single, hy]
    exact hinner
  have hlhs :
      ((unitaryThreeCallTree a₀).channel
        (qubitDephasing.prod (Channel.idChannel (Fin 2 × Bool)))
        ((Channel.idChannel (Fin 2)).prod (Channel.idChannel (Fin 2 × Bool)))).map X_coh = 0 := by
    unfold unitaryThreeCallTree
    simp only [tree_node_map_apply, Fintype.sum_unique,
      preInstrument, cswapTrueInstrument, cswapFalseInstrument,
      tree_query_map_apply, tree_stop_map_apply, Bool.false_eq_true, ite_false, ite_true]
    rw [hpre, hcall1]
    simp [map_zero]
  have hid_kraus :
      (Channel.idChannel (Fin 2)).map =
        MatrixMap.ofKraus (fun _ : PUnit.{1} => (1 : CMatrix (Fin 2))) := by
    ext Y x y
    simp [Channel.idChannel, MatrixMap.ofKraus]
  have hrhs_entry :
      (channelSwitch qubitDephasing (Channel.idChannel (Fin 2))).map X_coh
        (a₁, false) (a₁, true) = 1 := by
    rw [channelSwitch_map_ofKraus qubitDephasing (Channel.idChannel (Fin 2))
      qubitDephasingKraus (fun _ : PUnit.{1} => (1 : CMatrix (Fin 2))) rfl hid_kraus,
      ofKraus_apply]
    simp only [Matrix.sum_apply, Fintype.sum_prod_type, Fintype.sum_unique]
    simp_rw [controlled_sandwich_entry]
    simp only [Bool.false_eq_true, ite_false, ite_true, Matrix.one_mul, Matrix.mul_one]
    rw [Finset.sum_eq_single a₁]
    · rw [Finset.sum_eq_single a₁]
      · rw [Finset.sum_eq_single a₁]
        · simp [X_coh, qubitDephasingKraus, Matrix.single]
        · intro q _ hq
          simp [X_coh, Matrix.single, hq.symm]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
      · intro p _ hp
        refine Finset.sum_eq_zero fun q _ => ?_
        simp [X_coh, Matrix.single, hp.symm]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · intro i _ hi
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
      simp [qubitDephasingKraus, Matrix.single, hi]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  have heval := congrFun (congrFun (congrArg (fun Φ => Φ.map X_coh) heq) (a₁, false)) (a₁, true)
  dsimp only at heval
  rw [hlhs, hrhs_entry] at heval
  exact zero_ne_one heval

/-- **Remark `rem:unitary` (Existential non-unitary failure witness)**:
There exists a non-unitary qubit channel `A_ch : Channel (Fin 2) (Fin 2)` such that
for every initial dummy basis state `a₀ : Fin 2`, `unitaryThreeCallTree a₀` fails to
simulate `channelSwitch A_ch (Channel.idChannel (Fin 2))`. -/
theorem exists_nonunitary_unitaryThreeCallTree_ne_channelSwitch :
    ∃ A_ch : Channel (Fin 2) (Fin 2),
      (¬ ∃ U : Matrix.unitaryGroup (Fin 2) ℂ, A_ch = unitaryTargetChannel U) ∧
      ∀ a₀ : Fin 2,
        (unitaryThreeCallTree a₀).channel
          (A_ch.prod (Channel.idChannel (Fin 2 × Bool)))
          ((Channel.idChannel (Fin 2)).prod (Channel.idChannel (Fin 2 × Bool))) ≠
        channelSwitch A_ch (Channel.idChannel (Fin 2)) :=
  ⟨qubitDephasing, qubitDephasing_not_unitary, unitaryThreeCallTree_fails_nonunitary⟩

/-- Pauli-`X` bit-flip matrix on `Fin 2`. -/
def qubitPauliXMatrix : CMatrix (Fin 2) :=
  fun i j => if i ≠ j then 1 else 0

theorem qubitPauliXMatrix_mem_unitaryGroup :
    qubitPauliXMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitPauliXMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

/-- Pauli-`X` gate as an element of `U(Fin 2)`. -/
def qubitPauliX : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨qubitPauliXMatrix, qubitPauliXMatrix_mem_unitaryGroup⟩

/-- **Remark `rem:unitary` (Non-unitarity of the diluted box `x A + (1 - x) id`)**:
For every dilution parameter `0 < x < 1`, the diluted unitary channel
`x Ad(σ_x) + (1 - x) id` on `Fin 2` is not equal to any unitary channel `Ad(W)`,
witnessing that the set of unitary channels is not convex. -/
theorem diluted_unitary_not_unitary {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ¬ ∃ W : Matrix.unitaryGroup (Fin 2) ℂ,
      x • (unitaryTargetChannel qubitPauliX).map +
        (1 - x) • (Channel.idChannel (Fin 2)).map =
      (unitaryTargetChannel W).map := by
  rintro ⟨W, hW⟩
  let E₀ : CMatrix (Fin 2) := Matrix.single 0 0 1
  have hE₀_idem : E₀ * E₀ = E₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E₀, Matrix.mul_apply, Matrix.single]
  have hE₀_tr : E₀.trace = 1 := by
    simp [E₀, Matrix.trace, Matrix.single]
  let Y : CMatrix (Fin 2) := (unitaryTargetChannel W).map E₀
  have hW_id : (W : CMatrix (Fin 2))ᴴ * (W : CMatrix (Fin 2)) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self W
  have hY_idem : Y * Y = Y := by
    dsimp only [Y, unitaryTargetChannel]
    rw [ICO.ClassicalDilation.isometryChannel_apply]
    calc
      ((W : CMatrix (Fin 2)) * E₀ * (W : CMatrix (Fin 2))ᴴ) *
          ((W : CMatrix (Fin 2)) * E₀ * (W : CMatrix (Fin 2))ᴴ) =
        (W : CMatrix (Fin 2)) *
          (E₀ * ((W : CMatrix (Fin 2))ᴴ * (W : CMatrix (Fin 2))) * E₀) *
          (W : CMatrix (Fin 2))ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = (W : CMatrix (Fin 2)) * E₀ * (W : CMatrix (Fin 2))ᴴ := by
        rw [hW_id, Matrix.mul_one, hE₀_idem]
  have hY_sq_tr : (Y * Y).trace = 1 := by
    rw [hY_idem]
    exact ((unitaryTargetChannel W).tracePreserving E₀).trans hE₀_tr
  let L : CMatrix (Fin 2) :=
    (x • (unitaryTargetChannel qubitPauliX).map +
      (1 - x) • (Channel.idChannel (Fin 2)).map) E₀
  have hLY : L = Y := congrArg (fun f => f E₀) hW
  have hL_entry (i j : Fin 2) :
      L i j = if i = 0 ∧ j = 0 then ((1 - x : ℝ) : ℂ)
        else if i = 1 ∧ j = 1 then (x : ℂ) else 0 := by
    fin_cases i <;> fin_cases j <;>
      simp [L, E₀, unitaryTargetChannel, qubitPauliX, qubitPauliXMatrix,
        ICO.ClassicalDilation.isometryChannel_apply, Channel.idChannel, MatrixMap.ofKraus,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Matrix.single, Complex.real_smul]
  have hL_sq_tr :
      (L * L).trace = ((1 - x : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) + (x : ℂ) * (x : ℂ) := by
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, hL_entry]
  rw [hLY, hY_sq_tr] at hL_sq_tr
  have hre := congrArg Complex.re hL_sq_tr.symm
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.one_re] at hre
  nlinarith

/-! ## 2. Remark `rem:approx-content`: Numerical Regime (`d ≥ 235` and `d ≥ 65536`) -/

/-- At `q = 2` and `r = 2` (`r + 1 = 3`), the Theorem 2 lower bound equals
`1/6 - 39/d`. -/
theorem two_query_tradeoff_at_r2 (d : ℕ) :
    (1 / 2 : ℝ) - 13 * (((2 + 1) * (2 + 1) : ℕ) : ℝ) / (3 * (d : ℝ)) -
      ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1) / (2 * ((2 : ℕ) + 1)) =
    1 / 6 - 39 / (d : ℝ) := by
  push_cast
  ring

/-- For `d ≥ 235`, the `q = 2, r + 1 = 3` tradeoff bound is at least `1/1410 > 0`. -/
theorem two_query_tradeoff_pos_of_ge_235 {d : ℕ} (hd : 235 ≤ d) :
    1 / 1410 ≤
      (1 / 2 : ℝ) - 13 * (((2 + 1) * (2 + 1) : ℕ) : ℝ) / (3 * (d : ℝ)) -
        ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1) / (2 * ((2 : ℕ) + 1)) := by
  rw [two_query_tradeoff_at_r2]
  have hdR : (235 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdiv : 39 / (d : ℝ) ≤ 39 / 235 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hdR
  linarith

/-- **Remark `rem:approx-content` (`q = 2, d ≥ 235` positive lower bound)**:
For every target system `A` with `Fintype.card A ≥ 235` and every 2-query
strategy `tree`, there exists a 3-unitary sample `UV : Sample A 2` on which
`tree` incurs diamond error at least `1/6 - 39/d ≥ 1/1410 > 0`. -/
theorem exists_two_query_switch_error_ge_235 [Nontrivial A] [Nonempty M]
    (hd : 235 ≤ Fintype.card A)
    (tree : Tree (A × M) (A × Bool) 2 (A × Bool)) :
    ∃ UV : Sample A 2,
      1 / 6 - 39 / (Fintype.card A : ℝ) ≤
        (fullSwitch UV).diamondTraceDistance (fullCircuit tree UV) ∧
      1 / 1410 ≤
        (fullSwitch UV).diamondTraceDistance (fullCircuit tree UV) := by
  obtain ⟨UV, hbound⟩ := exists_full_switch_error_bound (q := 2) (r := 2) tree
  refine ⟨UV, ?_, ?_⟩
  · have heq := two_query_tradeoff_at_r2 (Fintype.card A)
    linarith
  · have hpos := two_query_tradeoff_pos_of_ge_235 hd
    linarith

/-- **Remark `rem:approx-content` (`q = 2, 1 ≤ d ≤ 234` nonpositivity)**:
When `1 ≤ d ≤ 234`, the `q = 2` tradeoff expression is nonpositive for every `r : ℕ`. -/
theorem two_query_tradeoff_nonpos_of_le_234 (d r : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ 234) :
    (1 / 2 : ℝ) - 13 * (((r + 1) * (r + 1) : ℕ) : ℝ) / (3 * (d : ℝ)) -
      ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1) / (2 * ((r : ℝ) + 1)) ≤ 0 := by
  have hRpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hDpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hd1)
  have hDle : (d : ℝ) ≤ 234 := by exact_mod_cast hd
  have hdiv : 13 * (((r + 1) * (r + 1) : ℕ) : ℝ) / (3 * 234) ≤
      13 * (((r + 1) * (r + 1) : ℕ) : ℝ) / (3 * (d : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hid :
      (1 / 2 : ℝ) - 13 * (((r + 1) * (r + 1) : ℕ) : ℝ) / (3 * 234) -
        ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1) / (2 * ((r : ℝ) + 1)) =
      - ((13 * ((r : ℝ) - 2) ^ 2 * ((r : ℝ) + 7)) /
        (702 * ((r : ℝ) + 1))) := by
    have hRne : (r : ℝ) + 1 ≠ 0 := ne_of_gt hRpos
    push_cast
    field_simp [hRne]
    ring
  have hnonneg :
      0 ≤ (13 * ((r : ℝ) - 2) ^ 2 * ((r : ℝ) + 7)) /
        (702 * ((r : ℝ) + 1)) := by
    positivity
  linarith

/-- **Remark `rem:approx-content` (`d ≥ 65536` forces `q ≥ 3` at `ε = 1/48`)**:
When `Fintype.card A ≥ 65536 = 8⁴ · 2⁴`, any strategy achieving diamond error
`≤ 1/48` on all unitary-mixture samples `UV : Sample A r` must make at least `3` queries. -/
theorem full_switch_one_over_48_three_queries_of_ge_65536 [Nontrivial A] [Nonempty M] {q : ℕ}
    (hd : 65536 ≤ Fintype.card A)
    (tree : Tree (A × M) (A × Bool) q (A × Bool))
    (haccurate : ∀ r (UV : Sample A r),
      (fullSwitch UV).diamondTraceDistance (fullCircuit tree UV) ≤ 1 / 48) :
    3 ≤ q := by
  have hd64 : 64 ≤ Fintype.card A := by omega
  have hlt := full_switch_one_over_48 tree hd64 haccurate
  have hdR : (65536 : ℝ) ≤ (Fintype.card A : ℝ) := by exact_mod_cast hd
  by_contra hq
  have hq2 : q ≤ 2 := by omega
  have hqR : (q : ℝ) ≤ 2 := by exact_mod_cast hq2
  have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hpow : (q : ℝ) ^ 4 ≤ (2 : ℝ) ^ 4 := pow_le_pow_left₀ hqnonneg hqR 4
  linarith

/-- Conversely, for `d < 65536` (`d ≤ 65535`), the inequality `d < 4096 q⁴`
already holds at `q = 2`. -/
theorem full_switch_one_over_48_vacuous_at_two_queries_lt_65536 {d : ℕ} (hd : d < 65536) :
    (d : ℝ) < 4096 * ((2 : ℕ) : ℝ) ^ 4 := by
  have hdR : (d : ℝ) < 65536 := by exact_mod_cast hd
  have hpow : (4096 : ℝ) * ((2 : ℕ) : ℝ) ^ 4 = 65536 := by norm_num
  linarith

/-! ### 2b. Almost-sure non-unitarity of uniform Haar mixtures (`r ≥ 2`, `rem:approx-content`) -/

omit [Nontrivial A] in
theorem conj_single_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : CMatrix ι) (p₀ q₀ r₀ s₀ : ι) :
    (K * Matrix.single p₀ q₀ (1 : ℂ) * Kᴴ) r₀ s₀ = K r₀ p₀ * star (K s₀ q₀) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q₀]
  · rw [Matrix.mul_apply, Finset.sum_eq_single p₀]
    · simp [Matrix.single]
    · intro p _ hp
      simp [Matrix.single, hp.symm]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  · intro q _ hq
    have hzero : (K * Matrix.single p₀ q₀ (1 : ℂ)) r₀ q = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun p _ => ?_
      simp [Matrix.single, hq.symm]
    simp [hzero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- If the uniform mixture of `r` unitary oracle channels on `A × M` coincides with any
isometric/unitary channel `X ↦ V X Vᴴ` (`Vᴴ V = 1`), then all `U i` are equal up to unit-modulus
scalar phase factors. -/
theorem uniform_unitary_mixture_eq_isometry_implies_proportional [Nonempty M]
    {r : ℕ} [NeZero r] (U : Fin r → Matrix.unitaryGroup A ℂ)
    (V : CMatrix (A × M)) (hV : Vᴴ * V = 1)
    (hEq : ICO.SamplingOrdinary.uniformChannel
      (fun i : Fin r => ICO.ClassicalDilation.oracleChannel (M := M) (U i)) =
        ICO.ClassicalDilation.isometryChannel V hV) :
    ∀ i : Fin r, ∃ c : ℂ, ‖c‖ = 1 ∧ (U i : CMatrix A) = c • (U 0 : CMatrix A) := by
  let m₀ : M := Classical.arbitrary M
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hentry (a b x y : A) (m₁ m₂ : M) :
      (r : ℂ)⁻¹ *
        (∑ i : Fin r,
          ((U i : CMatrix A) x a * (if m₁ = m₀ then (1 : ℂ) else 0)) *
            star ((U i : CMatrix A) y b * (if m₂ = m₀ then (1 : ℂ) else 0))) =
      V (x, m₁) (a, m₀) * star (V (y, m₂) (b, m₀)) := by
    have hmap := congrFun (congrFun
      (congrArg (fun Φ : Channel (A × M) (A × M) =>
        Φ.map (Matrix.single (a, m₀) (b, m₀) (1 : ℂ))) hEq) (x, m₁)) (y, m₂)
    dsimp only at hmap
    rw [ICO.SamplingOrdinary.uniformChannel_map] at hmap
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul, ICO.ClassicalDilation.oracleChannel_apply,
      ICO.ClassicalDilation.isometryChannel_apply, conj_single_entry,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply] at hmap
    exact hmap
  have hV_off (a x : A) (m : M) (hm : m ≠ m₀) : V (x, m) (a, m₀) = 0 := by
    have h0 := hentry a a x x m m
    simp only [hm, ↓reduceIte, mul_zero, star_zero, Finset.sum_const_zero] at h0
    have hre := congrArg Complex.re h0.symm
    have hsq : (V (x, m) (a, m₀) * star (V (x, m) (a, m₀))).re =
        Complex.normSq (V (x, m) (a, m₀)) := by
      simp [Complex.normSq_apply, Complex.mul_re]
    rw [hsq, Complex.zero_re] at hre
    exact Complex.normSq_eq_zero.mp hre
  let W₀ : CMatrix A := fun x a => V (x, m₀) (a, m₀)
  have hW₀_left : W₀ᴴ * W₀ = 1 := by
    ext a b
    have hVab := congrFun (congrFun hV (a, m₀)) (b, m₀)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.one_apply, Prod.mk.injEq, and_true] at hVab
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [← hVab]
    refine Finset.sum_congr rfl fun x _ => ?_
    symm
    refine Finset.sum_eq_single m₀ ?_ ?_
    · intro m _ hm
      rw [hV_off a x m hm, star_zero, zero_mul]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  have hW₀_right : W₀ * W₀ᴴ = 1 := mul_eq_one_comm.mpr hW₀_left
  let W : Matrix.unitaryGroup A ℂ := ⟨W₀, Unitary.mem_iff.mpr ⟨hW₀_left, hW₀_right⟩⟩
  have hUW (a b x y : A) :
      (∑ i : Fin r, (U i : CMatrix A) x a * star ((U i : CMatrix A) y b)) =
        (r : ℂ) * ((W : CMatrix A) x a * star ((W : CMatrix A) y b)) := by
    have hm := hentry a b x y m₀ m₀
    simp only [↓reduceIte, mul_one] at hm
    have hm' : (r : ℂ) * ((r : ℂ)⁻¹ *
        ∑ i : Fin r, (U i : CMatrix A) x a * star ((U i : CMatrix A) y b)) =
        (r : ℂ) * ((W : CMatrix A) x a * star ((W : CMatrix A) y b)) :=
      congrArg ((r : ℂ) * ·) hm
    rwa [mul_inv_cancel_left₀ hr_ne] at hm'
  let N : Fin r → Matrix.unitaryGroup A ℂ := fun i => W⁻¹ * U i
  have hN_val (i : Fin r) : (N i : CMatrix A) = (W : CMatrix A)ᴴ * (U i : CMatrix A) := rfl
  have hN_diag_prod (a b : A) :
      (∑ i : Fin r, (N i : CMatrix A) a a * star ((N i : CMatrix A) b b)) = (r : ℂ) := by
    have hexp (i : Fin r) :
        (N i : CMatrix A) a a * star ((N i : CMatrix A) b b) =
          ∑ x : A, ∑ y : A,
            (star ((W : CMatrix A) x a) * (W : CMatrix A) y b) *
              ((U i : CMatrix A) x a * star ((U i : CMatrix A) y b)) := by
      simp only [hN_val, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul,
        star_star]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    have hswap :
        (∑ x : A, ∑ i : Fin r, ∑ y : A,
          (star ((W : CMatrix A) x a) * (W : CMatrix A) y b) *
            ((U i : CMatrix A) x a * star ((U i : CMatrix A) y b))) =
        ∑ x : A, ∑ y : A,
          (star ((W : CMatrix A) x a) * (W : CMatrix A) y b) *
            (∑ i : Fin r, (U i : CMatrix A) x a * star ((U i : CMatrix A) y b)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => by rw [← Finset.mul_sum]
    rw [hswap]
    simp_rw [hUW a b]
    have hcolW (c : A) : ∑ z : A, star ((W : CMatrix A) z c) * (W : CMatrix A) z c = 1 := by
      have hc := congrFun (congrFun (Matrix.UnitaryGroup.star_mul_self W) c) c
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hc
    calc
      (∑ x : A, ∑ y : A,
          (star ((W : CMatrix A) x a) * (W : CMatrix A) y b) *
            ((r : ℂ) * ((W : CMatrix A) x a * star ((W : CMatrix A) y b)))) =
        ∑ x : A, ((r : ℂ) * (star ((W : CMatrix A) x a) * (W : CMatrix A) x a)) *
          (∑ y : A, star ((W : CMatrix A) y b) * (W : CMatrix A) y b) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      _ = ((r : ℂ) * ∑ x : A, star ((W : CMatrix A) x a) * (W : CMatrix A) x a) *
          (∑ y : A, star ((W : CMatrix A) y b) * (W : CMatrix A) y b) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = (r : ℂ) := by rw [hcolW a, hcolW b, mul_one, mul_one]
  have hcolN (i : Fin r) (a : A) :
      ∑ x : A, Complex.normSq ((N i : CMatrix A) x a) = 1 := by
    have hc := congrArg Complex.re (ICO.HaarSecondMoment.column_norm (N i) a)
    have hre (z : ℂ) : (z * star z).re = Complex.normSq z := by
      simp [Complex.normSq_apply, Complex.mul_re]
    simpa [Complex.re_sum, hre] using hc
  have hN_diag_normSq (i : Fin r) (a : A) :
      Complex.normSq ((N i : CMatrix A) a a) = 1 := by
    have hle (j : Fin r) : Complex.normSq ((N j : CMatrix A) a a) ≤ 1 := by
      have hsplit := Finset.add_sum_erase Finset.univ
        (fun x : A => Complex.normSq ((N j : CMatrix A) x a)) (Finset.mem_univ a)
      rw [hcolN j a] at hsplit
      have hrest : 0 ≤ ∑ x ∈ Finset.univ.erase a, Complex.normSq ((N j : CMatrix A) x a) :=
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
      linarith
    have hsum_re : ∑ j : Fin r, Complex.normSq ((N j : CMatrix A) a a) = (r : ℝ) := by
      have hre := congrArg Complex.re (hN_diag_prod a a)
      have hz (z : ℂ) : (z * star z).re = Complex.normSq z := by
        simp [Complex.normSq_apply, Complex.mul_re]
      simpa [Complex.re_sum, hz] using hre
    have hzero : ∑ j : Fin r, (1 - Complex.normSq ((N j : CMatrix A) a a)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, hsum_re, sub_self]
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hle j))).mp
      hzero i (Finset.mem_univ i)
    linarith
  have hN_off (i : Fin r) (x a : A) (hxa : x ≠ a) : (N i : CMatrix A) x a = 0 := by
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun y : A => Complex.normSq ((N i : CMatrix A) y a)) (Finset.mem_univ a)
    dsimp only at hsplit
    rw [hcolN i a, hN_diag_normSq i a] at hsplit
    have herase : ∑ y ∈ Finset.univ.erase a, Complex.normSq ((N i : CMatrix A) y a) = 0 := by
      linarith
    have hx0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp
      herase x (Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩)
    exact Complex.normSq_eq_zero.mp hx0
  have hN_const (i : Fin r) (a b : A) :
      (N i : CMatrix A) a a = (N i : CMatrix A) b b := by
    have hdiff_id (u v : ℂ) :
        Complex.normSq (u - v) = Complex.normSq u + Complex.normSq v - 2 * (u * star v).re := by
      simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.conj_re, Complex.conj_im]
      ring
    have hsum_diff :
        ∑ j : Fin r, Complex.normSq ((N j : CMatrix A) a a - (N j : CMatrix A) b b) = 0 := by
      have hterm (j : Fin r) :
          Complex.normSq ((N j : CMatrix A) a a - (N j : CMatrix A) b b) =
            2 - 2 * ((N j : CMatrix A) a a * star ((N j : CMatrix A) b b)).re := by
        rw [hdiff_id, hN_diag_normSq j a, hN_diag_normSq j b]
        ring
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have hre := congrArg Complex.re (hN_diag_prod a b)
      simp only [Complex.re_sum, Complex.natCast_re] at hre
      rw [hre]
      ring
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp
      hsum_diff i (Finset.mem_univ i)
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hi0)
  let a₀ : A := Classical.arbitrary A
  let d : Fin r → ℂ := fun i => (N i : CMatrix A) a₀ a₀
  have hd_normSq (i : Fin r) : Complex.normSq (d i) = 1 := hN_diag_normSq i a₀
  have hd_norm (i : Fin r) : ‖d i‖ = 1 := by
    have hsq : ‖d i‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, hd_normSq i]
    nlinarith [norm_nonneg (d i)]
  have hN_scalar (i : Fin r) : (N i : CMatrix A) = d i • (1 : CMatrix A) := by
    ext x a
    by_cases hxa : x = a
    · subst hxa
      simp [d, hN_const i x a₀]
    · simp [hxa, hN_off i x a hxa]
  have hU_scalar (i : Fin r) : (U i : CMatrix A) = d i • (W : CMatrix A) := by
    have hmul : (W : CMatrix A) * (N i : CMatrix A) = (U i : CMatrix A) := by
      rw [hN_val, ← Matrix.mul_assoc, hW₀_right, Matrix.one_mul]
    rw [← hmul, hN_scalar i, Matrix.mul_smul, Matrix.mul_one]
  intro i
  refine ⟨d i * star (d 0), ?_, ?_⟩
  · rw [norm_mul, norm_star, hd_norm i, hd_norm 0, mul_one]
  · rw [hU_scalar i, hU_scalar 0, smul_smul]
    have hd0 : star (d 0) * d 0 = 1 := by
      simp [Complex.conj_mul', hd_norm 0]
    rw [mul_assoc, hd0, mul_one]

/-- **Deterministic characterization of unitary-mixture channels**:
The uniform mixture of `r` unitary oracle channels `U i` on `A × M` (`[Nonempty M]`) equals a
unitary oracle channel `oracleChannel W` if and only if every `U i` is a unit-modulus scalar
multiple of `U 0`. -/
theorem uniform_unitary_mixture_eq_oracleChannel_iff [Nonempty M]
    {r : ℕ} [NeZero r] (U : Fin r → Matrix.unitaryGroup A ℂ) :
    (∃ W : Matrix.unitaryGroup A ℂ,
      ICO.SamplingOrdinary.uniformChannel
        (fun i : Fin r => ICO.ClassicalDilation.oracleChannel (M := M) (U i)) =
          ICO.ClassicalDilation.oracleChannel (M := M) W) ↔
    (∀ i : Fin r, ∃ c : ℂ, ‖c‖ = 1 ∧ (U i : CMatrix A) = c • (U 0 : CMatrix A)) := by
  constructor
  · rintro ⟨W, hW⟩
    exact uniform_unitary_mixture_eq_isometry_implies_proportional U
      (Matrix.kronecker (W : CMatrix A) (1 : CMatrix M))
      (ICO.ClassicalDilation.isometry_kronecker_one _ (Matrix.UnitaryGroup.star_mul_self W)) hW
  · intro hprop
    refine ⟨U 0, ?_⟩
    apply channel_eq_of_map_eq
    have hmap_eq (i : Fin r) :
        (ICO.ClassicalDilation.oracleChannel (M := M) (U i)).map =
          (ICO.ClassicalDilation.oracleChannel (M := M) (U 0)).map := by
      obtain ⟨c, hc, hUi⟩ := hprop i
      have hc_mul : star c * c = 1 := by
        simp [Complex.conj_mul', hc]
      ext X p q
      rw [ICO.ClassicalDilation.oracleChannel_apply, ICO.ClassicalDilation.oracleChannel_apply]
      have hkron :
          Matrix.kronecker (U i : CMatrix A) (1 : CMatrix M) =
            c • Matrix.kronecker (U 0 : CMatrix A) (1 : CMatrix M) := by
        ext ⟨x, m₁⟩ ⟨y, m₂⟩
        simp [hUi, Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc]
      rw [hkron, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_smul, hc_mul, one_smul]
    rw [ICO.SamplingOrdinary.uniformChannel_map]
    simp_rw [hmap_eq]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne r)), one_smul]

/-- Stereographic unit-circle sequence `m ↦ ((1 - m²) + 2m i) / (1 + m²)` for `m : ℕ`. -/
def stereoPhase (m : ℕ) : ℂ :=
  ⟨(1 - (m : ℝ) ^ 2) / (1 + (m : ℝ) ^ 2), (2 * (m : ℝ)) / (1 + (m : ℝ) ^ 2)⟩

theorem stereoPhase_star_mul_self (m : ℕ) : star (stereoPhase m) * stereoPhase m = 1 := by
  have hpos : (1 : ℝ) + (m : ℝ) ^ 2 ≠ 0 := by positivity
  apply Complex.ext
  · simp only [stereoPhase, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.one_re]
    field_simp [hpos]
    ring
  · simp only [stereoPhase, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.one_im]
    ring

theorem stereoPhase_mul_star_self (m : ℕ) : stereoPhase m * star (stereoPhase m) = 1 := by
  rw [mul_comm]
  exact stereoPhase_star_mul_self m

theorem stereoPhase_injective : Function.Injective stereoPhase := by
  intro m n h
  have hre := congrArg Complex.re h
  dsimp [stereoPhase] at hre
  have hm : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
  have hn : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  rw [div_eq_div_iff hm.ne' hn.ne'] at hre
  have hsq : (m : ℝ) ^ 2 = (n : ℝ) ^ 2 := by linarith
  have hcast : (m : ℝ) = (n : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]
  exact_mod_cast hcast

/-- Diagonal unitary placing `stereoPhase m` on basis state `a₀` and `1` elsewhere. -/
def phaseDiagUnitary (a₀ : A) (m : ℕ) : Matrix.unitaryGroup A ℂ :=
  ⟨Matrix.diagonal (fun x : A => if x = a₀ then stereoPhase m else 1), by
    rw [Unitary.mem_iff]
    have h1 : (Matrix.diagonal (fun x : A => if x = a₀ then stereoPhase m else 1))ᴴ *
        Matrix.diagonal (fun x : A => if x = a₀ then stereoPhase m else 1) = 1 := by
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      convert Matrix.diagonal_one (n := A) (α := ℂ) with x
      by_cases hx : x = a₀
      · simp only [Pi.star_apply, hx, ↓reduceIte]
        exact stereoPhase_star_mul_self m
      · simp [hx]
    have h2 : Matrix.diagonal (fun x : A => if x = a₀ then stereoPhase m else 1) *
        (Matrix.diagonal (fun x : A => if x = a₀ then stereoPhase m else 1))ᴴ = 1 := by
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      convert Matrix.diagonal_one (n := A) (α := ℂ) with x
      by_cases hx : x = a₀
      · simp only [Pi.star_apply, hx, ↓reduceIte]
        exact stereoPhase_mul_star_self m
      · simp [hx]
    exact ⟨h1, h2⟩⟩

/-- Closed subset of `U(A)` consisting of scalar multiples of the identity matrix. -/
def scalarUnitarySet (a₀ : A) : Set (Matrix.unitaryGroup A ℂ) :=
  {W | (W : CMatrix A) = ((W : CMatrix A) a₀ a₀) • (1 : CMatrix A)}

omit [Nontrivial A] in
theorem mem_scalarUnitarySet_iff (a₀ : A) (W : Matrix.unitaryGroup A ℂ) :
    W ∈ scalarUnitarySet a₀ ↔ ∃ c : ℂ, (W : CMatrix A) = c • (1 : CMatrix A) := by
  constructor
  · intro hW
    exact ⟨(W : CMatrix A) a₀ a₀, hW⟩
  · rintro ⟨c, hc⟩
    have hc_eq : (W : CMatrix A) a₀ a₀ = c := by simp [hc]
    change (W : CMatrix A) = ((W : CMatrix A) a₀ a₀) • (1 : CMatrix A)
    rw [hc_eq]
    exact hc

omit [Nontrivial A] in
theorem scalarUnitarySet_measurable (a₀ : A) : MeasurableSet (scalarUnitarySet a₀) :=
  (isClosed_eq continuous_subtype_val
    ((ICO.HaarSecondMoment.entry_continuous a₀ a₀).smul continuous_const)).measurableSet

omit [Nontrivial A] in
theorem unitary_conjTranspose_mul_self (U : Matrix.unitaryGroup A ℂ) :
    (U : CMatrix A)ᴴ * (U : CMatrix A) = 1 :=
  U.property.1

omit [Nontrivial A] in
theorem unitary_mul_conjTranspose_self (U : Matrix.unitaryGroup A ℂ) :
    (U : CMatrix A) * (U : CMatrix A)ᴴ = 1 :=
  U.property.2

omit [Nontrivial A] in
theorem unitary_eq_smul_iff_inv_mul_mem_scalarUnitarySet (a₀ : A)
    (U₀ V : Matrix.unitaryGroup A ℂ) :
    (∃ c : ℂ, (V : CMatrix A) = c • (U₀ : CMatrix A)) ↔
      U₀⁻¹ * V ∈ scalarUnitarySet a₀ := by
  rw [mem_scalarUnitarySet_iff a₀]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    change (U₀ : CMatrix A)ᴴ * (V : CMatrix A) = c • (1 : CMatrix A)
    rw [hc, Matrix.mul_smul, unitary_conjTranspose_mul_self U₀]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hmul := congrArg ((U₀ : CMatrix A) * ·) hc
    change (U₀ : CMatrix A) * ((U₀ : CMatrix A)ᴴ * (V : CMatrix A)) =
      (U₀ : CMatrix A) * (c • (1 : CMatrix A)) at hmul
    rwa [← Matrix.mul_assoc, unitary_mul_conjTranspose_self U₀, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one] at hmul

/-- When `[Nontrivial A]` (`d ≥ 2`), the scalar subgroup `{W ∈ U(A) | ∃ c, W = c • I}` has
Haar measure zero, proved by pairwise disjoint left cosets under `phaseDiagUnitary`. -/
theorem haar_scalarUnitarySet_zero [Nontrivial A] (a₀ : A) :
    unitaryHaarMeasure (a := A) (scalarUnitarySet a₀) = 0 := by
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : A, a₁ ≠ a₀ := exists_ne a₀
  let μ := unitaryHaarMeasure (a := A)
  let T : ℕ → Set (Matrix.unitaryGroup A ℂ) :=
    fun m => (fun W : Matrix.unitaryGroup A ℂ => phaseDiagUnitary a₀ m * W) ⁻¹' scalarUnitarySet a₀
  have hT_meas (m : ℕ) : MeasurableSet (T m) :=
    (scalarUnitarySet_measurable a₀).preimage (continuous_const.mul continuous_id).measurable
  have hT_mu (m : ℕ) : μ (T m) = μ (scalarUnitarySet a₀) := by
    have hmap : MeasureTheory.Measure.map
        (fun W : Matrix.unitaryGroup A ℂ => phaseDiagUnitary a₀ m * W) μ = μ :=
      MeasureTheory.map_mul_left_eq_self μ (phaseDiagUnitary a₀ m)
    have happ := MeasureTheory.Measure.map_apply
      (continuous_const.mul continuous_id).measurable (scalarUnitarySet_measurable a₀)
      (μ := μ) (f := fun W : Matrix.unitaryGroup A ℂ => phaseDiagUnitary a₀ m * W)
    rw [hmap] at happ
    exact happ.symm
  have hT_disj : Pairwise fun m n => Disjoint (T m) (T n) := by
    intro m n hmn
    rw [Set.disjoint_left]
    intro W hWm hWn
    obtain ⟨cm, hcm⟩ := (mem_scalarUnitarySet_iff a₀ (phaseDiagUnitary a₀ m * W)).mp hWm
    obtain ⟨cn, hcn⟩ := (mem_scalarUnitarySet_iff a₀ (phaseDiagUnitary a₀ n * W)).mp hWn
    have hWW : (W : CMatrix A) * (W : CMatrix A)ᴴ = 1 := unitary_mul_conjTranspose_self W
    have hDm : (phaseDiagUnitary a₀ m : CMatrix A) = cm • (W : CMatrix A)ᴴ := by
      have hmul := congrArg (· * (W : CMatrix A)ᴴ) hcm
      change ((phaseDiagUnitary a₀ m : CMatrix A) * (W : CMatrix A)) * (W : CMatrix A)ᴴ =
        (cm • (1 : CMatrix A)) * (W : CMatrix A)ᴴ at hmul
      rwa [Matrix.mul_assoc, hWW, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at hmul
    have hDn : (phaseDiagUnitary a₀ n : CMatrix A) = cn • (W : CMatrix A)ᴴ := by
      have hmul := congrArg (· * (W : CMatrix A)ᴴ) hcn
      change ((phaseDiagUnitary a₀ n : CMatrix A) * (W : CMatrix A)) * (W : CMatrix A)ᴴ =
        (cn • (1 : CMatrix A)) * (W : CMatrix A)ᴴ at hmul
      rwa [Matrix.mul_assoc, hWW, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at hmul
    have ha₁_m : (1 : ℂ) = cm * ((W : CMatrix A)ᴴ) a₁ a₁ := by
      have he := congrFun (congrFun hDm a₁) a₁
      simpa [phaseDiagUnitary, ha₁] using he
    have ha₁_n : (1 : ℂ) = cn * ((W : CMatrix A)ᴴ) a₁ a₁ := by
      have he := congrFun (congrFun hDn a₁) a₁
      simpa [phaseDiagUnitary, ha₁] using he
    have hw_ne : ((W : CMatrix A)ᴴ) a₁ a₁ ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at ha₁_m
      exact one_ne_zero ha₁_m
    have hcm_eq_cn : cm = cn := mul_right_cancel₀ hw_ne (ha₁_m.symm.trans ha₁_n)
    have ha₀_m : stereoPhase m = cm * ((W : CMatrix A)ᴴ) a₀ a₀ := by
      have he := congrFun (congrFun hDm a₀) a₀
      simpa [phaseDiagUnitary] using he
    have ha₀_n : stereoPhase n = cn * ((W : CMatrix A)ᴴ) a₀ a₀ := by
      have he := congrFun (congrFun hDn a₀) a₀
      simpa [phaseDiagUnitary] using he
    have hphase_eq : stereoPhase m = stereoPhase n := by
      rw [ha₀_m, ha₀_n, hcm_eq_cn]
    exact hmn (stereoPhase_injective hphase_eq)
  have hbound (k : ℕ) : (k : ℝ) * (μ (scalarUnitarySet a₀)).toReal ≤ 1 := by
    have hpwd : ( ↑(Finset.range k) : Set ℕ).PairwiseDisjoint T :=
      fun m _ n _ hmn => hT_disj hmn
    have hunion : μ (⋃ m ∈ Finset.range k, T m) = (k : ENNReal) * μ (scalarUnitarySet a₀) := by
      rw [MeasureTheory.measure_biUnion_finset hpwd (fun m _ => hT_meas m)]
      simp_rw [hT_mu]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hle1 : (k : ENNReal) * μ (scalarUnitarySet a₀) ≤ 1 := by
      rw [← hunion, ← MeasureTheory.measure_univ (μ := μ)]
      exact MeasureTheory.measure_mono (Set.subset_univ _)
    have htoReal := ENNReal.toReal_mono ENNReal.one_ne_top hle1
    simpa [ENNReal.toReal_mul] using htoReal
  by_contra hne
  have hlt_top : μ (scalarUnitarySet a₀) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← MeasureTheory.measure_univ (μ := μ)]
    exact MeasureTheory.measure_mono (Set.subset_univ _)
  have hpos : 0 < (μ (scalarUnitarySet a₀)).toReal := ENNReal.toReal_pos hne hlt_top
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (μ (scalarUnitarySet a₀)).toReal)
  have hgt : 1 < (k : ℝ) * (μ (scalarUnitarySet a₀)).toReal := (div_lt_iff₀ hpos).mp hk
  linarith [hbound k]

/-- For any fixed `U₀ ∈ U(A)` with `[Nontrivial A]`, the set of unitaries proportional to `U₀`
has Haar measure zero. -/
theorem haar_proportional_measure_zero [Nontrivial A] (U₀ : Matrix.unitaryGroup A ℂ) :
    unitaryHaarMeasure (a := A)
      {V : Matrix.unitaryGroup A ℂ | ∃ c : ℂ, (V : CMatrix A) = c • (U₀ : CMatrix A)} = 0 := by
  let a₀ : A := Classical.arbitrary A
  let μ := unitaryHaarMeasure (a := A)
  have hset :
      {V : Matrix.unitaryGroup A ℂ | ∃ c : ℂ, (V : CMatrix A) = c • (U₀ : CMatrix A)} =
        (fun V : Matrix.unitaryGroup A ℂ => U₀⁻¹ * V) ⁻¹' scalarUnitarySet a₀ := by
    ext V
    exact unitary_eq_smul_iff_inv_mul_mem_scalarUnitarySet a₀ U₀ V
  rw [hset]
  have hmap : MeasureTheory.Measure.map
      (fun V : Matrix.unitaryGroup A ℂ => U₀⁻¹ * V) μ = μ :=
    MeasureTheory.map_mul_left_eq_self μ U₀⁻¹
  have happ := MeasureTheory.Measure.map_apply
    (continuous_const.mul continuous_id).measurable (scalarUnitarySet_measurable a₀)
    (μ := μ) (f := fun V : Matrix.unitaryGroup A ℂ => U₀⁻¹ * V)
  rw [hmap] at happ
  rw [← happ]
  exact haar_scalarUnitarySet_zero a₀

/-- Under the `r`-fold product Haar measure (`r ≥ 2`, `[Nontrivial A]`), the event that
`U i₁` (`i₁ = ⟨1, _⟩`) is scalar-proportional to `U i₀` (`i₀ = ⟨0, _⟩`) has measure zero. -/
theorem haar_pi_proportional_pair_measure_zero [Nontrivial A]
    {r : ℕ} (hr : 2 ≤ r) :
    MeasureTheory.Measure.pi (fun _ : Fin r => unitaryHaarMeasure (a := A))
      {U : Fin r → Matrix.unitaryGroup A ℂ |
        ∃ c : ℂ, (U ⟨1, by omega⟩ : CMatrix A) = c • (U ⟨0, by omega⟩ : CMatrix A)} = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n + 2 := ⟨r - 2, by omega⟩
  let a₀ : A := Classical.arbitrary A
  let μ := unitaryHaarMeasure (a := A)
  let ν := MeasureTheory.Measure.pi (fun _ : Fin (n + 1) => μ)
  let Bad : Set (Fin (n + 2) → Matrix.unitaryGroup A ℂ) :=
    {U | ((U 0)⁻¹ * U 1 : Matrix.unitaryGroup A ℂ) ∈ scalarUnitarySet a₀}
  have hBad_eq :
      {U : Fin (n + 2) → Matrix.unitaryGroup A ℂ |
        ∃ c : ℂ, (U ⟨1, by omega⟩ : CMatrix A) = c • (U ⟨0, by omega⟩ : CMatrix A)} = Bad := by
    ext U
    exact unitary_eq_smul_iff_inv_mul_mem_scalarUnitarySet a₀ (U 0) (U 1)
  rw [hBad_eq]
  have hBad_meas : MeasurableSet Bad := by
    have hcont : Continuous
        (fun U : Fin (n + 2) → Matrix.unitaryGroup A ℂ => (U 0)⁻¹ * U 1) :=
      ((continuous_apply 0).inv).mul (continuous_apply 1)
    exact (scalarUnitarySet_measurable a₀).preimage hcont.measurable
  have hpres := (MeasureTheory.measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 2) => μ) (1 : Fin (n + 2))).symm
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 2) => Matrix.unitaryGroup A ℂ) (1 : Fin (n + 2))
  have hpre_meas : MeasurableSet (e.symm ⁻¹' Bad) := hBad_meas.preimage hpres.measurable
  rw [← hpres.map_eq, MeasureTheory.Measure.map_apply hpres.measurable hBad_meas]
  change (μ.prod ν) (e.symm ⁻¹' Bad) = 0
  rw [MeasureTheory.Measure.prod_apply_symm hpre_meas]
  have hfiber (rest : Fin (n + 1) → Matrix.unitaryGroup A ℂ) :
      μ ((fun U₁ : Matrix.unitaryGroup A ℂ => (U₁, rest)) ⁻¹' (e.symm ⁻¹' Bad)) = 0 := by
    have hfib_eq :
        ((fun U₁ : Matrix.unitaryGroup A ℂ => (U₁, rest)) ⁻¹' (e.symm ⁻¹' Bad)) =
          {U₁ : Matrix.unitaryGroup A ℂ | ∃ c : ℂ, (U₁ : CMatrix A) = c • (rest 0 : CMatrix A)} := by
      ext U₁
      have h0 : e.symm (U₁, rest) 0 = rest 0 := by
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
        have hsucc : (1 : Fin (n + 2)).succAbove (0 : Fin (n + 1)) = 0 := by simp
        rw [← hsucc, Fin.insertNth_apply_succAbove]
      have h1 : e.symm (U₁, rest) 1 = U₁ := by
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      change ((e.symm (U₁, rest) 0)⁻¹ * e.symm (U₁, rest) 1 : Matrix.unitaryGroup A ℂ) ∈
        scalarUnitarySet a₀ ↔ ∃ c : ℂ, (U₁ : CMatrix A) = c • (rest 0 : CMatrix A)
      rw [h0, h1]
      exact (unitary_eq_smul_iff_inv_mul_mem_scalarUnitarySet a₀ (rest 0) U₁).symm
    rw [hfib_eq]
    exact haar_proportional_measure_zero (rest 0)
  simp_rw [hfiber]
  simp

/-- **Remark `rem:approx-content` (`r ≥ 2` uniform Haar mixture is a.s. not any ambient unitary channel)**:
For `[Nontrivial A]` (`d ≥ 2`), `[Nonempty M]`, and `r ≥ 2`, for almost every `r`-tuple `U` under
the product Haar measure, the uniform-mixture channel `uniformChannel (fun i => oracleChannel (U i))`
does not equal any unitary channel `isometryChannel W _` on `A × M`. -/
theorem uniform_haar_mixture_ae_not_ambient_unitary [Nontrivial A] [Nonempty M]
    {r : ℕ} [NeZero r] (hr : 2 ≤ r) :
    ∀ᵐ U ∂MeasureTheory.Measure.pi (fun _ : Fin r => unitaryHaarMeasure (a := A)),
      ¬ ∃ W : Matrix.unitaryGroup (A × M) ℂ,
        ICO.SamplingOrdinary.uniformChannel
          (fun i : Fin r => ICO.ClassicalDilation.oracleChannel (M := M) (U i)) =
            ICO.ClassicalDilation.isometryChannel (W : CMatrix (A × M))
              (Matrix.UnitaryGroup.star_mul_self W) := by
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null _ (haar_pi_proportional_pair_measure_zero (A := A) hr)
  intro U hU
  rw [Set.mem_setOf_eq, not_not] at hU
  obtain ⟨W, hW⟩ := hU
  have hprop := uniform_unitary_mixture_eq_isometry_implies_proportional U
    (W : CMatrix (A × M)) (Matrix.UnitaryGroup.star_mul_self W) hW ⟨1, by omega⟩
  obtain ⟨c, _, hc⟩ := hprop
  have h0 : (⟨0, by omega⟩ : Fin r) = 0 := Fin.ext (by simp)
  exact ⟨c, by simpa [h0] using hc⟩

/-- **Remark `rem:approx-content` (`r ≥ 2` uniform Haar mixture is a.s. not a unitary oracle channel)**:
For `[Nontrivial A]` (`d ≥ 2`), `[Nonempty M]`, and `r ≥ 2`, for almost every `r`-tuple `U` under
the product Haar measure `Measure.pi (fun _ : Fin r => unitaryHaarMeasure)`, the uniform-mixture
box `uniformChannel (fun i => oracleChannel (U i))` is not a unitary oracle channel `oracleChannel W`. -/
theorem uniform_haar_mixture_ae_not_unitary [Nontrivial A] [Nonempty M]
    {r : ℕ} [NeZero r] (hr : 2 ≤ r) :
    ∀ᵐ U ∂MeasureTheory.Measure.pi (fun _ : Fin r => unitaryHaarMeasure (a := A)),
      ¬ ∃ W : Matrix.unitaryGroup A ℂ,
        ICO.SamplingOrdinary.uniformChannel
          (fun i : Fin r => ICO.ClassicalDilation.oracleChannel (M := M) (U i)) =
            ICO.ClassicalDilation.oracleChannel (M := M) W := by
  filter_upwards [uniform_haar_mixture_ae_not_ambient_unitary (A := A) (M := M) hr] with U hU
  rintro ⟨W, hW⟩
  apply hU
  have hWM_left :
      (Matrix.kronecker (W : CMatrix A) (1 : CMatrix M))ᴴ *
        Matrix.kronecker (W : CMatrix A) (1 : CMatrix M) = 1 :=
    ICO.ClassicalDilation.isometry_kronecker_one _ (Matrix.UnitaryGroup.star_mul_self W)
  have hWM_right :
      Matrix.kronecker (W : CMatrix A) (1 : CMatrix M) *
        (Matrix.kronecker (W : CMatrix A) (1 : CMatrix M))ᴴ = 1 :=
    mul_eq_one_comm.mpr hWM_left
  refine ⟨⟨Matrix.kronecker (W : CMatrix A) (1 : CMatrix M),
    Unitary.mem_iff.mpr ⟨hWM_left, hWM_right⟩⟩, ?_⟩
  exact hW

/-! ## 3. Archival `SAME`/`MUB` Crossover Thresholds `n = 107` and `n = 155`

These six endpoints formalize the unattenuated `SAME`/`MUB` crossover thresholds (`n = 107` and
`n = 155`, comparing `2^(n/16) / 100` against `1` and `8`) from an earlier draft and are retained as
audited supplementary results outside the Round-6 manuscript. The Round-6 Remark `rem:crossover`
(`n ≥ 142` and `n ≥ 238`, together with `21 / p ≤ 14 * ⌈3 / (2p)⌉` and the trivial `1 / (3p)`
diamond-distance lower bound) is formalized in Section 4 below. -/

theorem two_pow_rpow_one_sixteenth_pow_sixteen (n : ℕ) :
    ((((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) = (2 : ℝ) ^ n := by
  have hpos : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos]
  norm_num

/-- Archival `SAME`/`MUB` crossover bound (outside the Round-6 manuscript; see Section 4 for
Round-6 `rem:crossover`): for `n ≤ 106`, `2^(n/16) / 100 < 1`. -/
theorem two_pow_div_sixteen_div_100_lt_one_of_le_106 {n : ℕ} (hn : n ≤ 106) :
    ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) / 100 < 1 := by
  by_contra hge
  have h100 : (100 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) := by linarith
  have hpow : (100 : ℝ) ^ (16 : ℕ) ≤ ((((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) :=
    pow_le_pow_left₀ (by norm_num) h100 16
  rw [two_pow_rpow_one_sixteenth_pow_sixteen] at hpow
  have hmono : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (106 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) hn
  have hlt : (2 : ℝ) ^ (106 : ℕ) < (100 : ℝ) ^ (16 : ℕ) := by norm_num
  linarith

/-- Archival `SAME`/`MUB` crossover bound (outside the Round-6 manuscript; see Section 4 for
Round-6 `rem:crossover`): for `n ≥ 107`, `1 < 2^(n/16) / 100`. -/
theorem one_lt_two_pow_div_sixteen_div_100_of_ge_107 {n : ℕ} (hn : 107 ≤ n) :
    1 < ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) / 100 := by
  by_contra hle
  have h100 : ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) ≤ 100 := by linarith
  have hnonneg : 0 ≤ ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) := by positivity
  have hpow : ((((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) ≤ (100 : ℝ) ^ (16 : ℕ) :=
    pow_le_pow_left₀ hnonneg h100 16
  rw [two_pow_rpow_one_sixteenth_pow_sixteen] at hpow
  have hmono : (2 : ℝ) ^ (107 : ℕ) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hgt : (100 : ℝ) ^ (16 : ℕ) < (2 : ℝ) ^ (107 : ℕ) := by norm_num
  linarith

/-- Archival `SAME`/`MUB` crossover corollary (outside the Round-6 manuscript; see Section 4 for
Round-6 `rem:crossover`): for an `n`-qubit target (`Fintype.card A = 2^n`) with `n ≥ 107`, any
adaptive strategy distinguishing `SAME` from `MUB` with advantage `(2/3, 1/3)` must make at least
`2` queries (`same_mub_query_lower_bound`). -/
theorem same_mub_at_least_two_queries_of_ge_107 {n q : ℕ} [Nontrivial A] [Nonempty M]
    (T : BinaryHypothesisTest O) (tree : Tree (A × M) O q B) (ρ : State B)
    (hd : Fintype.card A = 2 ^ n) (hn : 107 ≤ n)
    (hhigh : ∀ U : Matrix.unitaryGroup A ℂ,
      (2 / 3 : ℝ) ≤ acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀ U V : Matrix.unitaryGroup A ℂ,
      MutuallyUnbiased U V → acceptance T tree ρ (hidden U) (hidden V) ≤ 1 / 3) :
    2 ≤ q := by
  have hbound := same_mub_query_lower_bound T tree ρ n hd hhigh hlow
  rw [hd] at hbound
  have h1 := one_lt_two_pow_div_sixteen_div_100_of_ge_107 hn
  have hq : (1 : ℝ) < (q : ℝ) := lt_trans h1 hbound
  have hqNat : 1 < q := by exact_mod_cast hq
  omega

/-- Archival `SAME`/`MUB` crossover bound (outside the Round-6 manuscript; see Section 4 for
Round-6 `rem:crossover`): for `n ≤ 154`, `2^(n/16) / 100 < 8`. -/
theorem two_pow_div_sixteen_div_100_lt_eight_of_le_154 {n : ℕ} (hn : n ≤ 154) :
    ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) / 100 < 8 := by
  by_contra hge
  have h800 : (800 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) := by linarith
  have hpow : (800 : ℝ) ^ (16 : ℕ) ≤ ((((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) :=
    pow_le_pow_left₀ (by norm_num) h800 16
  rw [two_pow_rpow_one_sixteenth_pow_sixteen] at hpow
  have hmono : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (154 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) hn
  have hlt : (2 : ℝ) ^ (154 : ℕ) < (800 : ℝ) ^ (16 : ℕ) := by norm_num
  linarith

/-- Archival `SAME`/`MUB` crossover bound (outside the Round-6 manuscript; see Section 4 for
Round-6 `rem:crossover`): for `n ≥ 155`, `8 < 2^(n/16) / 100`. -/
theorem eight_lt_two_pow_div_sixteen_div_100_of_ge_155 {n : ℕ} (hn : 155 ≤ n) :
    8 < ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) / 100 := by
  by_contra hle
  have h800 : ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) ≤ 800 := by linarith
  have hnonneg : 0 ≤ ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) := by positivity
  have hpow : ((((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) ≤ (800 : ℝ) ^ (16 : ℕ) :=
    pow_le_pow_left₀ hnonneg h800 16
  rw [two_pow_rpow_one_sixteenth_pow_sixteen] at hpow
  have hmono : (2 : ℝ) ^ (155 : ℕ) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hgt : (800 : ℝ) ^ (16 : ℕ) < (2 : ℝ) ^ (155 : ℕ) := by norm_num
  linarith

/-- Archival `SAME`/`MUB` crossover corollary (outside the Round-6 manuscript; see Section 4 for
Round-6 `rem:crossover`): for an `n`-qubit target (`Fintype.card A = 2^n`) with `n ≥ 155`, any
adaptive strategy distinguishing `SAME` from `MUB` with advantage `(2/3, 1/3)` must make at least
`9` queries (`8 < q`), strictly exceeding the `8` box calls of a four-repetition switch test. -/
theorem same_mub_exceeds_eight_queries_of_ge_155 {n q : ℕ} [Nontrivial A] [Nonempty M]
    (T : BinaryHypothesisTest O) (tree : Tree (A × M) O q B) (ρ : State B)
    (hd : Fintype.card A = 2 ^ n) (hn : 155 ≤ n)
    (hhigh : ∀ U : Matrix.unitaryGroup A ℂ,
      (2 / 3 : ℝ) ≤ acceptance T tree ρ (hidden U) (hidden U))
    (hlow : ∀ U V : Matrix.unitaryGroup A ℂ,
      MutuallyUnbiased U V → acceptance T tree ρ (hidden U) (hidden V) ≤ 1 / 3) :
    9 ≤ q := by
  have hbound := same_mub_query_lower_bound T tree ρ n hd hhigh hlow
  rw [hd] at hbound
  have h8 := eight_lt_two_pow_div_sixteen_div_100_of_ge_155 hn
  have hq : (8 : ℝ) < (q : ℝ) := lt_trans h8 hbound
  have hqNat : 8 < q := by exact_mod_cast hq
  omega

/-! ## 4. Remark `rem:crossover` (Round-6 Manuscript): Thresholds `n ≥ 142` and `n ≥ 238`,
Switch-Test Call Bound `21 / p ≤ 14 ⌈3 / (2p)⌉`, and Trivial `1 / (3p)` Lower Bound -/

/-- **Remark `rem:crossover` (`n ≤ 141` strict sub-threshold)**:
For `n ≤ 141`, `2^(n/16) / 1400 < 1 / 3`. -/
theorem two_pow_div_sixteen_div_1400_lt_one_third_of_le_141 {n : ℕ} (hn : n ≤ 141) :
    ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400 < 1 / 3 := by
  by_contra hge
  have h1400 : (1400 : ℝ) ≤ 3 * ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) := by linarith
  have hpow :
      (1400 : ℝ) ^ (16 : ℕ) ≤ ((3 * ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) :=
    pow_le_pow_left₀ (by norm_num) h1400 16
  rw [mul_pow, two_pow_rpow_one_sixteenth_pow_sixteen] at hpow
  have hmono : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (141 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) hn
  have hlt : (3 : ℝ) ^ (16 : ℕ) * (2 : ℝ) ^ (141 : ℕ) < (1400 : ℝ) ^ (16 : ℕ) := by norm_num
  nlinarith [show (0 : ℝ) < (3 : ℝ) ^ (16 : ℕ) by norm_num]

/-- **Remark `rem:crossover` (`n ≤ 141` non-strict sub-threshold)**:
For `n ≤ 141`, `2^(n/16) / 1400 ≤ 1 / 3`. -/
theorem two_pow_div_sixteen_div_1400_le_one_third_of_le_141 {n : ℕ} (hn : n ≤ 141) :
    ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400 ≤ 1 / 3 :=
  le_of_lt (two_pow_div_sixteen_div_1400_lt_one_third_of_le_141 hn)

/-- **Remark `rem:crossover` (`n ≥ 142` threshold)**:
For `n ≥ 142`, `1 / 3 < 2^(n/16) / 1400`. -/
theorem one_third_lt_two_pow_div_sixteen_div_1400_of_ge_142 {n : ℕ} (hn : 142 ≤ n) :
    (1 / 3 : ℝ) < ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400 := by
  by_contra hle
  have h1400 : 3 * ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) ≤ 1400 := by linarith
  have hnonneg : 0 ≤ 3 * ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) := by positivity
  have hpow :
      ((3 * ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) ≤ (1400 : ℝ) ^ (16 : ℕ) :=
    pow_le_pow_left₀ hnonneg h1400 16
  rw [mul_pow, two_pow_rpow_one_sixteenth_pow_sixteen] at hpow
  have hmono : (2 : ℝ) ^ (142 : ℕ) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hgt : (1400 : ℝ) ^ (16 : ℕ) < (3 : ℝ) ^ (16 : ℕ) * (2 : ℝ) ^ (142 : ℕ) := by norm_num
  nlinarith [show (0 : ℝ) < (3 : ℝ) ^ (16 : ℕ) by norm_num]

/-- **Remark `rem:crossover` (exact `n ≥ 142` equivalence)**:
`1 / 3 < 2^(n/16) / 1400` holds if and only if `142 ≤ n`. -/
theorem one_third_lt_two_pow_div_sixteen_div_1400_iff {n : ℕ} :
    ((1 / 3 : ℝ) < ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400) ↔ 142 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hle : n ≤ 141 := by omega
    linarith [two_pow_div_sixteen_div_1400_lt_one_third_of_le_141 hle]
  · exact one_third_lt_two_pow_div_sixteen_div_1400_of_ge_142

/-- **Remark `rem:crossover` (`n ≤ 237` sub-threshold)**:
For `n ≤ 237`, `2^(n/16) / 1400 < 21`. -/
theorem two_pow_div_sixteen_div_1400_lt_twenty_one_of_le_237 {n : ℕ} (hn : n ≤ 237) :
    ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400 < 21 := by
  by_contra hge
  have h29400 : (29400 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) := by linarith
  have hpow : (29400 : ℝ) ^ (16 : ℕ) ≤ ((((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) :=
    pow_le_pow_left₀ (by norm_num) h29400 16
  rw [two_pow_rpow_one_sixteenth_pow_sixteen] at hpow
  have hmono : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (237 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) hn
  have hlt : (2 : ℝ) ^ (237 : ℕ) < (29400 : ℝ) ^ (16 : ℕ) := by norm_num
  linarith

/-- **Remark `rem:crossover` (`n ≥ 238` threshold)**:
For `n ≥ 238`, `21 < 2^(n/16) / 1400`. -/
theorem twenty_one_lt_two_pow_div_sixteen_div_1400_of_ge_238 {n : ℕ} (hn : 238 ≤ n) :
    (21 : ℝ) < ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400 := by
  by_contra hle
  have h29400 : ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) ≤ 29400 := by linarith
  have hnonneg : 0 ≤ ((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ) := by positivity
  have hpow : ((((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) ≤ (29400 : ℝ) ^ (16 : ℕ) :=
    pow_le_pow_left₀ hnonneg h29400 16
  rw [two_pow_rpow_one_sixteenth_pow_sixteen] at hpow
  have hmono : (2 : ℝ) ^ (238 : ℕ) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hgt : (29400 : ℝ) ^ (16 : ℕ) < (2 : ℝ) ^ (238 : ℕ) := by norm_num
  linarith

/-- **Remark `rem:crossover` (exact `n ≥ 238` equivalence)**:
`21 < 2^(n/16) / 1400` holds if and only if `238 ≤ n`. -/
theorem twenty_one_lt_two_pow_div_sixteen_div_1400_iff {n : ℕ} :
    ((21 : ℝ) < ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400) ↔ 238 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hle : n ≤ 237 := by omega
    linarith [two_pow_div_sixteen_div_1400_lt_twenty_one_of_le_237 hle]
  · exact twenty_one_lt_two_pow_div_sixteen_div_1400_of_ge_238

/-- **Remark `rem:crossover` (`p`-scaled `n ≥ 142` equivalence)**:
For `0 < p`, the Theorem 3 (`thm:c6`) lower bound `2^(n/16) / (1400 p)` strictly exceeds the
trivial diamond-distance lower bound `1 / (3p)` if and only if `142 ≤ n`. -/
theorem one_div_three_p_lt_validation_bound_iff {n : ℕ} {p : ℝ} (hp : 0 < p) :
    (1 / (3 * p) < ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / (1400 * p)) ↔ 142 ≤ n := by
  have hL : (1 : ℝ) / (3 * p) = (1 / 3 : ℝ) / p := by ring
  have hR :
      ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / (1400 * p) =
        (((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400) / p := by ring
  rw [hL, hR, div_lt_div_iff_of_pos_right hp]
  exact one_third_lt_two_pow_div_sixteen_div_1400_iff

/-- **Remark `rem:crossover` (`p`-scaled `n ≥ 238` equivalence)**:
For `0 < p`, the Theorem 3 (`thm:c6`) lower bound `2^(n/16) / (1400 p)` strictly exceeds `21 / p`
if and only if `238 ≤ n`. -/
theorem twenty_one_div_p_lt_validation_bound_iff {n : ℕ} {p : ℝ} (hp : 0 < p) :
    (21 / p < ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / (1400 * p)) ↔ 238 ≤ n := by
  have hR :
      ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / (1400 * p) =
        (((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400) / p := by ring
  rw [hR, div_lt_div_iff_of_pos_right hp]
  exact twenty_one_lt_two_pow_div_sixteen_div_1400_iff

/-- **Remark `rem:crossover` (`21 / p ≤ 14 ⌈3 / (2p)⌉`)**:
For every `0 < p`, `21 / p` is a lower bound on the `14 ⌈3 / (2p)⌉` device uses of the
seven-repetition quantum switch test. -/
theorem switch_test_calls_ge_twenty_one_div_p {p : ℝ} (hp : 0 < p) :
    21 / p ≤ 14 * (⌈3 / (2 * p)⌉₊ : ℝ) := by
  have hceil : 3 / (2 * p) ≤ (⌈3 / (2 * p)⌉₊ : ℝ) := Nat.le_ceil (3 / (2 * p))
  have hid : (21 : ℝ) / p = 14 * (3 / (2 * p)) := by
    field_simp [ne_of_gt hp]
    ring
  linarith

/-- For `n ≤ 237` and `0 < p`, the Theorem 3 lower bound `2^(n/16) / (1400 p)` is strictly less
than the `14 ⌈3 / (2p)⌉` device uses of the switch test. -/
theorem validation_bound_lt_switch_test_calls_of_le_237 {n : ℕ} {p : ℝ}
    (hn : n ≤ 237) (hp : 0 < p) :
    ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / (1400 * p) < 14 * (⌈3 / (2 * p)⌉₊ : ℝ) := by
  have hlt21 : ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / (1400 * p) < 21 / p := by
    have hR :
        ((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / (1400 * p) =
          (((2 ^ n : ℕ) : ℝ) ^ ((1 : ℝ) / 16) / 1400) / p := by ring
    rw [hR, div_lt_div_iff_of_pos_right hp]
    exact two_pow_div_sixteen_div_1400_lt_twenty_one_of_le_237 hn
  exact lt_of_lt_of_le hlt21 (switch_test_calls_ge_twenty_one_div_p hp)

/-! ### 4b. General `Q`-query diamond-distance output bound and trivial `1 / (3p) ≤ Q` lower bound -/

omit [Nontrivial A] in
theorem applyState_distance_le_diamond {H K : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype K] [DecidableEq K] (Φ Ψ : Channel H K) (σ : State H) :
    (Φ.applyState σ).normalizedTraceDistance (Ψ.applyState σ) ≤ Φ.diamondTraceDistance Ψ := by
  let ω : State (H × H) := σ.prod σ
  have hmarg : ω.marginalA = σ := State.ext (State.partialTraceB_prod σ σ)
  have hΦ :
      (Channel.traceOutRight K H).applyState ((Φ.prod (Channel.idChannel H)).applyState ω) =
        Φ.applyState σ := by
    rw [Channel.traceOutRight_applyState, State.marginalA_applyState_prod_id, hmarg]
  have hΨ :
      (Channel.traceOutRight K H).applyState ((Ψ.prod (Channel.idChannel H)).applyState ω) =
        Ψ.applyState σ := by
    rw [Channel.traceOutRight_applyState, State.marginalA_applyState_prod_id, hmarg]
  rw [← hΦ, ← hΨ]
  exact (Channel.normalizedTraceDistance_applyState_le (Channel.traceOutRight K H) _ _).trans
    (ICO.DiamondPreprocessing.input_distance_le_diamond Φ Ψ ω)

omit [Nontrivial A] in
theorem traceNorm_real_smul_nonneg {H : Type} [Fintype H] [DecidableEq H]
    {c : ℝ} (hc : 0 ≤ c) (X : CMatrix H) :
    traceNorm ((c : ℂ) • X) ≤ c * traceNorm X := by
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace ((c : ℂ) • X)
  rw [← hU, Matrix.smul_mul, Matrix.trace_smul]
  change ‖(c : ℂ) * (X * (U : CMatrix H)).trace‖ ≤ c * traceNorm X
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (traceNorm_variational_unitary_abs_trace_le X U) hc

omit [Nontrivial A] in
theorem channel_psd_diff_traceNorm_le {H K : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype K] [DecidableEq K] (Φ Ψ : Channel H K) {ε : ℝ}
    (hdiam : Φ.diamondTraceDistance Ψ ≤ ε) (X : CMatrix H) (hX : X.PosSemidef) :
    (1 / 2 : ℝ) * traceNorm (Φ.map X - Ψ.map X) ≤ ε * X.trace.re := by
  by_cases hX0 : X = 0
  · subst hX0
    simp [traceNorm_zero]
  · have htr_ne : X.trace.re ≠ 0 := State.posSemidef_trace_ne_zero_of_ne_zero hX hX0
    have htr_pos : 0 < X.trace.re := State.posSemidef_trace_pos_of_ne_zero hX hX0
    let σ : State H := State.normalizePSD X hX htr_ne
    have hX_eq : X = ((X.trace.re : ℂ)) • σ.matrix := by
      ext i j
      simp [σ, State.normalizePSD_matrix, Complex.real_smul, mul_inv_cancel_left₀
        (Complex.ofReal_ne_zero.mpr htr_ne)]
    have hΦX : Φ.map X = (X.trace.re : ℂ) • Φ.map σ.matrix := by
      rw [← LinearMap.map_smul, ← hX_eq]
    have hΨX : Ψ.map X = (X.trace.re : ℂ) • Ψ.map σ.matrix := by
      rw [← LinearMap.map_smul, ← hX_eq]
    have hdiff : Φ.map X - Ψ.map X = (X.trace.re : ℂ) • (Φ.map σ.matrix - Ψ.map σ.matrix) := by
      rw [hΦX, hΨX, ← smul_sub]
    rw [hdiff]
    have hsmul := traceNorm_real_smul_nonneg htr_pos.le (Φ.map σ.matrix - Ψ.map σ.matrix)
    have hst : (1 / 2 : ℝ) * traceNorm (Φ.map σ.matrix - Ψ.map σ.matrix) ≤ ε :=
      (applyState_distance_le_diamond Φ Ψ σ).trans hdiam
    nlinarith

omit [Nontrivial A] in
theorem tree_psd_diff_traceNorm_le {H O B : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B] {Q : ℕ}
    (tree : Tree H O Q B)
    (Φ₁ Φ₂ Ψ₁ Ψ₂ : Channel H H) {ε : ℝ} (hε : 0 ≤ ε)
    (h₁ : Φ₁.diamondTraceDistance Ψ₁ ≤ ε)
    (h₂ : Φ₂.diamondTraceDistance Ψ₂ ≤ ε)
    (X : CMatrix B) (hX : X.PosSemidef) :
    (1 / 2 : ℝ) * traceNorm ((tree.channel Φ₁ Φ₂).map X - (tree.channel Ψ₁ Ψ₂).map X) ≤
      (Q : ℝ) * ε * X.trace.re := by
  induction tree with
  | @stop q B' _ _ after =>
    rw [Tree.stop_map, Tree.stop_map, sub_self, traceNorm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg q) hε) (Matrix.PosSemidef.trace_nonneg hX).1
  | @query q b after ih =>
    rw [Tree.query_map, Tree.query_map, LinearMap.comp_apply, LinearMap.comp_apply]
    set Φb : Channel H H := if b then Φ₂ else Φ₁
    set Ψb : Channel H H := if b then Ψ₂ else Ψ₁
    have hdiam_b : Φb.diamondTraceDistance Ψb ≤ ε := by
      cases b
      · exact h₁
      · exact h₂
    have hsplit :
        (after.channel Φ₁ Φ₂).map (Φb.map X) - (after.channel Ψ₁ Ψ₂).map (Ψb.map X) =
          ((after.channel Φ₁ Φ₂).map (Φb.map X) - (after.channel Ψ₁ Ψ₂).map (Φb.map X)) +
            (after.channel Ψ₁ Ψ₂).map (Φb.map X - Ψb.map X) := by
      rw [map_sub]
      abel
    rw [hsplit]
    have htri := traceNorm_add_le
      ((after.channel Φ₁ Φ₂).map (Φb.map X) - (after.channel Ψ₁ Ψ₂).map (Φb.map X))
      ((after.channel Ψ₁ Ψ₂).map (Φb.map X - Ψb.map X))
    have hpart1 :
        (1 / 2 : ℝ) *
          traceNorm ((after.channel Φ₁ Φ₂).map (Φb.map X) -
            (after.channel Ψ₁ Ψ₂).map (Φb.map X)) ≤
        (q : ℝ) * ε * X.trace.re := by
      have hih := ih (Φb.map X) (Φb.mapsPositive X hX)
      rwa [Φb.tracePreserving X] at hih
    have hpart2 :
        (1 / 2 : ℝ) * traceNorm ((after.channel Ψ₁ Ψ₂).map (Φb.map X - Ψb.map X)) ≤
          ε * X.trace.re := by
      have hHerm : (Φb.map X - Ψb.map X).IsHermitian :=
        (Φb.mapsPositive X hX).isHermitian.sub (Ψb.mapsPositive X hX).isHermitian
      have htr0 : (Φb.map X - Ψb.map X).trace = 0 := by
        rw [Matrix.trace_sub, Φb.tracePreserving X, Ψb.tracePreserving X, sub_self]
      have hcontr := MatrixMap.traceNorm_apply_le_of_traceNonincreasingCP
        (Channel.traceNonincreasingCP_map (after.channel Ψ₁ Ψ₂)) hHerm htr0
      have hstep := channel_psd_diff_traceNorm_le Φb Ψb hdiam_b X hX
      linarith
    have hqcast : ((q + 1 : ℕ) : ℝ) * ε * X.trace.re =
        (q : ℝ) * ε * X.trace.re + ε * X.trace.re := by
      push_cast
      ring
    linarith
  | @node q B' C' L _ _ _ _ _ _ I next ih =>
    rw [tree_node_map_apply, tree_node_map_apply, ← Finset.sum_sub_distrib]
    have hsum_tn := traceNorm_sum_le_sum_traceNorm Finset.univ
      (fun l : L => ((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l)ᴴ) -
        ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l)ᴴ))
    have hbranch (l : L) :
        (1 / 2 : ℝ) * traceNorm (((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l)ᴴ) -
          ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l)ᴴ)) ≤
        (q : ℝ) * ε * (I.op l * X * (I.op l)ᴴ).trace.re :=
      ih l (I.op l * X * (I.op l)ᴴ) (hX.mul_mul_conjTranspose_same (I.op l))
    have hsum_le :
        (∑ l : L, (1 / 2 : ℝ) *
          traceNorm (((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l)ᴴ) -
            ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l)ᴴ))) ≤
        ∑ l : L, (q : ℝ) * ε * (I.op l * X * (I.op l)ᴴ).trace.re :=
      Finset.sum_le_sum fun l _ => hbranch l
    have htp : (∑ l : L, (I.op l * X * (I.op l)ᴴ).trace.re) = X.trace.re := by
      have hI : MatrixMap.krausAdjoint I.op (1 : CMatrix C') = 1 := by
        simpa [MatrixMap.krausAdjoint] using I.complete
      have htr := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one I.op hI X
      have hre := congrArg Complex.re htr
      simpa [MatrixMap.ofKraus, Matrix.trace_sum, Complex.re_sum] using hre
    have hLHS :
        (1 / 2 : ℝ) *
          (∑ l : L, traceNorm (((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l)ᴴ) -
            ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l)ᴴ))) =
        ∑ l : L, (1 / 2 : ℝ) *
          traceNorm (((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l)ᴴ) -
            ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l)ᴴ)) :=
      Finset.mul_sum _ _ _
    have hRHS :
        (∑ l : L, (q : ℝ) * ε * (I.op l * X * (I.op l)ᴴ).trace.re) =
          (q : ℝ) * ε * X.trace.re := by
      rw [← Finset.mul_sum, htp]
    linarith

omit [Nontrivial A] in
/-- **Budget-`Q` adaptive output trace-distance bound from diamond trace distance**:
For any budget-`Q` adaptive strategy `tree` and channel pairs `(Φ₁, Ψ₁), (Φ₂, Ψ₂)` on `A × M`
with half-diamond distance at most `p` (`0 ≤ p`), the output states on any input `ρ` have
normalized trace distance at most `Q * p`. -/
theorem tree_state_distance_le_of_diamond [Nonempty A] [Nonempty M] {Q : ℕ}
    (tree : Tree (A × M) O Q B) (ρ : State B)
    (Φ₁ Φ₂ Ψ₁ Ψ₂ : Channel (A × M) (A × M)) {p : ℝ} (hp : 0 ≤ p)
    (h₁ : Φ₁.diamondTraceDistance Ψ₁ ≤ p)
    (h₂ : Φ₂.diamondTraceDistance Ψ₂ ≤ p) :
    ((tree.channel Φ₁ Φ₂).applyState ρ).normalizedTraceDistance
      ((tree.channel Ψ₁ Ψ₂).applyState ρ) ≤ (Q : ℝ) * p := by
  have h := tree_psd_diff_traceNorm_le tree Φ₁ Φ₂ Ψ₁ Ψ₂ hp h₁ h₂ ρ.matrix ρ.pos
  rw [ρ.trace_re_eq_one, mul_one] at h
  exact h

omit [Nontrivial A] in
/-- **Remark `rem:crossover` (Trivial `1 / (3p) ≤ Q` lower bound from diamond distance `≤ p`)**:
For any two channels `Φ, Ψ` on `A × M` with `Φ.diamondTraceDistance Ψ ≤ p` (`0 < p`), any
budget-`Q` adaptive tree `tree`, input state `ρ`, and binary test `T` achieving acceptance
`≥ 2/3` on `Φ` and `≤ 1/3` on `Ψ`, at least `1 / (3p)` queries are required:
`1 / (3 * p) ≤ Q`. -/
theorem trivial_query_lower_bound_of_diamond_le [Nonempty A] [Nonempty M] {Q : ℕ}
    {p : ℝ} (hp : 0 < p)
    (Φ Ψ : Channel (A × M) (A × M))
    (hdiam : Φ.diamondTraceDistance Ψ ≤ p)
    (T : BinaryHypothesisTest O)
    (tree : Tree (A × M) O Q B) (ρ : State B)
    (hhigh : (2 / 3 : ℝ) ≤ acceptance T tree ρ Φ Φ)
    (hlow : acceptance T tree ρ Ψ Ψ ≤ 1 / 3) :
    (1 : ℝ) / (3 * p) ≤ (Q : ℝ) := by
  rw [acceptance_eq] at hhigh hlow
  have hgap : (1 / 3 : ℝ) ≤
      ((tree.channel Φ Φ).applyState ρ).normalizedTraceDistance
        ((tree.channel Ψ Ψ).applyState ρ) :=
    ICO.QuantumDecision.successful_decision_requires_distance T _ _ hhigh hlow
  have hub := tree_state_distance_le_of_diamond tree ρ Φ Φ Ψ Ψ hp.le hdiam hdiam
  have hQp : (1 / 3 : ℝ) ≤ (Q : ℝ) * p := hgap.trans hub
  rw [div_le_iff₀ (by positivity)]
  linarith

omit [Nontrivial A] in
/-- **Remark `rem:crossover` (Balanced-prior `1 / (3p) ≤ Q` lower bound from diamond distance `≤ p`)**:
Same `1 / (3p) ≤ Q` lower bound under balanced-prior success probability at least `2 / 3`. -/
theorem trivial_balanced_query_lower_bound_of_diamond_le [Nonempty A] [Nonempty M] {Q : ℕ}
    {p : ℝ} (hp : 0 < p)
    (Φ Ψ : Channel (A × M) (A × M))
    (hdiam : Φ.diamondTraceDistance Ψ ≤ p)
    (T : BinaryHypothesisTest O)
    (tree : Tree (A × M) O Q B) (ρ : State B)
    (hsucc : (2 / 3 : ℝ) ≤
      (1 / 2 : ℝ) * (acceptance T tree ρ Φ Φ + (1 - acceptance T tree ρ Ψ Ψ))) :
    (1 : ℝ) / (3 * p) ≤ (Q : ℝ) := by
  have hdiff : (1 / 3 : ℝ) ≤ acceptance T tree ρ Φ Φ - acceptance T tree ρ Ψ Ψ := by linarith
  rw [acceptance_eq, acceptance_eq] at hdiff
  have hgap := ICO.QuantumDecision.accept_gap_le_traceDistance T
    ((tree.channel Φ Φ).applyState ρ) ((tree.channel Ψ Ψ).applyState ρ)
  have hub := tree_state_distance_le_of_diamond tree ρ Φ Φ Ψ Ψ hp.le hdiam hdiam
  have hQp : (1 / 3 : ℝ) ≤ (Q : ℝ) * p := by linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

end

end ICO.RemarksUnitaryNumerical

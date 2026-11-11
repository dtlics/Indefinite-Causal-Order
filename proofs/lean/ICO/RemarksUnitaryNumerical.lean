import ICO.C4FullSwitchTheorem
import ICO.C6OperationalDecision

/-!
# Remark `rem:unitary` and Numerical Remarks `rem:approx-content` and `rem:crossover`

1. **Remark `rem:unitary` (Three calls suffice for unitary boxes)**:
   For unitary boxes `U, V ∈ U(A)`, a 3-call circuit in the `BudgetQueryTree.Tree`
   model with a dummy register initialized in a fixed basis state `|a₀⟩` and
   controlled swaps between the target and dummy registers implements the exact
   quantum switch channel `SW[U, V]`.
2. **Remark `rem:approx-content` (Numerical regime of Theorem 2 / Corollary 11)**:
   At `q = 2`, the tradeoff bound `1/2 - 13(r+1)²/(3d) - q(q-1)/(2(r+1))` is
   strictly positive at `r + 1 = 3` (`r = 2`) for all `d ≥ 235` (giving error
   `≥ 1/6 - 39/d ≥ 1/1410 > 0`), and is nonpositive for all `r` when `1 ≤ d ≤ 234`.
   Furthermore, the constant-error corollary `d < 4096 q⁴` at `ε = 1/48` forces
   `q ≥ 3` whenever `d ≥ 65536`.
3. **Remark `rem:crossover` (Numerical crossover thresholds `n = 107` and `n = 155`)**:
   For `d = 2^n`, the lower bound `d^(1/16)/100 = 2^(n/16)/100` satisfies
   `2^(n/16)/100 < 1` for `n ≤ 106` and `2^(n/16)/100 > 1` for `n ≥ 107`
   (forcing `q ≥ 2`), and satisfies `2^(n/16)/100 < 8` for `n ≤ 154` and
   `2^(n/16)/100 > 8` for `n ≥ 155` (forcing `q ≥ 9 > 8`, exceeding the 8 box
   calls of the four-repetition switch test).
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

/-! ## 1. Remark `rem:unitary`: Three Calls Suffice for Unitary Boxes -/

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

/-! ## 3. Remark `rem:crossover`: Crossover Thresholds `n = 107` and `n = 155` -/

theorem two_pow_rpow_one_sixteenth_pow_sixteen (n : ℕ) :
    ((((2 ^ n : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ)) = (2 : ℝ) ^ n := by
  have hpos : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos]
  norm_num

/-- For `n ≤ 106`, `2^(n/16) / 100 < 1`. -/
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

/-- For `n ≥ 107`, `1 < 2^(n/16) / 100`. -/
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

/-- **Remark `rem:crossover` (`n ≥ 107` forces `q ≥ 2` in `same_mub_query_lower_bound`)**:
For an `n`-qubit target (`Fintype.card A = 2^n`) with `n ≥ 107`, any adaptive
strategy distinguishing `SAME` from `MUB` with advantage `(2/3, 1/3)` must make
at least `2` queries. -/
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

/-- For `n ≤ 154`, `2^(n/16) / 100 < 8`. -/
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

/-- For `n ≥ 155`, `8 < 2^(n/16) / 100`. -/
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

/-- **Remark `rem:crossover` (`n ≥ 155` forces `q ≥ 9 > 8` in `same_mub_query_lower_bound`)**:
For an `n`-qubit target (`Fintype.card A = 2^n`) with `n ≥ 155`, any adaptive
strategy distinguishing `SAME` from `MUB` with advantage `(2/3, 1/3)` must make
at least `9` queries (`8 < q`), strictly exceeding the `8` box calls used by
four repetitions of the quantum switch test. -/
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

#print axioms unitaryThreeCallTree_channel_eq
#print axioms unitaryThreeCallTree_fullChannel_eq
#print axioms unitaryThreeCallTree_allChannel_eq
#print axioms unitaryThreeCallTree_diamond_zero
#print axioms exists_two_query_switch_error_ge_235
#print axioms two_query_tradeoff_nonpos_of_le_234
#print axioms full_switch_one_over_48_three_queries_of_ge_65536
#print axioms two_pow_div_sixteen_div_100_lt_one_of_le_106
#print axioms one_lt_two_pow_div_sixteen_div_100_of_ge_107
#print axioms same_mub_at_least_two_queries_of_ge_107
#print axioms two_pow_div_sixteen_div_100_lt_eight_of_le_154
#print axioms eight_lt_two_pow_div_sixteen_div_100_of_ge_155
#print axioms same_mub_exceeds_eight_queries_of_ge_155

end

end ICO.RemarksUnitaryNumerical

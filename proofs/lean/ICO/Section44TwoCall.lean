import ICO.C4FullSwitchTheorem

/-!
# Section 4.4: Two-Call Measure-Control Strategy With Error at Most 1/2

Measuring the control qubit in the computational basis `{|0⟩, |1⟩}` and applying
the two unknown boxes in the corresponding order (`B ∘ A` on `|0⟩`, `A ∘ B`
on `|1⟩`) uses two queries (`q = 2`) and implements `dephaseControl ∘ SW[A, B]`,
where `dephaseControl` dephases the control qubit in the computational basis.
Because `dephaseControl(ρ) - ρ = (1/2) (Z_c ρ Z_c - ρ)`, its diamond trace
distance to the ideal switch channel is at most `1/2` for every pair of channels
and every unitary-mixture sample `UV : Sample A r`.
-/

namespace ICO.Section44TwoCall

open Matrix QIT ICO.InstrumentCompression ICO.BudgetQueryTree
open ICO.AllChannelDilation ICO.FullSwitchChannel ICO.BudgetHaarBound
open ICO.C4PhysicalEnsemble ICO.SwitchChoiWitness
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

instance : Nonempty A := Nontrivial.to_nonempty

/-- Project the control qubit onto computational basis state `b : Bool`. -/
def dephaseKraus (b : Bool) : CMatrix (A × Bool) :=
  if b then controlled (0 : CMatrix A) (1 : CMatrix A)
  else controlled (1 : CMatrix A) (0 : CMatrix A)

theorem dephaseKraus_conjTranspose (b : Bool) :
    (dephaseKraus (A := A) b)ᴴ = dephaseKraus (A := A) b := by
  cases b <;> simp [dephaseKraus, controlled_star]

theorem dephaseKraus_mul_self (b : Bool) :
    (dephaseKraus (A := A) b)ᴴ * dephaseKraus (A := A) b = dephaseKraus (A := A) b := by
  cases b <;> simp [dephaseKraus, controlled_star, controlled_mul]

theorem dephaseKraus_complete :
    ∑ b : Bool, (dephaseKraus (A := A) b)ᴴ * dephaseKraus (A := A) b = 1 := by
  simp_rw [dephaseKraus_mul_self]
  rw [Fintype.sum_bool]
  ext ⟨a₁, c₁⟩ ⟨a₂, c₂⟩
  cases c₁ <;> cases c₂ <;> simp [dephaseKraus, controlled, Matrix.one_apply]

/-- Two-outcome instrument measuring the control qubit in `{|0⟩, |1⟩}`. -/
def dephaseInstrument : Instrument (A × Bool) (A × Bool) Bool where
  op := dephaseKraus (A := A)
  complete := dephaseKraus_complete (A := A)

/-- Computational-basis dephasing channel on the control qubit of `A × Bool`. -/
def dephaseControl : Channel (A × Bool) (A × Bool) where
  map := MatrixMap.ofKraus (dephaseKraus (A := A))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using dephaseKraus_complete (A := A))
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem controlled_proj_conj_apply (b : Bool) (X : CMatrix (A × Bool)) (ij kl : A × Bool) :
    (dephaseKraus (A := A) b * X * (dephaseKraus (A := A) b)ᴴ) ij kl =
      if ij.2 = b ∧ kl.2 = b then X ij kl else 0 := by
  rcases ij with ⟨a₁, c₁⟩
  rcases kl with ⟨a₂, c₂⟩
  rw [dephaseKraus_conjTranspose]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  rw [Finset.sum_eq_single c₂]
  · rw [Finset.sum_eq_single a₂]
    · rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      rw [Finset.sum_eq_single c₁]
      · rw [Finset.sum_eq_single a₁]
        · cases b <;> cases c₁ <;> cases c₂ <;>
            simp [dephaseKraus, controlled]
        · intro x _ hx
          have hne : a₁ ≠ x := Ne.symm hx
          cases b <;> cases c₁ <;> simp [dephaseKraus, controlled, hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
      · intro c _ hc
        apply Finset.sum_eq_zero
        intro x _
        have hne : c₁ ≠ c := Ne.symm hc
        cases b <;> simp [dephaseKraus, controlled, hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · intro y _ hy
      have hne : y ≠ a₂ := hy
      cases b <;> cases c₂ <;> simp [dephaseKraus, controlled, Matrix.one_apply, hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro y _
    have hne : c ≠ c₂ := hc
    cases b <;> simp [dephaseKraus, controlled, hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

@[simp]
theorem dephaseControl_map_apply (X : CMatrix (A × Bool)) (ij kl : A × Bool) :
    (dephaseControl (A := A)).map X ij kl = if ij.2 = kl.2 then X ij kl else 0 := by
  change (∑ b : Bool, dephaseKraus (A := A) b * X * (dephaseKraus (A := A) b)ᴴ) ij kl = _
  simp only [Matrix.sum_apply, Fintype.sum_bool, controlled_proj_conj_apply]
  cases ij.2 <;> cases kl.2 <;> simp

/-- Pauli-`Z` phase-flip unitary `I_A ⊗ Z` on `A × Bool`. -/
def phaseFlipMatrix : CMatrix (A × Bool) :=
  controlled (1 : CMatrix A) (-1 : CMatrix A)

theorem phaseFlipMatrix_conjTranspose :
    (phaseFlipMatrix (A := A))ᴴ = phaseFlipMatrix (A := A) := by
  simp [phaseFlipMatrix, controlled_star]

theorem phaseFlipMatrix_complete :
    (phaseFlipMatrix (A := A))ᴴ * phaseFlipMatrix (A := A) = 1 := by
  rw [phaseFlipMatrix_conjTranspose, phaseFlipMatrix, controlled_mul]
  simp [controlled_one]

/-- Unitary channel conjugating `A × Bool` by `I_A ⊗ Z`. -/
def phaseFlipControl : Channel (A × Bool) (A × Bool) :=
  ICO.ClassicalDilation.isometryChannel (phaseFlipMatrix (A := A))
    (phaseFlipMatrix_complete (A := A))

@[simp]
theorem phaseFlipControl_map_apply (X : CMatrix (A × Bool)) (ij kl : A × Bool) :
    (phaseFlipControl (A := A)).map X ij kl =
      if ij.2 = kl.2 then X ij kl else - X ij kl := by
  rcases ij with ⟨a₁, c₁⟩
  rcases kl with ⟨a₂, c₂⟩
  rw [phaseFlipControl, ICO.ClassicalDilation.isometryChannel_apply,
    phaseFlipMatrix_conjTranspose]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  rw [Finset.sum_eq_single c₂]
  · rw [Finset.sum_eq_single a₂]
    · rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      rw [Finset.sum_eq_single c₁]
      · rw [Finset.sum_eq_single a₁]
        · cases c₁ <;> cases c₂ <;> simp [phaseFlipMatrix, controlled]
        · intro x _ hx
          have hne : a₁ ≠ x := Ne.symm hx
          cases c₁ <;> simp [phaseFlipMatrix, controlled, hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
      · intro c _ hc
        apply Finset.sum_eq_zero
        intro x _
        have hne : c₁ ≠ c := Ne.symm hc
        simp [phaseFlipMatrix, controlled, hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · intro y _ hy
      have hne : y ≠ a₂ := hy
      cases c₂ <;> simp [phaseFlipMatrix, controlled, Matrix.one_apply, hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro y _
    have hne : c ≠ c₂ := hc
    simp [phaseFlipMatrix, controlled, hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- Normalized trace distance between any two density states is at most `1`. -/
theorem state_normalizedTraceDistance_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (ρ σ : State α) :
    ρ.normalizedTraceDistance σ ≤ 1 := by
  change (1 / 2 : ℝ) * traceNorm (ρ.matrix - σ.matrix) ≤ 1
  have hsub : ρ.matrix - σ.matrix = ρ.matrix + (-σ.matrix) := sub_eq_add_neg _ _
  have htri : traceNorm (ρ.matrix - σ.matrix) ≤ traceNorm ρ.matrix + traceNorm σ.matrix := by
    rw [hsub, ← traceNorm_neg σ.matrix]
    exact traceNorm_add_le ρ.matrix (-σ.matrix)
  have hρ : traceNorm ρ.matrix = 1 := by
    rw [traceNorm_posSemidef_eq_trace_re ρ.matrix ρ.pos, ρ.trace_eq_one]
    rfl
  have hσ : traceNorm σ.matrix = 1 := by
    rw [traceNorm_posSemidef_eq_trace_re σ.matrix σ.pos, σ.trace_eq_one]
    rfl
  linarith

/-- On any bipartite state `ω`, dephasing the control after `Ψ` differs from `Ψ`
by `(1/2)` times the difference between control-phase-flipping after `Ψ` and `Ψ`. -/
theorem dephaseControl_comp_output_sub (Ψ : Channel (A × Bool) (A × Bool))
    (ω : State ((A × Bool) × (A × Bool))) :
    ((((dephaseControl (A := A)).comp Ψ).prod (Channel.idChannel (A × Bool))).applyState ω).matrix -
      ((Ψ.prod (Channel.idChannel (A × Bool))).applyState ω).matrix =
    ((1 / 2 : ℝ) : ℂ) •
      (((((phaseFlipControl (A := A)).comp Ψ).prod (Channel.idChannel (A × Bool))).applyState ω).matrix -
        ((Ψ.prod (Channel.idChannel (A × Bool))).applyState ω).matrix) := by
  ext x y
  change MatrixMap.kron ((dephaseControl (A := A)).map.comp Ψ.map)
      (Channel.idChannel (A × Bool)).map ω.matrix x y -
    MatrixMap.kron Ψ.map (Channel.idChannel (A × Bool)).map ω.matrix x y =
    ((1 / 2 : ℝ) : ℂ) *
      (MatrixMap.kron ((phaseFlipControl (A := A)).map.comp Ψ.map)
        (Channel.idChannel (A × Bool)).map ω.matrix x y -
      MatrixMap.kron Ψ.map (Channel.idChannel (A × Bool)).map ω.matrix x y)
  rw [MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_apply_slice,
    MatrixMap.kron_idChannel_apply_slice]
  simp only [LinearMap.comp_apply, dephaseControl_map_apply, phaseFlipControl_map_apply]
  by_cases h : x.1.2 = y.1.2
  · simp [h]
  · simp [h]; ring

/-- Post-composing any channel on `A × Bool` with control dephasing incurs
diamond trace distance at most `1/2`. -/
theorem dephaseControl_comp_diamond_le_half (Ψ : Channel (A × Bool) (A × Bool)) :
    Channel.diamondTraceDistance ((dephaseControl (A := A)).comp Ψ) Ψ ≤ 1 / 2 := by
  apply Channel.diamondTraceDistance_le_of_inputReferenceBound
  intro ω
  let σ₁ := (((dephaseControl (A := A)).comp Ψ).prod (Channel.idChannel (A × Bool))).applyState ω
  let σ₂ := (((phaseFlipControl (A := A)).comp Ψ).prod (Channel.idChannel (A × Bool))).applyState ω
  let τ := (Ψ.prod (Channel.idChannel (A × Bool))).applyState ω
  change (1 / 2 : ℝ) * traceNorm (σ₁.matrix - τ.matrix) ≤ 1 / 2
  rw [dephaseControl_comp_output_sub Ψ ω,
    traceNorm_real_smul_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hle : σ₂.normalizedTraceDistance τ ≤ 1 := state_normalizedTraceDistance_le_one σ₂ τ
  change (1 / 2 : ℝ) * traceNorm (σ₂.matrix - τ.matrix) ≤ 1 at hle
  linarith

/-- Symmetric version: `Ψ.diamondTraceDistance ((dephaseControl (A := A)).comp Ψ) ≤ 1/2`. -/
theorem diamond_dephaseControl_comp_le_half (Ψ : Channel (A × Bool) (A × Bool)) :
    Ψ.diamondTraceDistance ((dephaseControl (A := A)).comp Ψ) ≤ 1 / 2 := by
  apply Channel.diamondTraceDistance_le_of_inputReferenceBound
  intro ω
  let σ₁ := (((dephaseControl (A := A)).comp Ψ).prod (Channel.idChannel (A × Bool))).applyState ω
  let σ₂ := (((phaseFlipControl (A := A)).comp Ψ).prod (Channel.idChannel (A × Bool))).applyState ω
  let τ := (Ψ.prod (Channel.idChannel (A × Bool))).applyState ω
  change (1 / 2 : ℝ) * traceNorm (τ.matrix - σ₁.matrix) ≤ 1 / 2
  have hneg : τ.matrix - σ₁.matrix = -(σ₁.matrix - τ.matrix) := by abel
  rw [hneg, traceNorm_neg, dephaseControl_comp_output_sub Ψ ω,
    traceNorm_real_smul_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hle : σ₂.normalizedTraceDistance τ ≤ 1 := state_normalizedTraceDistance_le_one σ₂ τ
  change (1 / 2 : ℝ) * traceNorm (σ₂.matrix - τ.matrix) ≤ 1 at hle
  linarith

/-- Control dephasing on `A × Bool` has diamond trace distance at most `1/2`
from the identity channel (`(1/2) ‖id - D‖_⋄ ≤ 1/2`). -/
theorem dephaseControl_diamond_id_le_half :
    (dephaseControl (A := A)).diamondTraceDistance
      (Channel.idChannel (A × Bool)) ≤ 1 / 2 := by
  have hid : (dephaseControl (A := A)).comp (Channel.idChannel (A × Bool)) =
      dephaseControl (A := A) := by
    apply channel_eq_of_map_eq
    ext X ij kl
    simp [Channel.comp, Channel.idChannel, MatrixMap.ofKraus]
  rw [← hid]
  exact dephaseControl_comp_diamond_le_half (Channel.idChannel (A × Bool))

/-- **Section 4.4 two-call strategy (`q = 2`)**:
A three-node `BudgetQueryTree.Tree` on `A × Bool` that measures the control
qubit in `{|0⟩, |1⟩}` (`dephaseInstrument`) and applies two queries in order
`B ∘ A` (`false`, then `true`) on branch `false` and `A ∘ B` (`true`, then `false`)
on branch `true`. -/
def twoCallTree : Tree (A × Bool) (A × Bool) 2 (A × Bool) :=
  .node (dephaseInstrument (A := A)) (fun b =>
    if b then
      .query true (.query false (.stop (Channel.idChannel (A × Bool))))
    else
      .query false (.query true (.stop (Channel.idChannel (A × Bool)))))

theorem kronecker_one_eq_controlled (U : CMatrix A) :
    Matrix.kronecker U (1 : CMatrix Bool) = controlled U U := by
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  cases b₁ <;> cases b₂ <;>
    simp [controlled, Matrix.kronecker, Matrix.kroneckerMap_apply]

theorem conj_controlled_mul (T₁ S₁ T₂ S₂ : CMatrix A) (X : CMatrix (A × Bool)) :
    controlled T₁ S₁ * (controlled T₂ S₂ * X * (controlled T₂ S₂)ᴴ) * (controlled T₁ S₁)ᴴ =
      controlled (T₁ * T₂) (S₁ * S₂) * X * (controlled (T₁ * T₂) (S₁ * S₂))ᴴ := by
  calc
    controlled T₁ S₁ * (controlled T₂ S₂ * X * (controlled T₂ S₂)ᴴ) * (controlled T₁ S₁)ᴴ =
        (controlled T₁ S₁ * controlled T₂ S₂) * X * (controlled T₁ S₁ * controlled T₂ S₂)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = controlled (T₁ * T₂) (S₁ * S₂) * X * (controlled (T₁ * T₂) (S₁ * S₂))ᴴ := by
      rw [controlled_mul]

theorem oracleChannel_controlled_conj {I : Type} [Fintype I] [DecidableEq I]
    (U : I → CMatrix A) (hU : ∑ k, (U k)ᴴ * U k = 1)
    (T S : CMatrix A) (X : CMatrix (A × Bool)) :
    (oracleChannel (M := Bool) U hU).map (controlled T S * X * (controlled T S)ᴴ) =
      ∑ k : I, controlled (U k * T) (U k * S) * X * (controlled (U k * T) (U k * S))ᴴ := by
  change (∑ k : I, Matrix.kronecker (U k) (1 : CMatrix Bool) *
      (controlled T S * X * (controlled T S)ᴴ) *
      (Matrix.kronecker (U k) (1 : CMatrix Bool))ᴴ) = _
  simp_rw [kronecker_one_eq_controlled, conj_controlled_mul]

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

/-- General Kraus switch operators `controlled (F j * E i) (E i * F j)` on `A × Bool`. -/
def krausSwitch {r s : ℕ} (E : Fin r → CMatrix A) (F : Fin s → CMatrix A)
    (ij : Fin r × Fin s) : CMatrix (A × Bool) :=
  controlled (F ij.2 * E ij.1) (E ij.1 * F ij.2)

theorem krausSwitch_complete {r s : ℕ} (E : Fin r → CMatrix A) (F : Fin s → CMatrix A)
    (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1) :
    ∑ ij : Fin r × Fin s, (krausSwitch E F ij)ᴴ * krausSwitch E F ij = 1 := by
  have h1 :
      ∑ i : Fin r, ∑ j : Fin s, (F j * E i)ᴴ * (F j * E i) = 1 := by
    calc
      ∑ i : Fin r, ∑ j : Fin s, (F j * E i)ᴴ * (F j * E i) =
          ∑ i : Fin r, (E i)ᴴ * (∑ j : Fin s, (F j)ᴴ * F j) * E i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = 1 := by simp [hF, hE]
  have h2 :
      ∑ i : Fin r, ∑ j : Fin s, (E i * F j)ᴴ * (E i * F j) = 1 := by
    rw [Finset.sum_comm]
    calc
      ∑ j : Fin s, ∑ i : Fin r, (E i * F j)ᴴ * (E i * F j) =
          ∑ j : Fin s, (F j)ᴴ * (∑ i : Fin r, (E i)ᴴ * E i) * F j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = 1 := by simp [hE, hF]
  ext ⟨a₁, c₁⟩ ⟨a₂, c₂⟩
  simp only [krausSwitch, controlled_star, controlled_mul, Fintype.sum_prod_type,
    Matrix.sum_apply, controlled, Matrix.one_apply]
  cases c₁ <;> cases c₂
  · have h1' := congrFun (congrFun h1 a₁) a₂
    simpa [Matrix.sum_apply, Matrix.one_apply] using h1'
  · simp
  · simp
  · have h2' := congrFun (congrFun h2 a₁) a₂
    simpa [Matrix.sum_apply, Matrix.one_apply] using h2'

/-- Full switch channel on `A × Bool` for arbitrary complete Kraus families `E` and `F`. -/
def krausFullChannel {r s : ℕ} (E : Fin r → CMatrix A) (F : Fin s → CMatrix A)
    (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1) :
    Channel (A × Bool) (A × Bool) where
  map := MatrixMap.ofKraus (krausSwitch E F)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using krausSwitch_complete E F hE hF)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

/-- On any complete Kraus channels `(E, hE)` and `(F, hF)`, `twoCallTree`
implements `dephaseControl ∘ krausFullChannel E F hE hF`. -/
theorem twoCallTree_krausChannel_eq {r s : ℕ}
    (E : Fin r → CMatrix A) (F : Fin s → CMatrix A)
    (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1) :
    (twoCallTree (A := A)).channel
      (oracleChannel (M := Bool) E hE) (oracleChannel (M := Bool) F hF) =
    (dephaseControl (A := A)).comp (krausFullChannel E F hE hF) := by
  apply channel_eq_of_map_eq
  ext X ij kl
  have hid (Y : CMatrix (A × Bool)) : (Channel.idChannel (A × Bool)).map Y = Y := by
    simp [Channel.idChannel, MatrixMap.ofKraus]
  have hmap :
      ((twoCallTree (A := A)).channel
        (oracleChannel (M := Bool) E hE) (oracleChannel (M := Bool) F hF)).map X =
      ((dephaseControl (A := A)).comp (krausFullChannel E F hE hF)).map X := by
    unfold twoCallTree
    rw [tree_node_map_apply, Fintype.sum_bool]
    simp only [dephaseInstrument, ite_true, Bool.false_eq_true, ite_false,
      tree_query_map_apply, tree_stop_map_apply, hid, dephaseKraus]
    rw [oracleChannel_controlled_conj F hF 0 1, map_sum,
      oracleChannel_controlled_conj E hE 1 0, map_sum]
    simp_rw [Matrix.mul_zero, Matrix.mul_one,
      oracleChannel_controlled_conj E hE, oracleChannel_controlled_conj F hF,
      Matrix.mul_zero]
    change _ = ∑ b : Bool, dephaseKraus (A := A) b *
      (∑ p : Fin r × Fin s, krausSwitch E F p * X * (krausSwitch E F p)ᴴ) *
      (dephaseKraus (A := A) b)ᴴ
    rw [Fintype.sum_bool]
    simp only [dephaseKraus, ite_true, Bool.false_eq_true, ite_false,
      Matrix.mul_sum, Matrix.sum_mul, Fintype.sum_prod_type,
      krausSwitch, conj_controlled_mul, Matrix.one_mul, Matrix.zero_mul]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  exact congrFun (congrFun hmap ij) kl

/-- **Section 4.4 (Two-call upper bound for general Kraus channels)**:
For any complete Kraus families `(E, hE)` and `(F, hF)` on `A`, `twoCallTree`
approximates `krausFullChannel E F hE hF` within diamond trace distance `1/2`. -/
theorem twoCallTree_krausChannel_error_le_half {r s : ℕ}
    (E : Fin r → CMatrix A) (F : Fin s → CMatrix A)
    (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1) :
    Channel.diamondTraceDistance
      ((twoCallTree (A := A)).channel
        (oracleChannel (M := Bool) E hE) (oracleChannel (M := Bool) F hF))
      (krausFullChannel E F hE hF) ≤ 1 / 2 := by
  rw [twoCallTree_krausChannel_eq E F hE hF]
  exact dephaseControl_comp_diamond_le_half (krausFullChannel E F hE hF)

/-- On any unitary-mixture sample `UV : Sample A r`, `fullCircuit twoCallTree UV`
equals `dephaseControl ∘ fullSwitch UV`. -/
theorem twoCallTree_fullCircuit_eq {r : ℕ} (UV : Sample A r) :
    fullCircuit (M := Bool) (twoCallTree (A := A)) UV =
      (dephaseControl (A := A)).comp (fullSwitch UV) := by
  let E : Fin (r + 1) → CMatrix A := fun i =>
    (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) • (UV.1 i : CMatrix A)
  let F : Fin (r + 1) → CMatrix A := fun j =>
    (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) • (UV.2 j : CMatrix A)
  have hsq : (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) = ((r + 1 : ℕ) : ℂ)⁻¹ := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (r + 1 : ℝ) by positivity)
    have he : (Real.sqrt (r + 1 : ℝ))⁻¹ * (Real.sqrt (r + 1 : ℝ))⁻¹ = ((r + 1 : ℕ) : ℝ)⁻¹ := by
      rw [Nat.cast_add, Nat.cast_one, ← mul_inv, ← pow_two, hs]
    have h1 := congrArg Complex.ofReal he
    simpa [Complex.ofReal_mul, Complex.ofReal_inv] using h1
  have hE : ∑ i : Fin (r + 1), (E i)ᴴ * E i = 1 := by
    have hentry (i : Fin (r + 1)) : (E i)ᴴ * E i = ((r + 1 : ℕ) : ℂ)⁻¹ • (1 : CMatrix A) := by
      simp only [E, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq]
      congr 1
      exact Matrix.UnitaryGroup.star_mul_self (UV.1 i)
    simp_rw [hentry, ← Finset.sum_smul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hr' : ((r + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    rw [mul_inv_cancel₀ hr', one_smul]
  have hF : ∑ j : Fin (r + 1), (F j)ᴴ * F j = 1 := by
    have hentry (j : Fin (r + 1)) : (F j)ᴴ * F j = ((r + 1 : ℕ) : ℂ)⁻¹ • (1 : CMatrix A) := by
      simp only [F, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq]
      congr 1
      exact Matrix.UnitaryGroup.star_mul_self (UV.2 j)
    simp_rw [hentry, ← Finset.sum_smul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hr' : ((r + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    rw [mul_inv_cancel₀ hr', one_smul]
  have horacle₁ :
      ICO.SamplingOrdinary.uniformChannel
        (fun a => ICO.AtMostFamilyCoherence.familyChannels (M := Bool) UV.1 UV.2 (.inl a)) =
      oracleChannel (M := Bool) E hE := by
    apply channel_eq_of_map_eq
    rw [ICO.SamplingOrdinary.uniformChannel_map]
    ext X x y
    simp only [ICO.AtMostFamilyCoherence.familyChannels, Sum.elim_inl,
      ICO.ClassicalDilation.oracleChannel_apply, oracleChannel, oracleMap,
      MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      LinearMap.sum_apply, Matrix.smul_apply, Matrix.sum_apply, Finset.smul_sum, E]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hk :
        Matrix.kronecker ((((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) • (UV.1 i : CMatrix A))
          (1 : CMatrix Bool) =
        (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) •
          Matrix.kronecker (UV.1 i : CMatrix A) (1 : CMatrix Bool) := by
      ext u v
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc]
    rw [hk, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hsq]
    rfl
  have horacle₂ :
      ICO.SamplingOrdinary.uniformChannel
        (fun b => ICO.AtMostFamilyCoherence.familyChannels (M := Bool) UV.1 UV.2 (.inr b)) =
      oracleChannel (M := Bool) F hF := by
    apply channel_eq_of_map_eq
    rw [ICO.SamplingOrdinary.uniformChannel_map]
    ext X x y
    simp only [ICO.AtMostFamilyCoherence.familyChannels, Sum.elim_inr,
      ICO.ClassicalDilation.oracleChannel_apply, oracleChannel, oracleMap,
      MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      LinearMap.sum_apply, Matrix.smul_apply, Matrix.sum_apply, Finset.smul_sum, F]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hk :
        Matrix.kronecker ((((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) • (UV.2 j : CMatrix A))
          (1 : CMatrix Bool) =
        (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) •
          Matrix.kronecker (UV.2 j : CMatrix A) (1 : CMatrix Bool) := by
      ext u v
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc]
    rw [hk, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hsq]
    rfl
  have hswitch : krausFullChannel E F hE hF = fullSwitch UV := by
    apply channel_eq_of_map_eq
    ext X x y
    simp only [krausFullChannel, fullSwitch, fullChannel, MatrixMap.ofKraus,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun ij _ => ?_
    have hk : krausSwitch E F ij = fullKraus UV.1 UV.2 ij := by
      ext ⟨a₁, c₁⟩ ⟨a₂, c₂⟩
      have hcoef :
          (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) =
            uniformCoefficient (r + 1) (r + 1) := by
        rw [hsq, uniformCoefficient]
        have hs := Real.sqrt_mul_self (show (0 : ℝ) ≤ (r + 1 : ℝ) by positivity)
        simp only [Nat.cast_add, Nat.cast_one, hs, Complex.ofReal_inv,
          Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
      have hcoef' :
          ((Real.sqrt ((r : ℝ) + 1) : ℂ))⁻¹ * ((Real.sqrt ((r : ℝ) + 1) : ℂ))⁻¹ =
            uniformCoefficient (r + 1) (r + 1) := by
        simpa using hcoef
      cases c₁ <;> cases c₂ <;>
        simp [krausSwitch, fullKraus, pair, controlled, E, F, ← mul_assoc, hcoef']
    rw [hk]
  unfold fullCircuit ICO.SamplingOrdinary.ordinaryChannel
  rw [horacle₁, horacle₂, ← hswitch]
  exact twoCallTree_krausChannel_eq E F hE hF

/-- **Section 4.4 (Two-call upper bound for `fullSwitch` vs `fullCircuit`)**:
For every `r : ℕ` and every unitary-mixture sample `UV : Sample A r`, the
two-call strategy `twoCallTree` achieves `(fullSwitch UV).diamondTraceDistance
(fullCircuit twoCallTree UV) ≤ 1/2`. -/
theorem twoCallTree_fullSwitch_error_le_half {r : ℕ} (UV : Sample A r) :
    (fullSwitch UV).diamondTraceDistance
      (fullCircuit (M := Bool) (twoCallTree (A := A)) UV) ≤ 1 / 2 := by
  rw [twoCallTree_fullCircuit_eq UV]
  exact diamond_dephaseControl_comp_le_half (fullSwitch UV)

#print axioms dephaseControl_diamond_id_le_half
#print axioms twoCallTree_krausChannel_eq
#print axioms twoCallTree_krausChannel_error_le_half
#print axioms twoCallTree_fullCircuit_eq
#print axioms twoCallTree_fullSwitch_error_le_half

end

end ICO.Section44TwoCall

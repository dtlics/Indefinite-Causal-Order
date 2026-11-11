import ICO.C6OperationalDecision
import ICO.C6OTOCChannelBoundary
import ICO.AllChannelDilation
import ICO.OrderedCircuit
import ICO.DiamondPreprocessing
import QIT.States.Purification.Canonical

/-!
# Theorem 3 (`\label{thm:c6}`): Validating dephasing vs. depolarizing noise (`\label{sec:switch-test}`, `\label{sec:validation}`)

This module formalizes the weak-noise decision separation of Theorem 3
("One bit: dephasing or depolarizing", `\label{thm:c6}`), the seven-use block switch test
of Section 5.1 (`\label{sec:switch-test}`), the weak-to-strong noise reduction of
Section 5.3 (`\label{sec:validation}`), the trivial `1 / (3p)` query bound of
Remark `rem:crossover`, and audited supplementary switch-contractivity results:
- **Audited supplementary switch-contractivity and model-mismatch bounds**
  (retained outside the current manuscript): slotwise one-call Stinespring/Kraus
  dilations and unconditional diamond-norm contractivity of the quantum switch
  (`ancillaTraceDistanceBound_diamond`, `switch_slot_left_diamond_le`,
  `switch_slot_left_diamond_le_diamond`, `switch_slot_right_diamond_le`,
  `switch_slot_right_diamond_le_diamond`), together with the resulting visibility
  continuity bounds (`model_mismatch_bound`, `model_mismatch_diamond_bound`).
- **Identities `eq:validation-visibility`** (`\label{sec:switch-test}`,
  `dephasing_noise_self_visibility` and `depolarizing_model_self_visibility`): exact
  switch self-visibilities `v(\mathcal{E}_{p,U}) = 1` and
  `v(\mathcal{M}_p) = 1 - p^2 (d - 1) / (d + 1)`.
- **Theorem 3 (`\label{thm:c6}`), ordinary query lower bound (`\label{sec:validation}`)**
  (`validation_ordinary_query_lower_bound`, `validation_ordinary_balanced_query_lower_bound`,
  and `validation_ordinary_lower_bound`): exponential-in-qubit ordinary query lower bound
  `Q > d^{1/16} / (1400 p)`.
- **Theorem 3 (`\label{thm:c6}`), seven-use block switch upper bound (`\label{sec:switch-test}`)**
  (`channelPow`, `dephasingNoiseChannel_pow`, `depolarizingModelChannel_pow`,
  `validation_switch_block_power_upper_bound`, and `validation_switch_upper_bound`):
  exact `m`-fold channel-power identities `\mathcal{E}_{p,U}^m = \mathcal{E}_{1-(1-p)^m, U}`
  and `\mathcal{M}_p^m = α^m id + (1 - α^m) Ω` and the `14 m`-call (`m ≥ 3 / (2p)`)
  quantum-switch validation test.
- **Remark `rem:crossover`, trivial `1 / (3p)` query lower bound**
  (`dephasing_depolarizing_diamond_le_p`, `dephasing_depolarizing_withMemory_diamond_le_p`,
  `validation_trivial_query_lower_bound`, `validation_trivial_balanced_query_lower_bound`,
  and `validation_trivial_single_unitary_query_lower_bound`): diamond trace distance at most
  `p` and universal `1 / (3p) ≤ Q` lower bound.
-/

namespace ICO.Section54Validation

open Matrix QIT MeasureTheory
open ICO.SwitchObservable ICO.SwitchExperiment ICO.SwitchSampling
open ICO.C6SwitchTest ICO.C6OperationalDecision ICO.C6UniformBounds
open ICO.ClassicalDilation ICO.AllChannelDilation ICO.QuantumDecision
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 1600000
set_option Elab.async false

variable {A : Type} [Fintype A] [DecidableEq A]

/-! ## 1. Kraus channels and slotwise diamond-norm contractivity (audited supplementary results) -/

/-- CPTP channel associated to a complete Kraus family `K : ι → Matrix B A ℂ`. -/
def krausChannel {B ι : Type} [Fintype B] [DecidableEq B] [Fintype ι]
    (K : ι → Matrix B A ℂ) (hK : (∑ i, (K i).conjTranspose * K i) = 1) :
    Channel A B where
  map := MatrixMap.ofKraus K
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using hK)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

/-- Paired Kraus family `(i, j) ↦ switchKraus (E i) (F j)` for the quantum switch. -/
def switchKrausFamily {ι κ : Type} (E : ι → CMatrix A) (F : κ → CMatrix A) (p : ι × κ) :
    CMatrix (A ⊕ A) :=
  switchKraus (E p.1) (F p.2)

theorem switchKrausFamily_complete {ι κ : Type} [Fintype ι] [Fintype κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    (∑ p : ι × κ, (switchKrausFamily E F p).conjTranspose * switchKrausFamily E F p) = 1 := by
  simpa [switchKrausFamily, Fintype.sum_prod_type] using switch_kraus_complete E F hE hF

/-- The quantum switch on `A ⊕ A` as a CPTP `Channel (A ⊕ A) (A ⊕ A)` for complete
Kraus families `E : ι → CMatrix A` and `F : κ → CMatrix A`. -/
def switchChannel {ι κ : Type} [Fintype ι] [Fintype κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    Channel (A ⊕ A) (A ⊕ A) :=
  krausChannel (switchKrausFamily E F) (switchKrausFamily_complete E F hE hF)

theorem switchedState_eq_applyState {ι κ : Type} [Fintype ι] [Fintype κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1) (ρ : State A) :
    switchedState E F hE hF ρ =
      (switchChannel E F hE hF).applyState (plusState ρ) := by
  apply State.ext
  change switchOutput E F ρ.matrix =
    MatrixMap.ofKraus (switchKrausFamily E F) (plusTarget ρ.matrix)
  simp [switchOutput, MatrixMap.ofKraus, switchKrausFamily, Fintype.sum_prod_type]

/-- Pre-processing matrix `W_pre : (A ⊕ A) → A × (Unit ⊕ κ)` in the one-call
dilation of `S(E, F)` with respect to the first slot `E` (fixing `F`):
maps `|0⟩_C |ψ⟩_A ↦ |ψ⟩_A ⊗ |0⟩_{M_0}` and `|1⟩_C |ψ⟩_A ↦ ∑_j (F_j |ψ⟩_A) ⊗ |j⟩_{M_1}`. -/
def slotLeftPre {κ : Type} (F : κ → CMatrix A) :
    Matrix (A × (Unit ⊕ κ)) (A ⊕ A) ℂ
  | (a', Sum.inl ()), Sum.inl a => if a' = a then 1 else 0
  | (a', Sum.inr j), Sum.inr a => F j a' a
  | _, _ => 0

theorem slotLeftPre_isometry {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : κ → CMatrix A) (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    (slotLeftPre F).conjTranspose * slotLeftPre F = 1 := by
  ext x y
  cases x with
  | inl a₁ =>
    cases y with
    | inl a₂ =>
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Fintype.sum_sum_type, Fintype.sum_unique, slotLeftPre,
        Matrix.one_apply, Sum.inl.injEq]
      simp [eq_comm]
    | inr a₂ =>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Fintype.sum_sum_type, slotLeftPre]
  | inr a₁ =>
    cases y with
    | inl a₂ =>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Fintype.sum_sum_type, slotLeftPre]
    | inr a₂ =>
      have hF_entry := congrFun (congrFun hF a₁) a₂
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply] at hF_entry
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Fintype.sum_sum_type, slotLeftPre,
        Matrix.one_apply, Sum.inr.injEq, star_zero, zero_mul, Finset.sum_const_zero, zero_add]
      rw [Finset.sum_comm]
      exact hF_entry

/-- Isometric pre-processing channel `W_pre` for the first slot of the switch. -/
def slotLeftPreChannel {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : κ → CMatrix A) (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    Channel (A ⊕ A) (A × (Unit ⊕ κ)) :=
  isometryChannel (slotLeftPre F) (slotLeftPre_isometry F hF)

/-- Post-processing Kraus operators `K_j : A × (Unit ⊕ κ) → (A ⊕ A)` in the one-call
dilation of `S(E, F)` with respect to the first slot `E`:
maps `|φ⟩_A ⊗ |0⟩_{M_0} ↦ |0⟩_C ⊗ F_j |φ⟩_A` and `|φ⟩_A ⊗ |j'⟩_{M_1} ↦ δ_{j,j'} |1⟩_C ⊗ |φ⟩_A`. -/
def slotLeftPostKraus {κ : Type} [DecidableEq κ] (F : κ → CMatrix A) (j : κ) :
    Matrix (A ⊕ A) (A × (Unit ⊕ κ)) ℂ
  | Sum.inl a'', (a', Sum.inl ()) => F j a'' a'
  | Sum.inr a'', (a', Sum.inr j') => if j = j' ∧ a'' = a' then 1 else 0
  | _, _ => 0

theorem slotLeftPostKraus_complete {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : κ → CMatrix A) (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    (∑ j, (slotLeftPostKraus F j).conjTranspose * slotLeftPostKraus F j) = 1 := by
  ext ⟨a₁, m₁⟩ ⟨a₂, m₂⟩
  cases m₁ with
  | inl u₁ =>
    cases u₁
    cases m₂ with
    | inl u₂ =>
      cases u₂
      have hF_entry := congrFun (congrFun hF a₁) a₂
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply] at hF_entry
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_sum_type, slotLeftPostKraus, star_zero, zero_mul, Finset.sum_const_zero,
        add_zero, Matrix.one_apply, Prod.mk.injEq, and_true]
      exact hF_entry
    | inr j₂ =>
      simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_sum_type, slotLeftPostKraus]
  | inr j₁ =>
    cases m₂ with
    | inl u₂ =>
      cases u₂
      simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_sum_type, slotLeftPostKraus]
    | inr j₂ =>
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_sum_type, slotLeftPostKraus, star_zero, zero_mul, Finset.sum_const_zero,
        zero_add, Matrix.one_apply, Prod.mk.injEq, Sum.inr.injEq]
      rw [Finset.sum_eq_single j₁]
      · rw [Finset.sum_eq_single a₁]
        · by_cases hj : j₁ = j₂ <;> by_cases ha : a₁ = a₂ <;> simp [hj, ha]
        · intro a' _ ha'
          have hne : a' ≠ a₁ := ha'
          simp [hne]
        · simp
      · intro j' _ hj'
        apply Finset.sum_eq_zero
        intro a' _
        have hne : j' ≠ j₁ := hj'
        simp [hne]
      · simp

/-- Post-processing CPTP channel `Φ_post` for the first slot of the switch. -/
def slotLeftPostChannel {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : κ → CMatrix A) (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    Channel (A × (Unit ⊕ κ)) (A ⊕ A) :=
  krausChannel (slotLeftPostKraus F) (slotLeftPostKraus_complete F hF)

omit [DecidableEq A] in
theorem kronecker_identity_mul_entry {M colT : Type} [Fintype M] [DecidableEq M]
    (U : CMatrix A) (Y : Matrix (A × M) colT ℂ) (a₁ : A) (m₁ : M) (c : colT) :
    (Matrix.kronecker U (1 : CMatrix M) * Y) (a₁, m₁) c =
      ∑ a₂ : A, U a₁ a₂ * Y (a₂, m₁) c := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  rw [Finset.sum_eq_single m₁]
  · simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  · intro m₂ _ hm₂
    have hne : m₁ ≠ m₂ := hm₂.symm
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hne]
  · simp

theorem kronecker_one_mul_slotLeftPre {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A) (i : ι) :
    Matrix.kronecker (E i) (1 : CMatrix (Unit ⊕ κ)) * slotLeftPre F =
      fun am y =>
        match am.2, y with
        | Sum.inl (), Sum.inl a => E i am.1 a
        | Sum.inr j, Sum.inr a => (E i * F j) am.1 a
        | _, _ => 0 := by
  ext ⟨a₁, m⟩ y
  rw [kronecker_identity_mul_entry]
  cases m with
  | inl u =>
    cases u
    cases y with
    | inl a => simp [slotLeftPre]
    | inr a => simp [slotLeftPre]
  | inr j =>
    cases y with
    | inl a => simp [slotLeftPre]
    | inr a => simp [slotLeftPre, Matrix.mul_apply]

/-- Key Kraus factorization `K_j (E_i ⊗ I_M) W_pre = S_{i,j}` for the slotwise
one-call dilation of the quantum switch. -/
theorem slotLeft_kraus_factorization {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A) (i : ι) (j : κ) :
    slotLeftPostKraus F j *
      (Matrix.kronecker (E i) (1 : CMatrix (Unit ⊕ κ)) * slotLeftPre F) =
      switchKraus (E i) (F j) := by
  rw [kronecker_one_mul_slotLeftPre]
  ext x y
  cases x with
  | inl a₂ =>
    cases y with
    | inl a₁ =>
      simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
        Fintype.sum_unique, slotLeftPostKraus, mul_zero,
        Finset.sum_const_zero, add_zero, switchKraus, Matrix.fromBlocks_apply₁₁]
    | inr a₁ =>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
        slotLeftPostKraus, switchKraus]
  | inr a₂ =>
    cases y with
    | inl a₁ =>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
        slotLeftPostKraus, switchKraus]
    | inr a₁ =>
      simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
        slotLeftPostKraus, zero_mul,
        Finset.sum_const_zero, zero_add, switchKraus, Matrix.fromBlocks_apply₂₂]
      rw [Finset.sum_eq_single a₂]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj'
          have hne : j ≠ j' := hj'.symm
          simp [hne]
        · simp
      · intro a' _ ha'
        apply Finset.sum_eq_zero
        intro j' _
        have hne : a₂ ≠ a' := ha'.symm
        simp [hne]
      · simp

/-- `((krausChannel E hE).prod (Channel.idChannel M)).map` coincides with
`ICO.AllChannelDilation.oracleMap (M := M) E`. -/
theorem prod_id_map_eq_oracleMap {M ι : Type} [Fintype M] [DecidableEq M] [Fintype ι]
    (E : ι → CMatrix A) (hE : (∑ i, (E i).conjTranspose * E i) = 1) (X : CMatrix (A × M)) :
    ((krausChannel E hE).prod (Channel.idChannel M)).map X =
      ICO.AllChannelDilation.oracleMap (M := M) E X := by
  ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
  symm
  change (ICO.AllChannelDilation.oracleMap (M := M) E X) (b₁, m₁) (b₂, m₂) =
    MatrixMap.kron (MatrixMap.ofKraus E) (Channel.idChannel M).map X (b₁, m₁) (b₂, m₂)
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp only [ICO.AllChannelDilation.oracleMap, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL (am : A × M) :
      (Matrix.kronecker (E i) (1 : CMatrix M) * X) (b₁, m₁) am =
        ∑ a : A, E i b₁ a * X (a, m₁) am :=
    kronecker_identity_mul_entry (E i) X b₁ m₁ am
  rw [Matrix.mul_apply]
  simp_rw [hL]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single m₂]
  · simp [Matrix.mul_apply, Finset.sum_mul, mul_assoc]
  · intro m' _ hm'
    have hne : m₂ ≠ m' := hm'.symm
    simp [hne]
  · simp

/-- Exact factorization of `MatrixMap.ofKraus (switchKrausFamily E F)` through one call
to `E ⊗ id_{Unit ⊕ κ}`. -/
theorem switchKrausMap_eq_slotLeft {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A) (X : CMatrix (A ⊕ A)) :
    MatrixMap.ofKraus (switchKrausFamily E F) X =
      MatrixMap.ofKraus (slotLeftPostKraus F)
        (ICO.AllChannelDilation.oracleMap (M := Unit ⊕ κ) E
          (slotLeftPre F * X * (slotLeftPre F).conjTranspose)) := by
  ext x y
  simp only [switchKrausFamily, ICO.AllChannelDilation.oracleMap, MatrixMap.ofKraus,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfac := slotLeft_kraus_factorization E F i j
  have hassoc :
      slotLeftPostKraus F j *
          (Matrix.kronecker (E i) (1 : CMatrix (Unit ⊕ κ)) *
            (slotLeftPre F * X * (slotLeftPre F).conjTranspose) *
            (Matrix.kronecker (E i) (1 : CMatrix (Unit ⊕ κ))).conjTranspose) *
          (slotLeftPostKraus F j).conjTranspose =
        (slotLeftPostKraus F j *
          (Matrix.kronecker (E i) (1 : CMatrix (Unit ⊕ κ)) * slotLeftPre F)) * X *
          (slotLeftPostKraus F j *
            (Matrix.kronecker (E i) (1 : CMatrix (Unit ⊕ κ)) * slotLeftPre F)).conjTranspose := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hassoc, hfac]

/-- Channel-level factorization `S(E, F) = Φ_post,F ∘ (E ⊗ id_{Unit ⊕ κ}) ∘ W_pre,F`. -/
theorem switchChannel_eq_slotLeft_comp {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    switchChannel E F hE hF =
      (slotLeftPostChannel F hF).comp
        (((krausChannel E hE).prod (Channel.idChannel (Unit ⊕ κ))).comp
          (slotLeftPreChannel F hF)) := by
  cases hL : switchChannel E F hE hF
  cases hR : (slotLeftPostChannel F hF).comp
    (((krausChannel E hE).prod (Channel.idChannel (Unit ⊕ κ))).comp (slotLeftPreChannel F hF))
  suffices hmap :
      (switchChannel E F hE hF).map =
        ((slotLeftPostChannel F hF).comp
          (((krausChannel E hE).prod (Channel.idChannel (Unit ⊕ κ))).comp
            (slotLeftPreChannel F hF))).map by
    rw [hL, hR] at hmap
    congr
  ext X x y
  change MatrixMap.ofKraus (switchKrausFamily E F) X x y =
    MatrixMap.ofKraus (slotLeftPostKraus F)
      (((krausChannel E hE).prod (Channel.idChannel (Unit ⊕ κ))).map
        ((slotLeftPreChannel F hF).map X)) x y
  rw [prod_id_map_eq_oracleMap E hE, slotLeftPreChannel, isometryChannel_apply,
    switchKrausMap_eq_slotLeft]

/-- Unitary matrix `X_C` on `A ⊕ A` swapping the two control branches. -/
def swapControlMatrix : CMatrix (A ⊕ A) :=
  (ReferenceIsometry.ofEquiv (Equiv.sumComm A A)).matrix

/-- Isometric channel `X_C` on `A ⊕ A` swapping the two control branches. -/
def swapControlChannel : Channel (A ⊕ A) (A ⊕ A) :=
  isometryChannel swapControlMatrix
    (ReferenceIsometry.ofEquiv (Equiv.sumComm A A)).isometry

/-- Swapping the control qubit conjugates `switchKraus (F j) (E i)` into `switchKraus (E i) (F j)`. -/
theorem switchKraus_sumComm {ι κ : Type} (E : ι → CMatrix A) (F : κ → CMatrix A)
    (i : ι) (j : κ) :
    swapControlMatrix *
      switchKraus (F j) (E i) *
      (swapControlMatrix : CMatrix (A ⊕ A)).conjTranspose =
      switchKraus (E i) (F j) := by
  ext x y
  simp only [swapControlMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ReferenceIsometry.ofEquiv, Fintype.sum_sum_type, Equiv.sumComm_apply, Sum.swap]
  cases x with
  | inl a₁ =>
    cases y with
    | inl a₂ =>
      simp [switchKraus, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
    | inr a₂ =>
      simp [switchKraus]
  | inr a₁ =>
    cases y with
    | inl a₂ =>
      simp [switchKraus]
    | inr a₂ =>
      simp [switchKraus, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

/-- Swapping the control qubit relates the second slot of the switch to the first slot:
`S(F, E) = X_C ∘ S(E, F) ∘ X_C` where `X_C = swapControlChannel`. -/
theorem switchChannel_eq_sumComm_conj {ι κ : Type} [Fintype ι] [Fintype κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    switchChannel F E hF hE =
      swapControlChannel.comp ((switchChannel E F hE hF).comp swapControlChannel) := by
  let V : CMatrix (A ⊕ A) := swapControlMatrix
  cases hL : switchChannel F E hF hE
  cases hR : swapControlChannel.comp ((switchChannel E F hE hF).comp swapControlChannel)
  suffices hmap :
      (switchChannel F E hF hE).map =
        (swapControlChannel.comp ((switchChannel E F hE hF).comp swapControlChannel)).map by
    rw [hL, hR] at hmap
    congr
  ext X x y
  change MatrixMap.ofKraus (switchKrausFamily F E) X x y =
    swapControlChannel.map
      (MatrixMap.ofKraus (switchKrausFamily E F) (swapControlChannel.map X)) x y
  rw [swapControlChannel, isometryChannel_apply, isometryChannel_apply]
  change MatrixMap.ofKraus (switchKrausFamily F E) X x y =
    (V * (MatrixMap.ofKraus (switchKrausFamily E F) (V * X * V.conjTranspose)) * V.conjTranspose) x y
  simp only [switchKrausFamily, MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hswap := switchKraus_sumComm E F i j
  have hV_symm : V.conjTranspose = V := by
    ext u v
    cases u <;> cases v <;> simp [V, swapControlMatrix, ReferenceIsometry.ofEquiv,
      Matrix.conjTranspose_apply, Equiv.sumComm_apply, Sum.swap, eq_comm]
  have hVV : V * V = 1 := by
    ext u v
    simp only [V, swapControlMatrix, Matrix.mul_apply, ReferenceIsometry.ofEquiv,
      Fintype.sum_sum_type, Equiv.sumComm_apply, Sum.swap, Matrix.one_apply]
    cases u <;> cases v <;> simp [eq_comm]
  have hFE : V * switchKraus (E i) (F j) * V = switchKraus (F j) (E i) := by
    have hswap' : V * switchKraus (F j) (E i) * V = switchKraus (E i) (F j) := by
      simpa [V, hV_symm] using hswap
    rw [← hswap']
    calc
      V * (V * switchKraus (F j) (E i) * V) * V =
          (V * V) * switchKraus (F j) (E i) * (V * V) := by
            simp only [Matrix.mul_assoc]
      _ = switchKraus (F j) (E i) := by rw [hVV, Matrix.one_mul, Matrix.mul_one]
  have hassoc :
      V * (switchKraus (E i) (F j) * (V * X * V.conjTranspose) *
          (switchKraus (E i) (F j)).conjTranspose) * V.conjTranspose =
        (V * switchKraus (E i) (F j) * V) * X *
          (V * switchKraus (E i) (F j) * V).conjTranspose := by
    rw [hV_symm]
    simp only [Matrix.conjTranspose_mul, hV_symm, Matrix.mul_assoc]
  rw [hassoc, hFE]

/-- Contractivity of the quantum switch in the first slot on any input state `σ : State (A ⊕ A)`. -/
theorem switch_slot_left_state_distance_le {ι ι' κ : Type}
    [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq κ]
    (E : ι → CMatrix A) (E' : ι' → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hE' : (∑ i, (E' i).conjTranspose * E' i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1)
    (σ : State (A ⊕ A)) {ε : ℝ}
    (hEM : Channel.AncillaTraceDistanceBound (a := A) (b := A) (r := Unit ⊕ κ)
      (krausChannel E hE) (krausChannel E' hE') ε) :
    ((switchChannel E F hE hF).applyState σ).normalizedTraceDistance
      ((switchChannel E' F hE' hF).applyState σ) ≤ ε := by
  rw [switchChannel_eq_slotLeft_comp E F hE hF,
      switchChannel_eq_slotLeft_comp E' F hE' hF,
      Channel.applyState_comp, Channel.applyState_comp,
      Channel.applyState_comp, Channel.applyState_comp]
  exact (Channel.normalizedTraceDistance_applyState_le (slotLeftPostChannel F hF) _ _).trans
    (hEM ((slotLeftPreChannel F hF).applyState σ))

/-- Contractivity of the quantum switch in the second slot on any input state `σ : State (A ⊕ A)`. -/
theorem switch_slot_right_state_distance_le {ι κ κ' : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype κ']
    (F : ι → CMatrix A) (E : κ → CMatrix A) (E' : κ' → CMatrix A)
    (hF : (∑ i, (F i).conjTranspose * F i) = 1)
    (hE : (∑ j, (E j).conjTranspose * E j) = 1)
    (hE' : (∑ j, (E' j).conjTranspose * E' j) = 1)
    (σ : State (A ⊕ A)) {ε : ℝ}
    (hEM : Channel.AncillaTraceDistanceBound (a := A) (b := A) (r := Unit ⊕ ι)
      (krausChannel E hE) (krausChannel E' hE') ε) :
    ((switchChannel F E hF hE).applyState σ).normalizedTraceDistance
      ((switchChannel F E' hF hE').applyState σ) ≤ ε := by
  rw [switchChannel_eq_sumComm_conj E F hE hF,
      switchChannel_eq_sumComm_conj E' F hE' hF,
      Channel.applyState_comp, Channel.applyState_comp,
      Channel.applyState_comp, Channel.applyState_comp]
  exact (Channel.normalizedTraceDistance_applyState_le swapControlChannel _ _).trans
    (switch_slot_left_state_distance_le E E' F hE hE' hF
      (swapControlChannel.applyState σ) hEM)

/-- Product-associativity equivalence `((A × M) × R) ≃ (A × (M × R))` commutes a left
product channel `(Φ ⊗ id_M) ⊗ id_R` into `Φ ⊗ id_{M × R}`. -/
theorem prod_id_prod_id_applyState_eq_reindex {M R : Type}
    [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]
    (Φ : Channel A A) (ω : State ((A × M) × R)) :
    (((Φ.prod (Channel.idChannel M)).prod (Channel.idChannel R)).applyState ω) =
      (Channel.reindex (Equiv.prodAssoc A M R).symm).applyState
        ((Φ.prod (Channel.idChannel (M × R))).applyState
          ((Channel.reindex (Equiv.prodAssoc A M R)).applyState ω)) := by
  apply State.ext
  ext ⟨⟨a₁, m₁⟩, r₁⟩ ⟨⟨a₂, m₂⟩, r₂⟩
  simp only [Channel.reindex_applyState]
  change MatrixMap.kron (MatrixMap.kron Φ.map (Channel.idChannel M).map)
      (Channel.idChannel R).map ω.matrix ((a₁, m₁), r₁) ((a₂, m₂), r₂) =
    MatrixMap.kron Φ.map (Channel.idChannel (M × R)).map
      (ω.reindex (Equiv.prodAssoc A M R)).matrix (a₁, (m₁, r₁)) (a₂, (m₂, r₂))
  rw [MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_apply_slice,
      MatrixMap.kron_idChannel_apply_slice]
  rfl

/-- Diamond-norm contractivity of the quantum switch in the first slot:
`D_◇(S(E, F), S(E', F)) ≤ ε` whenever `E` and `E'` are `ε`-close on ancilla `(Unit ⊕ κ) × (A ⊕ A)`. -/
theorem switch_slot_left_diamond_le [Nonempty A] {ι ι' κ : Type}
    [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq κ]
    (E : ι → CMatrix A) (E' : ι' → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hE' : (∑ i, (E' i).conjTranspose * E' i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1) {ε : ℝ}
    (hEM : Channel.AncillaTraceDistanceBound (a := A) (b := A)
      (r := (Unit ⊕ κ) × (A ⊕ A)) (krausChannel E hE) (krausChannel E' hE') ε) :
    (switchChannel E F hE hF).diamondTraceDistance (switchChannel E' F hE' hF) ≤ ε := by
  haveI : Nonempty (A ⊕ A) := ⟨Sum.inl (Classical.arbitrary A)⟩
  apply Channel.diamondTraceDistance_le_of_inputReferenceBound
  intro ω
  have hcomp (Φ : Channel (A × (Unit ⊕ κ)) (A × (Unit ⊕ κ))) :
      (((slotLeftPostChannel F hF).comp (Φ.comp (slotLeftPreChannel F hF))).prod
        (Channel.idChannel (A ⊕ A))).applyState ω =
      ((slotLeftPostChannel F hF).prod (Channel.idChannel (A ⊕ A))).applyState
        ((Φ.prod (Channel.idChannel (A ⊕ A))).applyState
          (((slotLeftPreChannel F hF).prod (Channel.idChannel (A ⊕ A))).applyState ω)) := by
    apply State.ext
    change MatrixMap.kron ((slotLeftPostChannel F hF).map.comp
        (Φ.map.comp (slotLeftPreChannel F hF).map))
        (Channel.idChannel (A ⊕ A)).map ω.matrix =
      MatrixMap.kron (slotLeftPostChannel F hF).map (Channel.idChannel (A ⊕ A)).map
        (MatrixMap.kron Φ.map (Channel.idChannel (A ⊕ A)).map
          (MatrixMap.kron (slotLeftPreChannel F hF).map (Channel.idChannel (A ⊕ A)).map ω.matrix))
    rw [MatrixMap.kron_comp_apply_general, MatrixMap.kron_comp_apply_general]
    simp only [ICO.DiamondPreprocessing.identity_map, LinearMap.id_comp, LinearMap.comp_assoc]
  rw [switchChannel_eq_slotLeft_comp E F hE hF,
      switchChannel_eq_slotLeft_comp E' F hE' hF,
      hcomp, hcomp]
  refine (Channel.normalizedTraceDistance_applyState_le
    ((slotLeftPostChannel F hF).prod (Channel.idChannel (A ⊕ A))) _ _).trans ?_
  rw [prod_id_prod_id_applyState_eq_reindex (krausChannel E hE),
      prod_id_prod_id_applyState_eq_reindex (krausChannel E' hE')]
  refine (Channel.normalizedTraceDistance_applyState_le
    (Channel.reindex (Equiv.prodAssoc A (Unit ⊕ κ) (A ⊕ A)).symm) _ _).trans ?_
  exact hEM _

/-- Diamond-norm contractivity of the quantum switch in the second slot:
`D_◇(S(F, E), S(F, E')) ≤ ε` whenever `E` and `E'` are `ε`-close on ancilla `(Unit ⊕ ι) × (A ⊕ A)`. -/
theorem switch_slot_right_diamond_le [Nonempty A] {ι κ κ' : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype κ']
    (F : ι → CMatrix A) (E : κ → CMatrix A) (E' : κ' → CMatrix A)
    (hF : (∑ i, (F i).conjTranspose * F i) = 1)
    (hE : (∑ j, (E j).conjTranspose * E j) = 1)
    (hE' : (∑ j, (E' j).conjTranspose * E' j) = 1) {ε : ℝ}
    (hEM : Channel.AncillaTraceDistanceBound (a := A) (b := A)
      (r := (Unit ⊕ ι) × (A ⊕ A)) (krausChannel E hE) (krausChannel E' hE') ε) :
    (switchChannel F E hF hE).diamondTraceDistance (switchChannel F E' hF hE') ≤ ε := by
  haveI : Nonempty (A ⊕ A) := ⟨Sum.inl (Classical.arbitrary A)⟩
  apply Channel.diamondTraceDistance_le_of_inputReferenceBound
  intro ω
  let X_C := swapControlChannel (A := A)
  have hcomp (Ψ : Channel (A ⊕ A) (A ⊕ A)) :
      ((X_C.comp (Ψ.comp X_C)).prod (Channel.idChannel (A ⊕ A))).applyState ω =
      (X_C.prod (Channel.idChannel (A ⊕ A))).applyState
        ((Ψ.prod (Channel.idChannel (A ⊕ A))).applyState
          ((X_C.prod (Channel.idChannel (A ⊕ A))).applyState ω)) := by
    apply State.ext
    change MatrixMap.kron (X_C.map.comp (Ψ.map.comp X_C.map))
        (Channel.idChannel (A ⊕ A)).map ω.matrix =
      MatrixMap.kron X_C.map (Channel.idChannel (A ⊕ A)).map
        (MatrixMap.kron Ψ.map (Channel.idChannel (A ⊕ A)).map
          (MatrixMap.kron X_C.map (Channel.idChannel (A ⊕ A)).map ω.matrix))
    rw [MatrixMap.kron_comp_apply_general, MatrixMap.kron_comp_apply_general]
    simp only [ICO.DiamondPreprocessing.identity_map, LinearMap.id_comp, LinearMap.comp_assoc]
  rw [switchChannel_eq_sumComm_conj E F hE hF,
      switchChannel_eq_sumComm_conj E' F hE' hF,
      hcomp, hcomp]
  refine (Channel.normalizedTraceDistance_applyState_le
    (X_C.prod (Channel.idChannel (A ⊕ A))) _ _).trans ?_
  exact (ICO.DiamondPreprocessing.input_distance_le_diamond
    (switchChannel E F hE hF) (switchChannel E' F hE' hF) _).trans
    (switch_slot_left_diamond_le E E' F hE hE' hF hEM)

/-- Triangle inequality for `State.normalizedTraceDistance`. -/
theorem normalizedTraceDistance_triangle {H : Type} [Fintype H] [DecidableEq H]
    (ρ σ τ : State H) :
    ρ.normalizedTraceDistance τ ≤
      ρ.normalizedTraceDistance σ + σ.normalizedTraceDistance τ := by
  change (1 / 2 : ℝ) * traceNorm (ρ.matrix - τ.matrix) ≤
    (1 / 2 : ℝ) * traceNorm (ρ.matrix - σ.matrix) +
      (1 / 2 : ℝ) * traceNorm (σ.matrix - τ.matrix)
  have hsub : ρ.matrix - τ.matrix = (ρ.matrix - σ.matrix) + (σ.matrix - τ.matrix) := by abel
  have htri := traceNorm_add_le (ρ.matrix - σ.matrix) (σ.matrix - τ.matrix)
  rw [← hsub] at htri
  linarith

/-- Two-sided Born probability gap bound for `controlMeasurement`. -/
theorem control_plus_gap_le_traceDistance (ρ σ : State (A ⊕ A)) :
    |(controlMeasurement.prob ρ true : ℝ) - (controlMeasurement.prob σ true : ℝ)| ≤
      ρ.normalizedTraceDistance σ := by
  have h1 := accept_gap_le_traceDistance controlMeasurement ρ σ
  have h2 := accept_gap_le_traceDistance controlMeasurement σ ρ
  rw [State.normalizedTraceDistance_comm] at h2
  change (controlMeasurement.prob ρ true : ℝ) - (controlMeasurement.prob σ true : ℝ) ≤
    ρ.normalizedTraceDistance σ at h1
  change (controlMeasurement.prob σ true : ℝ) - (controlMeasurement.prob ρ true : ℝ) ≤
    ρ.normalizedTraceDistance σ at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- **Model mismatch bound (audited supplementary result outside the current manuscript)**:
For any channels `E : ι → CMatrix A` and `M : κ → CMatrix A` with single-call diamond
distance bound `ε` on the switch dilation memories,
`(1 / 2) |p_+(E) - p_+(M)| = (1 / 4) |v(E) - v(M)| ≤ ε`. -/
theorem model_mismatch_bound [Nonempty A] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (E : ι → CMatrix A) (M : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hM : (∑ j, (M j).conjTranspose * M j) = 1) {ε : ℝ}
    (hEM_left : Channel.AncillaTraceDistanceBound (a := A) (b := A) (r := Unit ⊕ κ)
      (krausChannel E hE) (krausChannel M hM) ε)
    (hEM_right : Channel.AncillaTraceDistanceBound (a := A) (b := A) (r := Unit ⊕ ι)
      (krausChannel E hE) (krausChannel M hM) ε) :
    (1 / 2 : ℝ) *
      |(controlMeasurement.prob (switchedState E E hE hE mixedState) true : ℝ) -
       (controlMeasurement.prob (switchedState M M hM hM mixedState) true : ℝ)| =
      (1 / 4 : ℝ) * |interference E E - interference M M| ∧
    (1 / 4 : ℝ) * |interference E E - interference M M| ≤ ε := by
  have hpE := switch_plus_probability E E hE hE
  have hpM := switch_plus_probability M M hM hM
  have heq :
      (1 / 2 : ℝ) *
        |(controlMeasurement.prob (switchedState E E hE hE mixedState) true : ℝ) -
         (controlMeasurement.prob (switchedState M M hM hM mixedState) true : ℝ)| =
      (1 / 4 : ℝ) * |interference E E - interference M M| := by
    rw [hpE, hpM]
    have hsub :
        (1 + interference E E) / 2 - (1 + interference M M) / 2 =
          (1 / 2 : ℝ) * (interference E E - interference M M) := by ring
    rw [hsub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have hgap := control_plus_gap_le_traceDistance
    (switchedState E E hE hE mixedState) (switchedState M M hM hM mixedState)
  have htri := normalizedTraceDistance_triangle
    (switchedState E E hE hE mixedState)
    (switchedState E M hE hM mixedState)
    (switchedState M M hM hM mixedState)
  have hright :
      (switchedState E E hE hE mixedState).normalizedTraceDistance
        (switchedState E M hE hM mixedState) ≤ ε := by
    rw [switchedState_eq_applyState, switchedState_eq_applyState]
    exact switch_slot_right_state_distance_le E E M hE hE hM _ hEM_right
  have hleft :
      (switchedState E M hE hM mixedState).normalizedTraceDistance
        (switchedState M M hM hM mixedState) ≤ ε := by
    rw [switchedState_eq_applyState, switchedState_eq_applyState]
    exact switch_slot_left_state_distance_le E M M hE hM hM _ hEM_left
  refine ⟨heq, ?_⟩
  linarith

/-- Any finite-ancilla trace distance `(Φ ⊗ id_R)(ω)` vs `(Ψ ⊗ id_R)(ω)` is bounded
by `Φ.diamondTraceDistance Ψ` (attained on reference copy `A` via canonical purification
and purification equivalence). -/
theorem ancillaTraceDistanceBound_diamond [Nonempty A] {B R : Type}
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (Φ Ψ : Channel A B) :
    Channel.AncillaTraceDistanceBound (a := A) (b := B) (r := R) Φ Ψ
      (Φ.diamondTraceDistance Ψ) := by
  intro ω
  haveI : Nonempty R := ⟨(Classical.choice ω.nonempty).2⟩
  let ρ : State A := ω.marginalA
  let ψ₁ : PureVector (A × A) := ρ.canonicalPurification
  have hψ₁ : ψ₁.Purifies ρ := State.canonicalPurification_purifies ρ
  let φ₀ : State (A × A) := (ψ₁.reindex (Equiv.prodComm A A)).state
  let ψω : PureVector ((A × R) × (A × R)) := ω.canonicalPurification
  have hψω : partialTraceA (a := A × R) (b := A × R) ψω.state.matrix = ω.matrix :=
    State.canonicalPurification_purifies ω
  let e : ((A × R) × (A × R)) ≃ (((A × R) × R) × A) :=
    { toFun := fun x => ((x.1, x.2.2), x.2.1)
      invFun := fun y => (y.1.1, (y.2, y.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let ψ₂ : PureVector (((A × R) × R) × A) := ψω.reindex e
  have hψ₂ : ψ₂.Purifies ρ := by
    rw [PureVector.purifies_iff]
    ext a₁ a₂
    change (∑ pr : (A × R) × R, ψ₂.state.matrix (pr, a₁) (pr, a₂)) =
      (partialTraceB (a := A) (b := R) ω.matrix) a₁ a₂
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [partialTraceB]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hentry := congrFun (congrFun hψω (a₁, r)) (a₂, r)
    simpa [partialTraceA, ψ₂, e] using hentry
  have hcard : Fintype.card A ≤ Fintype.card ((A × R) × R) := by
    have hR_pos : 1 ≤ Fintype.card R := Fintype.card_pos
    have hRR_pos : 1 ≤ Fintype.card R * Fintype.card R := Nat.mul_pos hR_pos hR_pos
    simp only [Fintype.card_prod, Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right (Fintype.card A) hRR_pos
  obtain ⟨V, hV⟩ :=
    PureVector.exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state hψ₁ hψ₂ hcard
  let K : (A × R) → Matrix R A ℂ := fun p r j => V.matrix (p, r) j
  have hK : (∑ p : A × R, (K p).conjTranspose * K p) = 1 := by
    ext j₁ j₂
    have hiso := congrFun (congrFun V.isometry j₁) j₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type] at hiso
    simpa only [K, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type] using hiso
  let N : Channel A R := krausChannel K hK
  have hamp (p : A × R) (a : A) (r : R) :
      ∑ j : A, V.matrix (p, r) j * ψ₁.amp (j, a) = ψω.amp (p, (a, r)) := by
    have h := congrFun (congrArg PureVector.amp hV) ((p, r), a)
    simpa [ψ₂, e, ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
      Matrix.mulVec, dotProduct] using h.symm
  have hω : ((Channel.idChannel A).prod N).applyState φ₀ = ω := by
    apply State.ext
    ext ⟨a₁, r₁⟩ ⟨a₂, r₂⟩
    change MatrixMap.kron (Channel.idChannel A).map N.map φ₀.matrix (a₁, r₁) (a₂, r₂) =
      ω.matrix (a₁, r₁) (a₂, r₂)
    rw [MatrixMap.kron_idChannel_left_apply_slice]
    let φ_slice : CMatrix A := fun j₁ j₂ => φ₀.matrix (a₁, j₁) (a₂, j₂)
    change (∑ p : A × R, K p * φ_slice * (K p).conjTranspose) r₁ r₂ =
      ω.matrix (a₁, r₁) (a₂, r₂)
    rw [Matrix.sum_apply]
    have hentry := congrFun (congrFun hψω (a₁, r₁)) (a₂, r₂)
    rw [← hentry]
    simp only [partialTraceA, PureVector.state_matrix_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K, φ_slice, φ₀,
      PureVector.state_matrix_apply, PureVector.reindex_amp,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [← hamp p a₁ r₁, ← hamp p a₂ r₂, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    simp only [Finset.sum_mul, star_mul, mul_assoc]
  have hcomm (Ξ : Channel A B) :
      (Ξ.prod (Channel.idChannel R)).applyState (((Channel.idChannel A).prod N).applyState φ₀) =
        ((Channel.idChannel B).prod N).applyState ((Ξ.prod (Channel.idChannel A)).applyState φ₀) := by
    apply State.ext
    change MatrixMap.kron Ξ.map (Channel.idChannel R).map
        (MatrixMap.kron (Channel.idChannel A).map N.map φ₀.matrix) =
      MatrixMap.kron (Channel.idChannel B).map N.map
        (MatrixMap.kron Ξ.map (Channel.idChannel A).map φ₀.matrix)
    rw [MatrixMap.kron_comp_apply, MatrixMap.kron_comp_apply]
    simp only [ICO.DiamondPreprocessing.identity_map, LinearMap.id_comp, LinearMap.comp_id]
  rw [← hω, hcomm Φ, hcomm Ψ]
  refine (Channel.normalizedTraceDistance_applyState_le
    ((Channel.idChannel B).prod N) _ _).trans ?_
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro y ⟨τ, rfl⟩
    exact ICO.ChoiWitnessState.state_distance_le_one _ _
  · exact ⟨φ₀, rfl⟩

/-- Unconditional diamond-norm contractivity of the quantum switch in the first slot:
`D_◇(S(E, F), S(E', F)) ≤ D_◇(E, E')`. -/
theorem switch_slot_left_diamond_le_diamond [Nonempty A] {ι ι' κ : Type}
    [Fintype ι] [Fintype ι'] [Fintype κ]
    (E : ι → CMatrix A) (E' : ι' → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hE' : (∑ i, (E' i).conjTranspose * E' i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    (switchChannel E F hE hF).diamondTraceDistance (switchChannel E' F hE' hF) ≤
      (krausChannel E hE).diamondTraceDistance (krausChannel E' hE') := by
  letI := Classical.decEq κ
  exact switch_slot_left_diamond_le E E' F hE hE' hF
    (ancillaTraceDistanceBound_diamond (krausChannel E hE) (krausChannel E' hE'))

/-- Unconditional diamond-norm contractivity of the quantum switch in the second slot:
`D_◇(S(F, E), S(F, E')) ≤ D_◇(E, E')`. -/
theorem switch_slot_right_diamond_le_diamond [Nonempty A] {ι κ κ' : Type}
    [Fintype ι] [Fintype κ] [Fintype κ']
    (F : ι → CMatrix A) (E : κ → CMatrix A) (E' : κ' → CMatrix A)
    (hF : (∑ i, (F i).conjTranspose * F i) = 1)
    (hE : (∑ j, (E j).conjTranspose * E j) = 1)
    (hE' : (∑ j, (E' j).conjTranspose * E' j) = 1) :
    (switchChannel F E hF hE).diamondTraceDistance (switchChannel F E' hF hE') ≤
      (krausChannel E hE).diamondTraceDistance (krausChannel E' hE') := by
  letI := Classical.decEq ι
  exact switch_slot_right_diamond_le F E E' hF hE hE'
    (ancillaTraceDistanceBound_diamond (krausChannel E hE) (krausChannel E' hE'))

/-- **Model mismatch bound, unconditional diamond-norm form (audited supplementary result
outside the current manuscript)**:
For any channels `E : ι → CMatrix A` and `M : κ → CMatrix A`,
`(1 / 2) |p_+(E) - p_+(M)| = (1 / 4) |v(E) - v(M)| ≤ D_◇(E, M)`. -/
theorem model_mismatch_diamond_bound [Nonempty A] {ι κ : Type}
    [Fintype ι] [Fintype κ]
    (E : ι → CMatrix A) (M : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hM : (∑ j, (M j).conjTranspose * M j) = 1) :
    (1 / 2 : ℝ) *
      |(controlMeasurement.prob (switchedState E E hE hE mixedState) true : ℝ) -
       (controlMeasurement.prob (switchedState M M hM hM mixedState) true : ℝ)| =
      (1 / 4 : ℝ) * |interference E E - interference M M| ∧
    (1 / 4 : ℝ) * |interference E E - interference M M| ≤
      (krausChannel E hE).diamondTraceDistance (krausChannel M hM) := by
  letI := Classical.decEq ι
  letI := Classical.decEq κ
  exact model_mismatch_bound E M hE hM
    (ancillaTraceDistanceBound_diamond (krausChannel E hE) (krausChannel M hM))
    (ancillaTraceDistanceBound_diamond (krausChannel E hE) (krausChannel M hM))

/-! ## 2. Self-visibility identities `eq:validation-visibility` (`\label{sec:switch-test}`) -/

/-- Any complete Kraus family of Hermitian, pairwise commuting Kraus operators has
switch self-visibility `1`. -/
theorem commuting_hermitian_self_visibility [Nonempty A] {ι : Type} [Fintype ι]
    (E : ι → CMatrix A) (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hHerm : ∀ i, (E i).conjTranspose = E i)
    (hComm : ∀ i j, E i * E j = E j * E i) :
    interference E E = 1 := by
  have hraw : rawInterference E E = (Fintype.card A : ℂ) := by
    unfold rawInterference
    have hterm (i j : ι) :
        E j * E i * (E j).conjTranspose * (E i).conjTranspose =
          ((E i).conjTranspose * E i) * ((E j).conjTranspose * E j) := by
      rw [hHerm i, hHerm j, hComm j i]
      calc
        E i * E j * E j * E i = E i * (E j * (E j * E i)) := by simp only [Matrix.mul_assoc]
        _ = E i * (E j * (E i * E j)) := by rw [hComm j i]
        _ = E i * ((E j * E i) * E j) := by simp only [Matrix.mul_assoc]
        _ = E i * ((E i * E j) * E j) := by rw [hComm j i]
        _ = (E i * E i) * (E j * E j) := by simp only [Matrix.mul_assoc]
    simp_rw [hterm]
    simp only [← Matrix.trace_sum, ← Matrix.mul_sum, hE,
      Matrix.mul_one, Matrix.trace_one, Fintype.card]
  unfold interference
  rw [hraw, Complex.natCast_re]
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact div_self hd

/-- Complete Kraus family for the weak dephasing-noise channel
`\mathcal{E}_{p,U} = (1 - p) id + p Δ_U`. -/
def dephasingNoiseKraus (p : ℝ) (U : Matrix.unitaryGroup A ℂ) :
    Option A → CMatrix A
  | none => (Real.sqrt (1 - p) : ℂ) • (1 : CMatrix A)
  | some i => (Real.sqrt p : ℂ) • basisProjection (U : CMatrix A) i

theorem dephasingNoiseKraus_hermitian (p : ℝ) (U : Matrix.unitaryGroup A ℂ)
    (k : Option A) :
    (dephasingNoiseKraus p U k).conjTranspose = dephasingNoiseKraus p U k := by
  cases k with
  | none =>
    simp [dephasingNoiseKraus, Matrix.conjTranspose_smul]
  | some i =>
    simp [dephasingNoiseKraus, Matrix.conjTranspose_smul,
      basisProjection_hermitian (U : CMatrix A) i]

theorem dephasingNoiseKraus_comm (p : ℝ) (U : Matrix.unitaryGroup A ℂ)
    (k l : Option A) :
    dephasingNoiseKraus p U k * dephasingNoiseKraus p U l =
      dephasingNoiseKraus p U l * dephasingNoiseKraus p U k := by
  cases k with
  | none =>
    cases l <;> simp [dephasingNoiseKraus, smul_smul, mul_comm]
  | some i =>
    cases l with
    | none =>
      simp [dephasingNoiseKraus, smul_smul, mul_comm]
    | some j =>
      simp only [dephasingNoiseKraus, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [basisProjection_mul (U : CMatrix A) U.property.1 i j,
          basisProjection_mul (U : CMatrix A) U.property.1 j i]
      by_cases hij : i = j <;> simp [hij, eq_comm]

theorem dephasingNoiseKraus_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Matrix.unitaryGroup A ℂ) :
    (∑ k : Option A, (dephasingNoiseKraus p U k).conjTranspose * dephasingNoiseKraus p U k) = 1 := by
  simp_rw [dephasingNoiseKraus_hermitian]
  rw [Fintype.sum_option]
  simp only [dephasingNoiseKraus, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul]
  have h1 : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by linarith)
  have h2 : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hp0
  have hproj :
      (∑ i : A, basisProjection (U : CMatrix A) i * basisProjection (U : CMatrix A) i) = 1 := by
    have h := hidden_basis_kraus_complete (U : CMatrix A) U.property.1 U.property.2
    simpa [basisProjection_hermitian] using h
  rw [h1, h2, ← Finset.smul_sum, hproj, ← add_smul]
  have hsum : ((1 - p : ℝ) : ℂ) + (p : ℂ) = 1 := by push_cast; ring
  rw [hsum, one_smul]

/-- **Equation `eq:validation-visibility` (Part 1)**:
For every `p ∈ [0, 1]` and unitary `U`, the weak dephasing-noise channel
`\mathcal{E}_{p,U} = (1 - p) id + p Δ_U` has self-visibility `v(\mathcal{E}_{p,U}) = 1`
and plus acceptance probability `p_+(\mathcal{E}_{p,U}) = 1`. -/
theorem dephasing_noise_self_visibility [Nonempty A] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Matrix.unitaryGroup A ℂ) :
    interference (dephasingNoiseKraus p U) (dephasingNoiseKraus p U) = 1 ∧
    (controlMeasurement.prob
      (switchedState (dephasingNoiseKraus p U) (dephasingNoiseKraus p U)
        (dephasingNoiseKraus_complete hp0 hp1 U)
        (dephasingNoiseKraus_complete hp0 hp1 U) mixedState) true : ℝ) = 1 := by
  have hint : interference (dephasingNoiseKraus p U) (dephasingNoiseKraus p U) = 1 :=
    commuting_hermitian_self_visibility (dephasingNoiseKraus p U)
      (dephasingNoiseKraus_complete hp0 hp1 U)
      (dephasingNoiseKraus_hermitian p U)
      (dephasingNoiseKraus_comm p U)
  refine ⟨hint, ?_⟩
  rw [switch_plus_probability, hint]
  norm_num

/-- Complete Kraus family for any depolarizing channel `\mathcal{M}_α = α id + (1 - α) Ω`
with identity weight `α ∈ [0, 1]`. -/
def depolarizingModelKraus (α : ℝ) : Option (A × A) → CMatrix A
  | none => (Real.sqrt α : ℂ) • (1 : CMatrix A)
  | some ij => (Real.sqrt (1 - α) : ℂ) • depolarizingKraus (n := A) ij

theorem depolarizingModelKraus_complete [Nonempty A] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (∑ k : Option (A × A),
      (depolarizingModelKraus (A := A) α k).conjTranspose *
        depolarizingModelKraus (A := A) α k) = 1 := by
  rw [Fintype.sum_option]
  simp only [depolarizingModelKraus, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.one_mul]
  have h1 : (Real.sqrt α : ℂ) * (Real.sqrt α : ℂ) = (α : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hα0
  have h2 : (Real.sqrt (1 - α) : ℂ) * (Real.sqrt (1 - α) : ℂ) = ((1 - α : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by linarith)
  rw [h1, h2, ← Finset.smul_sum, depolarizing_kraus_complete (n := A), ← add_smul]
  have hsum : (α : ℂ) + ((1 - α : ℝ) : ℂ) = 1 := by push_cast; ring
  rw [hsum, one_smul]

/-- Self-visibility of `\mathcal{M}_α = α id + (1 - α) Ω` for any `α ∈ [0, 1]`:
`v(\mathcal{M}_α) = 1 - (1 - α)^2 (1 - 1 / d^2)`. -/
theorem depolarizing_alpha_self_visibility [Nonempty A] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    interference (depolarizingModelKraus (A := A) α)
      (depolarizingModelKraus (A := A) α) =
      1 - (1 - α) ^ 2 * (1 - 1 / (Fintype.card A : ℝ) ^ 2) := by
  have h1 : (Real.sqrt α : ℂ) * (Real.sqrt α : ℂ) = (α : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hα0
  have h2 : (Real.sqrt (1 - α) : ℂ) * (Real.sqrt (1 - α) : ℂ) = ((1 - α : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by linarith)
  have hsc :
      (Real.sqrt α : ℂ) * (Real.sqrt (1 - α) : ℂ) *
          (Real.sqrt (1 - α) : ℂ) * (Real.sqrt α : ℂ) =
        (α : ℂ) * ((1 - α : ℝ) : ℂ) := by
    linear_combination (Real.sqrt (1 - α) : ℂ) ^ 2 * h1 + (α : ℂ) * h2
  have h_none_none :
      Matrix.trace (depolarizingModelKraus (A := A) α none *
        depolarizingModelKraus (A := A) α none *
        (depolarizingModelKraus (A := A) α none).conjTranspose *
        (depolarizingModelKraus (A := A) α none).conjTranspose) =
        (α : ℂ) ^ 2 * (Fintype.card A : ℂ) := by
    simp only [depolarizingModelKraus, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.conjTranspose_one, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    linear_combination ((α : ℂ) + (Real.sqrt α : ℂ) ^ 2) * (Fintype.card A : ℂ) * h1
  have h_none_some :
      (∑ j : A × A,
        Matrix.trace (depolarizingModelKraus (A := A) α (some j) *
          depolarizingModelKraus (A := A) α none *
          (depolarizingModelKraus (A := A) α (some j)).conjTranspose *
          (depolarizingModelKraus (A := A) α none).conjTranspose)) =
        (α : ℂ) * ((1 - α : ℝ) : ℂ) * (Fintype.card A : ℂ) := by
    have hterm (j : A × A) :
        Matrix.trace (depolarizingModelKraus (A := A) α (some j) *
          depolarizingModelKraus (A := A) α none *
          (depolarizingModelKraus (A := A) α (some j)).conjTranspose *
          (depolarizingModelKraus (A := A) α none).conjTranspose) =
          ((α : ℂ) * ((1 - α : ℝ) : ℂ)) *
            Matrix.trace ((depolarizingKraus (n := A) j).conjTranspose *
              depolarizingKraus (n := A) j) := by
      simp only [depolarizingModelKraus, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_one, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal, Matrix.conjTranspose_one, Matrix.trace_smul, smul_eq_mul]
      rw [Matrix.trace_mul_comm (depolarizingKraus (n := A) j)]
      linear_combination
        Matrix.trace ((depolarizingKraus (n := A) j).conjTranspose *
          depolarizingKraus (n := A) j) * hsc
    simp_rw [hterm, ← Finset.mul_sum, ← Matrix.trace_sum,
      depolarizing_kraus_complete (n := A), Matrix.trace_one]
  have h_some_none :
      (∑ i : A × A,
        Matrix.trace (depolarizingModelKraus (A := A) α none *
          depolarizingModelKraus (A := A) α (some i) *
          (depolarizingModelKraus (A := A) α none).conjTranspose *
          (depolarizingModelKraus (A := A) α (some i)).conjTranspose)) =
        (α : ℂ) * ((1 - α : ℝ) : ℂ) * (Fintype.card A : ℂ) := by
    have hterm (i : A × A) :
        Matrix.trace (depolarizingModelKraus (A := A) α none *
          depolarizingModelKraus (A := A) α (some i) *
          (depolarizingModelKraus (A := A) α none).conjTranspose *
          (depolarizingModelKraus (A := A) α (some i)).conjTranspose) =
          ((α : ℂ) * ((1 - α : ℝ) : ℂ)) *
            Matrix.trace ((depolarizingKraus (n := A) i).conjTranspose *
              depolarizingKraus (n := A) i) := by
      simp only [depolarizingModelKraus, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal, Matrix.conjTranspose_one, Matrix.trace_smul, smul_eq_mul]
      rw [Matrix.trace_mul_comm (depolarizingKraus (n := A) i)]
      linear_combination
        Matrix.trace ((depolarizingKraus (n := A) i).conjTranspose *
          depolarizingKraus (n := A) i) * hsc
    simp_rw [hterm, ← Finset.mul_sum, ← Matrix.trace_sum,
      depolarizing_kraus_complete (n := A), Matrix.trace_one]
  have h_some_some :
      (∑ i : A × A, ∑ j : A × A,
        Matrix.trace (depolarizingModelKraus (A := A) α (some j) *
          depolarizingModelKraus (A := A) α (some i) *
          (depolarizingModelKraus (A := A) α (some j)).conjTranspose *
          (depolarizingModelKraus (A := A) α (some i)).conjTranspose)) =
        ((1 - α : ℝ) : ℂ) ^ 2 *
          rawInterference (depolarizingKraus (n := A)) (depolarizingKraus (n := A)) := by
    unfold rawInterference
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [depolarizingModelKraus, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.trace_smul, smul_eq_mul]
    linear_combination
      (((1 - α : ℝ) : ℂ) + (Real.sqrt (1 - α) : ℂ) ^ 2) *
        Matrix.trace (depolarizingKraus (n := A) j * depolarizingKraus (n := A) i *
          (depolarizingKraus (n := A) j).conjTranspose *
          (depolarizingKraus (n := A) i).conjTranspose) * h2
  have hraw :
      rawInterference (depolarizingModelKraus (A := A) α)
        (depolarizingModelKraus (A := A) α) =
      (α : ℂ) ^ 2 * (Fintype.card A : ℂ) +
        2 * (α : ℂ) * ((1 - α : ℝ) : ℂ) * (Fintype.card A : ℂ) +
        ((1 - α : ℝ) : ℂ) ^ 2 *
          rawInterference (depolarizingKraus (n := A)) (depolarizingKraus (n := A)) := by
    change (∑ i : Option (A × A), ∑ j : Option (A × A),
      Matrix.trace (depolarizingModelKraus (A := A) α j *
        depolarizingModelKraus (A := A) α i *
        (depolarizingModelKraus (A := A) α j).conjTranspose *
        (depolarizingModelKraus (A := A) α i).conjTranspose)) = _
    rw [Fintype.sum_option]
    simp_rw [Fintype.sum_option]
    rw [Finset.sum_add_distrib, h_none_none, h_none_some, h_some_none, h_some_some]
    ring
  have hdep := depolarizing_low (n := A)
  unfold interference at hdep ⊢
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hraw_dep_re :
      (rawInterference (depolarizingKraus (n := A)) (depolarizingKraus (n := A))).re =
        1 / (Fintype.card A : ℝ) := by
    have hmul := congrArg (fun x : ℝ => x * (Fintype.card A : ℝ)) hdep
    dsimp at hmul
    rw [div_mul_cancel₀ _ hd] at hmul
    rw [hmul]
    field_simp
  have hraw_re :
      (rawInterference (depolarizingModelKraus (A := A) α)
        (depolarizingModelKraus (A := A) α)).re =
      α ^ 2 * (Fintype.card A : ℝ) +
        2 * α * (1 - α) * (Fintype.card A : ℝ) +
        (1 - α) ^ 2 * (1 / (Fintype.card A : ℝ)) := by
    have hcast :
        rawInterference (depolarizingModelKraus (A := A) α)
          (depolarizingModelKraus (A := A) α) =
        ((α ^ 2 * (Fintype.card A : ℝ) +
          2 * α * (1 - α) * (Fintype.card A : ℝ) : ℝ) : ℂ) +
          (((1 - α) ^ 2 : ℝ) : ℂ) *
            rawInterference (depolarizingKraus (n := A)) (depolarizingKraus (n := A)) := by
      rw [hraw]
      push_cast
      ring
    rw [hcast, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hraw_dep_re]
  rw [hraw_re]
  field_simp
  ring

/-- **Equation `eq:validation-visibility` (Part 2)**:
For `\mathcal{M}_p = (1 - p) id + p Λ` with `Λ = (id + d Ω) / (d + 1)`, the identity
weight is `α = 1 - p d / (d + 1)` and the switch self-visibility is
`v(\mathcal{M}_p) = 1 - p^2 (d - 1) / (d + 1)`. -/
theorem depolarizing_model_self_visibility [Nonempty A] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let d : ℝ := Fintype.card A
    let α : ℝ := 1 - p * d / (d + 1)
    0 ≤ α ∧ α ≤ 1 ∧
    interference (depolarizingModelKraus (A := A) α)
      (depolarizingModelKraus (A := A) α) =
      1 - p ^ 2 * (d - 1) / (d + 1) := by
  intro d α
  have hd_pos : (0 : ℝ) < d := by
    change (0 : ℝ) < Fintype.card A
    exact_mod_cast Fintype.card_pos (α := A)
  have hd1_pos : (0 : ℝ) < d + 1 := by linarith
  have hα0 : 0 ≤ α := by
    change 0 ≤ 1 - p * d / (d + 1)
    have hle : p * d ≤ d + 1 := by nlinarith
    have hdiv : p * d / (d + 1) ≤ 1 := (div_le_iff₀ hd1_pos).mpr (by linarith)
    linarith
  have hα1 : α ≤ 1 := by
    change 1 - p * d / (d + 1) ≤ 1
    have hnonneg : 0 ≤ p * d / (d + 1) :=
      div_nonneg (mul_nonneg hp0 (le_of_lt hd_pos)) (le_of_lt hd1_pos)
    linarith
  refine ⟨hα0, hα1, ?_⟩
  rw [depolarizing_alpha_self_visibility hα0 hα1]
  change 1 - (1 - (1 - p * d / (d + 1))) ^ 2 * (1 - 1 / d ^ 2) =
    1 - p ^ 2 * (d - 1) / (d + 1)
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hd1_ne : d + 1 ≠ 0 := ne_of_gt hd1_pos
  field_simp
  ring

/-! ## 3. Theorem 3 (`\label{thm:c6}`): ordinary lower bound (`\label{sec:validation}`) and switch upper bound (`\label{sec:switch-test}`) -/

/-- **Theorem 3 (`\label{thm:c6}`) / Section 5.3 (`\label{sec:validation}`), numeric reduction for the ordinary query lower bound**:
For any `2L`-call ordinary adaptive tree representing an `L`-effective-call strategy
with `1 ≤ L ≤ d^{1/16} / 200` and `d^{1/16} / 200 < L + 1` (`L = ⌊d^{1/16} / 200⌋`):
1. The Haar-averaged trace distance between `sameDensity` (`Δ_U`) and `mubDensity` (`Ω`)
   is at most `215 / 10000`.
2. Including the `L`-step hybrid cost `L / (d + 1) ≤ 1 / 200` between `Ω` and `Λ`,
   the strong-device trace distance is at most `53 / 2000`, so the balanced-prior
   strong-device success probability is at most `2053 / 4000`.
3. By the Bernoulli-`p` Markov truncation bound `2 / 3 ≤ p_succ ≤ 2053 / 4000 + p Q / (L + 1)`,
   any `Q`-call ordinary strategy succeeding with probability at least `2 / 3` at noise
   rate `p > 0` requires `Q > d^{1/16} / (1400 p)`. -/
theorem validation_ordinary_lower_bound [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {L : ℕ} (tree : ICO.BudgetQueryTree.Tree (A × M) O (2 * L) B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ)
    (hL1 : 1 ≤ L)
    (hLd : (L : ℝ) ≤ (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 200)
    (hL_floor : (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 200 < (L : ℝ) + 1)
    {p Q : ℝ} (hp : 0 < p)
    (hsucc : (2 / 3 : ℝ) ≤
      (1 / 2 : ℝ) + (1 / 2 : ℝ) *
        (normalizedTraceDistance (ICO.C6Decision.sameDensity tree ρ)
          (ICO.C6Decision.mubDensity tree ρ H) +
          (L : ℝ) / ((Fintype.card A : ℝ) + 1)) +
        p * Q / ((L : ℝ) + 1)) :
    normalizedTraceDistance (ICO.C6Decision.sameDensity tree ρ)
      (ICO.C6Decision.mubDensity tree ρ H) ≤ 215 / 10000 ∧
    normalizedTraceDistance (ICO.C6Decision.sameDensity tree ρ)
      (ICO.C6Decision.mubDensity tree ρ H) +
      (L : ℝ) / ((Fintype.card A : ℝ) + 1) ≤ 53 / 2000 ∧
    (1 / 2 : ℝ) + (1 / 2 : ℝ) *
      (normalizedTraceDistance (ICO.C6Decision.sameDensity tree ρ)
        (ICO.C6Decision.mubDensity tree ρ H) +
        (L : ℝ) / ((Fintype.card A : ℝ) + 1)) ≤ 2053 / 4000 ∧
    (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / (1400 * p) < Q := by
  let r : ℝ := (Fintype.card A : ℝ) ^ (1 / 16 : ℝ)
  have hrpow : r ^ 16 = (Fintype.card A : ℝ) :=
    ICO.QuantumDecision.radius_power_sixteen (Fintype.card A) (by positivity)
  have hq1 : 1 ≤ 2 * L := by omega
  have hqr : ((2 * L : ℕ) : ℝ) ≤ r / 100 := by
    push_cast
    linarith
  have hr_dims := ICO.C6Bounds.radius_dimensions (by exact_mod_cast hq1) hqr
  have hfour : 4 * (2 * L) ≤ Fintype.card A := by
    have hqreal : (1 : ℝ) ≤ (2 * L : ℕ) := by exact_mod_cast hq1
    have hr1 : 1 ≤ r := by linarith
    have h14 : r ≤ r ^ 4 := by
      simpa using pow_le_pow_right₀ hr1 (show (1 : ℕ) ≤ 4 by norm_num)
    have hr4_le : r ^ 4 ≤ r ^ 16 - 2 * ((2 * L : ℕ) : ℝ) := hr_dims.2.2
    exact_mod_cast (show (4 * (2 * L : ℕ) : ℝ) ≤ Fintype.card A by linarith)
  have hdist_u := ICO.C6OperationalDecision.same_mub_distance tree ρ H hq1 hfour
  have hunif := ICO.C6UniformBounds.uniformError_le hq1 hqr
  rw [hrpow] at hunif
  have hdist :
      normalizedTraceDistance (ICO.C6Decision.sameDensity tree ρ)
        (ICO.C6Decision.mubDensity tree ρ H) ≤ 215 / 10000 :=
    hdist_u.trans hunif
  have hr_le_d : r ≤ (Fintype.card A : ℝ) := by
    have hr1 : 1 ≤ r := by
      have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
      linarith
    have h1_16 : r ≤ r ^ 16 := by
      simpa using pow_le_pow_right₀ hr1 (show (1 : ℕ) ≤ 16 by norm_num)
    rwa [hrpow] at h1_16
  have hhybrid : (L : ℝ) / ((Fintype.card A : ℝ) + 1) ≤ 1 / 200 := by
    have hd1_pos : (0 : ℝ) < (Fintype.card A : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hd1_pos]
    linarith
  have htotal :
      normalizedTraceDistance (ICO.C6Decision.sameDensity tree ρ)
        (ICO.C6Decision.mubDensity tree ρ H) +
        (L : ℝ) / ((Fintype.card A : ℝ) + 1) ≤ 53 / 2000 := by
    linarith
  have hstrong :
      (1 / 2 : ℝ) + (1 / 2 : ℝ) *
        (normalizedTraceDistance (ICO.C6Decision.sameDensity tree ρ)
          (ICO.C6Decision.mubDensity tree ρ H) +
          (L : ℝ) / ((Fintype.card A : ℝ) + 1)) ≤ 2053 / 4000 := by
    linarith
  have hmarkov : (1841 : ℝ) / 12000 ≤ p * Q / ((L : ℝ) + 1) := by linarith
  have hmarkov_gt : (1 : ℝ) / 7 < p * Q / ((L : ℝ) + 1) := by linarith
  have hL1_pos : (0 : ℝ) < (L : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    linarith
  have hpQ_mul : (1 / 7 : ℝ) * ((L : ℝ) + 1) < p * Q :=
    (lt_div_iff₀ hL1_pos).mp hmarkov_gt
  have hr_lt_pQ : (r / 200) / 7 < p * Q := by linarith
  have hQ : r / (1400 * p) < Q := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 1400 * p)]
    linarith
  exact ⟨hdist, htotal, hstrong, hQ⟩

/-! ### End-to-end operational proof of the ordinary query lower bound in Theorem 3 (`\label{thm:c6}`, `\label{sec:validation}`) -/

/-- Weak dephasing-noise channel `\mathcal{E}_{p,U} = (1 - p) id + p Δ_U` acting on `A`
while preserving arbitrary finite side memory `M`. -/
def dephasingNoiseWithMemory (M : Type) [Fintype M] [DecidableEq M]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U : Matrix.unitaryGroup A ℂ) :
    Channel (A × M) (A × M) :=
  (krausChannel (dephasingNoiseKraus p U) (dephasingNoiseKraus_complete hp0 hp1 U)).prod
    (Channel.idChannel M)

theorem dephasingNoiseWithMemory_map [Nonempty A] {M : Type} [Fintype M] [DecidableEq M]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U : Matrix.unitaryGroup A ℂ)
    (Y : CMatrix (A × M)) :
    (dephasingNoiseWithMemory M hp0 hp1 U).map Y =
      ((1 - p : ℝ) : ℂ) • (Channel.idChannel (A × M)).map Y +
        (p : ℂ) • (ICO.BudgetContinuity.hidden (M := M) U).map Y := by
  have hid :
      (ICO.BudgetContinuity.hidden (M := M) U).map Y =
        ((krausChannel (basisProjection (U : CMatrix A))
          (hidden_basis_kraus_complete _ U.property.1 U.property.2)).prod
          (Channel.idChannel M)).map Y :=
    (prod_id_map_eq_oracleMap _ _ Y).symm
  rw [hid, ICO.DiamondPreprocessing.identity_map]
  have h1 : star (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt (by linarith)
  have h2 : star (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt hp0
  ext ⟨a₁, m₁⟩ ⟨a₂, m₂⟩
  change MatrixMap.kron (MatrixMap.ofKraus (dephasingNoiseKraus p U))
      (Channel.idChannel M).map Y (a₁, m₁) (a₂, m₂) =
    (((1 - p : ℝ) : ℂ) • Y +
      (p : ℂ) • MatrixMap.kron (MatrixMap.ofKraus (basisProjection (U : CMatrix A)))
        (Channel.idChannel M).map Y) (a₁, m₁) (a₂, m₂)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_apply_slice]
  let S : CMatrix A := fun i j => Y (i, m₁) (j, m₂)
  suffices hS :
      MatrixMap.ofKraus (dephasingNoiseKraus p U) S =
        ((1 - p : ℝ) : ℂ) • S + (p : ℂ) • MatrixMap.ofKraus (basisProjection (U : CMatrix A)) S by
    simpa [S, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
      congrFun (congrFun hS a₁) a₂
  change (∑ k : Option A, dephasingNoiseKraus p U k * S * (dephasingNoiseKraus p U k).conjTranspose) = _
  rw [Fintype.sum_option]
  simp only [dephasingNoiseKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  rw [h1]
  simp_rw [h2, ← Finset.smul_sum]
  rfl

/-- Depolarizing channel `\mathcal{M}_α = α id + (1 - α) Ω` acting on `A` while preserving
side memory `M`. -/
def depolarizingAlphaWithMemory (M : Type) [Fintype M] [DecidableEq M] [Nonempty A]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : Channel (A × M) (A × M) :=
  (krausChannel (depolarizingModelKraus (A := A) α)
    (depolarizingModelKraus_complete hα0 hα1)).prod (Channel.idChannel M)

theorem depolarizingAlphaWithMemory_map [Nonempty A] {M : Type} [Fintype M] [DecidableEq M]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (Y : CMatrix (A × M)) :
    (depolarizingAlphaWithMemory (A := A) M hα0 hα1).map Y =
      (α : ℂ) • (Channel.idChannel (A × M)).map Y +
        ((1 - α : ℝ) : ℂ) • (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map Y := by
  rw [ICO.DiamondPreprocessing.identity_map]
  have h1 : star (Real.sqrt α : ℂ) * (Real.sqrt α : ℂ) = (α : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt hα0
  have h2 : star (Real.sqrt (1 - α) : ℂ) * (Real.sqrt (1 - α) : ℂ) = ((1 - α : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt (by linarith)
  ext ⟨a₁, m₁⟩ ⟨a₂, m₂⟩
  change MatrixMap.kron (MatrixMap.ofKraus (depolarizingModelKraus (A := A) α))
      (Channel.idChannel M).map Y (a₁, m₁) (a₂, m₂) =
    ((α : ℂ) • Y +
      ((1 - α : ℝ) : ℂ) • MatrixMap.kron (ICO.RecordingDepolarizing.depolarizing (α := A)).map
        (Channel.idChannel M).map Y) (a₁, m₁) (a₂, m₂)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_apply_slice]
  let S : CMatrix A := fun i j => Y (i, m₁) (j, m₂)
  have hdep : MatrixMap.ofKraus (depolarizingKraus (n := A)) S =
      (ICO.RecordingDepolarizing.depolarizing (α := A)).map S := by
    ext i j
    change (∑ p : A × A, depolarizingKraus (n := A) p * S *
        (depolarizingKraus (n := A) p).conjTranspose) i j =
      (ICO.RecordingDepolarizing.depolarizing (α := A)).map S i j
    rw [depolarizing_channel S, ICO.RecordingDepolarizing.depolarizing_entry]
    by_cases hij : i = j <;> simp [hij, div_eq_mul_inv, mul_comm]
  suffices hS :
      MatrixMap.ofKraus (depolarizingModelKraus (A := A) α) S =
        (α : ℂ) • S + ((1 - α : ℝ) : ℂ) • (ICO.RecordingDepolarizing.depolarizing (α := A)).map S by
    simpa [S, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
      congrFun (congrFun hS a₁) a₂
  rw [← hdep]
  change (∑ k : Option (A × A), depolarizingModelKraus (A := A) α k * S *
      (depolarizingModelKraus (A := A) α k).conjTranspose) = _
  rw [Fintype.sum_option]
  simp only [depolarizingModelKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  rw [h1]
  simp_rw [h2, ← Finset.smul_sum]
  rfl

/-- Identity weight `α = 1 - p d / (d + 1)` of the depolarizing noise model
`\mathcal{M}_p = (1 - p) id + p Λ`. -/
def depolarizingModelAlpha (A : Type) [Fintype A] (p : ℝ) : ℝ :=
  1 - p * (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) + 1)

omit [DecidableEq A] in
theorem depolarizingModelAlpha_nonneg [Nonempty A] {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ depolarizingModelAlpha A p := by
  unfold depolarizingModelAlpha
  have hd_pos : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
  have hd1_pos : (0 : ℝ) < (Fintype.card A : ℝ) + 1 := by linarith
  have hdiv : p * (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) + 1) ≤ 1 :=
    (div_le_iff₀ hd1_pos).mpr (by nlinarith)
  linarith

omit [DecidableEq A] in
theorem depolarizingModelAlpha_le_one [Nonempty A] {p : ℝ} (hp0 : 0 ≤ p) :
    depolarizingModelAlpha A p ≤ 1 := by
  unfold depolarizingModelAlpha
  have hnonneg : 0 ≤ p * (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) + 1) :=
    div_nonneg (mul_nonneg hp0 (Nat.cast_nonneg _)) (by positivity)
  linarith

/-- Depolarizing model channel `\mathcal{M}_p = (1 - p) id + p Λ` acting on `A` while
preserving side memory `M`. -/
def depolarizingModelWithMemory (M : Type) [Fintype M] [DecidableEq M] [Nonempty A]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Channel (A × M) (A × M) :=
  depolarizingAlphaWithMemory (A := A) M
    (depolarizingModelAlpha_nonneg (A := A) hp0 hp1)
    (depolarizingModelAlpha_le_one (A := A) hp0)

/-- Haar-averaged strong dephasing channel `Λ = (id + d Ω) / (d + 1)` acting on `A`
while preserving side memory `M`. -/
def haarDepolarizingWithMemory (M : Type) [Fintype M] [DecidableEq M] [Nonempty A] :
    Channel (A × M) (A × M) :=
  depolarizingModelWithMemory (A := A) M zero_le_one le_rfl

theorem haarDepolarizingWithMemory_map [Nonempty A] {M : Type} [Fintype M] [DecidableEq M]
    (Y : CMatrix (A × M)) :
    (haarDepolarizingWithMemory (A := A) M).map Y =
      ((1 - 1 / ((Fintype.card A : ℝ) + 1) : ℝ) : ℂ) •
          (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map Y +
        ((1 / ((Fintype.card A : ℝ) + 1) : ℝ) : ℂ) •
          (Channel.idChannel (A × M)).map Y := by
  unfold haarDepolarizingWithMemory depolarizingModelWithMemory
  rw [depolarizingAlphaWithMemory_map]
  have hd1_ne : ((Fintype.card A : ℝ) + 1) ≠ 0 := by positivity
  have hα : depolarizingModelAlpha A 1 = 1 / ((Fintype.card A : ℝ) + 1) := by
    unfold depolarizingModelAlpha
    field_simp
    ring
  rw [hα, add_comm]

theorem depolarizingModelWithMemory_map [Nonempty A] {M : Type} [Fintype M] [DecidableEq M]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Y : CMatrix (A × M)) :
    (depolarizingModelWithMemory (A := A) M hp0 hp1).map Y =
      ((1 - p : ℝ) : ℂ) • (Channel.idChannel (A × M)).map Y +
        (p : ℂ) • (haarDepolarizingWithMemory (A := A) M).map Y := by
  unfold depolarizingModelWithMemory
  rw [depolarizingAlphaWithMemory_map, haarDepolarizingWithMemory_map]
  have hd1_ne : ((Fintype.card A : ℝ) + 1) ≠ 0 := by positivity
  have hc_id :
      (depolarizingModelAlpha A p : ℂ) =
        ((1 - p : ℝ) : ℂ) + (p : ℂ) * ((1 / ((Fintype.card A : ℝ) + 1) : ℝ) : ℂ) := by
    have hr :
        depolarizingModelAlpha A p =
          (1 - p) + p * (1 / ((Fintype.card A : ℝ) + 1)) := by
      unfold depolarizingModelAlpha
      field_simp
      ring
    exact_mod_cast hr
  have hc_dep :
      ((1 - depolarizingModelAlpha A p : ℝ) : ℂ) =
        (p : ℂ) * ((1 - 1 / ((Fintype.card A : ℝ) + 1) : ℝ) : ℂ) := by
    have hr :
        1 - depolarizingModelAlpha A p =
          p * (1 - 1 / ((Fintype.card A : ℝ) + 1)) := by
      unfold depolarizingModelAlpha
      field_simp
      ring
    exact_mod_cast hr
  rw [hc_id, hc_dep, smul_add, smul_smul, smul_smul, add_smul]
  abel

/-- Equivalence splitting a `(q + 1)`-step coin tape into its head bit and tail tape. -/
def tapeConsEquiv (q : ℕ) : (Bool × (Fin q → Bool)) ≃ (Fin (q + 1) → Bool) where
  toFun bc := Fin.cases bc.1 bc.2
  invFun c := (c 0, fun i => c i.succ)
  left_inv bc := by
    rcases bc with ⟨b, c⟩
    simp
  right_inv c := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp

/-- Product Bernoulli-`q` weight of a length-`Q` coin tape. -/
def bernoulliWeight (q : ℝ) : {Q : ℕ} → (Fin Q → Bool) → ℝ
  | 0, _ => 1
  | _ + 1, c => (if c 0 then q else 1 - q) * bernoulliWeight q (fun i => c i.succ)

/-- Number of `true` entries (strong-device uses) in a length-`Q` coin tape. -/
def tapeCount : {Q : ℕ} → (Fin Q → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, c => (if c 0 then 1 else 0) + tapeCount (fun i => c i.succ)

theorem bernoulliWeight_nonneg {Q : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (c : Fin Q → Bool) :
    0 ≤ bernoulliWeight q c := by
  induction Q with
  | zero => simp [bernoulliWeight]
  | succ Q ih =>
    simp only [bernoulliWeight]
    refine mul_nonneg ?_ (ih (fun i => c i.succ))
    split_ifs <;> linarith

theorem sum_bernoulliWeight (Q : ℕ) (q : ℝ) :
    (∑ c : Fin Q → Bool, bernoulliWeight q c) = 1 := by
  induction Q with
  | zero =>
    letI : Unique (Fin 0 → Bool) := ⟨⟨Fin.elim0⟩, fun c => by ext i; exact i.elim0⟩
    rw [Fintype.sum_unique]
    rfl
  | succ Q ih =>
    rw [← Equiv.sum_comp (tapeConsEquiv Q), Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [tapeConsEquiv, Equiv.coe_fn_mk, bernoulliWeight, Fin.cases_zero, Fin.cases_succ,
      ↓reduceIte, Bool.false_eq_true, ← Finset.mul_sum, ih, mul_one]
    ring

theorem sum_tapeCount_mul_bernoulliWeight (Q : ℕ) (q : ℝ) :
    (∑ c : Fin Q → Bool, (tapeCount c : ℝ) * bernoulliWeight q c) = q * (Q : ℝ) := by
  induction Q with
  | zero =>
    letI : Unique (Fin 0 → Bool) := ⟨⟨Fin.elim0⟩, fun c => by ext i; exact i.elim0⟩
    rw [Fintype.sum_unique]
    simp [tapeCount]
  | succ Q ih =>
    rw [← Equiv.sum_comp (tapeConsEquiv Q), Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [tapeConsEquiv, Equiv.coe_fn_mk, bernoulliWeight, tapeCount,
      Fin.cases_zero, Fin.cases_succ, ↓reduceIte, Bool.false_eq_true, Nat.cast_add,
      Nat.cast_one, zero_add]
    have htrue :
        (∑ c : Fin Q → Bool, (1 + (tapeCount c : ℝ)) * (q * bernoulliWeight q c)) =
          q * (∑ c : Fin Q → Bool, bernoulliWeight q c) +
            q * (∑ c : Fin Q → Bool, (tapeCount c : ℝ) * bernoulliWeight q c) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    have hfalse :
        (∑ c : Fin Q → Bool, (tapeCount c : ℝ) * ((1 - q) * bernoulliWeight q c)) =
          (1 - q) * (∑ c : Fin Q → Bool, (tapeCount c : ℝ) * bernoulliWeight q c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [htrue, hfalse, sum_bernoulliWeight, ih]
    ring

/-- Markov's inequality for the number of `true` coins in `Q` independent Bernoulli-`q` tosses. -/
theorem sum_bernoulliWeight_filter_gt {Q L : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => L < tapeCount c),
      bernoulliWeight q c) ≤ q * (Q : ℝ) / ((L : ℝ) + 1) := by
  have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hL1, mul_comm ((∑ c ∈ _, bernoulliWeight q c)), Finset.mul_sum]
  calc
    (∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => L < tapeCount c),
        ((L : ℝ) + 1) * bernoulliWeight q c) ≤
      ∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => L < tapeCount c),
        (tapeCount c : ℝ) * bernoulliWeight q c := by
      refine Finset.sum_le_sum fun c hc => ?_
      have hgt : L + 1 ≤ tapeCount c := by
        have hlt := (Finset.mem_filter.mp hc).2
        omega
      have hcast : (L : ℝ) + 1 ≤ (tapeCount c : ℝ) := by exact_mod_cast hgt
      exact mul_le_mul_of_nonneg_right hcast (bernoulliWeight_nonneg hq0 hq1 c)
    _ ≤ ∑ c : Fin Q → Bool, (tapeCount c : ℝ) * bernoulliWeight q c := by
      refine Finset.sum_le_univ_sum_of_nonneg fun c => ?_
      exact mul_nonneg (Nat.cast_nonneg _) (bernoulliWeight_nonneg hq0 hq1 c)
    _ = q * (Q : ℝ) := sum_tapeCount_mul_bernoulliWeight Q q

/-- Run a `Q`-budget adaptive tree against a deterministic coin tape `c : Fin Q → Bool`,
applying `Φ₁` when the next coin is `true` and `Φ₀` when it is `false`. -/
def runCoinTree {H O B : Type} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] {Q : ℕ}
    (tree : ICO.BudgetQueryTree.Tree H O Q B) :
    (Fin Q → Bool) → Channel H H → Channel H H → Channel B O := by
  induction tree with
  | stop after => exact fun _ _ _ => after
  | query _ after ih =>
      exact fun c Φ₀ Φ₁ =>
        (ih (fun i => c i.succ) Φ₀ Φ₁).comp (if c 0 then Φ₁ else Φ₀)
  | node I next ih =>
      exact fun c Φ₀ Φ₁ =>
        ICO.InstrumentCompression.adaptiveChannel I (fun l => ih l c Φ₀ Φ₁)

/-- Exact coin-tape expansion of a single-box `Q`-budget adaptive tree on a convex
combination `Φ = (1 - q) Φ₀ + q Φ₁`. -/
theorem tree_channel_convex_combination {H O B : Type}
    [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q : ℕ} (tree : ICO.BudgetQueryTree.Tree H O Q B)
    (Φ Φ₀ Φ₁ : Channel H H) (q : ℝ)
    (hΦ : ∀ Y : CMatrix H,
      Φ.map Y = ((1 - q : ℝ) : ℂ) • Φ₀.map Y + (q : ℂ) • Φ₁.map Y)
    (X : CMatrix B) :
    (tree.channel Φ Φ).map X =
      ∑ c : Fin Q → Bool, (bernoulliWeight q c : ℂ) • (runCoinTree tree c Φ₀ Φ₁).map X := by
  induction tree with
  | stop after =>
    change after.map X = ∑ c, (bernoulliWeight q c : ℂ) • after.map X
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, sum_bernoulliWeight,
      Complex.ofReal_one, one_smul]
  | query b after ih =>
    have hb : (if b then Φ else Φ) = Φ := by cases b <;> rfl
    change (after.channel Φ Φ).map ((if b then Φ else Φ).map X) = _
    rw [hb, hΦ X, map_add, map_smul, map_smul, ih (Φ₀.map X), ih (Φ₁.map X)]
    rw [← Equiv.sum_comp (tapeConsEquiv _), Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [tapeConsEquiv, Equiv.coe_fn_mk, bernoulliWeight, runCoinTree,
      Fin.cases_zero, Fin.cases_succ, ↓reduceIte, Bool.false_eq_true,
      Complex.ofReal_mul, Finset.smul_sum, smul_smul]
    exact add_comm _ _
  | node I next ih =>
    change ICO.InstrumentCompression.adaptiveMap I (fun l => (next l).channel Φ Φ) X =
      ∑ c, (bernoulliWeight q c : ℂ) •
        ICO.InstrumentCompression.adaptiveMap I (fun l => runCoinTree (next l) c Φ₀ Φ₁) X
    simp only [ICO.InstrumentCompression.adaptiveMap_apply]
    simp_rw [ih]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.smul_sum]

theorem tree_acceptance_convex_combination [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q : ℕ} (T : BinaryHypothesisTest O)
    (tree : ICO.BudgetQueryTree.Tree (A × M) O Q B) (ρ : State B)
    (Φ Φ₀ Φ₁ : Channel (A × M) (A × M)) (q : ℝ)
    (hΦ : ∀ Y : CMatrix (A × M),
      Φ.map Y = ((1 - q : ℝ) : ℂ) • Φ₀.map Y + (q : ℂ) • Φ₁.map Y) :
    ICO.BudgetTesting.acceptance T tree ρ Φ Φ =
      ∑ c : Fin Q → Bool,
        bernoulliWeight q c *
          (T.acceptProb ((runCoinTree tree c Φ₀ Φ₁).applyState ρ) : ℝ) := by
  unfold ICO.BudgetTesting.acceptance
  rw [tree_channel_convex_combination tree Φ Φ₀ Φ₁ q hΦ ρ.matrix]
  have hreal :
      (∑ c : Fin Q → Bool,
          (bernoulliWeight q c : ℂ) • (runCoinTree tree c Φ₀ Φ₁).map ρ.matrix) =
        ∑ c : Fin Q → Bool,
          bernoulliWeight q c • (runCoinTree tree c Φ₀ Φ₁).map ρ.matrix := by
    refine Finset.sum_congr rfl fun c _ => ?_
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hreal, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  exact ICO.BornAverage.accept_eq T ((runCoinTree tree c Φ₀ Φ₁).applyState ρ)

theorem runCoinTree_zero_count {H O B : Type}
    [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q : ℕ} (tree : ICO.BudgetQueryTree.Tree H O Q B) (c : Fin Q → Bool)
    (Φ₀ Φ₁ : Channel H H) (hc : tapeCount c = 0) :
    (runCoinTree tree c Φ₀ Φ₁).map = (tree.channel Φ₀ Φ₀).map := by
  induction tree with
  | stop after => rfl
  | query b after ih =>
    have h0 : c 0 = false := by
      by_cases h : c 0 = true
      · simp [tapeCount, h] at hc
      · exact Bool.eq_false_iff.mpr h
    have htail : tapeCount (fun i => c i.succ) = 0 := by
      simpa [tapeCount, h0] using hc
    have hb : (if b then Φ₀ else Φ₀) = Φ₀ := by cases b <;> rfl
    change (runCoinTree after (fun i => c i.succ) Φ₀ Φ₁).map.comp
        (if c 0 then Φ₁ else Φ₀).map =
      (after.channel Φ₀ Φ₀).map.comp (if b then Φ₀ else Φ₀).map
    rw [h0, hb, ih (fun i => c i.succ) htail]
    rfl
  | node I next ih =>
    ext X i j
    change ICO.InstrumentCompression.adaptiveMap I (fun l => runCoinTree (next l) c Φ₀ Φ₁) X i j =
      ICO.InstrumentCompression.adaptiveMap I (fun l => (next l).channel Φ₀ Φ₀) X i j
    simp only [ICO.InstrumentCompression.adaptiveMap_apply]
    simp_rw [show ∀ l, (runCoinTree (next l) c Φ₀ Φ₁).map = ((next l).channel Φ₀ Φ₀).map from
      fun l => ih l c hc]

theorem runCoinTree_output_continuous {H O B Ω : Type}
    [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] [TopologicalSpace Ω] {Q : ℕ}
    (tree : ICO.BudgetQueryTree.Tree H O Q B) (c : Fin Q → Bool)
    (Φ₀ Φ₁ : Ω → Channel H H)
    (hΦ₀ : Continuous (fun p : Ω × CMatrix H => (Φ₀ p.1).map p.2))
    (hΦ₁ : Continuous (fun p : Ω × CMatrix H => (Φ₁ p.1).map p.2))
    (X : Ω → CMatrix B) (hX : Continuous X) :
    Continuous (fun ω => (runCoinTree tree c (Φ₀ ω) (Φ₁ ω)).map (X ω)) := by
  induction tree with
  | stop after => exact after.map.continuous_of_finiteDimensional.comp hX
  | query _ after ih =>
    apply ih (fun i => c i.succ)
    by_cases h0 : c 0 = true
    · simpa [h0] using hΦ₁.comp (continuous_id.prodMk hX)
    · have hf : c 0 = false := Bool.eq_false_iff.mpr h0
      simpa [hf] using hΦ₀.comp (continuous_id.prodMk hX)
  | node I next ih =>
    change Continuous (fun ω => ICO.InstrumentCompression.adaptiveMap I
      (fun l => runCoinTree (next l) c (Φ₀ ω) (Φ₁ ω)) (X ω))
    simp_rw [ICO.InstrumentCompression.adaptiveMap_apply]
    apply continuous_finsetSum
    intro l _
    apply ih l c
    exact (continuous_const.matrix_mul hX).matrix_mul continuous_const

/-- Compile any `Q`-budget tree along a coin tape `c` with `tapeCount c ≤ L` into an
`L`-budget tree on the strong device (eliding `false` identity steps). -/
def truncateTree {H O B : Type} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] {Q : ℕ}
    (tree : ICO.BudgetQueryTree.Tree H O Q B) :
    (c : Fin Q → Bool) → (L : ℕ) → tapeCount c ≤ L →
      ICO.BudgetQueryTree.Tree H O L B := by
  induction tree with
  | stop after => exact fun _ _ _ => .stop after
  | query _ after ih =>
    intro c L hc
    by_cases h0 : c 0 = true
    · cases L with
      | zero =>
        exfalso
        simp [tapeCount, h0] at hc
      | succ L' =>
        have hc' : tapeCount (fun i => c i.succ) ≤ L' := by
          simp [tapeCount, h0] at hc
          omega
        exact .query false (ih (fun i => c i.succ) L' hc')
    · have hc' : tapeCount (fun i => c i.succ) ≤ L := by
        have hf : c 0 = false := Bool.eq_false_iff.mpr h0
        simpa [tapeCount, hf] using hc
      exact ih (fun i => c i.succ) L hc'
  | node I next ih =>
    exact fun c L hc => .node I (fun l => ih l c L hc)

theorem truncateTree_channel {H O B : Type}
    [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q : ℕ} (tree : ICO.BudgetQueryTree.Tree H O Q B)
    (c : Fin Q → Bool) (L : ℕ) (hc : tapeCount c ≤ L) (Ψ : Channel H H) :
    ((truncateTree tree c L hc).channel Ψ Ψ).map =
      (runCoinTree tree c (Channel.idChannel H) Ψ).map := by
  induction tree generalizing L with
  | stop after => rfl
  | query b after ih =>
    change ((truncateTree (.query b after) c L hc).channel Ψ Ψ).map =
      (runCoinTree after (fun i => c i.succ) (Channel.idChannel H) Ψ).map.comp
        (if c 0 then Ψ else Channel.idChannel H).map
    by_cases h0 : c 0 = true
    · cases L with
      | zero =>
        exfalso
        simp [tapeCount, h0] at hc
      | succ L' =>
        have hc' : tapeCount (fun i => c i.succ) ≤ L' := by
          simp [tapeCount, h0] at hc
          omega
        have htrunc :
            truncateTree (.query b after) c (L' + 1) hc =
              .query false (truncateTree after (fun i => c i.succ) L' hc') := by
          simp [truncateTree, h0]
        rw [htrunc, h0]
        change ((truncateTree after (fun i => c i.succ) L' hc').channel Ψ Ψ).map.comp Ψ.map =
          (runCoinTree after (fun i => c i.succ) (Channel.idChannel H) Ψ).map.comp Ψ.map
        rw [ih (fun i => c i.succ) L' hc']
    · have hf : c 0 = false := Bool.eq_false_iff.mpr h0
      have hc' : tapeCount (fun i => c i.succ) ≤ L := by
        simpa [tapeCount, hf] using hc
      have htrunc :
          truncateTree (.query b after) c L hc =
            truncateTree after (fun i => c i.succ) L hc' := by
        simp [truncateTree, h0]
      rw [htrunc, hf]
      simp only [Bool.false_eq_true, ↓reduceIte, ICO.DiamondPreprocessing.identity_map,
        LinearMap.comp_id]
      exact ih (fun i => c i.succ) L hc'
  | node I next ih =>
    ext X i j
    change ICO.InstrumentCompression.adaptiveMap I
        (fun l => (truncateTree (next l) c L hc).channel Ψ Ψ) X i j =
      ICO.InstrumentCompression.adaptiveMap I
        (fun l => runCoinTree (next l) c (Channel.idChannel H) Ψ) X i j
    simp only [ICO.InstrumentCompression.adaptiveMap_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact congrArg (fun f : MatrixMap _ O => f (I.op l * X * (I.op l).conjTranspose) i j)
      (ih l c L hc)

/-- Replace each query in an `L`-budget tree by a call to the first box followed by a call
to the second box (`second ∘ first`), producing a `(2 * L)`-budget two-box tree. -/
def pairQueries {H O B : Type} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] {q : ℕ}
    (tree : ICO.BudgetQueryTree.Tree H O q B) :
    ICO.BudgetQueryTree.Tree H O (2 * q) B := by
  induction tree with
  | stop after => exact .stop after
  | query _ after ih => exact .query false (.query true ih)
  | node I next ih => exact .node I ih

theorem pairQueries_channel {H O B : Type} [Fintype H] [DecidableEq H]
    [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B] {q : ℕ}
    (tree : ICO.BudgetQueryTree.Tree H O q B) (first second : Channel H H) :
    ((pairQueries tree).channel first second).map =
      (tree.channel (second.comp first) (second.comp first)).map := by
  induction tree with
  | stop after => rfl
  | query b after ih =>
    change (((pairQueries after).channel first second).map.comp second.map).comp first.map =
      (after.channel (second.comp first) (second.comp first)).map.comp
        (if b then second.comp first else second.comp first).map
    rw [ih]
    cases b <;> rfl
  | node I next ih =>
    ext X i j
    change ICO.InstrumentCompression.adaptiveMap I
        (fun l => (pairQueries (next l)).channel first second) X i j =
      ICO.InstrumentCompression.adaptiveMap I
        (fun l => (next l).channel (second.comp first) (second.comp first)) X i j
    simp only [ICO.InstrumentCompression.adaptiveMap_apply]
    simp_rw [show ∀ l, ((pairQueries (next l)).channel first second).map =
      ((next l).channel (second.comp first) (second.comp first)).map from ih]

theorem hidden_comp_self [Nonempty A] {M : Type} [Fintype M] [DecidableEq M]
    (U : Matrix.unitaryGroup A ℂ) :
    (ICO.BudgetContinuity.hidden (M := M) U).comp
      (ICO.BudgetContinuity.hidden (M := M) U) =
      ICO.BudgetContinuity.hidden (M := M) U := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  let Δ := krausChannel (basisProjection (U : CMatrix A))
    (hidden_basis_kraus_complete _ U.property.1 U.property.2)
  have hhid (Y : CMatrix (A × M)) :
      (ICO.BudgetContinuity.hidden (M := M) U).map Y =
        (Δ.prod (Channel.idChannel M)).map Y :=
    (prod_id_map_eq_oracleMap _ _ Y).symm
  ext X ⟨a₁, m₁⟩ ⟨a₂, m₂⟩
  change (ICO.BudgetContinuity.hidden (M := M) U).map
      ((ICO.BudgetContinuity.hidden (M := M) U).map X) (a₁, m₁) (a₂, m₂) =
    (ICO.BudgetContinuity.hidden (M := M) U).map X (a₁, m₁) (a₂, m₂)
  rw [hhid X, hhid ((Δ.prod (Channel.idChannel M)).map X)]
  change MatrixMap.kron Δ.map (Channel.idChannel M).map
      (MatrixMap.kron Δ.map (Channel.idChannel M).map X) (a₁, m₁) (a₂, m₂) =
    MatrixMap.kron Δ.map (Channel.idChannel M).map X (a₁, m₁) (a₂, m₂)
  rw [MatrixMap.kron_comp_apply]
  simp only [ICO.DiamondPreprocessing.identity_map, LinearMap.comp_id]
  have hΔ : Δ.map.comp Δ.map = Δ.map := by
    apply LinearMap.ext
    intro S
    change MatrixMap.ofKraus (basisProjection (U : CMatrix A))
        (MatrixMap.ofKraus (basisProjection (U : CMatrix A)) S) =
      MatrixMap.ofKraus (basisProjection (U : CMatrix A)) S
    rw [ICO.C6OTOCChannelBoundary.dephasing_expansion (U : CMatrix A) S, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    change (∑ j : A, basisProjection (U : CMatrix A) j * basisProjection (U : CMatrix A) i *
        (basisProjection (U : CMatrix A) j).conjTranspose) = basisProjection (U : CMatrix A) i
    rw [Finset.sum_eq_single i]
    · rw [basisProjection_hermitian, basisProjection_mul _ U.property.1, if_pos rfl,
        basisProjection_mul _ U.property.1, if_pos rfl]
    · intro j _ hj
      rw [basisProjection_hermitian, basisProjection_mul _ U.property.1, if_neg hj,
        Matrix.zero_mul]
    · simp
  rw [hΔ]

theorem hidden_mub_comp [Nonempty A] {M : Type} [Fintype M] [DecidableEq M]
    (U V : Matrix.unitaryGroup A ℂ) (hUV : MutuallyUnbiased U V) :
    (ICO.BudgetContinuity.hidden (M := M) V).comp
      (ICO.BudgetContinuity.hidden (M := M) U) =
      ICO.RecordingDepolarizing.withMemory (α := A) (μ := M) := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  let ΔU := krausChannel (basisProjection (U : CMatrix A))
    (hidden_basis_kraus_complete _ U.property.1 U.property.2)
  let ΔV := krausChannel (basisProjection (V : CMatrix A))
    (hidden_basis_kraus_complete _ V.property.1 V.property.2)
  have hhidU (Y : CMatrix (A × M)) :
      (ICO.BudgetContinuity.hidden (M := M) U).map Y =
        (ΔU.prod (Channel.idChannel M)).map Y :=
    (prod_id_map_eq_oracleMap _ _ Y).symm
  have hhidV (Y : CMatrix (A × M)) :
      (ICO.BudgetContinuity.hidden (M := M) V).map Y =
        (ΔV.prod (Channel.idChannel M)).map Y :=
    (prod_id_map_eq_oracleMap _ _ Y).symm
  ext X ⟨a₁, m₁⟩ ⟨a₂, m₂⟩
  change (ICO.BudgetContinuity.hidden (M := M) V).map
      ((ICO.BudgetContinuity.hidden (M := M) U).map X) (a₁, m₁) (a₂, m₂) =
    (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)).map X (a₁, m₁) (a₂, m₂)
  rw [hhidU X, hhidV ((ΔU.prod (Channel.idChannel M)).map X)]
  change MatrixMap.kron ΔV.map (Channel.idChannel M).map
      (MatrixMap.kron ΔU.map (Channel.idChannel M).map X) (a₁, m₁) (a₂, m₂) =
    MatrixMap.kron (ICO.RecordingDepolarizing.depolarizing (α := A)).map
      (Channel.idChannel M).map X (a₁, m₁) (a₂, m₂)
  rw [MatrixMap.kron_comp_apply]
  have hVU : ΔV.map.comp ΔU.map = (ICO.RecordingDepolarizing.depolarizing (α := A)).map := by
    apply LinearMap.ext
    intro S
    ext i j
    change MatrixMap.ofKraus (basisProjection (V : CMatrix A))
        (MatrixMap.ofKraus (basisProjection (U : CMatrix A)) S) i j =
      (ICO.RecordingDepolarizing.depolarizing (α := A)).map S i j
    rw [ICO.C6OTOCChannelBoundary.mub_composition V U
      (ICO.C6OTOCChannelBoundary.mutuallyUnbiased_symm U V hUV) S,
      ICO.RecordingDepolarizing.depolarizing_entry]
    by_cases hij : i = j <;> simp [hij]
  rw [hVU]
  simp only [ICO.DiamondPreprocessing.identity_map, LinearMap.comp_id]

/-- `L`-step acceptance gap between the completely depolarizing channel `Ω` and the
Haar-averaged dephasing channel `Λ = (id + d Ω) / (d + 1)` is at most `L / (d + 1)`. -/
theorem depolarizing_hybrid_accept_gap [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {L : ℕ} (T : BinaryHypothesisTest O)
    (tree : ICO.BudgetQueryTree.Tree (A × M) O L B) (ρ : State B) :
    ICO.BudgetTesting.acceptance T tree ρ
        (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M))
        (ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)) -
      ICO.BudgetTesting.acceptance T tree ρ
        (haarDepolarizingWithMemory (A := A) M)
        (haarDepolarizingWithMemory (A := A) M) ≤
      (L : ℝ) / ((Fintype.card A : ℝ) + 1) := by
  let Ω_M := ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)
  let q : ℝ := 1 / ((Fintype.card A : ℝ) + 1)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    change 1 / ((Fintype.card A : ℝ) + 1) ≤ 1
    rw [div_le_iff₀ (by positivity)]
    have hd0 : (0 : ℝ) ≤ Fintype.card A := Nat.cast_nonneg _
    linarith
  have hΩ_exp :
      ICO.BudgetTesting.acceptance T tree ρ Ω_M Ω_M =
        ∑ c : Fin L → Bool,
          bernoulliWeight q c *
            (T.acceptProb ((tree.channel Ω_M Ω_M).applyState ρ) : ℝ) := by
    rw [ICO.BudgetTesting.acceptance_eq, ← Finset.sum_mul, sum_bernoulliWeight, one_mul]
  have hΛ_exp := tree_acceptance_convex_combination T tree ρ
    (haarDepolarizingWithMemory (A := A) M) Ω_M (Channel.idChannel (A × M)) q
    (haarDepolarizingWithMemory_map (A := A) (M := M))
  rw [hΩ_exp, hΛ_exp, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : Fin L → Bool => 0 < tapeCount c)]
  have hzero :
      (∑ c ∈ Finset.univ.filter (fun c : Fin L → Bool => ¬ 0 < tapeCount c),
        bernoulliWeight q c *
          ((T.acceptProb ((tree.channel Ω_M Ω_M).applyState ρ) : ℝ) -
            (T.acceptProb ((runCoinTree tree c Ω_M (Channel.idChannel (A × M))).applyState ρ) : ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have hc0 : tapeCount c = 0 := by
      have hnot := (Finset.mem_filter.mp hc).2
      omega
    have hst :
        (runCoinTree tree c Ω_M (Channel.idChannel (A × M))).applyState ρ =
          (tree.channel Ω_M Ω_M).applyState ρ := by
      apply State.ext
      exact congrArg (fun f : MatrixMap B O => f ρ.matrix)
        (runCoinTree_zero_count tree c Ω_M (Channel.idChannel (A × M)) hc0)
    rw [hst, sub_self, mul_zero]
  rw [hzero, add_zero]
  calc
    (∑ c ∈ Finset.univ.filter (fun c : Fin L → Bool => 0 < tapeCount c),
        bernoulliWeight q c *
          ((T.acceptProb ((tree.channel Ω_M Ω_M).applyState ρ) : ℝ) -
            (T.acceptProb ((runCoinTree tree c Ω_M (Channel.idChannel (A × M))).applyState ρ) : ℝ))) ≤
      ∑ c ∈ Finset.univ.filter (fun c : Fin L → Bool => 0 < tapeCount c),
        bernoulliWeight q c := by
      refine Finset.sum_le_sum fun c _ => ?_
      have h1 : (T.acceptProb ((tree.channel Ω_M Ω_M).applyState ρ) : ℝ) ≤ 1 := by
        exact_mod_cast T.prob_le_one _ true
      have h0 : 0 ≤ (T.acceptProb ((runCoinTree tree c Ω_M (Channel.idChannel (A × M))).applyState ρ) : ℝ) :=
        NNReal.coe_nonneg _
      exact mul_le_of_le_one_right (bernoulliWeight_nonneg hq0 hq1 c) (by linarith)
    _ ≤ q * (L : ℝ) / (((0 : ℕ) : ℝ) + 1) := sum_bernoulliWeight_filter_gt (Q := L) (L := 0) hq0 hq1
    _ = (L : ℝ) / ((Fintype.card A : ℝ) + 1) := by
      dsimp [q]
      push_cast
      ring

/-- Strong-device `L`-call acceptance-gap bound from Section 5.3 (`\label{sec:validation}`):
for any `L ≤ d^{1/16} / 200` and `L`-budget adaptive tree, the Haar-averaged acceptance on
`Δ_U` exceeds the acceptance on `Λ` by at most `53 / 2000`. -/
theorem validation_strong_device_accept_gap [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {L n : ℕ} (hd : Fintype.card A = 2 ^ n)
    (hLd : (L : ℝ) ≤ (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / 200)
    (T : BinaryHypothesisTest O)
    (tree : ICO.BudgetQueryTree.Tree (A × M) O L B) (ρ : State B) :
    (∫ U, ICO.BudgetTesting.acceptance T tree ρ
        (ICO.BudgetContinuity.hidden (M := M) U)
        (ICO.BudgetContinuity.hidden (M := M) U) ∂unitaryHaarMeasure (a := A)) -
      ICO.BudgetTesting.acceptance T tree ρ
        (haarDepolarizingWithMemory (A := A) M)
        (haarDepolarizingWithMemory (A := A) M) ≤ 53 / 2000 := by
  by_cases hL0 : L = 0
  · subst hL0
    have heq (U : Matrix.unitaryGroup A ℂ) :
        ICO.BudgetTesting.acceptance T tree ρ
          (ICO.BudgetContinuity.hidden (M := M) U)
          (ICO.BudgetContinuity.hidden (M := M) U) =
        ICO.BudgetTesting.acceptance T tree ρ
          (haarDepolarizingWithMemory (A := A) M)
          (haarDepolarizingWithMemory (A := A) M) :=
      congrArg (fun f : MatrixMap B O => ICO.BornAverage.acceptCLM T (f ρ.matrix))
        (ICO.BudgetHaarBound.zero_budget_map tree rfl _ _ _ _)
    simp_rw [heq]
    simp only [integral_const, probReal_univ, one_smul, sub_self]
    norm_num
  · have hL1 : 1 ≤ L := by omega
    obtain ⟨H, hH⟩ := ICO.C6FlatUnitary.flat_unitary (A := A) n hd
    let Ω_M := ICO.RecordingDepolarizing.withMemory (α := A) (μ := M)
    let r : ℝ := (Fintype.card A : ℝ) ^ (1 / 16 : ℝ)
    have hrpow : r ^ 16 = (Fintype.card A : ℝ) :=
      ICO.QuantumDecision.radius_power_sixteen (Fintype.card A) (by positivity)
    have hq1 : 1 ≤ 2 * L := by omega
    have hqr : ((2 * L : ℕ) : ℝ) ≤ r / 100 := by
      push_cast
      linarith
    have hr_dims := ICO.C6Bounds.radius_dimensions (by exact_mod_cast hq1) hqr
    have hfour : 4 * (2 * L) ≤ Fintype.card A := by
      have hqreal : (1 : ℝ) ≤ (2 * L : ℕ) := by exact_mod_cast hq1
      have hr1 : 1 ≤ r := by linarith
      have h14 : r ≤ r ^ 4 := by
        simpa using pow_le_pow_right₀ hr1 (show (1 : ℕ) ≤ 4 by norm_num)
      have hr4_le : r ^ 4 ≤ r ^ 16 - 2 * ((2 * L : ℕ) : ℝ) := hr_dims.2.2
      exact_mod_cast (show (4 * (2 * L : ℕ) : ℝ) ≤ Fintype.card A by linarith)
    let t2 := pairQueries tree
    have hdist_u := ICO.C6OperationalDecision.same_mub_distance t2 ρ H hq1 hfour
    have hunif := ICO.C6UniformBounds.uniformError_le hq1 hqr
    rw [hrpow] at hunif
    have hdist2 :
        normalizedTraceDistance (ICO.C6Decision.sameDensity t2 ρ)
          (ICO.C6Decision.mubDensity t2 ρ H) ≤ 215 / 10000 :=
      hdist_u.trans hunif
    have hsame_eq :
        ICO.C6Decision.sameDensity t2 ρ =
          ∫ U, ((tree.channel (ICO.BudgetContinuity.hidden (M := M) U)
            (ICO.BudgetContinuity.hidden (M := M) U)).applyState ρ).matrix
            ∂unitaryHaarMeasure (a := A) := by
      unfold ICO.C6Decision.sameDensity
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      have hp := congrArg (fun f : MatrixMap B O => f ρ.matrix)
        (pairQueries_channel tree (ICO.BudgetContinuity.hidden (M := M) U)
          (ICO.BudgetContinuity.hidden (M := M) U))
      rw [hidden_comp_self U] at hp
      exact hp
    have hmub_eq :
        ICO.C6Decision.mubDensity t2 ρ H = ((tree.channel Ω_M Ω_M).applyState ρ).matrix := by
      unfold ICO.C6Decision.mubDensity
      have hconst (U : Matrix.unitaryGroup A ℂ) :
          (t2.channel (ICO.BudgetContinuity.hidden (M := M) U)
              (ICO.BudgetContinuity.hidden (M := M) (U * H))).map ρ.matrix =
            (tree.channel Ω_M Ω_M).map ρ.matrix := by
        have hp := congrArg (fun f : MatrixMap B O => f ρ.matrix)
          (pairQueries_channel tree (ICO.BudgetContinuity.hidden (M := M) U)
            (ICO.BudgetContinuity.hidden (M := M) (U * H)))
        rw [hidden_mub_comp U (U * H) (flat_translate U H hH)] at hp
        exact hp
      simp_rw [hconst]
      simp only [integral_const, probReal_univ, one_smul]
      rfl
    rw [hsame_eq, hmub_eq] at hdist2
    let F := fun U : Matrix.unitaryGroup A ℂ =>
      (tree.channel (ICO.BudgetContinuity.hidden (M := M) U)
        (ICO.BudgetContinuity.hidden (M := M) U)).applyState ρ
    have hiF : Integrable (fun U => (F U).matrix) (unitaryHaarMeasure (a := A)) :=
      (ICO.BudgetContinuity.luders_output_continuous tree ρ.matrix).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hgap_Ω := (ICO.BornAverage.mean_accept_gap_le T F
      ((tree.channel Ω_M Ω_M).applyState ρ) hiF).trans hdist2
    have hgap_Ω' :
        (∫ U, ICO.BudgetTesting.acceptance T tree ρ
            (ICO.BudgetContinuity.hidden (M := M) U)
            (ICO.BudgetContinuity.hidden (M := M) U) ∂unitaryHaarMeasure (a := A)) -
          ICO.BudgetTesting.acceptance T tree ρ Ω_M Ω_M ≤ 215 / 10000 := by
      simpa only [F, ← ICO.BudgetTesting.acceptance_eq] using hgap_Ω
    have hgap_Λ := depolarizing_hybrid_accept_gap T tree ρ
    have hr_le_d : r ≤ (Fintype.card A : ℝ) := by
      have hr1 : 1 ≤ r := by
        have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
        linarith
      have h1_16 : r ≤ r ^ 16 := by
        simpa using pow_le_pow_right₀ hr1 (show (1 : ℕ) ≤ 16 by norm_num)
      rwa [hrpow] at h1_16
    have hhybrid : (L : ℝ) / ((Fintype.card A : ℝ) + 1) ≤ 1 / 200 := by
      have hd1_pos : (0 : ℝ) < (Fintype.card A : ℝ) + 1 := by positivity
      rw [div_le_iff₀ hd1_pos]
      linarith
    linarith

/-- **Theorem 3 (`\label{thm:c6}`), balanced-prior operational ordinary query lower bound
(`\label{sec:validation}`)**:
For `d = Fintype.card A = 2^n`, `0 < p ≤ 1`, and any `Q`-budget ordinary adaptive strategy
`(tree, ρ, T)` querying a single unknown device, if `T` achieves balanced Haar-prior
success probability at least `2 / 3` between `\mathcal{E}_{p,U}` and `\mathcal{M}_p`,
then `d^{1/16} / (1400 p) < Q`. -/
theorem validation_ordinary_balanced_query_lower_bound [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q n : ℕ} (hd : Fintype.card A = 2 ^ n)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (T : BinaryHypothesisTest O)
    (tree : ICO.BudgetQueryTree.Tree (A × M) O Q B) (ρ : State B)
    (hsucc : (2 / 3 : ℝ) ≤
      (1 / 2 : ℝ) *
        ((∫ U, ICO.BudgetTesting.acceptance T tree ρ
            (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U)
            (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U) ∂unitaryHaarMeasure (a := A)) +
          (1 - ICO.BudgetTesting.acceptance T tree ρ
            (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1)
            (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1)))) :
    (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / (1400 * p) < (Q : ℝ) := by
  let hp0_le : 0 ≤ p := le_of_lt hp0
  let μ := unitaryHaarMeasure (a := A)
  let r : ℝ := (Fintype.card A : ℝ) ^ (1 / 16 : ℝ)
  let L : ℕ := ⌊r / 200⌋₊
  have hLd : (L : ℝ) ≤ r / 200 := Nat.floor_le (by positivity)
  have hL_floor : r / 200 < (L : ℝ) + 1 := Nat.lt_floor_add_one (r / 200)
  have hgap_lb :
      (1 / 3 : ℝ) ≤
        (∫ U, ICO.BudgetTesting.acceptance T tree ρ
            (dephasingNoiseWithMemory M hp0_le hp1 U)
            (dephasingNoiseWithMemory M hp0_le hp1 U) ∂μ) -
          ICO.BudgetTesting.acceptance T tree ρ
            (depolarizingModelWithMemory (A := A) M hp0_le hp1)
            (depolarizingModelWithMemory (A := A) M hp0_le hp1) := by
    linarith
  let g (c : Fin Q → Bool) (U : Matrix.unitaryGroup A ℂ) : ℝ :=
    (T.acceptProb ((runCoinTree tree c (Channel.idChannel (A × M))
      (ICO.BudgetContinuity.hidden (M := M) U)).applyState ρ) : ℝ)
  let m (c : Fin Q → Bool) : ℝ :=
    (T.acceptProb ((runCoinTree tree c (Channel.idChannel (A × M))
      (haarDepolarizingWithMemory (A := A) M)).applyState ρ) : ℝ)
  have hg_int (c : Fin Q → Bool) : Integrable (g c) μ := by
    have hcont_mat :
        Continuous (fun U : Matrix.unitaryGroup A ℂ =>
          (runCoinTree tree c (Channel.idChannel (A × M))
            (ICO.BudgetContinuity.hidden (M := M) U)).map ρ.matrix) :=
      runCoinTree_output_continuous tree c
        (fun _ => Channel.idChannel (A × M))
        (ICO.BudgetContinuity.hidden (M := M))
        (ICO.BudgetContinuity.fixed_continuous (Channel.idChannel (A × M)))
        ICO.BudgetContinuity.hidden_continuous
        (fun _ => ρ.matrix) continuous_const
    have hcont : Continuous (fun U => ICO.BornAverage.acceptCLM T
        ((runCoinTree tree c (Channel.idChannel (A × M))
          (ICO.BudgetContinuity.hidden (M := M) U)).map ρ.matrix)) :=
      (ICO.BornAverage.acceptCLM T).continuous.comp hcont_mat
    exact (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).congr
      (Filter.Eventually.of_forall fun U =>
        ICO.BornAverage.accept_eq T
          ((runCoinTree tree c (Channel.idChannel (A × M))
            (ICO.BudgetContinuity.hidden (M := M) U)).applyState ρ))
  have hE_pt (U : Matrix.unitaryGroup A ℂ) :
      ICO.BudgetTesting.acceptance T tree ρ
        (dephasingNoiseWithMemory M hp0_le hp1 U)
        (dephasingNoiseWithMemory M hp0_le hp1 U) =
      ∑ c : Fin Q → Bool, bernoulliWeight p c * g c U :=
    tree_acceptance_convex_combination T tree ρ
      (dephasingNoiseWithMemory M hp0_le hp1 U)
      (Channel.idChannel (A × M)) (ICO.BudgetContinuity.hidden (M := M) U) p
      (dephasingNoiseWithMemory_map hp0_le hp1 U)
  have hE_int :
      (∫ U, ICO.BudgetTesting.acceptance T tree ρ
          (dephasingNoiseWithMemory M hp0_le hp1 U)
          (dephasingNoiseWithMemory M hp0_le hp1 U) ∂μ) =
        ∑ c : Fin Q → Bool, bernoulliWeight p c * (∫ U, g c U ∂μ) := by
    simp_rw [hE_pt]
    rw [integral_finsetSum _ (fun c _ => (hg_int c).const_mul (bernoulliWeight p c))]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact integral_const_mul (bernoulliWeight p c) (g c)
  have hM_exp :
      ICO.BudgetTesting.acceptance T tree ρ
        (depolarizingModelWithMemory (A := A) M hp0_le hp1)
        (depolarizingModelWithMemory (A := A) M hp0_le hp1) =
      ∑ c : Fin Q → Bool, bernoulliWeight p c * m c :=
    tree_acceptance_convex_combination T tree ρ
      (depolarizingModelWithMemory (A := A) M hp0_le hp1)
      (Channel.idChannel (A × M)) (haarDepolarizingWithMemory (A := A) M) p
      (depolarizingModelWithMemory_map hp0_le hp1)
  have hdiff_sum :
      (∫ U, ICO.BudgetTesting.acceptance T tree ρ
          (dephasingNoiseWithMemory M hp0_le hp1 U)
          (dephasingNoiseWithMemory M hp0_le hp1 U) ∂μ) -
        ICO.BudgetTesting.acceptance T tree ρ
          (depolarizingModelWithMemory (A := A) M hp0_le hp1)
          (depolarizingModelWithMemory (A := A) M hp0_le hp1) =
      ∑ c : Fin Q → Bool, bernoulliWeight p c * ((∫ U, g c U ∂μ) - m c) := by
    rw [hE_int, hM_exp, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have htail :
      (∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => L < tapeCount c),
        bernoulliWeight p c * ((∫ U, g c U ∂μ) - m c)) ≤
      p * (Q : ℝ) / ((L : ℝ) + 1) := by
    calc
      (∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => L < tapeCount c),
          bernoulliWeight p c * ((∫ U, g c U ∂μ) - m c)) ≤
        ∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => L < tapeCount c),
          bernoulliWeight p c := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hg_le1 : (∫ U, g c U ∂μ) ≤ 1 := by
          have hpt : ∀ U, g c U ≤ 1 := fun U => by
            exact_mod_cast T.prob_le_one _ true
          have hmono := integral_mono (hg_int c) (integrable_const (1 : ℝ)) hpt
          simpa [integral_const, probReal_univ] using hmono
        have hm_nonneg : 0 ≤ m c := NNReal.coe_nonneg _
        exact mul_le_of_le_one_right (bernoulliWeight_nonneg hp0_le hp1 c) (by linarith)
      _ ≤ p * (Q : ℝ) / ((L : ℝ) + 1) := sum_bernoulliWeight_filter_gt hp0_le hp1
  have hbody :
      (∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => ¬ L < tapeCount c),
        bernoulliWeight p c * ((∫ U, g c U ∂μ) - m c)) ≤
      53 / 2000 := by
    calc
      (∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => ¬ L < tapeCount c),
          bernoulliWeight p c * ((∫ U, g c U ∂μ) - m c)) ≤
        ∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => ¬ L < tapeCount c),
          bernoulliWeight p c * (53 / 2000) := by
        refine Finset.sum_le_sum fun c hc => ?_
        have hc_le : tapeCount c ≤ L := by
          have hnot := (Finset.mem_filter.mp hc).2
          omega
        let tc := truncateTree tree c L hc_le
        have hgc (U : Matrix.unitaryGroup A ℂ) :
            g c U = ICO.BudgetTesting.acceptance T tc ρ
              (ICO.BudgetContinuity.hidden (M := M) U)
              (ICO.BudgetContinuity.hidden (M := M) U) := by
          rw [ICO.BudgetTesting.acceptance_eq]
          have hst :
              (runCoinTree tree c (Channel.idChannel (A × M))
                  (ICO.BudgetContinuity.hidden (M := M) U)).applyState ρ =
                (tc.channel (ICO.BudgetContinuity.hidden (M := M) U)
                  (ICO.BudgetContinuity.hidden (M := M) U)).applyState ρ := by
            apply State.ext
            exact (congrArg (fun f : MatrixMap B O => f ρ.matrix)
              (truncateTree_channel tree c L hc_le (ICO.BudgetContinuity.hidden (M := M) U))).symm
          rw [← hst]
        have hmc :
            m c = ICO.BudgetTesting.acceptance T tc ρ
              (haarDepolarizingWithMemory (A := A) M)
              (haarDepolarizingWithMemory (A := A) M) := by
          rw [ICO.BudgetTesting.acceptance_eq]
          have hst :
              (runCoinTree tree c (Channel.idChannel (A × M))
                  (haarDepolarizingWithMemory (A := A) M)).applyState ρ =
                (tc.channel (haarDepolarizingWithMemory (A := A) M)
                  (haarDepolarizingWithMemory (A := A) M)).applyState ρ := by
            apply State.ext
            exact (congrArg (fun f : MatrixMap B O => f ρ.matrix)
              (truncateTree_channel tree c L hc_le (haarDepolarizingWithMemory (A := A) M))).symm
          rw [← hst]
        have hstrong := validation_strong_device_accept_gap (M := M) hd hLd T tc ρ
        simp_rw [hgc, hmc]
        exact mul_le_mul_of_nonneg_left hstrong (bernoulliWeight_nonneg hp0_le hp1 c)
      _ = (∑ c ∈ Finset.univ.filter (fun c : Fin Q → Bool => ¬ L < tapeCount c),
            bernoulliWeight p c) * (53 / 2000) := by
        rw [← Finset.sum_mul]
      _ ≤ (∑ c : Fin Q → Bool, bernoulliWeight p c) * (53 / 2000) := by
        refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
        exact Finset.sum_le_univ_sum_of_nonneg fun c => bernoulliWeight_nonneg hp0_le hp1 c
      _ = 53 / 2000 := by rw [sum_bernoulliWeight, one_mul]
  have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun c : Fin Q → Bool => L < tapeCount c)
    (fun c => bernoulliWeight p c * ((∫ U, g c U ∂μ) - m c))).symm
  rw [hdiff_sum, hsplit] at hgap_lb
  have hmarkov : (1841 : ℝ) / 6000 ≤ p * (Q : ℝ) / ((L : ℝ) + 1) := by linarith
  have hmarkov_gt : (1 : ℝ) / 7 < p * (Q : ℝ) / ((L : ℝ) + 1) := by linarith
  have hL1_pos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hpQ_mul : (1 / 7 : ℝ) * ((L : ℝ) + 1) < p * (Q : ℝ) :=
    (lt_div_iff₀ hL1_pos).mp hmarkov_gt
  have hr_lt_pQ : (r / 200) / 7 < p * (Q : ℝ) := by linarith
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 1400 * p)]
  linarith

/-- **Theorem 3 (`\label{thm:c6}`), unconditional operational ordinary query lower bound
(`\label{sec:validation}`)**:
Let `d = Fintype.card A = 2^n` and `0 < p ≤ 1`. Every ordinary adaptive strategy with
query budget `Q`, arbitrary finite quantum memory `M`, mixed initial state `ρ : State B`,
and binary final measurement `T : BinaryHypothesisTest O` that decides between the
depolarizing model `\mathcal{M}_p = (1 - p) id + p Λ` and `\mathcal{E}_{p,U} = (1 - p) id + p Δ_U`
with success probability at least `2 / 3` on `\mathcal{M}_p` and on every unitary `U`
satisfies `d^{1/16} / (1400 p) < Q`. -/
theorem validation_ordinary_query_lower_bound [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q n : ℕ} (hd : Fintype.card A = 2 ^ n)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (T : BinaryHypothesisTest O)
    (tree : ICO.BudgetQueryTree.Tree (A × M) O Q B) (ρ : State B)
    (hhigh : ∀ U : Matrix.unitaryGroup A ℂ,
      (2 / 3 : ℝ) ≤ ICO.BudgetTesting.acceptance T tree ρ
        (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U)
        (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U))
    (hlow : ICO.BudgetTesting.acceptance T tree ρ
      (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1)
      (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1) ≤ 1 / 3) :
    (Fintype.card A : ℝ) ^ (1 / 16 : ℝ) / (1400 * p) < (Q : ℝ) := by
  let hp0_le : 0 ≤ p := le_of_lt hp0
  have hdeph_cont :
      Continuous (fun ux : Matrix.unitaryGroup A ℂ × CMatrix (A × M) =>
        (dephasingNoiseWithMemory M hp0_le hp1 ux.1).map ux.2) := by
    have hfun :
        (fun ux : Matrix.unitaryGroup A ℂ × CMatrix (A × M) =>
          (dephasingNoiseWithMemory M hp0_le hp1 ux.1).map ux.2) =
        (fun ux : Matrix.unitaryGroup A ℂ × CMatrix (A × M) =>
          ((1 - p : ℝ) : ℂ) • ux.2 +
            (p : ℂ) • (ICO.BudgetContinuity.hidden (M := M) ux.1).map ux.2) := by
      ext ⟨U, X⟩ i j
      have hm := dephasingNoiseWithMemory_map hp0_le hp1 U X
      rw [ICO.DiamondPreprocessing.identity_map] at hm
      exact congrFun (congrFun hm i) j
    rw [hfun]
    exact (continuous_const.smul continuous_snd).add
      (continuous_const.smul ICO.BudgetContinuity.hidden_continuous)
  have hout_cont :
      Continuous (fun U : Matrix.unitaryGroup A ℂ =>
        ICO.BudgetTesting.acceptance T tree ρ
          (dephasingNoiseWithMemory M hp0_le hp1 U)
          (dephasingNoiseWithMemory M hp0_le hp1 U)) :=
    (ICO.BornAverage.acceptCLM T).continuous.comp
      (ICO.BudgetContinuity.output_continuous tree
        (dephasingNoiseWithMemory M hp0_le hp1)
        (dephasingNoiseWithMemory M hp0_le hp1)
        hdeph_cont hdeph_cont (fun _ => ρ.matrix) continuous_const)
  have hint :
      Integrable (fun U : Matrix.unitaryGroup A ℂ =>
        ICO.BudgetTesting.acceptance T tree ρ
          (dephasingNoiseWithMemory M hp0_le hp1 U)
          (dephasingNoiseWithMemory M hp0_le hp1 U))
        (unitaryHaarMeasure (a := A)) :=
    hout_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean := ICO.AveragedPromiseDecision.high_mean_ge _ hint hhigh
  apply validation_ordinary_balanced_query_lower_bound hd hp0 hp1 T tree ρ
  change (2 / 3 : ℝ) ≤ ∫ U, ICO.BudgetTesting.acceptance T tree ρ
    (dephasingNoiseWithMemory M hp0_le hp1 U)
    (dephasingNoiseWithMemory M hp0_le hp1 U) ∂unitaryHaarMeasure (a := A) at hmean
  linarith

/-- **Theorem 3 (`\label{thm:c6}`), switch validation upper bound in closed block-parameter
form (`\label{sec:switch-test}`)**:
For any dimension `d = Fintype.card A ≥ 2`, noise rate `0 < p ≤ 1`, and block length
`k : ℕ` with `3 / (2 p) ≤ k` (such as `k = ⌈3 / (2 p)⌉`):
1. The `k`-fold composition `\mathcal{E}_{p,U}^k = \mathcal{E}_{1-(1-p)^k, U}` has
   self-visibility `1`, and `7` switch repetitions accept all `7` times with
   probability `1` (false-rejection error `0`).
2. The `k`-fold composition `\mathcal{M}_p^k = α^k id + (1 - α^k) Ω` with
   `α = 1 - p d / (d + 1)` satisfies `α^k ≤ exp(-1) ≤ (20 / 21)^20`, single-use
   minus probability `p_{-,k} ≥ (3 / 8) (1 - exp(-1))^2 > 1455 / 10000`, and `7`-repetition
   all-plus probability `< 1 / 3`.
3. Total device calls used by the `7` switch runs is `7 * (2 * k) = 14 * k`.
See `validation_switch_block_power_upper_bound` below for the channel-power formulation
directly feeding `channelPow` into the quantum switch. -/
theorem validation_switch_upper_bound [Nonempty A] (hd : 2 ≤ Fintype.card A)
    (U : Matrix.unitaryGroup A ℂ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {k : ℕ} (hk : 3 / (2 * p) ≤ (k : ℝ)) :
    let d : ℝ := Fintype.card A
    let pk : ℝ := 1 - (1 - p) ^ k
    let α : ℝ := 1 - p * d / (d + 1)
    let αk : ℝ := α ^ k
    ∃ (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) (hαk0 : 0 ≤ αk) (hαk1 : αk ≤ 1),
      let stateE := switchedState (dephasingNoiseKraus pk U) (dephasingNoiseKraus pk U)
        (dephasingNoiseKraus_complete hpk0 hpk1 U)
        (dephasingNoiseKraus_complete hpk0 hpk1 U) mixedState
      let stateM := switchedState (depolarizingModelKraus (A := A) αk)
        (depolarizingModelKraus (A := A) αk)
        (depolarizingModelKraus_complete hαk0 hαk1)
        (depolarizingModelKraus_complete hαk0 hαk1) mixedState
      (repetitions 7 (controlMeasurement.prob stateE true)
        (QIT.POVM.prob_le_one _ _ _)).real {ω | ∀ i, ω i = true} = 1 ∧
      αk ≤ Real.exp (-1) ∧
      (repetitions 7 (controlMeasurement.prob stateM true)
        (QIT.POVM.prob_le_one _ _ _)).real {ω | ∀ i, ω i = true} < 1 / 3 ∧
      7 * (2 * k) = 14 * k := by
  intro d pk α αk
  have hd_ge2 : (2 : ℝ) ≤ d := by
    change (2 : ℝ) ≤ Fintype.card A
    exact_mod_cast hd
  have hd1_pos : (0 : ℝ) < d + 1 := by linarith
  have h1p0 : 0 ≤ 1 - p := by linarith
  have h1p1 : 1 - p ≤ 1 := by linarith
  have hpk0 : 0 ≤ pk := by
    change 0 ≤ 1 - (1 - p) ^ k
    have hpow : (1 - p) ^ k ≤ 1 := pow_le_one₀ h1p0 h1p1
    linarith
  have hpk1 : pk ≤ 1 := by
    change 1 - (1 - p) ^ k ≤ 1
    have hpow : 0 ≤ (1 - p) ^ k := pow_nonneg h1p0 k
    linarith
  have hα0 : 0 ≤ α := by
    change 0 ≤ 1 - p * d / (d + 1)
    have hle : p * d ≤ d + 1 := by nlinarith
    have hdiv : p * d / (d + 1) ≤ 1 := (div_le_iff₀ hd1_pos).mpr (by linarith)
    linarith
  have hα1 : α ≤ 1 := by
    change 1 - p * d / (d + 1) ≤ 1
    have hnonneg : 0 ≤ p * d / (d + 1) := div_nonneg (by positivity) (le_of_lt hd1_pos)
    linarith
  have hαk0 : 0 ≤ αk := pow_nonneg hα0 k
  have hαk1 : αk ≤ 1 := pow_le_one₀ hα0 hα1
  refine ⟨hpk0, hpk1, hαk0, hαk1, ?_⟩
  intro stateE stateM
  -- 1. True device E_{p,U}^k accepts all 7 repetitions with probability 1
  have hprobE : (controlMeasurement.prob stateE true : ℝ) = 1 :=
    (dephasing_noise_self_visibility hpk0 hpk1 U).2
  have haccE :
      (repetitions 7 (controlMeasurement.prob stateE true)
        (QIT.POVM.prob_le_one _ _ _)).real {ω | ∀ i, ω i = true} = 1 := by
    rw [all_plus_probability, hprobE]
    norm_num
  -- 2. Upper bound α^k ≤ exp(-1)
  have h_ratio : (2 / 3 : ℝ) * p ≤ p * d / (d + 1) := by
    rw [le_div_iff₀ hd1_pos]
    nlinarith
  have hα_le : α ≤ 1 - (2 / 3 : ℝ) * p := by
    change 1 - p * d / (d + 1) ≤ 1 - (2 / 3 : ℝ) * p
    linarith
  have h_exp_step : 1 - (2 / 3 : ℝ) * p ≤ Real.exp (-((2 / 3 : ℝ) * p)) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-((2 / 3 : ℝ) * p))
  have hα_exp : α ≤ Real.exp (-((2 / 3 : ℝ) * p)) := hα_le.trans h_exp_step
  have hαk_exp : αk ≤ Real.exp (-1) := by
    have hpow := pow_le_pow_left₀ hα0 hα_exp k
    rw [← Real.exp_nat_mul] at hpow
    have h_exponent : (k : ℝ) * (-((2 / 3 : ℝ) * p)) ≤ -1 := by
      have hkp : (3 : ℝ) ≤ (k : ℝ) * (2 * p) :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * p)).mp hk
      linarith
    exact hpow.trans (Real.exp_le_exp.mpr h_exponent)
  -- Rational upper bound on exp(-1) via (1 + 1/20)^20 ≤ exp(1)
  have hexp1_lower : (21 / 20 : ℝ) ^ 20 ≤ Real.exp 1 := by
    have hstep : (21 / 20 : ℝ) ≤ Real.exp (1 / 20 : ℝ) := by
      have h := Real.add_one_le_exp (1 / 20 : ℝ)
      linarith
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 21 / 20) hstep 20
    have h20 : ((20 : ℕ) : ℝ) * (1 / 20 : ℝ) = 1 := by norm_num
    rw [← Real.exp_nat_mul, h20] at hpow
    exact hpow
  have hexp_neg1_upper : Real.exp (-1) ≤ (20 / 21 : ℝ) ^ 20 := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    have hmul : (20 / 21 : ℝ) ^ 20 * (21 / 20 : ℝ) ^ 20 = 1 := by norm_num
    calc
      (1 : ℝ) = (20 / 21 : ℝ) ^ 20 * (21 / 20 : ℝ) ^ 20 := hmul.symm
      _ ≤ (20 / 21 : ℝ) ^ 20 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hexp1_lower (by positivity)
  have hαk_rat : αk ≤ 377 / 1000 :=
    hαk_exp.trans (hexp_neg1_upper.trans (by norm_num))
  -- 3. Bound single-use plus probability on M_p^k
  have hprobM_eq :
      (controlMeasurement.prob stateM true : ℝ) =
        1 - (1 / 2 : ℝ) * (1 - αk) ^ 2 * (1 - 1 / d ^ 2) := by
    rw [switch_plus_probability, depolarizing_alpha_self_visibility (A := A) hαk0 hαk1]
    change (1 + (1 - (1 - αk) ^ 2 * (1 - 1 / d ^ 2))) / 2 =
      1 - 1 / 2 * (1 - αk) ^ 2 * (1 - 1 / d ^ 2)
    ring
  have hd2_ge4 : (4 : ℝ) ≤ d ^ 2 := by nlinarith
  have h_inv_d2 : 1 / d ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < d ^ 2)]
    linarith
  have h_one_minus_inv_d2 : (3 / 4 : ℝ) ≤ 1 - 1 / d ^ 2 := by linarith
  have h1_αk_ge : (623 / 1000 : ℝ) ≤ 1 - αk := by linarith
  have h1_αk_sq : (623 / 1000 : ℝ) ^ 2 ≤ (1 - αk) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) h1_αk_ge 2
  have hprobM_le : (controlMeasurement.prob stateM true : ℝ) ≤ 8545 / 10000 := by
    rw [hprobM_eq]
    nlinarith
  have haccM_lt :
      (repetitions 7 (controlMeasurement.prob stateM true)
        (QIT.POVM.prob_le_one _ _ _)).real {ω | ∀ i, ω i = true} < 1 / 3 := by
    rw [all_plus_probability]
    have hpow := pow_le_pow_left₀ (NNReal.coe_nonneg (controlMeasurement.prob stateM true))
      hprobM_le 7
    have hnum : (8545 / 10000 : ℝ) ^ 7 < 1 / 3 := by norm_num
    exact lt_of_le_of_lt hpow hnum
  exact ⟨haccE, hαk_exp, haccM_lt, by ring⟩

/-! ## 4. Channel powers and the `m`-fold block switch test (`\label{sec:switch-test}`, Theorem 3) -/

/-- `m`-fold sequential channel power `Φ^m` of an endomorphism channel `Φ : Channel H H`,
modeling a block of `m` consecutive uses of the device `Φ`
(Section 5.1, `\label{sec:switch-test}`). -/
def channelPow {H : Type} [Fintype H] [DecidableEq H] (Φ : Channel H H) : ℕ → Channel H H
  | 0 => Channel.idChannel H
  | m + 1 => Φ.comp (channelPow Φ m)

@[simp]
theorem channelPow_zero {H : Type} [Fintype H] [DecidableEq H] (Φ : Channel H H) :
    channelPow Φ 0 = Channel.idChannel H := rfl

@[simp]
theorem channelPow_succ {H : Type} [Fintype H] [DecidableEq H] (Φ : Channel H H) (m : ℕ) :
    channelPow Φ (m + 1) = Φ.comp (channelPow Φ m) := rfl

/-- The linear map underlying `channelPow Φ m` is the `m`-fold iterate `(Φ.map)^[m]`. -/
theorem channelPow_map {H : Type} [Fintype H] [DecidableEq H] (Φ : Channel H H) (m : ℕ) :
    ((channelPow Φ m).map : CMatrix H → CMatrix H) = (Φ.map : CMatrix H → CMatrix H)^[m] := by
  induction m with
  | zero =>
    funext X
    simp [channelPow, ICO.DiamondPreprocessing.identity_map]
  | succ m ih =>
    funext X
    change Φ.map ((channelPow Φ m).map X) = (Φ.map : CMatrix H → CMatrix H)^[m + 1] X
    rw [Function.iterate_succ_apply']
    exact congrArg Φ.map (congrFun ih X)

theorem channelPow_map_apply {H : Type} [Fintype H] [DecidableEq H]
    (Φ : Channel H H) (m : ℕ) (X : CMatrix H) :
    (channelPow Φ m).map X = (Φ.map : CMatrix H → CMatrix H)^[m] X :=
  congrFun (channelPow_map Φ m) X

/-- General power law for a convex combination `α id + (1 - α) Δ` with an idempotent
linear map `Δ` (`Δ ∘ Δ = Δ`): its `m`-fold channel power has map `α^m id + (1 - α^m) Δ`. -/
theorem channelPow_affine_idempotent_map {H : Type} [Fintype H] [DecidableEq H]
    (Φ : Channel H H) (Δ : MatrixMap H H) (α : ℝ)
    (hΦ : ∀ X : CMatrix H, Φ.map X = (α : ℂ) • X + ((1 - α : ℝ) : ℂ) • Δ X)
    (hΔ : ∀ X : CMatrix H, Δ (Δ X) = Δ X)
    (m : ℕ) (X : CMatrix H) :
    (channelPow Φ m).map X =
      ((α ^ m : ℝ) : ℂ) • X + ((1 - α ^ m : ℝ) : ℂ) • Δ X := by
  induction m with
  | zero =>
    change (Channel.idChannel H).map X = _
    rw [ICO.DiamondPreprocessing.identity_map]
    simp
  | succ m ih =>
    have hfix : Φ.map (Δ X) = Δ X := by
      rw [hΦ (Δ X), hΔ X, ← add_smul]
      have hs : (α : ℂ) + ((1 - α : ℝ) : ℂ) = 1 := by push_cast; ring
      rw [hs, one_smul]
    change Φ.map ((channelPow Φ m).map X) = _
    rw [ih, map_add, map_smul, map_smul, hΦ X, hfix]
    simp only [smul_add, smul_smul]
    rw [add_assoc, ← add_smul]
    have hc1 : ((α ^ m : ℝ) : ℂ) * (α : ℂ) = ((α ^ (m + 1) : ℝ) : ℂ) := by
      push_cast; ring
    have hc2 :
        ((α ^ m : ℝ) : ℂ) * ((1 - α : ℝ) : ℂ) + ((1 - α ^ m : ℝ) : ℂ) =
          ((1 - α ^ (m + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hc1, hc2]

/-- Standalone weak dephasing-noise channel `\mathcal{E}_{p,U} = (1 - p) id + p Δ_U` on `A`. -/
def dephasingNoiseChannel {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Matrix.unitaryGroup A ℂ) : Channel A A :=
  krausChannel (dephasingNoiseKraus p U) (dephasingNoiseKraus_complete hp0 hp1 U)

theorem dephasingNoiseChannel_map {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Matrix.unitaryGroup A ℂ) (X : CMatrix A) :
    (dephasingNoiseChannel hp0 hp1 U).map X =
      ((1 - p : ℝ) : ℂ) • X +
        (p : ℂ) • MatrixMap.ofKraus (basisProjection (U : CMatrix A)) X := by
  have h1 : star (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt (by linarith)
  have h2 : star (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt hp0
  change (∑ k : Option A, dephasingNoiseKraus p U k * X *
      (dephasingNoiseKraus p U k).conjTranspose) = _
  rw [Fintype.sum_option]
  simp only [dephasingNoiseKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  rw [h1]
  simp_rw [h2, ← Finset.smul_sum]
  rfl

theorem basisProjection_ofKraus_idem (U : Matrix.unitaryGroup A ℂ) (X : CMatrix A) :
    MatrixMap.ofKraus (basisProjection (U : CMatrix A))
      (MatrixMap.ofKraus (basisProjection (U : CMatrix A)) X) =
      MatrixMap.ofKraus (basisProjection (U : CMatrix A)) X := by
  by_cases hne : Nonempty A
  · haveI : Nonempty A := hne
    rw [ICO.C6OTOCChannelBoundary.dephasing_expansion (U : CMatrix A) X, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    change (∑ j : A, basisProjection (U : CMatrix A) j * basisProjection (U : CMatrix A) i *
        (basisProjection (U : CMatrix A) j).conjTranspose) = basisProjection (U : CMatrix A) i
    rw [Finset.sum_eq_single i]
    · rw [basisProjection_hermitian, basisProjection_mul _ U.property.1, if_pos rfl,
        basisProjection_mul _ U.property.1, if_pos rfl]
    · intro j _ hj
      rw [basisProjection_hermitian, basisProjection_mul _ U.property.1, if_neg hj,
        Matrix.zero_mul]
    · simp
  · haveI : IsEmpty A := not_nonempty_iff.mp hne
    ext i
    exact isEmptyElim i

theorem blockDephasingRate_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    0 ≤ 1 - (1 - p) ^ m := by
  have hpow : (1 - p) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  linarith

theorem blockDephasingRate_le_one {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    1 - (1 - p) ^ m ≤ 1 := by
  have hpow : 0 ≤ (1 - p) ^ m := pow_nonneg (by linarith) m
  linarith

/-- **Section 5.1 (`\label{sec:switch-test}`), `m`-fold block power of dephasing noise**:
For `0 ≤ p ≤ 1`, every unitary `U : Matrix.unitaryGroup A ℂ`, and every block length `m : ℕ`,
the `m`-fold channel power `\mathcal{E}_{p,U}^m` equals dephasing noise of strength
`1 - (1 - p)^m`. -/
theorem dephasingNoiseChannel_pow {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Matrix.unitaryGroup A ℂ) (m : ℕ) :
    channelPow (dephasingNoiseChannel hp0 hp1 U) m =
      dephasingNoiseChannel
        (blockDephasingRate_nonneg hp0 hp1 m)
        (blockDephasingRate_le_one hp0 hp1 m) U := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  apply LinearMap.ext
  intro X
  have haff : ∀ Y : CMatrix A,
      (dephasingNoiseChannel hp0 hp1 U).map Y =
        ((1 - p : ℝ) : ℂ) • Y +
          ((1 - (1 - p) : ℝ) : ℂ) • MatrixMap.ofKraus (basisProjection (U : CMatrix A)) Y := by
    intro Y
    rw [dephasingNoiseChannel_map hp0 hp1 U Y]
    have hsub : (1 - (1 - p) : ℝ) = p := by ring
    rw [hsub]
  rw [channelPow_affine_idempotent_map
    (dephasingNoiseChannel hp0 hp1 U)
    (MatrixMap.ofKraus (basisProjection (U : CMatrix A)))
    (1 - p) haff (basisProjection_ofKraus_idem U) m X,
    dephasingNoiseChannel_map
      (blockDephasingRate_nonneg hp0 hp1 m)
      (blockDephasingRate_le_one hp0 hp1 m) U X]
  have hsub : (1 - (1 - (1 - p) ^ m) : ℝ) = (1 - p) ^ m := by ring
  rw [hsub]

/-- Standalone depolarizing channel `\mathcal{M}_α = α id + (1 - α) Ω` on `A` with
identity weight `α ∈ [0, 1]`. -/
def depolarizingAlphaChannel [Nonempty A] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Channel A A :=
  krausChannel (depolarizingModelKraus (A := A) α) (depolarizingModelKraus_complete hα0 hα1)

theorem depolarizingAlphaChannel_map [Nonempty A] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (X : CMatrix A) :
    (depolarizingAlphaChannel (A := A) hα0 hα1).map X =
      (α : ℂ) • X +
        ((1 - α : ℝ) : ℂ) • (ICO.RecordingDepolarizing.depolarizing (α := A)).map X := by
  have h1 : star (Real.sqrt α : ℂ) * (Real.sqrt α : ℂ) = (α : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt hα0
  have h2 : star (Real.sqrt (1 - α) : ℂ) * (Real.sqrt (1 - α) : ℂ) = ((1 - α : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt (by linarith)
  have hdep : MatrixMap.ofKraus (depolarizingKraus (n := A)) X =
      (ICO.RecordingDepolarizing.depolarizing (α := A)).map X := by
    ext i j
    change (∑ p : A × A, depolarizingKraus (n := A) p * X *
        (depolarizingKraus (n := A) p).conjTranspose) i j =
      (ICO.RecordingDepolarizing.depolarizing (α := A)).map X i j
    rw [depolarizing_channel X, ICO.RecordingDepolarizing.depolarizing_entry]
    by_cases hij : i = j <;> simp [hij, div_eq_mul_inv, mul_comm]
  rw [← hdep]
  change (∑ k : Option (A × A), depolarizingModelKraus (A := A) α k * X *
      (depolarizingModelKraus (A := A) α k).conjTranspose) = _
  rw [Fintype.sum_option]
  simp only [depolarizingModelKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  rw [h1]
  simp_rw [h2, ← Finset.smul_sum]
  rfl

/-- Standalone depolarizing noise model `\mathcal{M}_p = (1 - p) id + p Λ = α id + (1 - α) Ω`
on `A`, where `α = 1 - p d / (d + 1)`. -/
def depolarizingModelChannel [Nonempty A] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel A A :=
  depolarizingAlphaChannel (A := A)
    (depolarizingModelAlpha_nonneg (A := A) hp0 hp1)
    (depolarizingModelAlpha_le_one (A := A) hp0)

theorem depolarizing_map_idem [Nonempty A] (X : CMatrix A) :
    (ICO.RecordingDepolarizing.depolarizing (α := A)).map
      ((ICO.RecordingDepolarizing.depolarizing (α := A)).map X) =
      (ICO.RecordingDepolarizing.depolarizing (α := A)).map X := by
  ext i j
  rw [ICO.RecordingDepolarizing.depolarizing_entry,
    ICO.RecordingDepolarizing.depolarizing_entry,
    (ICO.RecordingDepolarizing.depolarizing (α := A)).tracePreserving X]

theorem depolarizingAlphaChannel_pow [Nonempty A] {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (m : ℕ) :
    channelPow (depolarizingAlphaChannel (A := A) hα0 hα1) m =
      depolarizingAlphaChannel (A := A) (pow_nonneg hα0 m) (pow_le_one₀ hα0 hα1) := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  apply LinearMap.ext
  intro X
  rw [channelPow_affine_idempotent_map
    (depolarizingAlphaChannel (A := A) hα0 hα1)
    (ICO.RecordingDepolarizing.depolarizing (α := A)).map α
    (depolarizingAlphaChannel_map hα0 hα1) depolarizing_map_idem m X,
    depolarizingAlphaChannel_map (pow_nonneg hα0 m) (pow_le_one₀ hα0 hα1) X]

/-- **Section 5.1 (`\label{sec:switch-test}`), `m`-fold block power of the depolarizing model**:
For `0 ≤ p ≤ 1` and every block length `m : ℕ`, the `m`-fold channel power `\mathcal{M}_p^m`
of `\mathcal{M}_p = α id + (1 - α) Ω` (`α = 1 - p d / (d + 1)`) equals
`α^m id + (1 - α^m) Ω` (`depolarizingAlphaChannel` of parameter `α^m`). -/
theorem depolarizingModelChannel_pow [Nonempty A] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    channelPow (depolarizingModelChannel (A := A) hp0 hp1) m =
      depolarizingAlphaChannel (A := A)
        (pow_nonneg (depolarizingModelAlpha_nonneg (A := A) hp0 hp1) m)
        (pow_le_one₀ (depolarizingModelAlpha_nonneg (A := A) hp0 hp1)
          (depolarizingModelAlpha_le_one (A := A) hp0)) :=
  depolarizingAlphaChannel_pow
    (depolarizingModelAlpha_nonneg (A := A) hp0 hp1)
    (depolarizingModelAlpha_le_one (A := A) hp0) m

theorem depolarizingModelChannel_pow_map [Nonempty A] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (X : CMatrix A) :
    (channelPow (depolarizingModelChannel (A := A) hp0 hp1) m).map X =
      ((depolarizingModelAlpha A p ^ m : ℝ) : ℂ) • X +
        ((1 - depolarizingModelAlpha A p ^ m : ℝ) : ℂ) •
          (ICO.RecordingDepolarizing.depolarizing (α := A)).map X := by
  rw [depolarizingModelChannel_pow hp0 hp1 m, depolarizingAlphaChannel_map]

/-- Completeness of the canonical Choi-extracted Kraus family `channelKraus Φ` of a CPTP
channel `Φ : Channel A A`. -/
theorem channelKraus_complete (Φ : Channel A A) :
    (∑ i : A × A, (channelKraus Φ i).conjTranspose * channelKraus Φ i) = 1 := by
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus (channelKraus Φ)) := by
    rw [← channelKraus_map Φ]
    exact Φ.tracePreserving
  simpa [MatrixMap.krausAdjoint] using
    MatrixMap.krausAdjoint_one_of_tracePreserving (channelKraus Φ) hTP

theorem krausChannel_channelKraus (Φ : Channel A A) :
    krausChannel (channelKraus Φ) (channelKraus_complete Φ) = Φ := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  exact (channelKraus_map Φ).symm

/-- Kraus-representation independence of `switchChannel`: any two complete Kraus families
representing the same slot channels define the exact same switch channel on `A ⊕ A`. -/
theorem switchChannel_congr {ι ι' κ κ' : Type}
    [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (E : ι → CMatrix A) (E' : ι' → CMatrix A)
    (F : κ → CMatrix A) (F' : κ' → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hE' : (∑ i, (E' i).conjTranspose * E' i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1)
    (hF' : (∑ j, (F' j).conjTranspose * F' j) = 1)
    (hEE' : krausChannel E hE = krausChannel E' hE')
    (hFF' : krausChannel F hF = krausChannel F' hF') :
    switchChannel E F hE hF = switchChannel E' F' hE' hF' := by
  letI := Classical.decEq κ
  letI := Classical.decEq ι'
  have hleft : switchChannel E F hE hF = switchChannel E' F hE' hF := by
    rw [switchChannel_eq_slotLeft_comp E F hE hF,
      switchChannel_eq_slotLeft_comp E' F hE' hF, hEE']
  have hright : switchChannel E' F hE' hF = switchChannel E' F' hE' hF' := by
    rw [switchChannel_eq_sumComm_conj F E' hF hE',
      switchChannel_eq_sumComm_conj F' E' hF' hE',
      switchChannel_eq_slotLeft_comp F E' hF hE',
      switchChannel_eq_slotLeft_comp F' E' hF' hE', hFF']
  exact hleft.trans hright

theorem switchedState_congr {ι ι' κ κ' : Type}
    [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (E : ι → CMatrix A) (E' : ι' → CMatrix A)
    (F : κ → CMatrix A) (F' : κ' → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hE' : (∑ i, (E' i).conjTranspose * E' i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1)
    (hF' : (∑ j, (F' j).conjTranspose * F' j) = 1)
    (hEE' : krausChannel E hE = krausChannel E' hE')
    (hFF' : krausChannel F hF = krausChannel F' hF')
    (ρ : State A) :
    switchedState E F hE hF ρ = switchedState E' F' hE' hF' ρ := by
  rw [switchedState_eq_applyState, switchedState_eq_applyState,
    switchChannel_congr E E' F F' hE hE' hF hF' hEE' hFF']

/-- Canonical quantum switch channel `SW[Φ, Ψ]` on `A ⊕ A` defined directly on two CPTP
channels `Φ Ψ : Channel A A`. -/
def switchOfChannels (Φ Ψ : Channel A A) : Channel (A ⊕ A) (A ⊕ A) :=
  switchChannel (channelKraus Φ) (channelKraus Ψ)
    (channelKraus_complete Φ) (channelKraus_complete Ψ)

/-- Output state of `SW[Φ, Ψ]` on control `|+⟩` and target `ρ : State A`, defined directly on
two CPTP channels `Φ Ψ : Channel A A`. -/
def switchedStateOfChannels (Φ Ψ : Channel A A) (ρ : State A) : State (A ⊕ A) :=
  switchedState (channelKraus Φ) (channelKraus Ψ)
    (channelKraus_complete Φ) (channelKraus_complete Ψ) ρ

theorem switchedStateOfChannels_eq_applyState (Φ Ψ : Channel A A) (ρ : State A) :
    switchedStateOfChannels Φ Ψ ρ = (switchOfChannels Φ Ψ).applyState (plusState ρ) :=
  switchedState_eq_applyState _ _ _ _ ρ

theorem switchOfChannels_krausChannel {ι κ : Type} [Fintype ι] [Fintype κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1) :
    switchOfChannels (krausChannel E hE) (krausChannel F hF) = switchChannel E F hE hF :=
  switchChannel_congr _ E _ F _ hE _ hF
    (krausChannel_channelKraus _) (krausChannel_channelKraus _)

theorem switchedStateOfChannels_krausChannel {ι κ : Type} [Fintype ι] [Fintype κ]
    (E : ι → CMatrix A) (F : κ → CMatrix A)
    (hE : (∑ i, (E i).conjTranspose * E i) = 1)
    (hF : (∑ j, (F j).conjTranspose * F j) = 1) (ρ : State A) :
    switchedStateOfChannels (krausChannel E hE) (krausChannel F hF) ρ =
      switchedState E F hE hF ρ :=
  switchedState_congr _ E _ F _ hE _ hF
    (krausChannel_channelKraus _) (krausChannel_channelKraus _) ρ

/-- **Theorem 3 (`\label{thm:c6}`) / Section 5.1 (`\label{sec:switch-test}`), seven-use switch
upper bound directly on `m`-fold channel powers**:
For `2 ≤ Fintype.card A`, `0 < p ≤ 1`, and any block length `m : ℕ` with `3 / (2 p) ≤ m`
(such as `m = ⌈3 / (2 p)⌉`), feeding the `m`-fold channel powers
`channelPow (dephasingNoiseChannel ... U) m` and `channelPow (depolarizingModelChannel ...) m`
directly into both slots of the quantum switch on control `|+⟩` and target `mixedState` yields:
1. All `7` independent switch runs output `+` with probability `1` on `\mathcal{E}_{p,U}`
   (zero error on dephasing noise).
2. All `7` independent switch runs output `+` with probability `< 1 / 3` on `\mathcal{M}_p`.
3. Total device uses across the `7` switch runs is `7 * (2 * m) = 14 * m`. -/
theorem validation_switch_block_power_upper_bound [Nonempty A] (hd : 2 ≤ Fintype.card A)
    (U : Matrix.unitaryGroup A ℂ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {m : ℕ} (hm : 3 / (2 * p) ≤ (m : ℝ)) :
    let blockE : Channel A A :=
      channelPow (dephasingNoiseChannel (le_of_lt hp0) hp1 U) m
    let blockM : Channel A A :=
      channelPow (depolarizingModelChannel (A := A) (le_of_lt hp0) hp1) m
    let stateE : State (A ⊕ A) :=
      switchedStateOfChannels blockE blockE mixedState
    let stateM : State (A ⊕ A) :=
      switchedStateOfChannels blockM blockM mixedState
    (repetitions 7 (controlMeasurement.prob stateE true)
      (QIT.POVM.prob_le_one _ _ _)).real {ω | ∀ i, ω i = true} = 1 ∧
    (repetitions 7 (controlMeasurement.prob stateM true)
      (QIT.POVM.prob_le_one _ _ _)).real {ω | ∀ i, ω i = true} < 1 / 3 ∧
    7 * (2 * m) = 14 * m := by
  intro blockE blockM stateE stateM
  obtain ⟨hpm0, hpm1, hαm0, hαm1, haccE, _hαm_exp, haccM, hcalls⟩ :=
    validation_switch_upper_bound hd U hp0 hp1 hm
  have hstE :
      stateE = switchedState (dephasingNoiseKraus (1 - (1 - p) ^ m) U)
        (dephasingNoiseKraus (1 - (1 - p) ^ m) U)
        (dephasingNoiseKraus_complete hpm0 hpm1 U)
        (dephasingNoiseKraus_complete hpm0 hpm1 U) mixedState := by
    change switchedStateOfChannels
        (channelPow (dephasingNoiseChannel (le_of_lt hp0) hp1 U) m)
        (channelPow (dephasingNoiseChannel (le_of_lt hp0) hp1 U) m) mixedState = _
    rw [dephasingNoiseChannel_pow (le_of_lt hp0) hp1 U m]
    exact switchedStateOfChannels_krausChannel _ _ _ _ mixedState
  have hstM :
      stateM = switchedState (depolarizingModelKraus (A := A) (depolarizingModelAlpha A p ^ m))
        (depolarizingModelKraus (A := A) (depolarizingModelAlpha A p ^ m))
        (depolarizingModelKraus_complete hαm0 hαm1)
        (depolarizingModelKraus_complete hαm0 hαm1) mixedState := by
    change switchedStateOfChannels
        (channelPow (depolarizingModelChannel (A := A) (le_of_lt hp0) hp1) m)
        (channelPow (depolarizingModelChannel (A := A) (le_of_lt hp0) hp1) m) mixedState = _
    rw [depolarizingModelChannel_pow (le_of_lt hp0) hp1 m]
    exact switchedStateOfChannels_krausChannel _ _ _ _ mixedState
  refine ⟨?_, ?_, hcalls⟩
  · simpa only [hstE] using haccE
  · simpa only [hstM] using haccM

/-! ## 5. Remark `rem:crossover`: diamond distance `≤ p` and trivial `1 / (3p) ≤ Q` bound -/

/-- For every ancilla type `R`, noise rate `0 ≤ p ≤ 1`, and unitary `U`, the weak dephasing
channel `\mathcal{E}_{p,U}` and depolarizing model `\mathcal{M}_p` have ancilla-assisted
normalized trace distance at most `p`. -/
theorem dephasing_depolarizing_ancilla_le_p [Nonempty A] {R : Type} [Fintype R] [DecidableEq R]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U : Matrix.unitaryGroup A ℂ) :
    Channel.AncillaTraceDistanceBound (a := A) (b := A) (r := R)
      (dephasingNoiseChannel hp0 hp1 U)
      (depolarizingModelChannel (A := A) hp0 hp1) p := by
  intro ω
  change ((dephasingNoiseWithMemory R hp0 hp1 U).applyState ω).normalizedTraceDistance
    ((depolarizingModelWithMemory (A := A) R hp0 hp1).applyState ω) ≤ p
  let σ₁ : State (A × R) := (ICO.BudgetContinuity.hidden (M := R) U).applyState ω
  let σ₂ : State (A × R) := (haarDepolarizingWithMemory (A := A) R).applyState ω
  have hdiff :
      ((dephasingNoiseWithMemory R hp0 hp1 U).applyState ω).matrix -
        ((depolarizingModelWithMemory (A := A) R hp0 hp1).applyState ω).matrix =
      (p : ℂ) • (σ₁.matrix - σ₂.matrix) := by
    change (dephasingNoiseWithMemory R hp0 hp1 U).map ω.matrix -
        (depolarizingModelWithMemory (A := A) R hp0 hp1).map ω.matrix =
      (p : ℂ) • ((ICO.BudgetContinuity.hidden (M := R) U).map ω.matrix -
        (haarDepolarizingWithMemory (A := A) R).map ω.matrix)
    rw [dephasingNoiseWithMemory_map hp0 hp1 U ω.matrix,
      depolarizingModelWithMemory_map hp0 hp1 ω.matrix, smul_sub]
    abel
  change (1 / 2 : ℝ) * traceNorm
      (((dephasingNoiseWithMemory R hp0 hp1 U).applyState ω).matrix -
        ((depolarizingModelWithMemory (A := A) R hp0 hp1).applyState ω).matrix) ≤ p
  rw [hdiff, traceNorm_real_smul_eq hp0]
  have hle1 : σ₁.normalizedTraceDistance σ₂ ≤ 1 :=
    ICO.ChoiWitnessState.state_distance_le_one σ₁ σ₂
  change (1 / 2 : ℝ) * traceNorm (σ₁.matrix - σ₂.matrix) ≤ 1 at hle1
  nlinarith

/-- **Remark `rem:crossover`, diamond trace distance bound `(1/2) ‖E_{p,U} - M_p‖_⋄ ≤ p`**:
For every `0 ≤ p ≤ 1` and unitary `U : Matrix.unitaryGroup A ℂ`,
`(dephasingNoiseChannel hp0 hp1 U).diamondTraceDistance (depolarizingModelChannel hp0 hp1) ≤ p`. -/
theorem dephasing_depolarizing_diamond_le_p [Nonempty A] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Matrix.unitaryGroup A ℂ) :
    (dephasingNoiseChannel hp0 hp1 U).diamondTraceDistance
      (depolarizingModelChannel (A := A) hp0 hp1) ≤ p :=
  Channel.diamondTraceDistance_le_of_ancillaBound
    (dephasing_depolarizing_ancilla_le_p hp0 hp1 U)

/-- Lifted side-memory diamond trace distance bound: for every finite nonempty side memory `M`,
`(dephasingNoiseWithMemory M hp0 hp1 U).diamondTraceDistance (depolarizingModelWithMemory M hp0 hp1) ≤ p`. -/
theorem dephasing_depolarizing_withMemory_diamond_le_p [Nonempty A]
    (M : Type) [Fintype M] [DecidableEq M] [Nonempty M]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U : Matrix.unitaryGroup A ℂ) :
    (dephasingNoiseWithMemory M hp0 hp1 U).diamondTraceDistance
      (depolarizingModelWithMemory (A := A) M hp0 hp1) ≤ p := by
  apply Channel.diamondTraceDistance_le_of_inputReferenceBound
  intro ω
  rw [show (dephasingNoiseWithMemory M hp0 hp1 U) =
        (dephasingNoiseChannel hp0 hp1 U).prod (Channel.idChannel M) from rfl,
      show (depolarizingModelWithMemory (A := A) M hp0 hp1) =
        (depolarizingModelChannel (A := A) hp0 hp1).prod (Channel.idChannel M) from rfl,
      prod_id_prod_id_applyState_eq_reindex (dephasingNoiseChannel hp0 hp1 U) ω,
      prod_id_prod_id_applyState_eq_reindex (depolarizingModelChannel (A := A) hp0 hp1) ω]
  exact (Channel.normalizedTraceDistance_applyState_le
    (Channel.reindex (Equiv.prodAssoc A M (A × M)).symm) _ _).trans
    (dephasing_depolarizing_ancilla_le_p hp0 hp1 U _)

/-- Homogeneous PSD trace-norm bound for a single channel step: if `Ξ` and `Ξ'` differ by at
most `ε ≥ 0` in normalized trace distance on every state `σ : State H`, then for every
positive semidefinite matrix `X : CMatrix H`,
`(1 / 2) * traceNorm (Ξ.map X - Ξ'.map X) ≤ ε * X.trace.re`. -/
theorem channel_posSemidef_traceNorm_sub_le {H : Type} [Fintype H] [DecidableEq H]
    (Ξ Ξ' : Channel H H) {ε : ℝ} (_hε : 0 ≤ ε)
    (hΞ : ∀ σ : State H, (Ξ.applyState σ).normalizedTraceDistance (Ξ'.applyState σ) ≤ ε)
    (X : CMatrix H) (hX : X.PosSemidef) :
    (1 / 2 : ℝ) * traceNorm (Ξ.map X - Ξ'.map X) ≤ ε * X.trace.re := by
  by_cases ht : 0 < X.trace.re
  · let t : ℝ := X.trace.re
    have ht_pos : 0 < t := ht
    have htr_nonneg : 0 ≤ X.trace := Matrix.PosSemidef.trace_nonneg hX
    have htr_im : X.trace.im = 0 := (Complex.nonneg_iff.mp htr_nonneg).2.symm
    have htr_coe : X.trace = (t : ℂ) := Complex.ext rfl (by simp [htr_im])
    let r : ℝ := Real.sqrt (t⁻¹)
    have hr_sq : ((r : ℂ) * (r : ℂ)) = ((t⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (inv_nonneg.mpr (le_of_lt ht_pos))
    have hpos : (((t⁻¹ : ℝ) : ℂ) • X).PosSemidef := by
      have hconj := hX.conjTranspose_mul_mul_same ((r : ℂ) • (1 : CMatrix H))
      simpa only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_smul, hr_sq] using hconj
    let σ : State H :=
      { matrix := ((t⁻¹ : ℝ) : ℂ) • X
        pos := hpos
        trace_eq_one := by
          rw [Matrix.trace_smul, htr_coe, smul_eq_mul]
          exact_mod_cast inv_mul_cancel₀ (ne_of_gt ht_pos) }
    have hmul : (t : ℂ) * ((t⁻¹ : ℝ) : ℂ) = 1 := by
      exact_mod_cast mul_inv_cancel₀ (ne_of_gt ht_pos)
    have hmap_sub :
        Ξ.map X - Ξ'.map X = (t : ℂ) • ((Ξ.applyState σ).matrix - (Ξ'.applyState σ).matrix) := by
      symm
      change (t : ℂ) • (Ξ.map (((t⁻¹ : ℝ) : ℂ) • X) - Ξ'.map (((t⁻¹ : ℝ) : ℂ) • X)) =
        Ξ.map X - Ξ'.map X
      rw [map_smul, map_smul, ← smul_sub, smul_smul, hmul, one_smul]
    rw [hmap_sub, traceNorm_real_smul_eq (le_of_lt ht_pos)]
    have hdist := hΞ σ
    change (1 / 2 : ℝ) * traceNorm ((Ξ.applyState σ).matrix - (Ξ'.applyState σ).matrix) ≤ ε at hdist
    nlinarith
  · have htr_le : X.trace.re ≤ 0 := le_of_not_gt ht
    have htr_ge : 0 ≤ X.trace.re := by
      rw [← traceNorm_posSemidef_eq_trace_re X hX]
      exact traceNorm_nonneg X
    have htr_zero : X.trace.re = 0 := le_antisymm htr_le htr_ge
    have hn1 : traceNorm (Ξ.map X) = 0 := by
      rw [traceNorm_posSemidef_eq_trace_re _ (Ξ.mapsPositive X hX),
        Ξ.tracePreserving X, htr_zero]
    have hn2 : traceNorm (Ξ'.map X) = 0 := by
      rw [traceNorm_posSemidef_eq_trace_re _ (Ξ'.mapsPositive X hX),
        Ξ'.tracePreserving X, htr_zero]
    have htri : traceNorm (Ξ.map X - Ξ'.map X) ≤ 0 := by
      have h := traceNorm_add_le (Ξ.map X) (-(Ξ'.map X))
      rw [← sub_eq_add_neg, traceNorm_neg, hn1, hn2, add_zero] at h
      exact h
    rw [htr_zero, mul_zero]
    linarith

/-- Homogeneous `q`-query trace-norm stability bound for arbitrary adaptive trees
`tree : ICO.BudgetQueryTree.Tree H O q B` on positive semidefinite inputs `X : CMatrix B`. -/
theorem tree_posSemidef_traceNorm_sub_le {H O B : Type}
    [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : ICO.BudgetQueryTree.Tree H O q B)
    (Φ₁ Φ₂ Ψ₁ Ψ₂ : Channel H H) {ε : ℝ} (hε : 0 ≤ ε)
    (h₁ : ∀ σ : State H, (Φ₁.applyState σ).normalizedTraceDistance (Ψ₁.applyState σ) ≤ ε)
    (h₂ : ∀ σ : State H, (Φ₂.applyState σ).normalizedTraceDistance (Ψ₂.applyState σ) ≤ ε)
    (X : CMatrix B) (hX : X.PosSemidef) :
    (1 / 2 : ℝ) * traceNorm ((tree.channel Φ₁ Φ₂).map X - (tree.channel Ψ₁ Ψ₂).map X) ≤
      (q : ℝ) * ε * X.trace.re := by
  induction tree with
  | @stop q_stop B_stop _ _ after =>
    change (1 / 2 : ℝ) * traceNorm (after.map X - after.map X) ≤
      (q_stop : ℝ) * ε * X.trace.re
    rw [sub_self, traceNorm_zero, mul_zero]
    have htr_ge : 0 ≤ X.trace.re := by
      rw [← traceNorm_posSemidef_eq_trace_re X hX]
      exact traceNorm_nonneg X
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) htr_ge
  | @query q_prev b after ih =>
    let Ξ : Channel H H := if b then Φ₂ else Φ₁
    let Ξ' : Channel H H := if b then Ψ₂ else Ψ₁
    have hΞ : ∀ σ : State H, (Ξ.applyState σ).normalizedTraceDistance (Ξ'.applyState σ) ≤ ε := by
      cases b
      · exact h₁
      · exact h₂
    change (1 / 2 : ℝ) * traceNorm
        ((after.channel Φ₁ Φ₂).map (Ξ.map X) - (after.channel Ψ₁ Ψ₂).map (Ξ'.map X)) ≤
      ((q_prev + 1 : ℕ) : ℝ) * ε * X.trace.re
    have hsplit :
        (after.channel Φ₁ Φ₂).map (Ξ.map X) - (after.channel Ψ₁ Ψ₂).map (Ξ'.map X) =
          ((after.channel Φ₁ Φ₂).map (Ξ.map X) - (after.channel Ψ₁ Ψ₂).map (Ξ.map X)) +
            (after.channel Ψ₁ Ψ₂).map (Ξ.map X - Ξ'.map X) := by
      rw [map_sub]
      abel
    have htri := traceNorm_add_le
      ((after.channel Φ₁ Φ₂).map (Ξ.map X) - (after.channel Ψ₁ Ψ₂).map (Ξ.map X))
      ((after.channel Ψ₁ Ψ₂).map (Ξ.map X - Ξ'.map X))
    rw [← hsplit] at htri
    have hterm1 :
        (1 / 2 : ℝ) *
            traceNorm ((after.channel Φ₁ Φ₂).map (Ξ.map X) - (after.channel Ψ₁ Ψ₂).map (Ξ.map X)) ≤
          (q_prev : ℝ) * ε * X.trace.re := by
      have hih := ih (Ξ.map X) (Ξ.mapsPositive X hX)
      rwa [Ξ.tracePreserving X] at hih
    have hΔ_herm : (Ξ.map X - Ξ'.map X).IsHermitian :=
      (Ξ.mapsPositive X hX).isHermitian.sub (Ξ'.mapsPositive X hX).isHermitian
    have hΔ_tr : (Ξ.map X - Ξ'.map X).trace = 0 := by
      rw [Matrix.trace_sub, Ξ.tracePreserving X, Ξ'.tracePreserving X, sub_self]
    have hcontract :
        traceNorm ((after.channel Ψ₁ Ψ₂).map (Ξ.map X - Ξ'.map X)) ≤
          traceNorm (Ξ.map X - Ξ'.map X) :=
      MatrixMap.traceNorm_apply_le_of_traceNonincreasingCP
        (Channel.traceNonincreasingCP_map (after.channel Ψ₁ Ψ₂)) hΔ_herm hΔ_tr
    have hstep := channel_posSemidef_traceNorm_sub_le Ξ Ξ' hε hΞ X hX
    have hterm2 :
        (1 / 2 : ℝ) * traceNorm ((after.channel Ψ₁ Ψ₂).map (Ξ.map X - Ξ'.map X)) ≤
          ε * X.trace.re := by
      linarith
    push_cast
    linarith
  | @node q_node B_node C L _ _ _ _ _ _ I next ih =>
    change (1 / 2 : ℝ) * traceNorm
        (ICO.InstrumentCompression.adaptiveMap I (fun l => (next l).channel Φ₁ Φ₂) X -
          ICO.InstrumentCompression.adaptiveMap I (fun l => (next l).channel Ψ₁ Ψ₂) X) ≤
      (q_node : ℝ) * ε * X.trace.re
    rw [ICO.InstrumentCompression.adaptiveMap_apply,
      ICO.InstrumentCompression.adaptiveMap_apply, ← Finset.sum_sub_distrib]
    have hsum_tri := traceNorm_sum_le_sum_traceNorm Finset.univ (fun l : L =>
      ((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l).conjTranspose) -
        ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l).conjTranspose))
    have hbranch (l : L) :
        (1 / 2 : ℝ) * traceNorm
            (((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l).conjTranspose) -
              ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l).conjTranspose)) ≤
          (q_node : ℝ) * ε * (I.op l * X * (I.op l).conjTranspose).trace.re :=
      ih l (I.op l * X * (I.op l).conjTranspose) (hX.mul_mul_conjTranspose_same (I.op l))
    have hsum_le :
        (∑ l : L, (1 / 2 : ℝ) * traceNorm
            (((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l).conjTranspose) -
              ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l).conjTranspose))) ≤
          (q_node : ℝ) * ε * X.trace.re := by
      calc
        (∑ l : L, (1 / 2 : ℝ) * traceNorm
            (((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l).conjTranspose) -
              ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l).conjTranspose))) ≤
          ∑ l : L, (q_node : ℝ) * ε * (I.op l * X * (I.op l).conjTranspose).trace.re :=
            Finset.sum_le_sum fun l _ => hbranch l
        _ = (q_node : ℝ) * ε * (∑ l : L, (I.op l * X * (I.op l).conjTranspose).trace.re) := by
          rw [← Finset.mul_sum]
        _ = (q_node : ℝ) * ε * X.trace.re := by
          have hI : MatrixMap.krausAdjoint I.op (1 : CMatrix C) = 1 := by
            simpa [MatrixMap.krausAdjoint] using I.complete
          have htp := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one I.op hI X
          have htr_sum :
              (∑ l : L, (I.op l * X * (I.op l).conjTranspose).trace.re) = X.trace.re := by
            rw [← Complex.re_sum, ← Matrix.trace_sum]
            exact congrArg Complex.re htp
          rw [htr_sum]
    have hhalf :
        (1 / 2 : ℝ) * traceNorm
            (∑ l : L, (((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l).conjTranspose) -
              ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l).conjTranspose))) ≤
          ∑ l : L, (1 / 2 : ℝ) * traceNorm
            (((next l).channel Φ₁ Φ₂).map (I.op l * X * (I.op l).conjTranspose) -
              ((next l).channel Ψ₁ Ψ₂).map (I.op l * X * (I.op l).conjTranspose)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum_tri (by norm_num)
    exact hhalf.trans hsum_le

/-- `Q`-query state-distance subadditivity for any adaptive query tree `tree` on initial state `ρ`. -/
theorem tree_applyState_distance_le {H O B : Type}
    [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q : ℕ} (tree : ICO.BudgetQueryTree.Tree H O Q B) (ρ : State B)
    (Φ₁ Φ₂ Ψ₁ Ψ₂ : Channel H H) {ε : ℝ} (hε : 0 ≤ ε)
    (h₁ : ∀ σ : State H, (Φ₁.applyState σ).normalizedTraceDistance (Ψ₁.applyState σ) ≤ ε)
    (h₂ : ∀ σ : State H, (Φ₂.applyState σ).normalizedTraceDistance (Ψ₂.applyState σ) ≤ ε) :
    ((tree.channel Φ₁ Φ₂).applyState ρ).normalizedTraceDistance
      ((tree.channel Ψ₁ Ψ₂).applyState ρ) ≤ (Q : ℝ) * ε := by
  have h := tree_posSemidef_traceNorm_sub_le tree Φ₁ Φ₂ Ψ₁ Ψ₂ hε h₁ h₂ ρ.matrix ρ.pos
  rw [ρ.trace_eq_one, Complex.one_re, mul_one] at h
  exact h

/-- `Q`-query acceptance-gap bound between `\mathcal{E}_{p,U}` and `\mathcal{M}_p`: each of the
`Q` queries changes the state in normalized trace distance by at most `p`, so the acceptance
probabilities differ by at most `Q * p`. -/
theorem dephasing_depolarizing_tree_accept_gap_le [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Matrix.unitaryGroup A ℂ)
    (T : BinaryHypothesisTest O)
    (tree : ICO.BudgetQueryTree.Tree (A × M) O Q B) (ρ : State B) :
    ICO.BudgetTesting.acceptance T tree ρ
        (dephasingNoiseWithMemory M hp0 hp1 U)
        (dephasingNoiseWithMemory M hp0 hp1 U) -
      ICO.BudgetTesting.acceptance T tree ρ
        (depolarizingModelWithMemory (A := A) M hp0 hp1)
        (depolarizingModelWithMemory (A := A) M hp0 hp1) ≤
      (Q : ℝ) * p := by
  rw [ICO.BudgetTesting.acceptance_eq, ICO.BudgetTesting.acceptance_eq]
  have hstep : ∀ σ : State (A × M),
      ((dephasingNoiseWithMemory M hp0 hp1 U).applyState σ).normalizedTraceDistance
        ((depolarizingModelWithMemory (A := A) M hp0 hp1).applyState σ) ≤ p :=
    dephasing_depolarizing_ancilla_le_p (R := M) hp0 hp1 U
  exact (accept_gap_le_traceDistance T _ _).trans
    (tree_applyState_distance_le tree ρ _ _ _ _ hp0 hstep hstep)

/-- **Remark `rem:crossover`, trivial `1 / (3p) ≤ Q` query lower bound (fixed-unitary form)**:
Even for a single fixed unitary `U`, any `Q`-query strategy `(tree, ρ, T)` whose acceptance on
`\mathcal{E}_{p,U}` exceeds its acceptance on `\mathcal{M}_p` by at least `1 / 3` (in particular,
accepting `\mathcal{E}_{p,U}` with probability `≥ 2 / 3` and `\mathcal{M}_p` with probability
`≤ 1 / 3`) satisfies `1 / (3 p) ≤ Q`. -/
theorem validation_trivial_single_unitary_query_lower_bound [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (U : Matrix.unitaryGroup A ℂ)
    (T : BinaryHypothesisTest O)
    (tree : ICO.BudgetQueryTree.Tree (A × M) O Q B) (ρ : State B)
    (hhigh : (2 / 3 : ℝ) ≤ ICO.BudgetTesting.acceptance T tree ρ
      (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U)
      (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U))
    (hlow : ICO.BudgetTesting.acceptance T tree ρ
      (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1)
      (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1) ≤ 1 / 3) :
    (1 : ℝ) / (3 * p) ≤ (Q : ℝ) := by
  have hgap := dephasing_depolarizing_tree_accept_gap_le (le_of_lt hp0) hp1 U T tree ρ
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * p)]
  linarith

/-- **Remark `rem:crossover`, trivial `1 / (3p) ≤ Q` query lower bound (worst-case form)**:
For every `0 < p ≤ 1` and arbitrary dimension `d = Fintype.card A ≥ 1`, any `Q`-query adaptive
strategy `(tree, ρ, T)` succeeding with probability at least `2 / 3` on `\mathcal{M}_p` and on
every `\mathcal{E}_{p,U}` satisfies `1 / (3 p) ≤ Q`. -/
theorem validation_trivial_query_lower_bound [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (T : BinaryHypothesisTest O)
    (tree : ICO.BudgetQueryTree.Tree (A × M) O Q B) (ρ : State B)
    (hhigh : ∀ U : Matrix.unitaryGroup A ℂ,
      (2 / 3 : ℝ) ≤ ICO.BudgetTesting.acceptance T tree ρ
        (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U)
        (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U))
    (hlow : ICO.BudgetTesting.acceptance T tree ρ
      (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1)
      (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1) ≤ 1 / 3) :
    (1 : ℝ) / (3 * p) ≤ (Q : ℝ) :=
  validation_trivial_single_unitary_query_lower_bound hp0 hp1 1 T tree ρ (hhigh 1) hlow

/-- **Remark `rem:crossover`, trivial `1 / (3p) ≤ Q` query lower bound (balanced Haar-prior form)**:
For every `0 < p ≤ 1` and arbitrary dimension `d = Fintype.card A ≥ 1`, any `Q`-query adaptive
strategy `(tree, ρ, T)` achieving balanced Haar-prior success probability at least `2 / 3`
between `\mathcal{E}_{p,U}` and `\mathcal{M}_p` satisfies `1 / (3 p) ≤ Q`. -/
theorem validation_trivial_balanced_query_lower_bound [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {Q : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (T : BinaryHypothesisTest O)
    (tree : ICO.BudgetQueryTree.Tree (A × M) O Q B) (ρ : State B)
    (hsucc : (2 / 3 : ℝ) ≤
      (1 / 2 : ℝ) *
        ((∫ U, ICO.BudgetTesting.acceptance T tree ρ
            (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U)
            (dephasingNoiseWithMemory M (le_of_lt hp0) hp1 U) ∂unitaryHaarMeasure (a := A)) +
          (1 - ICO.BudgetTesting.acceptance T tree ρ
            (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1)
            (depolarizingModelWithMemory (A := A) M (le_of_lt hp0) hp1)))) :
    (1 : ℝ) / (3 * p) ≤ (Q : ℝ) := by
  let hp0_le : 0 ≤ p := le_of_lt hp0
  let μ := unitaryHaarMeasure (a := A)
  have hdeph_cont :
      Continuous (fun ux : Matrix.unitaryGroup A ℂ × CMatrix (A × M) =>
        (dephasingNoiseWithMemory M hp0_le hp1 ux.1).map ux.2) := by
    have hfun :
        (fun ux : Matrix.unitaryGroup A ℂ × CMatrix (A × M) =>
          (dephasingNoiseWithMemory M hp0_le hp1 ux.1).map ux.2) =
        (fun ux : Matrix.unitaryGroup A ℂ × CMatrix (A × M) =>
          ((1 - p : ℝ) : ℂ) • ux.2 +
            (p : ℂ) • (ICO.BudgetContinuity.hidden (M := M) ux.1).map ux.2) := by
      ext ⟨U, X⟩ i j
      have hm := dephasingNoiseWithMemory_map hp0_le hp1 U X
      rw [ICO.DiamondPreprocessing.identity_map] at hm
      exact congrFun (congrFun hm i) j
    rw [hfun]
    exact (continuous_const.smul continuous_snd).add
      (continuous_const.smul ICO.BudgetContinuity.hidden_continuous)
  have hout_cont :
      Continuous (fun U : Matrix.unitaryGroup A ℂ =>
        ICO.BudgetTesting.acceptance T tree ρ
          (dephasingNoiseWithMemory M hp0_le hp1 U)
          (dephasingNoiseWithMemory M hp0_le hp1 U)) :=
    (ICO.BornAverage.acceptCLM T).continuous.comp
      (ICO.BudgetContinuity.output_continuous tree
        (dephasingNoiseWithMemory M hp0_le hp1)
        (dephasingNoiseWithMemory M hp0_le hp1)
        hdeph_cont hdeph_cont (fun _ => ρ.matrix) continuous_const)
  have hint :
      Integrable (fun U : Matrix.unitaryGroup A ℂ =>
        ICO.BudgetTesting.acceptance T tree ρ
          (dephasingNoiseWithMemory M hp0_le hp1 U)
          (dephasingNoiseWithMemory M hp0_le hp1 U)) μ :=
    hout_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let accM : ℝ := ICO.BudgetTesting.acceptance T tree ρ
    (depolarizingModelWithMemory (A := A) M hp0_le hp1)
    (depolarizingModelWithMemory (A := A) M hp0_le hp1)
  have hpt : ∀ U : Matrix.unitaryGroup A ℂ,
      ICO.BudgetTesting.acceptance T tree ρ
          (dephasingNoiseWithMemory M hp0_le hp1 U)
          (dephasingNoiseWithMemory M hp0_le hp1 U) ≤
        accM + (Q : ℝ) * p := by
    intro U
    have hgap := dephasing_depolarizing_tree_accept_gap_le hp0_le hp1 U T tree ρ
    dsimp [accM]
    linarith
  have hint_le :
      (∫ U, ICO.BudgetTesting.acceptance T tree ρ
          (dephasingNoiseWithMemory M hp0_le hp1 U)
          (dephasingNoiseWithMemory M hp0_le hp1 U) ∂μ) ≤
        accM + (Q : ℝ) * p := by
    have hmono := integral_mono hint (integrable_const (accM + (Q : ℝ) * p)) hpt
    simpa [integral_const, probReal_univ] using hmono
  have hgap_lb :
      (1 / 3 : ℝ) ≤
        (∫ U, ICO.BudgetTesting.acceptance T tree ρ
            (dephasingNoiseWithMemory M hp0_le hp1 U)
            (dephasingNoiseWithMemory M hp0_le hp1 U) ∂μ) - accM := by
    dsimp [accM, μ, hp0_le]
    linarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * p)]
  linarith

end

end ICO.Section54Validation

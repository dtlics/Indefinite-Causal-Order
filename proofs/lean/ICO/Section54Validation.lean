import ICO.C6OperationalDecision
import ICO.AllChannelDilation
import ICO.OrderedCircuit
import ICO.DiamondPreprocessing

/-!
# Section 5.4: Validating a physical dephasing-noise model (`\label{sec:validation}`)

This module formalizes the new statements in Section 5.4 of the paper:
- **Proposition `prop:mismatch`** (`model_mismatch_bound`) together with the
  slotwise one-call Stinespring/Kraus dilations and diamond-norm contractivity
  of the quantum switch (`switch_slot_left_diamond_le`, `switch_slot_right_diamond_le`).
- **Identities `eq:validation-visibility`** (`dephasing_noise_self_visibility` and
  `depolarizing_model_self_visibility`): exact switch self-visibilities
  `v(\mathcal{E}_{p,U}) = 1` and `v(\mathcal{M}_p) = 1 - p^2 (d - 1) / (d + 1)`.
- **Corollary `cor:validation` (a) and (b)** (`validation_ordinary_lower_bound`
  and `validation_switch_upper_bound`): exponential-in-`d` ordinary query lower
  bound `Q > d^{1/16} / (1400 p)` versus dimension-independent `14 ⌈3 / (2p)⌉`-call
  switch validation protocol.
-/

namespace ICO.Section54Validation

open Matrix QIT MeasureTheory
open ICO.SwitchObservable ICO.SwitchExperiment ICO.SwitchSampling
open ICO.C6SwitchTest ICO.C6OperationalDecision ICO.C6UniformBounds
open ICO.ClassicalDilation ICO.AllChannelDilation ICO.QuantumDecision
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

set_option maxHeartbeats 1600000
set_option Elab.async false

variable {A : Type} [Fintype A] [DecidableEq A]

/-! ## 1. Kraus channels and the one-call slotwise dilation of the quantum switch -/

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

/-- Key Kraus factorization `K_j (E_i ⊗ I_M) W_pre = S_{i,j}` from the proof of
Proposition `prop:mismatch`. -/
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

/-- **Proposition `prop:mismatch` (Model mismatch)**:
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

/-! ## 2. Self-visibility identities `eq:validation-visibility` -/

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

/-! ## 3. Corollary `cor:validation` (a) and (b) -/

/-- **Corollary `cor:validation` (a) (Ordinary query lower bound)**:
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

/-- **Corollary `cor:validation` (b) (Switch validation upper bound)**:
For any dimension `d = Fintype.card A ≥ 2`, noise rate `0 < p ≤ 1`, and block length
`k : ℕ` with `3 / (2 p) ≤ k` (such as `k = ⌈3 / (2 p)⌉`):
1. The `k`-fold composition `\mathcal{E}_{p,U}^k = \mathcal{E}_{1-(1-p)^k, U}` has
   self-visibility `1`, and `7` switch repetitions accept all `7` times with
   probability `1` (false-rejection error `0`).
2. The `k`-fold composition `\mathcal{M}_p^k = α^k id + (1 - α^k) Ω` with
   `α = 1 - p d / (d + 1)` satisfies `α^k ≤ exp(-1) ≤ (20 / 21)^20`, single-use
   minus probability `p_{-,k} ≥ (3 / 8) (1 - exp(-1))^2 > 1455 / 10000`, and `7`-repetition
   all-plus probability `< 1 / 3`.
3. Total device calls used by the `7` switch runs is `7 * (2 * k) = 14 * k`. -/
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

#print axioms switch_slot_left_diamond_le
#print axioms switch_slot_right_diamond_le
#print axioms model_mismatch_bound
#print axioms dephasing_noise_self_visibility
#print axioms depolarizing_model_self_visibility
#print axioms validation_ordinary_lower_bound
#print axioms validation_switch_upper_bound

end

end ICO.Section54Validation

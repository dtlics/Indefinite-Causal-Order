import ICO.NormalFormQubitObstruction
import ICO.QubitSwitchConvention
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Named Exact-Qubit Lemmas and Appendix B Dimension / Invariance Theorems

This module exposes standalone paper-aligned declarations for Section 3 (`sec:exact`)
and Appendix B (`sec:certificate`) of `paper/main.tex`:

1. **Lemma 8 (`lem:support`)**:
   - Universal support `universalSupport` (`𝒱 ⊆ ℂ^128`) as the subspace sent by the
     link `ℒ(U, V)` into the four-operator span `fourKrausSpan U V` (`ℋ(U, V) ⊆ ℂ^8`)
     for every pair of qubit unitaries `U, V`.
   - Part (b) (`lem_support_part_b`): `𝒱 = range E`, `dim_ℂ 𝒱 = 25`, and `rank E = 25`.
   - Part (a) (`ordered_component_kraus_in_support`, `ordered_component_kraus_in_range_E`,
     `lem_support_part_a`, `lem_support_part_a_fin4`): every Kraus vector of both ordered
     components of any one-call-each qubit strategy implementing `T_{λ, μ}[U, V]` on all
     pairs of qubit unitaries (`0 ≤ λ, μ ≤ 1`) lies in `𝒱` (and hence in `range E`).
   - Unified Lemma 8 (`lem_support`).

2. **Appendix B.4 (`sec:diluted-coordinates`) — Switch-weight gauge invariance**:
   - Explicit 4-row rational dual certificate (`x24_24_in_gauge_row_space`,
     `x24_24_vanishes_on_gauge`) showing `X ↦ X_{24, 24}` lies in the gauge row space.
   - Direct physical `U = σ_x, V = σ_z` probe proof (`pauli_four_kraus_linearIndependent`,
     `pauli_probe_sandwich`, `x24_24_vanishes_of_pauli_link`).
   - Decomposition `f(X) = X_{24, 24} + g(X)` with `g` vanishing on and invariant under
     the CPTP gauge (`functional_eq_x24_24_add_gauge_invariant`).

3. **Appendix B.3 (`sec:functional-proof`) — Exact dimensions `126` and `199`**:
   - Exact solution-space dimension `Module.finrank ℝ ↥(solAB ⊔ solBA ⊔ solGauge) = 126`
     (`three_systems_solution_dim_126`).
   - Exact admissible-functional dimension `Module.finrank ℝ ↥AdmissibleFunctionals = 199`
     (`admissible_functionals_dim_199`) and exact row-space intersection characterization
     (`admissible_row_intersection_dim_199`).
-/

namespace ICO.ExactQubitNamedLemmas

open scoped BigOperators ComplexOrder ComplexConjugate MatrixOrder
open Matrix QIT
open ICO.ExactTensorCertificates ICO.ExactSeparation
open ICO.ExactSupportIndependence ICO.ExactSupportSpace
open ICO.QubitLink ICO.QubitUnitaryTests ICO.UnitaryTestCertificates
open ICO.PositiveSupport ICO.SupportFromUnitaryOutputs
open ICO.DilutedSwitchTarget ICO.QubitChannelLink
open ICO.SupportCoordinates ICO.TensorBitOrder ICO.TensorRowOperators
open ICO.QubitCircuitMatrix ICO.QubitCircuitLink
open ICO.GeneralOrderedQubitFamilies ICO.NormalFormQubitObstruction
open ICO.ExactQubitObstruction ICO.QubitSwitchConvention

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

noncomputable section
attribute [local irreducible] ICO.ExactSeparation.coordinate ICO.ExactSeparation.coordinateByNat

/-- Unshadowed alias for `ICO.ExactSeparation.Vector` (`Coord → ℝ`). -/
abbrev CoordVec : Type := Coord → ℝ

/-! ## Section 1: Lemma 8 (`lem:support`) — Universal Support `𝒱` -/

/-- The four-operator subspace `ℋ(U, V) ⊆ ℂ^8` spanned by the four operators
of equation (`eq:four-kraus`) (`outputVector U V b` for `b : Fin 4`). -/
def fourKrausSpan (U V : CMatrix (Fin 2)) : Submodule ℂ (Fin 8 → ℂ) :=
  Submodule.span ℂ (Set.range (outputVector U V))

/-- The universal support `𝒱 = { v ∈ ℂ^128 : ∀ U V unitary, ℒ(U, V) v ∈ ℋ(U, V) }`
of Lemma 8 (`lem:support`). -/
def universalSupport : Submodule ℂ (Fin 128 → ℂ) where
  carrier := { v | ∀ U V : CMatrix (Fin 2), Uᴴ * U = 1 → Vᴴ * V = 1 →
    linkMatrix U V *ᵥ v ∈ fourKrausSpan U V }
  add_mem' {v w} hv hw U V hU hV := by
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ (hv U V hU hV) (hw U V hU hV)
  zero_mem' U V _ _ := by
    rw [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  smul_mem' c {v} hv U V hU hV := by
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c (hv U V hU hV)

theorem mem_universalSupport_iff (v : Fin 128 → ℂ) :
    v ∈ universalSupport ↔
      ∀ U V : CMatrix (Fin 2), Uᴴ * U = 1 → Vᴴ * V = 1 →
        linkMatrix U V *ᵥ v ∈ fourKrausSpan U V :=
  Iff.rfl

theorem basisVector_mem_universalSupport (a : Fin 25) :
    basisVector a ∈ universalSupport := by
  intro U V _ _
  rw [linked_basis U V a]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨columnGroup a, rfl⟩)

theorem supportMatrix_mulVec_eq_sum (x : Fin 25 → ℂ) :
    supportMatrix *ᵥ x = ∑ a : Fin 25, x a • basisVector a := by
  funext i
  simp [Matrix.mulVec, dotProduct, supportMatrix, basisVector, mul_comm]

theorem annihilator_dot_fourKrausSpan (r : Fin 103) {w : Fin 8 → ℂ}
    (hw : w ∈ fourKrausSpan (normalizedMatrix (uData r.val)) (normalizedMatrix (vData r.val))) :
    annihilator r ⬝ᵥ w = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨b, rfl⟩
    exact annihilator_normalized_output r b
  · simp
  · intro x y _ _ hx hy
    rw [dotProduct_add, hx, hy, add_zero]
  · intro c x _ hx
    rw [dotProduct_smul, hx, smul_zero]

/-- **Lemma 8(b), subspace identity**: `𝒱 = range E`. -/
theorem universalSupport_eq_range_E :
    universalSupport = LinearMap.range (Matrix.mulVecLin supportMatrix) := by
  apply le_antisymm
  · intro v hv
    have hcon : ∀ r : Fin 128, r.val < 103 → (complexStack *ᵥ v) r = 0 := by
      intro r hr
      let rr : Fin 103 := ⟨r.val, hr⟩
      let U := normalizedMatrix (uData rr.val)
      let V := normalizedMatrix (vData rr.val)
      have hU : Uᴴ * U = 1 := normalized_unitary _ (all_norm_pos rr).1
      have hV : Vᴴ * V = 1 := normalized_unitary _ (all_norm_pos rr).2
      have hmem := hv U V hU hV
      have hzero : annihilator rr ⬝ᵥ (linkMatrix U V *ᵥ v) = 0 :=
        annihilator_dot_fourKrausSpan rr hmem
      rw [annihilator_normalized_link rr v] at hzero
      have hnonzero := mul_ne_zero
        (normalization_ne_zero _ (all_norm_pos rr).1)
        (normalization_ne_zero _ (all_norm_pos rr).2)
      have hcoef := (mul_eq_zero.mp hzero).resolve_left hnonzero
      have htwo : (2 : ℂ) ≠ 0 := by norm_num
      have hv0 := (mul_eq_zero.mp hcoef).resolve_left htwo
      simpa [headIndex, rr] using hv0
    obtain ⟨x, hx⟩ := support_of_constraints v hcon
    exact ⟨x, by simpa only [Matrix.mulVecLin_apply, ← encode_eq_mulVec] using hx⟩
  · rintro v ⟨x, rfl⟩
    change supportMatrix *ᵥ x ∈ universalSupport
    rw [supportMatrix_mulVec_eq_sum]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ (x a) (basisVector_mem_universalSupport a))

theorem supportMatrix_mulVecLin_injective :
    Function.Injective (Matrix.mulVecLin supportMatrix) := by
  intro x y hxy
  apply encode_injective
  simpa only [encode_eq_mulVec, Matrix.mulVecLin_apply] using hxy

/-- **Lemma 8(b), rank of `E`**: the integer matrix `E ∈ ℤ^{128 × 25}` has rank `25` over `ℂ`. -/
theorem supportMatrix_rank : Matrix.rank supportMatrix = 25 := by
  unfold Matrix.rank
  have heq := LinearEquiv.finrank_eq
    (LinearEquiv.ofInjective (Matrix.mulVecLin supportMatrix) supportMatrix_mulVecLin_injective)
  rw [← heq, Module.finrank_pi_fintype]
  simp

/-- **Lemma 8(b), dimension of `𝒱`**: `dim_ℂ 𝒱 = 25`. -/
theorem universalSupport_finrank : Module.finrank ℂ universalSupport = 25 := by
  rw [universalSupport_eq_range_E]
  exact supportMatrix_rank

/-- **Lemma 8(b) (`lem:support`, part (b))**: `𝒱` equals `range E` and has dimension `25`
(`rank E = 25`). -/
theorem lem_support_part_b :
    universalSupport = LinearMap.range (Matrix.mulVecLin supportMatrix) ∧
      Module.finrank ℂ universalSupport = 25 ∧
      Matrix.rank supportMatrix = 25 :=
  ⟨universalSupport_eq_range_E, universalSupport_finrank, supportMatrix_rank⟩

/-- **Lemma 8(a) at the Kraus-family level**: if two ordered Kraus vector families
`vAB` and `vBA` reproduce the diluted switch output on all pairs of qubit unitaries `U, V`
for some `λ, μ ∈ [0, 1]`, then every Kraus vector of both components lies in `𝒱`. -/
theorem ordered_component_kraus_in_support {KA KB : Type*} [Fintype KA] [Fintype KB]
    (lambda mu : ℝ) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1)
    (hm0 : 0 ≤ mu) (hm1 : mu ≤ 1)
    (vAB : KA → Fin 128 → ℂ) (vBA : KB → Fin 128 → ℂ)
    (hUnit : ∀ U V : CMatrix (Fin 2), Uᴴ * U = 1 → Vᴴ * V = 1 →
      linkMatrix U V * ((∑ a, rankOne (vAB a)) + ∑ b, rankOne (vBA b)) * (linkMatrix U V)ᴴ =
        dilutedSwitchOutput lambda mu (singleKraus U) (singleKraus V)) :
    (∀ a : KA, vAB a ∈ universalSupport) ∧ (∀ b : KB, vBA b ∈ universalSupport) := by
  let v : KA ⊕ KB → Fin 128 → ℂ := Sum.elim vAB vBA
  have hv : (∑ k, rankOne (v k)) = (∑ a, rankOne (vAB a)) + ∑ b, rankOne (vBA b) := by
    simp [v, Fintype.sum_sum_type]
  have hall (k : KA ⊕ KB) : v k ∈ universalSupport := by
    rw [universalSupport_eq_range_E]
    obtain ⟨x, hx⟩ := each_kraus_supported v (fun U V hU hV => by
      refine ⟨unitaryWeights lambda mu, ?_⟩
      rw [hv, hUnit U V hU hV]
      unfold dilutedSwitchOutput
      rw [← linked_target_kraus lambda mu (singleKraus U) (singleKraus V)
        (singleKraus_complete U hU) (singleKraus_complete V hV),
        singleKraus_link]
      exact target_unitary_support lambda mu hl0 hl1 hm0 hm1 U V hU hV) k
    exact ⟨x, by simpa only [Matrix.mulVecLin_apply, ← encode_eq_mulVec] using hx⟩
  exact ⟨fun a => hall (Sum.inl a), fun b => hall (Sum.inr b)⟩

/-- **Lemma 8(a) in `range E` form**: every Kraus vector of both ordered components
has explicit `Fin 25 → ℂ` coordinates in the columns of `E`. -/
theorem ordered_component_kraus_in_range_E {KA KB : Type*} [Fintype KA] [Fintype KB]
    (lambda mu : ℝ) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1)
    (hm0 : 0 ≤ mu) (hm1 : mu ≤ 1)
    (vAB : KA → Fin 128 → ℂ) (vBA : KB → Fin 128 → ℂ)
    (hUnit : ∀ U V : CMatrix (Fin 2), Uᴴ * U = 1 → Vᴴ * V = 1 →
      linkMatrix U V * ((∑ a, rankOne (vAB a)) + ∑ b, rankOne (vBA b)) * (linkMatrix U V)ᴴ =
        dilutedSwitchOutput lambda mu (singleKraus U) (singleKraus V)) :
    (∀ a : KA, ∃ x : Fin 25 → ℂ, supportMatrix *ᵥ x = vAB a) ∧
      (∀ b : KB, ∃ y : Fin 25 → ℂ, supportMatrix *ᵥ y = vBA b) := by
  have h := ordered_component_kraus_in_support lambda mu hl0 hl1 hm0 hm1 vAB vBA hUnit
  rw [universalSupport_eq_range_E] at h
  exact ⟨fun a => by simpa [Matrix.mulVecLin_apply] using h.1 a,
    fun b => by simpa [Matrix.mulVecLin_apply] using h.2 b⟩

section StrategySupport

variable {M : Type} [Fintype M] [DecidableEq M]

/-- Unitary qubit box `Ad(U)` acting on the query qubit and as identity on memory `M`. -/
def unitaryBoxChannel (U : CMatrix (Fin 2)) (hU : Uᴴ * U = 1) :
    Channel (Fin 2 × M) (Fin 2 × M) :=
  ICO.AllChannelDilation.oracleChannel (singleKraus U) (singleKraus_complete U hU)

theorem unitaryBoxChannel_apply (U : CMatrix (Fin 2)) (hU : Uᴴ * U = 1)
    (ρ : CMatrix (Fin 2 × M)) :
    (unitaryBoxChannel (M := M) U hU).map ρ =
      Matrix.kronecker U (1 : CMatrix M) * ρ * (Matrix.kronecker U (1 : CMatrix M))ᴴ := by
  simp [unitaryBoxChannel, ICO.AllChannelDilation.oracleChannel,
    ICO.AllChannelDilation.oracleMap, MatrixMap.ofKraus, Fin.sum_univ_four,
    singleKraus]

/-- The diluted switch `T_{λ, μ}[U, V]` of equation (`eq:dilution`) on qubit unitaries `U, V`,
as a `MatrixMap (Fin 2) (Fin 2 × Fin 2)` (target input to control×target output). -/
def dilutedSwitchUnitaryMap (lambda mu : ℝ) (U V : CMatrix (Fin 2)) :
    MatrixMap (Fin 2) (Fin 2 × Fin 2) :=
  ((lambda * mu) •
    ICO.EmbeddingSwitchChannels.switchMap (fun _ : Fin 1 => U) (fun _ : Fin 1 => V)) +
  ((lambda * (1 - mu)) •
    ICO.EmbeddingSwitchChannels.switchMap (fun _ : Fin 1 => U) (fun _ : Fin 1 => (1 : CMatrix (Fin 2)))) +
  (((1 - lambda) * mu) •
    ICO.EmbeddingSwitchChannels.switchMap (fun _ : Fin 1 => (1 : CMatrix (Fin 2))) (fun _ : Fin 1 => V)) +
  (((1 - lambda) * (1 - mu)) •
    ICO.EmbeddingSwitchChannels.switchMap
      (fun _ : Fin 1 => (1 : CMatrix (Fin 2))) (fun _ : Fin 1 => (1 : CMatrix (Fin 2))))

private theorem switchChoi_single_id_right (U : CMatrix (Fin 2)) :
    switchChoi (fun _ : Fin 1 => U) (fun _ : Fin 1 => (1 : CMatrix (Fin 2))) =
      queryChoi (singleKraus U) := by
  have hout : outputVector U (1 : CMatrix (Fin 2)) 3 = queryOutput U := by
    funext o
    simp [outputVector, queryOutput]
  have hzero : queryOutput (0 : CMatrix (Fin 2)) = 0 := by
    funext o
    simp [queryOutput, outputVector]
  have hr0 : rankOne (0 : Fin 8 → ℂ) = 0 := by
    ext i j; simp [rankOne, Matrix.vecMulVec_apply]
  simp [switchChoi, queryChoi, hout, singleKraus, apply_ite, hzero, hr0]

private theorem switchChoi_single_id_left (V : CMatrix (Fin 2)) :
    switchChoi (fun _ : Fin 1 => (1 : CMatrix (Fin 2))) (fun _ : Fin 1 => V) =
      queryChoi (singleKraus V) := by
  have hout : outputVector (1 : CMatrix (Fin 2)) V 3 = queryOutput V := by
    funext o
    simp [outputVector, queryOutput]
  have hzero : queryOutput (0 : CMatrix (Fin 2)) = 0 := by
    funext o
    simp [queryOutput, outputVector]
  have hr0 : rankOne (0 : Fin 8 → ℂ) = 0 := by
    ext i j; simp [rankOne, Matrix.vecMulVec_apply]
  simp [switchChoi, queryChoi, hout, singleKraus, apply_ite, hzero, hr0]

private theorem switchChoi_single_id_both :
    switchChoi (fun _ : Fin 1 => (1 : CMatrix (Fin 2))) (fun _ : Fin 1 => (1 : CMatrix (Fin 2))) =
      identityChoi := by
  have hout : outputVector (1 : CMatrix (Fin 2)) (1 : CMatrix (Fin 2)) 3 = identityOutput := by
    funext o
    fin_cases o <;> simp [outputVector, identityOutput, bit]
  simp [switchChoi, identityChoi, hout]

private theorem switchChoi_single_both (U V : CMatrix (Fin 2)) :
    switchChoi (fun _ : Fin 1 => U) (fun _ : Fin 1 => V) =
      switchChoi (singleKraus U) (singleKraus V) := by
  have houtU (V' : CMatrix (Fin 2)) : outputVector (0 : CMatrix (Fin 2)) V' 3 = 0 := by
    funext o; simp [outputVector]
  have houtV (U' : CMatrix (Fin 2)) : outputVector U' (0 : CMatrix (Fin 2)) 3 = 0 := by
    funext o; simp [outputVector]
  have hr0 : rankOne (0 : Fin 8 → ℂ) = 0 := by
    ext i j; simp [rankOne, Matrix.vecMulVec_apply]
  unfold switchChoi
  congr 1
  simp [Fin.sum_univ_four, singleKraus, houtU, houtV, hr0]

private theorem choi_add' {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (Φ Ψ : MatrixMap I O) : MatrixMap.choi (Φ + Ψ) = MatrixMap.choi Φ + MatrixMap.choi Ψ := rfl

private theorem choi_smul_real' {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (r : ℝ) (Φ : MatrixMap I O) : MatrixMap.choi (r • Φ) = r • MatrixMap.choi Φ := rfl

private theorem comp_smul_real' {I M0 O : Type*} [Fintype I] [Fintype M0] [Fintype O]
    [DecidableEq I] [DecidableEq M0] [DecidableEq O]
    (Ψ : MatrixMap M0 O) (r : ℝ) (Φ : MatrixMap I M0) :
    Ψ.comp (r • Φ) = r • (Ψ.comp Φ) := by
  ext X i j
  simp [LinearMap.comp_apply, Complex.real_smul]

theorem flattened_dilutedSwitchUnitaryMap (lambda mu : ℝ) (U V : CMatrix (Fin 2)) :
    ICO.QubitChoiIndex.flatten
      (MatrixMap.choi (permutationChannel.map.comp (dilutedSwitchUnitaryMap lambda mu U V))) =
        dilutedSwitchOutput lambda mu (singleKraus U) (singleKraus V) := by
  unfold dilutedSwitchUnitaryMap
  simp only [LinearMap.comp_add, comp_smul_real', choi_add', choi_smul_real',
    ICO.QubitChoiIndex.flatten_add, ICO.QubitChoiIndex.flatten_smul, flattened_switch]
  rw [switchChoi_single_id_right, switchChoi_single_id_left, switchChoi_single_id_both,
    switchChoi_single_both]
  unfold dilutedSwitchOutput
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

/-- Postcompose a one-query normal form with a fixed output channel. -/
def mapOutputOneQuery {A H O O' : Type} [Fintype A] [Fintype H] [Fintype O] [Fintype O']
    [DecidableEq A] [DecidableEq H] [DecidableEq O] [DecidableEq O']
    (postCh : Channel O O') (R : ICO.OneQueryTree.NormalForm A H O) :
    ICO.OneQueryTree.NormalForm A H O' where
  Branch := R.Branch
  pre := R.pre
  post := fun b => postCh.comp (R.post b)

/-- Postcompose a two-query normal form with a fixed output channel. -/
def mapOutputNormalForm {A H O O' : Type} [Fintype A] [Fintype H] [Fintype O] [Fintype O']
    [DecidableEq A] [DecidableEq H] [DecidableEq O] [DecidableEq O']
    (postCh : Channel O O') (R : ICO.TwoQueryTree.NormalForm A H O) :
    ICO.TwoQueryTree.NormalForm A H O' where
  Branch := R.Branch
  pre := R.pre
  order := R.order
  rest := fun b => mapOutputOneQuery postCh (R.rest b)

theorem mapOutputNormalForm_channel {A H O O' : Type}
    [Fintype A] [Fintype H] [Fintype O] [Fintype O']
    [DecidableEq A] [DecidableEq H] [DecidableEq O] [DecidableEq O']
    (postCh : Channel O O') (R : ICO.TwoQueryTree.NormalForm A H O)
    (first second : Channel H H) :
    ((mapOutputNormalForm postCh R).channel first second).map =
      postCh.map.comp ((R.channel first second).map) := by
  ext X i j
  simp [mapOutputNormalForm, mapOutputOneQuery,
    ICO.TwoQueryTree.NormalForm.channel_apply,
    ICO.OneQueryTree.NormalForm.channel_apply, Channel.comp, map_sum]

/-- Canonical `A`-before-`B` Kraus vectors of a normal-form two-query qubit strategy. -/
def normalFormABKraus (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4))
    (z : (b : R.Branch) × (abBranch R b).K) : Fin 128 → ℂ :=
  circuitVectors (abBranch R z.1).pre (abBranch R z.1).mid (abBranch R z.1).post z.2

/-- Canonical `B`-before-`A` Kraus vectors of a normal-form two-query qubit strategy. -/
def normalFormBAKraus (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4))
    (z : (b : R.Branch) × (baBranch R b).K) : Fin 128 → ℂ :=
  reverseVectors (baBranch R z.1).pre (baBranch R z.1).mid (baBranch R z.1).post z.2

theorem normalFormAB_sum_rankOne (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4)) :
    familyMatrix (abBranch R) = ∑ z, rankOne (normalFormABKraus R z) := by
  simp [familyMatrix, Branch.matrix, matrix_decomposition, Fintype.sum_sigma, normalFormABKraus]

theorem normalFormBA_sum_rankOne (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4)) :
    reverseFamilyMatrix (baBranch R) = ∑ z, rankOne (normalFormBAKraus R z) := by
  simp [reverseFamilyMatrix, Branch.reverse, reverse_decomposition, Fintype.sum_sigma,
    normalFormBAKraus]

/-- **Lemma 8(a) (`Fin 4` output convention)**: for any one-call-each qubit `QueryTree`
implementing `T_{λ, μ}[U, V]` on all pairs of qubit unitaries (`0 ≤ λ, μ ≤ 1`), every
canonical Kraus vector — and every Kraus vector of any rank-one Kraus decomposition of
its two ordered components — lies in `𝒱`. -/
theorem lem_support_part_a_fin4
    (lambda mu : ℝ) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1)
    (hm0 : 0 ≤ mu) (hm1 : mu ≤ 1)
    (tree : ICO.TwoQueryTree.QueryTree (Fin 2 × M) (Fin 4) (Fin 2))
    (hUnit : ∀ U V : CMatrix (Fin 2), ∀ (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1),
      flattenChoi (MatrixMap.choi
        ((tree.channel (unitaryBoxChannel U hU) (unitaryBoxChannel V hV)).map)) =
        dilutedSwitchOutput lambda mu (singleKraus U) (singleKraus V)) :
    (∀ z, normalFormABKraus tree.normalForm z ∈ universalSupport) ∧
      (∀ z, normalFormBAKraus tree.normalForm z ∈ universalSupport) ∧
      (∀ {KA KB : Type} [Fintype KA] [Fintype KB]
        (vAB : KA → Fin 128 → ℂ) (vBA : KB → Fin 128 → ℂ),
        familyMatrix (abBranch tree.normalForm) = ∑ a, rankOne (vAB a) →
        reverseFamilyMatrix (baBranch tree.normalForm) = ∑ b, rankOne (vBA b) →
        (∀ a, vAB a ∈ universalSupport) ∧ (∀ b, vBA b ∈ universalSupport)) := by
  let R := tree.normalForm
  have hLink : ∀ U V : CMatrix (Fin 2), Uᴴ * U = 1 → Vᴴ * V = 1 →
      linkMatrix U V * (familyMatrix (abBranch R) + reverseFamilyMatrix (baBranch R)) *
        (linkMatrix U V)ᴴ =
          dilutedSwitchOutput lambda mu (singleKraus U) (singleKraus V) := by
    intro U V hU hV
    rw [← singleKraus_link]
    have hout := hUnit U V hU hV
    rw [← ICO.TwoQueryTree.QueryTree.normalForm_correct] at hout
    unfold unitaryBoxChannel at hout
    rw [normalForm_output R (singleKraus U) (singleKraus V)
      (singleKraus_complete U hU) (singleKraus_complete V hV)] at hout
    rw [← hout]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Matrix.mul_add, Matrix.add_mul, linked_family, linked_reverseFamily]
  have hgen : ∀ {KA KB : Type} [Fintype KA] [Fintype KB]
      (vAB : KA → Fin 128 → ℂ) (vBA : KB → Fin 128 → ℂ),
      familyMatrix (abBranch R) = ∑ a, rankOne (vAB a) →
      reverseFamilyMatrix (baBranch R) = ∑ b, rankOne (vBA b) →
      (∀ a, vAB a ∈ universalSupport) ∧ (∀ b, vBA b ∈ universalSupport) := by
    intro KA KB _ _ vAB vBA hA hB
    apply ordered_component_kraus_in_support lambda mu hl0 hl1 hm0 hm1 vAB vBA
    intro U V hU hV
    rw [← hA, ← hB]
    exact hLink U V hU hV
  have hcan := hgen (normalFormABKraus R) (normalFormBAKraus R)
    (normalFormAB_sum_rankOne R) (normalFormBA_sum_rankOne R)
  exact ⟨hcan.1, hcan.2, hgen⟩

/-- Flattened normal form of a one-call-each qubit `QueryTree` with `Fin 2 × Fin 2`
control×target output. -/
def treeFlatNormalForm
    (tree : ICO.TwoQueryTree.QueryTree (Fin 2 × M) (Fin 2 × Fin 2) (Fin 2)) :
    ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4) :=
  mapOutputNormalForm permutationChannel tree.normalForm

/-- Canonical `A`-before-`B` Kraus vectors of a one-call-each qubit `QueryTree`
with `Fin 2 × Fin 2` control×target output. -/
def abKrausVector
    (tree : ICO.TwoQueryTree.QueryTree (Fin 2 × M) (Fin 2 × Fin 2) (Fin 2))
    (z : (b : (treeFlatNormalForm tree).Branch) × (abBranch (treeFlatNormalForm tree) b).K) :
    Fin 128 → ℂ :=
  normalFormABKraus (treeFlatNormalForm tree) z

/-- Canonical `B`-before-`A` Kraus vectors of a one-call-each qubit `QueryTree`
with `Fin 2 × Fin 2` control×target output. -/
def baKrausVector
    (tree : ICO.TwoQueryTree.QueryTree (Fin 2 × M) (Fin 2 × Fin 2) (Fin 2))
    (z : (b : (treeFlatNormalForm tree).Branch) × (baBranch (treeFlatNormalForm tree) b).K) :
    Fin 128 → ℂ :=
  normalFormBAKraus (treeFlatNormalForm tree) z

/-- **Lemma 8(a) (`lem:support`, part (a), paper `Fin 2 × Fin 2` output convention)**:
let an ordinary strategy with one call to each qubit box implement `T_{λ, μ}[U, V]`
for all pairs of qubit unitaries `U, V`, for some `λ, μ ∈ [0, 1]`. Then every Kraus
vector of the strategy (both its canonical Kraus vectors and those of any Kraus
decomposition of its two ordered components) lies in `𝒱`. -/
theorem lem_support_part_a
    (lambda mu : ℝ) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1)
    (hm0 : 0 ≤ mu) (hm1 : mu ≤ 1)
    (tree : ICO.TwoQueryTree.QueryTree (Fin 2 × M) (Fin 2 × Fin 2) (Fin 2))
    (hUnit : ∀ U V : CMatrix (Fin 2), ∀ (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1),
      (tree.channel (unitaryBoxChannel U hU) (unitaryBoxChannel V hV)).map =
        dilutedSwitchUnitaryMap lambda mu U V) :
    (∀ z, abKrausVector tree z ∈ universalSupport) ∧
      (∀ z, baKrausVector tree z ∈ universalSupport) ∧
      (∀ {KA KB : Type} [Fintype KA] [Fintype KB]
        (vAB : KA → Fin 128 → ℂ) (vBA : KB → Fin 128 → ℂ),
        familyMatrix (abBranch (treeFlatNormalForm tree)) = ∑ a, rankOne (vAB a) →
        reverseFamilyMatrix (baBranch (treeFlatNormalForm tree)) = ∑ b, rankOne (vBA b) →
        (∀ a, vAB a ∈ universalSupport) ∧ (∀ b, vBA b ∈ universalSupport)) := by
  let R := treeFlatNormalForm tree
  have hLink : ∀ U V : CMatrix (Fin 2), Uᴴ * U = 1 → Vᴴ * V = 1 →
      linkMatrix U V * (familyMatrix (abBranch R) + reverseFamilyMatrix (baBranch R)) *
        (linkMatrix U V)ᴴ =
          dilutedSwitchOutput lambda mu (singleKraus U) (singleKraus V) := by
    intro U V hU hV
    rw [← singleKraus_link]
    have hch : flattenChoi (MatrixMap.choi
        ((R.channel (unitaryBoxChannel (M := M) U hU) (unitaryBoxChannel (M := M) V hV)).map)) =
        dilutedSwitchOutput lambda mu (singleKraus U) (singleKraus V) := by
      change ICO.QubitChoiIndex.flatten (MatrixMap.choi
        (((mapOutputNormalForm permutationChannel tree.normalForm).channel
          (unitaryBoxChannel (M := M) U hU) (unitaryBoxChannel (M := M) V hV)).map)) = _
      rw [mapOutputNormalForm_channel, ICO.TwoQueryTree.QueryTree.normalForm_correct,
        hUnit U V hU hV]
      exact flattened_dilutedSwitchUnitaryMap lambda mu U V
    unfold unitaryBoxChannel at hch
    rw [normalForm_output R (singleKraus U) (singleKraus V)
      (singleKraus_complete U hU) (singleKraus_complete V hV)] at hch
    rw [← hch]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Matrix.mul_add, Matrix.add_mul, linked_family, linked_reverseFamily]
  have hgen : ∀ {KA KB : Type} [Fintype KA] [Fintype KB]
      (vAB : KA → Fin 128 → ℂ) (vBA : KB → Fin 128 → ℂ),
      familyMatrix (abBranch R) = ∑ a, rankOne (vAB a) →
      reverseFamilyMatrix (baBranch R) = ∑ b, rankOne (vBA b) →
      (∀ a, vAB a ∈ universalSupport) ∧ (∀ b, vBA b ∈ universalSupport) := by
    intro KA KB _ _ vAB vBA hA hB
    apply ordered_component_kraus_in_support lambda mu hl0 hl1 hm0 hm1 vAB vBA
    intro U V hU hV
    rw [← hA, ← hB]
    exact hLink U V hU hV
  have hcan := hgen (normalFormABKraus R) (normalFormBAKraus R)
    (normalFormAB_sum_rankOne R) (normalFormBA_sum_rankOne R)
  exact ⟨hcan.1, hcan.2, hgen⟩

/-- **Lemma 8 (`lem:support`, unified `(a) + (b)`)**: combines universal-support confinement
of one-call-each strategies on `[0, 1]^2` with `𝒱 = range E` and `dim_ℂ 𝒱 = 25`. -/
theorem lem_support :
    (∀ (lambda mu : ℝ), 0 ≤ lambda → lambda ≤ 1 → 0 ≤ mu → mu ≤ 1 →
      ∀ (tree : ICO.TwoQueryTree.QueryTree (Fin 2 × M) (Fin 2 × Fin 2) (Fin 2)),
      (∀ U V : CMatrix (Fin 2), ∀ (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1),
        (tree.channel (unitaryBoxChannel U hU) (unitaryBoxChannel V hV)).map =
          dilutedSwitchUnitaryMap lambda mu U V) →
      (∀ z, abKrausVector tree z ∈ universalSupport) ∧
        (∀ z, baKrausVector tree z ∈ universalSupport)) ∧
    (universalSupport = LinearMap.range (Matrix.mulVecLin supportMatrix) ∧
      Module.finrank ℂ universalSupport = 25 ∧
      Matrix.rank supportMatrix = 25) :=
  ⟨fun lambda mu hl0 hl1 hm0 hm1 tree hUnit =>
    ⟨(lem_support_part_a lambda mu hl0 hl1 hm0 hm1 tree hUnit).1,
     (lem_support_part_a lambda mu hl0 hl1 hm0 hm1 tree hUnit).2.1⟩,
   lem_support_part_b⟩

end StrategySupport

/-! ## Section 2: Non-Dependent Binary Trees & Sparse Row Bridge -/

/-- Non-dependent binary tree for fast kernel lookups and integer accumulation. -/
inductive GenTree (α : Type) where
  | leaf : α → GenTree α
  | branch : GenTree α → GenTree α → GenTree α

def genTreeConst {α : Type} (v : α) : Nat → GenTree α
  | 0 => .leaf v
  | d + 1 => .branch (genTreeConst v d) (genTreeConst v d)

def genTreeGet {α : Type} (default : α) : Nat → GenTree α → Nat → α
  | 0, .leaf v, _ => v
  | d + 1, .branch l r, idx =>
    if idx % 2 == 0 then genTreeGet default d l (idx / 2)
    else genTreeGet default d r (idx / 2)
  | _, _, _ => default

def GenTreeWF {α : Type} : Nat → GenTree α → Prop
  | 0, .leaf _ => True
  | d + 1, .branch l r => GenTreeWF d l ∧ GenTreeWF d r
  | _, _ => False

theorem genTreeWF_const {α : Type} (v : α) : ∀ d : Nat, GenTreeWF d (genTreeConst v d)
  | 0 => trivial
  | d + 1 => ⟨genTreeWF_const v d, genTreeWF_const v d⟩

theorem genTreeGet_const {α : Type} (v : α) :
    ∀ (d : Nat) (q : Nat), genTreeGet v d (genTreeConst v d) q = v
  | 0, _ => rfl
  | d + 1, q => by
    simp only [genTreeConst, genTreeGet]
    split_ifs <;> exact genTreeGet_const v d (q / 2)

abbrev IntTree := GenTree Int

def zeroIntTree (d : Nat) : IntTree := genTreeConst 0 d

def intTreeGet (d : Nat) (t : IntTree) (idx : Nat) : Int := genTreeGet 0 d t idx

@[simp] theorem intTreeGet_zero (d q : Nat) : intTreeGet d (zeroIntTree d) q = 0 :=
  genTreeGet_const 0 d q

def intTreeAdd : Nat → IntTree → Nat → Int → IntTree
  | 0, .leaf v, _, delta => .leaf (v + delta)
  | d + 1, .branch l r, idx, delta =>
    if idx % 2 == 0 then .branch (intTreeAdd d l (idx / 2) delta) r
    else .branch l (intTreeAdd d r (idx / 2) delta)
  | _, t, _, _ => t

theorem intTreeAdd_wf : ∀ (d : Nat) (t : IntTree) (idx : Nat) (delta : Int),
    GenTreeWF d t → GenTreeWF d (intTreeAdd d t idx delta)
  | 0, .leaf _, _, _, _ => trivial
  | d + 1, .branch l r, idx, delta, ⟨hl, hr⟩ => by
    simp only [intTreeAdd]
    split_ifs
    · exact ⟨intTreeAdd_wf d l _ _ hl, hr⟩
    · exact ⟨hl, intTreeAdd_wf d r _ _ hr⟩

theorem intTreeGet_add : ∀ (d : Nat) (t : IntTree) {idx q : Nat} (delta : Int),
    GenTreeWF d t → idx < 2 ^ d → q < 2 ^ d →
    intTreeGet d (intTreeAdd d t idx delta) q =
      intTreeGet d t q + (if q = idx then delta else 0)
  | 0, .leaf v, idx, q, delta, _, hidx, hq => by
    have h1 : q = idx := by omega
    simp [intTreeGet, genTreeGet, intTreeAdd, h1]
  | d + 1, .branch l r, idx, q, delta, ⟨hl, hr⟩, hidx, hq => by
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have hidx2 : idx / 2 < 2 ^ d := by omega
    have hq2 : q / 2 < 2 ^ d := by omega
    simp only [intTreeAdd]
    by_cases hi : (idx % 2 == 0) = true
    · rw [if_pos hi]
      simp only [intTreeGet, genTreeGet]
      by_cases hqm : (q % 2 == 0) = true
      · simp only [hqm, ↓reduceIte]
        have ih := intTreeGet_add d l delta hl hidx2 hq2
        simp only [intTreeGet] at ih
        rw [ih]
        have heq : (q = idx) ↔ (q / 2 = idx / 2) := by
          simp only [beq_iff_eq] at hi hqm; omega
        simp [heq]
      · have hqmf : (q % 2 == 0) = false := Bool.eq_false_iff.mpr hqm
        simp only [hqmf, Bool.false_eq_true, ↓reduceIte]
        have hne : q ≠ idx := by
          simp only [beq_iff_eq] at hi hqm; omega
        simp [hne]
    · rw [if_neg hi]
      simp only [intTreeGet, genTreeGet]
      by_cases hqm : (q % 2 == 0) = true
      · simp only [hqm, ↓reduceIte]
        have hne : q ≠ idx := by
          simp only [beq_iff_eq] at hi hqm; omega
        simp [hne]
      · have hqmf : (q % 2 == 0) = false := Bool.eq_false_iff.mpr hqm
        simp only [hqmf, Bool.false_eq_true, ↓reduceIte]
        have ih := intTreeGet_add d r delta hr hidx2 hq2
        simp only [intTreeGet] at ih
        rw [ih]
        have heq : (q = idx) ↔ (q / 2 = idx / 2) := by
          simp only [beq_iff_eq] at hi hqm; omega
        simp [heq]

def intTreeBeq : Nat → IntTree → IntTree → Bool
  | 0, .leaf a, .leaf b => a == b
  | d + 1, .branch al ar, .branch bl br => intTreeBeq d al bl && intTreeBeq d ar br
  | _, _, _ => false

theorem intTreeBeq_sound : ∀ (d : Nat) (a b : IntTree),
    intTreeBeq d a b = true → ∀ q < 2 ^ d, intTreeGet d a q = intTreeGet d b q
  | 0, .leaf va, .leaf vb, h, _, _ => by
    simp only [intTreeBeq, beq_iff_eq] at h
    simpa [intTreeGet, genTreeGet] using h
  | 0, .leaf _, .branch _ _, h, _, _ => by simp [intTreeBeq] at h
  | 0, .branch _ _, _, h, _, _ => by simp [intTreeBeq] at h
  | d + 1, .branch al ar, .branch bl br, h, q, hq => by
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have hq2 : q / 2 < 2 ^ d := by omega
    simp only [intTreeBeq, Bool.and_eq_true] at h
    simp only [intTreeGet, genTreeGet]
    split_ifs
    · exact intTreeBeq_sound d al bl h.1 (q / 2) hq2
    · exact intTreeBeq_sound d ar br h.2 (q / 2) hq2
  | d + 1, .leaf _, _, h, _, _ => by simp [intTreeBeq] at h
  | d + 1, .branch _ _, .leaf _, h, _, _ => by simp [intTreeBeq] at h

def addScaledPairsNatTree (t : IntTree) (scale : Int) (pairs : List (Nat × Int)) : IntTree :=
  pairs.foldl (fun acc cw => intTreeAdd 9 acc cw.1 (scale * cw.2)) t

theorem addScaledPairsNatTree_wf (t : IntTree) (scale : Int) (pairs : List (Nat × Int))
    (ht : GenTreeWF 9 t) : GenTreeWF 9 (addScaledPairsNatTree t scale pairs) := by
  induction pairs generalizing t with
  | nil => exact ht
  | cons cw rest ih =>
    exact ih (intTreeAdd 9 t cw.1 (scale * cw.2)) (intTreeAdd_wf 9 t cw.1 (scale * cw.2) ht)

private theorem sum_map_const_mul {α : Type*} (l : List α) (w : Int) (f : α → Int) :
    (l.map (fun x => w * f x)).sum = w * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x rest ih => simp [ih, mul_add]

theorem intTreeGet_addScaledPairsNatTree (t : IntTree) (scale : Int) (pairs : List (Nat × Int))
    (ht : GenTreeWF 9 t) (hp : ∀ cw ∈ pairs, cw.1 < 512) {q : Nat} (hq : q < 512) :
    intTreeGet 9 (addScaledPairsNatTree t scale pairs) q =
      intTreeGet 9 t q + scale * (pairs.map (fun cw => if q = cw.1 then cw.2 else 0)).sum := by
  induction pairs generalizing t with
  | nil => simp [addScaledPairsNatTree]
  | cons cw rest ih =>
    have hcw : cw.1 < 512 := hp cw (by simp)
    have hrest : ∀ x ∈ rest, x.1 < 512 := fun x hx => hp x (by simp [hx])
    simp only [addScaledPairsNatTree, List.foldl_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih _ (intTreeAdd_wf 9 t _ _ ht) hrest,
      intTreeGet_add 9 t (scale * cw.2) ht (by omega) (by omega)]
    by_cases he : q = cw.1
    · simp [he]; ring
    · simp [he]

def pairNat (a b : Nat) : Nat :=
  let lo := min a b
  let hi := max a b
  (25 * lo - lo * (lo - 1) / 2 + hi - lo) % 325

theorem pairNat_lt_325 (a b : Nat) : pairNat a b < 325 :=
  Nat.mod_lt _ (by decide)

theorem pairNat_eq_pairIndex_val (a b : Fin 25) :
    pairNat a.val b.val = (pairIndex a b).val := rfl

/-- Balanced depth-7 lookup tree of nonzero columns of `E` per row `i ∈ 0..127`. -/
def supportColsTree : GenTree (List Nat) :=
  .branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [0, 16, 20, 24]) (.leaf [])) (.branch (.leaf [8, 22]) (.leaf [16, 24]))) (.branch (.branch (.leaf [4, 21]) (.leaf [])) (.branch (.leaf [12, 23]) (.leaf [])))) (.branch (.branch (.branch (.leaf [2, 18]) (.leaf [20])) (.branch (.leaf [10]) (.leaf [18, 22]))) (.branch (.branch (.leaf [6, 24]) (.leaf [21])) (.branch (.leaf [14]) (.leaf [23, 24]))))) (.branch (.branch (.branch (.branch (.leaf [1, 17]) (.leaf [])) (.branch (.leaf [9]) (.leaf [17]))) (.branch (.branch (.leaf [5]) (.leaf [])) (.branch (.leaf [13]) (.leaf [])))) (.branch (.branch (.branch (.leaf [3, 19]) (.leaf [])) (.branch (.leaf [11]) (.leaf [19]))) (.branch (.branch (.leaf [7]) (.leaf [])) (.branch (.leaf [15]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [0, 16, 20, 24]) (.leaf [])) (.branch (.leaf [8, 22]) (.leaf [16]))) (.branch (.branch (.leaf [4, 21]) (.leaf [])) (.branch (.leaf [12, 23]) (.leaf [])))) (.branch (.branch (.branch (.leaf [2, 18]) (.leaf [20, 24])) (.branch (.leaf [10]) (.leaf [18, 22]))) (.branch (.branch (.leaf [6]) (.leaf [21])) (.branch (.leaf [14]) (.leaf [23]))))) (.branch (.branch (.branch (.branch (.leaf [1, 17]) (.leaf [])) (.branch (.leaf [9, 24]) (.leaf [17]))) (.branch (.branch (.leaf [5]) (.leaf [])) (.branch (.leaf [13]) (.leaf [])))) (.branch (.branch (.branch (.leaf [3, 19]) (.leaf [])) (.branch (.leaf [11]) (.leaf [19, 24]))) (.branch (.branch (.leaf [7]) (.leaf [])) (.branch (.leaf [15]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [0])) (.branch (.leaf []) (.leaf [8]))) (.branch (.branch (.leaf [16]) (.leaf [4])) (.branch (.leaf []) (.leaf [12, 16])))) (.branch (.branch (.branch (.leaf []) (.leaf [2])) (.branch (.leaf []) (.leaf [10]))) (.branch (.branch (.leaf [18]) (.leaf [6])) (.branch (.leaf []) (.leaf [14, 18]))))) (.branch (.branch (.branch (.branch (.leaf [20, 24]) (.leaf [1])) (.branch (.leaf [22]) (.leaf [9, 24]))) (.branch (.branch (.leaf [17, 21]) (.leaf [5])) (.branch (.leaf [23]) (.leaf [13, 17])))) (.branch (.branch (.branch (.leaf []) (.leaf [3, 20])) (.branch (.leaf []) (.leaf [11, 22]))) (.branch (.branch (.leaf [19, 24]) (.leaf [7, 21])) (.branch (.leaf []) (.leaf [15, 19, 23, 24])))))) (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [0])) (.branch (.leaf []) (.leaf [8]))) (.branch (.branch (.leaf [16, 24]) (.leaf [4])) (.branch (.leaf []) (.leaf [12, 16])))) (.branch (.branch (.branch (.leaf []) (.leaf [2])) (.branch (.leaf []) (.leaf [10]))) (.branch (.branch (.leaf [18]) (.leaf [6, 24])) (.branch (.leaf []) (.leaf [14, 18]))))) (.branch (.branch (.branch (.branch (.leaf [20]) (.leaf [1])) (.branch (.leaf [22]) (.leaf [9]))) (.branch (.branch (.leaf [17, 21]) (.leaf [5])) (.branch (.leaf [23, 24]) (.leaf [13, 17])))) (.branch (.branch (.branch (.leaf []) (.leaf [3, 20])) (.branch (.leaf []) (.leaf [11, 22]))) (.branch (.branch (.leaf [19]) (.leaf [7, 21])) (.branch (.leaf []) (.leaf [15, 19, 23, 24])))))))

def supportColsNat (i : Nat) : List Nat :=
  genTreeGet [] 7 supportColsTree (i % 128)

private def checkSupportColsNat : Bool :=
  (List.range 128).all (fun i =>
    let cols := supportColsNat i
    cols.Nodup &&
    cols.all (· < 25) &&
    (List.range 25).all (fun a =>
      basisEntry i a == (if a ∈ cols then 1 else 0)))

private theorem checkSupportColsNat_true : checkSupportColsNat = true := by
  decide +kernel

private theorem supportColsNat_spec {i : Nat} (hi : i < 128) :
    (supportColsNat i).Nodup ∧
    (∀ a ∈ supportColsNat i, a < 25) ∧
    (∀ a < 25, basisEntry i a = if a ∈ supportColsNat i then 1 else 0) := by
  have h := List.all_eq_true.mp checkSupportColsNat_true i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, fun a ha => h.2 a (List.mem_range.mpr ha)⟩

private theorem sum_finset_mem_list {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Int) :
    ∀ (l : List α), l.Nodup → (∀ x ∈ l, x ∈ s) →
      (∑ x ∈ s, if x ∈ l then f x else 0) = (l.map f).sum
  | [], _, _ => by simp
  | a :: rest, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ s := hsub a (by simp)
    rw [← Finset.add_sum_erase s _ ha]
    simp only [List.mem_cons, true_or, ↓reduceIte, List.map_cons, List.sum_cons]
    congr 1
    have hcongr : (∑ x ∈ s.erase a, if x = a ∨ x ∈ rest then f x else 0) =
        ∑ x ∈ s.erase a, if x ∈ rest then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hne : x ≠ a := (Finset.mem_erase.mp hx).1
      simp [hne]
    rw [hcongr]
    exact sum_finset_mem_list (s.erase a) f rest hnd.2 (fun x hx =>
      Finset.mem_erase.mpr ⟨fun hxa => hnd.1 (hxa ▸ hx), hsub x (by simp [hx])⟩)

theorem choiCoefficient_eq_sum_fin25 (c : Coord) (i j : Fin 128) :
    choiCoefficient (coordinate c).1 (coordinate c).2 i.val j.val =
      ∑ a : Fin 25, ∑ b : Fin 25,
        basisEntry i.val a.val * basisEntry j.val b.val *
          (if c = pairIndex a b then 1 else 0) := by
  apply Int.cast_inj (α := ℝ) |>.mp
  rw [← support_basis_coefficient c i j]
  simp only [Matrix.mul_apply, realSupport, Matrix.transpose_apply,
    symmetricBasis_entry, Finset.sum_mul, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  split_ifs <;> simp

def cellPairsNat (i j : Nat) (w : Int) : List (Nat × Int) :=
  (supportColsNat i).flatMap (fun a => (supportColsNat j).map (fun b => (pairNat a b, w)))

private theorem map_flatMap_sum {α β : Type*} (l : List α) (g : α → List β) (f : β → Int) :
    ((l.flatMap g).map f).sum = (l.map (fun a => ((g a).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons a rest ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem cellPairsNat_lt_325 (i j : Nat) (w : Int) :
    ∀ cw ∈ cellPairsNat i j w, cw.1 < 325 := by
  intro cw hcw
  unfold cellPairsNat at hcw
  rw [List.mem_flatMap] at hcw
  rcases hcw with ⟨a, _, hb⟩
  rw [List.mem_map] at hb
  rcases hb with ⟨b, _, rfl⟩
  exact pairNat_lt_325 a b

theorem cellPairsNat_sum (i j : Nat) (w : Int) (c : Coord) :
    ((cellPairsNat i j w).map (fun cw => if c.val = cw.1 then cw.2 else 0)).sum =
      w * choiCoefficient (coordinate c).1 (coordinate c).2 i j := by
  let im : Fin 128 := modIndex i
  let jm : Fin 128 := modIndex j
  have him : supportColsNat i = supportColsNat im.val := by
    simp [supportColsNat, im, modIndex]
  have hjm : supportColsNat j = supportColsNat jm.val := by
    simp [supportColsNat, jm, modIndex]
  have hchoi : choiCoefficient (coordinate c).1 (coordinate c).2 i j =
      choiCoefficient (coordinate c).1 (coordinate c).2 im.val jm.val := by
    simp [im, jm, modIndex, choiCoefficient_mod128]
  rw [hchoi, choiCoefficient_eq_sum_fin25 c im jm]
  have hpair (a b : Fin 25) : (c = pairIndex a b) ↔ (c.val = pairNat a.val b.val) :=
    ⟨fun h => by rw [h, pairNat_eq_pairIndex_val],
     fun h => Fin.ext (h.trans (pairNat_eq_pairIndex_val a b))⟩
  simp_rw [hpair]
  have hrange : (∑ a : Fin 25, ∑ b : Fin 25,
      basisEntry im.val a.val * basisEntry jm.val b.val *
        (if c.val = pairNat a.val b.val then (1 : Int) else 0)) =
      ∑ a ∈ Finset.range 25, ∑ b ∈ Finset.range 25,
        basisEntry im.val a * basisEntry jm.val b *
          (if c.val = pairNat a b then 1 else 0) := by
    rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin 25,
      basisEntry im.val a * basisEntry jm.val b.val *
        (if c.val = pairNat a b.val then (1 : Int) else 0)) 25]
    apply Finset.sum_congr rfl; intro a _
    exact Fin.sum_univ_eq_sum_range
      (fun b => basisEntry im.val a * basisEntry jm.val b *
        (if c.val = pairNat a b then (1 : Int) else 0)) 25
  rw [hrange]
  unfold cellPairsNat
  rw [him, hjm, map_flatMap_sum]
  simp only [List.map_map, Function.comp_def]
  rcases supportColsNat_spec im.isLt with ⟨hndi, hlti, hbi⟩
  rcases supportColsNat_spec jm.isLt with ⟨hndj, hltj, hbj⟩
  have inner (a : Nat) :
      ((supportColsNat jm.val).map (fun b => if c.val = pairNat a b then w else 0)).sum =
        ∑ b ∈ Finset.range 25,
          basisEntry jm.val b * (if c.val = pairNat a b then w else 0) := by
    rw [← sum_finset_mem_list (Finset.range 25)
      (fun b => if c.val = pairNat a b then w else 0)
      (supportColsNat jm.val) hndj (fun b hb => Finset.mem_range.mpr (hltj b hb))]
    apply Finset.sum_congr rfl; intro b hb
    rw [hbj b (Finset.mem_range.mp hb)]
    split_ifs <;> simp
  simp_rw [inner]
  rw [← sum_finset_mem_list (Finset.range 25)
    (fun a => ∑ b ∈ Finset.range 25,
      basisEntry jm.val b * (if c.val = pairNat a b then w else 0))
    (supportColsNat im.val) hndi (fun a ha => Finset.mem_range.mpr (hlti a ha))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a ha
  rw [hbi a (Finset.mem_range.mp ha), Finset.mul_sum]
  by_cases hmem : a ∈ supportColsNat im.val
  · simp only [hmem, ↓reduceIte]
    apply Finset.sum_congr rfl; intro b _
    split_ifs <;> ring
  · simp [hmem]

def evalNatTerms (C : Nat → Nat → Int) (terms : List ((Nat × Nat) × Int)) : Int :=
  (terms.map (fun t => t.2 * C t.1.1 t.1.2)).sum

def rawNatPairs (terms : List ((Nat × Nat) × Int)) : List (Nat × Int) :=
  terms.flatMap (fun ijw => cellPairsNat ijw.1.1 ijw.1.2 ijw.2)

theorem rawNatPairs_lt_325 (terms : List ((Nat × Nat) × Int)) :
    ∀ cw ∈ rawNatPairs terms, cw.1 < 325 := by
  intro cw hcw
  unfold rawNatPairs at hcw
  rw [List.mem_flatMap] at hcw
  rcases hcw with ⟨ijw, _, hmem⟩
  exact cellPairsNat_lt_325 ijw.1.1 ijw.1.2 ijw.2 cw hmem

theorem rawNatPairs_sum (terms : List ((Nat × Nat) × Int)) (c : Coord) :
    ((rawNatPairs terms).map (fun cw => if c.val = cw.1 then cw.2 else 0)).sum =
      evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2) terms := by
  unfold rawNatPairs evalNatTerms
  rw [map_flatMap_sum]
  congr 1
  apply List.map_congr_left
  intro ijw _
  exact cellPairsNat_sum ijw.1.1 ijw.1.2 ijw.2 c

theorem sum_map_range_eq_sumBelow (n : Nat) (f : Nat → Int) :
    ((List.range n).map f).sum = sumBelow n f := by
  induction n with
  | zero => rfl
  | succ m ih => simp [List.range_succ, sumBelow, ih]

def scaleNatTerms (s : Int) (terms : List ((Nat × Nat) × Int)) : List ((Nat × Nat) × Int) :=
  terms.map (fun t => (t.1, s * t.2))

theorem evalNatTerms_append (C : Nat → Nat → Int) (t1 t2 : List ((Nat × Nat) × Int)) :
    evalNatTerms C (t1 ++ t2) = evalNatTerms C t1 + evalNatTerms C t2 := by
  simp [evalNatTerms, List.map_append, List.sum_append]

theorem evalNatTerms_scale (C : Nat → Nat → Int) (s : Int) (terms : List ((Nat × Nat) × Int)) :
    evalNatTerms C (scaleNatTerms s terms) = s * evalNatTerms C terms := by
  unfold evalNatTerms scaleNatTerms
  rw [List.map_map]
  simpa [Function.comp_def, mul_assoc] using
    sum_map_const_mul terms s (fun t => t.2 * C t.1.1 t.1.2)

def causalOneNatTerms (k : Nat) : List ((Nat × Nat) × Int) :=
  let i := k / 32
  let j := k % 32
  ((List.range 4).map (fun f => ((4 * i + f, 4 * j + f), (2 : Int)))) ++
    if i % 2 == j % 2 then
      (List.range 8).map (fun h => ((8 * (i / 2) + h, 8 * (j / 2) + h), (-1 : Int)))
    else []

theorem evalNatTerms_causalOne (C : Nat → Nat → Int) (k : Nat) :
    evalNatTerms C (causalOneNatTerms k) = ICO.ExactTensorCertificates.causalOne C k := by
  unfold causalOneNatTerms ICO.ExactTensorCertificates.causalOne
  dsimp only
  rw [evalNatTerms_append]
  have h1 : evalNatTerms C ((List.range 4).map (fun f => ((4 * (k / 32) + f, 4 * (k % 32) + f), (2 : Int)))) =
      2 * sumBelow 4 (fun f => C (4 * (k / 32) + f) (4 * (k % 32) + f)) := by
    unfold evalNatTerms
    rw [List.map_map]
    simp only [Function.comp_def]
    rw [sum_map_const_mul, sum_map_range_eq_sumBelow]
  rw [h1]
  by_cases hm : ((k / 32) % 2 == (k % 32) % 2) = true
  · simp only [hm, ↓reduceIte]
    have h2 : evalNatTerms C
        ((List.range 8).map (fun h => ((8 * ((k / 32) / 2) + h, 8 * ((k % 32) / 2) + h), (-1 : Int)))) =
        -sumBelow 8 (fun h => C (8 * ((k / 32) / 2) + h) (8 * ((k % 32) / 2) + h)) := by
      unfold evalNatTerms
      rw [List.map_map]
      simp only [Function.comp_def]
      rw [sum_map_const_mul, sum_map_range_eq_sumBelow]
      omega
    rw [h2]; omega
  · have hmf : ((k / 32) % 2 == (k % 32) % 2) = false := Bool.eq_false_iff.mpr hm
    simp only [hmf, Bool.false_eq_true, ↓reduceIte, evalNatTerms,
      List.map_nil, List.sum_nil, add_zero, sub_zero]

def causalTwoNatTerms (k : Nat) : List ((Nat × Nat) × Int) :=
  let i := k / 8
  let j := k % 8
  ((List.range 16).map (fun h => ((16 * i + h, 16 * j + h), (2 : Int)))) ++
    if i % 2 == j % 2 then
      (List.range 32).map (fun h => ((32 * (i / 2) + h, 32 * (j / 2) + h), (-1 : Int)))
    else []

theorem evalNatTerms_causalTwo (C : Nat → Nat → Int) (k : Nat) :
    evalNatTerms C (causalTwoNatTerms k) = ICO.ExactTensorCertificates.causalTwo C k := by
  unfold causalTwoNatTerms ICO.ExactTensorCertificates.causalTwo
  dsimp only
  rw [evalNatTerms_append]
  have h1 : evalNatTerms C ((List.range 16).map (fun h => ((16 * (k / 8) + h, 16 * (k % 8) + h), (2 : Int)))) =
      2 * sumBelow 16 (fun h => C (16 * (k / 8) + h) (16 * (k % 8) + h)) := by
    unfold evalNatTerms
    rw [List.map_map]
    simp only [Function.comp_def]
    rw [sum_map_const_mul, sum_map_range_eq_sumBelow]
  rw [h1]
  by_cases hm : ((k / 8) % 2 == (k % 8) % 2) = true
  · simp only [hm, ↓reduceIte]
    have h2 : evalNatTerms C
        ((List.range 32).map (fun h => ((32 * ((k / 8) / 2) + h, 32 * ((k % 8) / 2) + h), (-1 : Int)))) =
        -sumBelow 32 (fun h => C (32 * ((k / 8) / 2) + h) (32 * ((k % 8) / 2) + h)) := by
      unfold evalNatTerms
      rw [List.map_map]
      simp only [Function.comp_def]
      rw [sum_map_const_mul, sum_map_range_eq_sumBelow]
      omega
    rw [h2]; omega
  · have hmf : ((k / 8) % 2 == (k % 8) % 2) = false := Bool.eq_false_iff.mpr hm
    simp only [hmf, Bool.false_eq_true, ↓reduceIte, evalNatTerms,
      List.map_nil, List.sum_nil, add_zero, sub_zero]

def abNatTerms (k : Nat) : List ((Nat × Nat) × Int) :=
  if k < 1024 then causalOneNatTerms k else causalTwoNatTerms (k - 1024)

theorem evalNatTerms_ab (k : Nat) (c : Coord) :
    evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2) (abNatTerms k) =
      coefficient rowAB k c := by
  unfold abNatTerms coefficient rowAB ICO.ExactTensorCertificates.causalRow
  split_ifs
  · exact evalNatTerms_causalOne _ k
  · exact evalNatTerms_causalTwo _ (k - 1024)

def baNatTerms (k : Nat) : List ((Nat × Nat) × Int) :=
  (abNatTerms k).map (fun t =>
    ((ICO.ExactTensorCertificates.swapSlots t.1.1,
      ICO.ExactTensorCertificates.swapSlots t.1.2), t.2))

theorem evalNatTerms_ba (k : Nat) (c : Coord) :
    evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2) (baNatTerms k) =
      coefficient rowBA k c := by
  have hswap (terms : List ((Nat × Nat) × Int)) :
      evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2)
        (terms.map (fun t =>
          ((ICO.ExactTensorCertificates.swapSlots t.1.1,
            ICO.ExactTensorCertificates.swapSlots t.1.2), t.2))) =
        evalNatTerms
          (fun i j => choiCoefficient (coordinate c).1 (coordinate c).2
            (ICO.ExactTensorCertificates.swapSlots i)
            (ICO.ExactTensorCertificates.swapSlots j)) terms := by
    unfold evalNatTerms
    rw [List.map_map]; rfl
  unfold baNatTerms coefficient rowBA ICO.ExactTensorCertificates.causalRow
  rw [hswap]
  unfold abNatTerms
  split_ifs
  · exact evalNatTerms_causalOne _ k
  · exact evalNatTerms_causalTwo _ (k - 1024)

def traceReplaceNatTerms (unit size i j : Nat) : List ((Nat × Nat) × Int) :=
  if i / unit % size == j / unit % size then
    (List.range size).map (fun h =>
      ((i / (unit * size) * (unit * size) + h * unit + i % unit,
        j / (unit * size) * (unit * size) + h * unit + j % unit), (1 : Int)))
  else []

theorem evalNatTerms_traceReplace (unit size : Nat) (C : Nat → Nat → Int) (i j : Nat) :
    evalNatTerms C (traceReplaceNatTerms unit size i j) =
      ICO.ExactTensorCertificates.traceReplace unit size C i j := by
  unfold traceReplaceNatTerms ICO.ExactTensorCertificates.traceReplace
  split_ifs
  · unfold evalNatTerms
    rw [List.map_map]
    simp only [Function.comp_def, one_mul]
    exact sum_map_range_eq_sumBelow size _
  · simp [evalNatTerms]

def b4NatTerms (i j : Nat) : List ((Nat × Nat) × Int) :=
  [((i, j), (4 : Int))] ++
    scaleNatTerms (-2) (traceReplaceNatTerms 4 2 i j) ++
    traceReplaceNatTerms 4 4 i j

theorem evalNatTerms_b4 (C : Nat → Nat → Int) (i j : Nat) :
    evalNatTerms C (b4NatTerms i j) = ICO.ExactTensorCertificates.projectB4 C i j := by
  unfold b4NatTerms ICO.ExactTensorCertificates.projectB4
  rw [evalNatTerms_append, evalNatTerms_append, evalNatTerms_scale,
    evalNatTerms_traceReplace, evalNatTerms_traceReplace]
  simp [evalNatTerms]; omega

def a4NatTerms (i j : Nat) : List ((Nat × Nat) × Int) :=
  [((i, j), (4 : Int))] ++
    scaleNatTerms (-2) (traceReplaceNatTerms 16 2 i j) ++
    traceReplaceNatTerms 16 4 i j

theorem evalNatTerms_a4 (C : Nat → Nat → Int) (i j : Nat) :
    evalNatTerms C (a4NatTerms i j) = ICO.ExactTensorCertificates.projectA4 C i j := by
  unfold a4NatTerms ICO.ExactTensorCertificates.projectA4
  rw [evalNatTerms_append, evalNatTerms_append, evalNatTerms_scale,
    evalNatTerms_traceReplace, evalNatTerms_traceReplace]
  simp [evalNatTerms]; omega

def gaugeNatTerms (k : Nat) : List ((Nat × Nat) × Int) :=
  (a4NatTerms (k % 128) (k / 128)).flatMap (fun t =>
    scaleNatTerms t.2 (b4NatTerms t.1.1 t.1.2))

theorem evalNatTerms_gauge (k : Nat) (c : Coord) :
    evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2) (gaugeNatTerms k) =
      coefficient rowGauge16 k c := by
  unfold gaugeNatTerms coefficient rowGauge16
  unfold evalNatTerms
  rw [map_flatMap_sum]
  have hinner (t : (Nat × Nat) × Int) :
      ((scaleNatTerms t.2 (b4NatTerms t.1.1 t.1.2)).map
        (fun x => x.2 * choiCoefficient (coordinate c).1 (coordinate c).2 x.1.1 x.1.2)).sum =
        t.2 * ICO.ExactTensorCertificates.projectB4
          (choiCoefficient (coordinate c).1 (coordinate c).2) t.1.1 t.1.2 := by
    change evalNatTerms _ (scaleNatTerms t.2 (b4NatTerms t.1.1 t.1.2)) = _
    rw [evalNatTerms_scale, evalNatTerms_b4]
  simp_rw [hinner]
  exact evalNatTerms_a4 _ (k % 128) (k / 128)

def buildCombinedNatTree (termsFn : Nat → List ((Nat × Nat) × Int))
    (comb : List (Nat × Int)) : IntTree :=
  comb.foldl (fun acc kc => addScaledPairsNatTree acc kc.2 (rawNatPairs (termsFn kc.1)))
    (zeroIntTree 9)

theorem intTreeGet_buildCombinedNatTree (termsFn : Nat → List ((Nat × Nat) × Int))
    (row : Nat → Nat → Nat → Int)
    (ht : ∀ k c, evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2) (termsFn k) =
      coefficient row k c)
    (comb : List (Nat × Int)) (c : Coord) :
    intTreeGet 9 (buildCombinedNatTree termsFn comb) c.val =
      combinedCoefficient comb (coefficient row) c := by
  unfold buildCombinedNatTree
  suffices h : ∀ (acc : IntTree), GenTreeWF 9 acc →
      intTreeGet 9
        (comb.foldl (fun a kc => addScaledPairsNatTree a kc.2 (rawNatPairs (termsFn kc.1))) acc)
        c.val = intTreeGet 9 acc c.val + combinedCoefficient comb (coefficient row) c by
    rw [h (zeroIntTree 9) (genTreeWF_const 0 9), intTreeGet_zero, zero_add]
  induction comb with
  | nil => intro acc _; simp [combinedCoefficient]
  | cons kc rest ih =>
    intro acc hwf
    simp only [List.foldl_cons]
    have hcc : combinedCoefficient (kc :: rest) (coefficient row) c =
        kc.2 * coefficient row kc.1 c + combinedCoefficient rest (coefficient row) c := by
      simp [combinedCoefficient]
    have hlt : ∀ cw ∈ rawNatPairs (termsFn kc.1), cw.1 < 512 :=
      fun cw hcw => Nat.lt_trans (rawNatPairs_lt_325 _ cw hcw) (by decide)
    rw [ih _ (addScaledPairsNatTree_wf acc kc.2 _ hwf),
      intTreeGet_addScaledPairsNatTree acc kc.2 _ hwf hlt (Nat.lt_trans c.isLt (by decide)),
      rawNatPairs_sum, ht, hcc]
    omega

/-! ## Section 3: R8(a) — Switch-Weight Functional `X_{24, 24}` and Gauge Invariance -/

/-- Coordinate index `324 : Coord` corresponding to `(24, 24)` (`X_{24, 24}`). -/
def switchCoord : Coord := ⟨324, by decide⟩

theorem coordinate_switchCoord : coordinate switchCoord = (24, 24) := by
  have hp : switchCoord = pairIndex 24 24 := by decide +kernel
  rw [hp, pairIndex_coordinate]
  rfl

/-- The switch-weight coordinate functional `X ↦ X_{24, 24}` on `ℝ^325`. -/
def x24_24 (X : CoordVec) : ℝ := X switchCoord

def x24_24_gaugeScale : Int := 8

/-- Explicit 4-row integer combination of `rowGauge16` yielding `8 * e_{24, 24}`. -/
def x24_24_gaugeRows : List (Nat × Int) := [(153, -1), (155, 1), (409, 1), (411, -1)]

theorem x24_24_gauge_rows_in_range : ∀ kc ∈ x24_24_gaugeRows, kc.1 < 16384 := by
  decide +kernel

private def checkX24GaugeBool : Bool :=
  intTreeBeq 9
    (buildCombinedNatTree gaugeNatTerms x24_24_gaugeRows)
    (intTreeAdd 9 (zeroIntTree 9) 324 x24_24_gaugeScale)

private theorem checkX24GaugeBool_true : checkX24GaugeBool = true := by
  decide +kernel

/-- **R8(a), row-space certificate**: `X ↦ X_{24, 24}` lies in the row space of the
gauge system `16 Λ_A Λ_B (E X Eᵀ)`, certified by 4 rows with denominator `8`. -/
theorem x24_24_in_gauge_row_space (c : Coord) :
    combinedCoefficient x24_24_gaugeRows (coefficient rowGauge16) c =
      x24_24_gaugeScale * (if c = switchCoord then 1 else 0) := by
  rw [← intTreeGet_buildCombinedNatTree gaugeNatTerms rowGauge16 evalNatTerms_gauge]
  have h := intTreeBeq_sound 9 _ _ checkX24GaugeBool_true c.val (Nat.lt_trans c.isLt (by decide))
  rw [h, intTreeGet_add 9 (zeroIntTree 9) x24_24_gaugeScale (genTreeWF_const 0 9)
    (by decide) (Nat.lt_trans c.isLt (by decide)), intTreeGet_zero, zero_add]
  have heq : (c.val = 324) ↔ (c = switchCoord) := ⟨fun h0 => Fin.ext h0, congrArg Fin.val⟩
  by_cases hc : c = switchCoord
  · subst hc; simp [switchCoord]
  · simp [heq, hc]

theorem x24_24_eq_gauge_combination (X : CoordVec) :
    x24_24 X = (1 / 8 : ℝ) * combinedValue x24_24_gaugeRows (coefficient rowGauge16) X := by
  rw [combination_expands]
  simp_rw [x24_24_in_gauge_row_space]
  simp [x24_24, x24_24_gaugeScale, mul_ite]

/-- **R8(a), vanishing on the gauge**: whenever `E X Eᵀ` lies in the CPTP gauge,
the switch weight `X_{24, 24}` vanishes. -/
theorem x24_24_vanishes_on_gauge (X : CoordVec)
    (hGauge : ∀ k < 16384, rowValue (coefficient rowGauge16) k X = 0) :
    x24_24 X = 0 := by
  rw [x24_24_eq_gauge_combination,
    combination_zero x24_24_gaugeRows (coefficient rowGauge16) X
      (fun kc hkc => hGauge kc.1 (x24_24_gauge_rows_in_range kc hkc)),
    mul_zero]

/-! ### Direct physical `U = σ_x, V = σ_z` argument (`sec:diluted-coordinates`) -/

/-- Pauli `σ_x` unitary used in `sec:diluted-coordinates` (`U = σ_x`). -/
def pauliX : CMatrix (Fin 2) := ![![0, 1], ![1, 0]]

/-- Pauli `σ_z` unitary used in `sec:diluted-coordinates` (`V = σ_z`). -/
def pauliZ : CMatrix (Fin 2) := ![![1, 0], ![0, -1]]

theorem pauliX_unitary : pauliXᴴ * pauliX = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_unitary : pauliZᴴ * pauliZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Probe vector in `ℂ^8` orthogonal to the first three operators of (`eq:four-kraus`)
for `(σ_x, σ_z)` and having inner product `4` with the fourth. -/
def pauliProbe : Fin 8 → ℂ := ![0, -1, 0, 1, 1, 0, -1, 0]

theorem pauli_outputVector_ortho (a b : Fin 4) :
    star (outputVector pauliX pauliZ a) ⬝ᵥ outputVector pauliX pauliZ b =
      if a = b then 4 else 0 := by
  fin_cases a <;> fin_cases b
  all_goals
    simp [outputVector, pauliX, pauliZ, bit, dotProduct, Fin.sum_univ_eight,
      Matrix.mul_apply, Fin.sum_univ_two]
    try norm_num

theorem pauli_four_kraus_linearIndependent :
    LinearIndependent ℂ (outputVector pauliX pauliZ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have hdot : star (outputVector pauliX pauliZ a) ⬝ᵥ
      (∑ b : Fin 4, g b • outputVector pauliX pauliZ b) = 0 := by
    rw [hg, dotProduct_zero]
  simp only [dotProduct_sum, dotProduct_smul, pauli_outputVector_ortho,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hdot
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hdot).resolve_right h4

theorem pauliProbe_eq_output3 : pauliProbe = outputVector pauliX pauliZ 3 := by
  funext o
  fin_cases o
  all_goals
    simp [pauliProbe, outputVector, pauliX, pauliZ, bit, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliProbe_dot_output (b : Fin 4) :
    star pauliProbe ⬝ᵥ outputVector pauliX pauliZ b = if b = 3 then 4 else 0 := by
  rw [pauliProbe_eq_output3, pauli_outputVector_ortho]
  by_cases hb : b = 3 <;> simp [hb, eq_comm]

theorem pauliProbe_dot_linked_basis (a : Fin 25) :
    star pauliProbe ⬝ᵥ (linkMatrix pauliX pauliZ *ᵥ basisVector a) =
      if a = 24 then 4 else 0 := by
  rw [linked_basis pauliX pauliZ a, dotProduct_smul, pauliProbe_dot_output]
  by_cases ha : a = 24
  · subst ha
    have hg24 : columnGroup 24 = 3 := by decide
    have hs24 : columnScale pauliX pauliZ 24 = 1 := by norm_num [columnScale]
    simp [hg24, hs24]
  · have hg : columnGroup a ≠ 3 := by
      have hlt : a.val < 24 := by
        have := a.isLt
        have : a.val ≠ 24 := fun h => ha (Fin.ext h)
        omega
      unfold columnGroup
      split_ifs <;> decide
    simp [ha, hg]

/-- The complex `128 × 128` matrix `E X Eᵀ` associated to a real `25 × 25` matrix `X`. -/
def supportedComplexMatrix (X : Matrix (Fin 25) (Fin 25) ℝ) : Matrix (Fin 128) (Fin 128) ℂ :=
  supportMatrix * X.map Complex.ofReal * supportMatrixᵀ

private def pauliLinkedCols : Matrix (Fin 8) (Fin 25) ℂ :=
  fun o a => (linkMatrix pauliX pauliZ *ᵥ basisVector a) o

theorem pauli_probe_sandwich (X : Matrix (Fin 25) (Fin 25) ℝ) :
    star pauliProbe ⬝ᵥ
      ((linkMatrix pauliX pauliZ * supportedComplexMatrix X * (linkMatrix pauliX pauliZ)ᴴ) *ᵥ
        pauliProbe) = 16 * (X 24 24 : ℂ) := by
  have hLM : linkMatrix pauliX pauliZ * supportMatrix = pauliLinkedCols := by
    ext o a
    simp [pauliLinkedCols, Matrix.mul_apply, Matrix.mulVec, dotProduct, supportMatrix, basisVector]
  have hsuppH : supportMatrixᴴ = supportMatrixᵀ := by
    ext a i; simp [supportMatrix]
  have hrewrite : linkMatrix pauliX pauliZ * supportedComplexMatrix X * (linkMatrix pauliX pauliZ)ᴴ =
      pauliLinkedCols * X.map Complex.ofReal * pauliLinkedColsᴴ := by
    calc linkMatrix pauliX pauliZ * supportedComplexMatrix X * (linkMatrix pauliX pauliZ)ᴴ
      _ = (linkMatrix pauliX pauliZ * supportMatrix) * X.map Complex.ofReal *
            (linkMatrix pauliX pauliZ * supportMatrix)ᴴ := by
            simp only [supportedComplexMatrix, ← hsuppH, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = pauliLinkedCols * X.map Complex.ofReal * pauliLinkedColsᴴ := by rw [hLM]
  let u : Fin 25 → ℂ := pauliLinkedColsᴴ *ᵥ pauliProbe
  have hu (a : Fin 25) : u a = if a = 24 then 4 else 0 := by
    have hdot : u a = star (star pauliProbe ⬝ᵥ (linkMatrix pauliX pauliZ *ᵥ basisVector a)) := by
      simp [u, pauliLinkedCols, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        star_sum, mul_comm]
    rw [hdot, pauliProbe_dot_linked_basis]
    by_cases ha : a = 24 <;> simp [ha]
  have hleft : star pauliProbe ᵥ* pauliLinkedCols = star u := by
    funext a
    simp [u, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      star_sum, mul_comm]
  rw [hrewrite, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, hleft]
  change ∑ a : Fin 25, star (u a) * (X.map Complex.ofReal *ᵥ u) a = 16 * (X 24 24 : ℂ)
  rw [Finset.sum_eq_single (24 : Fin 25)]
  · simp only [hu, ↓reduceIte, Matrix.mulVec, dotProduct, Matrix.map_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
    norm_num
    ring
  · intro a _ ha
    simp [hu a, ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **R8(a), direct Pauli `(σ_x, σ_z)` proof**: if `E X Eᵀ` vanishes on `(U, V) = (σ_x, σ_z)`,
then `X 24 24 = 0` (`x24_24 (coefficients X) = 0`). -/
theorem x24_24_vanishes_of_pauli_link (X : Matrix (Fin 25) (Fin 25) ℝ)
    (hPauli : linkMatrix pauliX pauliZ * supportedComplexMatrix X * (linkMatrix pauliX pauliZ)ᴴ = 0) :
    X 24 24 = 0 ∧ x24_24 (coefficients X) = 0 := by
  have h := pauli_probe_sandwich X
  rw [hPauli, Matrix.zero_mulVec, dotProduct_zero] at h
  have h16 : (16 : ℂ) ≠ 0 := by norm_num
  have hc : (X 24 24 : ℂ) = 0 := (mul_eq_zero.mp h.symm).resolve_left h16
  have hr : X 24 24 = 0 := Complex.ofReal_eq_zero.mp hc
  have hsw : coefficients X switchCoord = X 24 24 := by
    unfold coefficients
    simp only [coordinate_switchCoord]
    congr 1
  exact ⟨hr, by simpa [x24_24, hsw] using hr⟩

/-- The off-diagonal coherence part `g(X) = f(X) - X_{24, 24}` of the witness functional `f`. -/
def offDiagonalFunctional (X : CoordVec) : ℝ :=
  functional X - x24_24 X

theorem witnessCoefficient_switchCoord : witnessCoefficient switchCoord = 1 := by
  unfold witnessCoefficient
  rw [coordinate_switchCoord]
  decide +kernel

theorem offDiagonalFunctional_eq_sum_ne (X : CoordVec) :
    offDiagonalFunctional X =
      ∑ c ∈ Finset.univ.erase switchCoord, (witnessCoefficient c : ℝ) * X c := by
  unfold offDiagonalFunctional functional x24_24
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ switchCoord),
    witnessCoefficient_switchCoord]
  ring

theorem offDiagonalFunctional_sub (X Y : CoordVec) :
    offDiagonalFunctional (X - Y) = offDiagonalFunctional X - offDiagonalFunctional Y := by
  unfold offDiagonalFunctional x24_24
  rw [functional_sub, Pi.sub_apply]
  ring

theorem offDiagonalFunctional_vanishes_on_gauge (X : CoordVec)
    (hGauge : ∀ k < 16384, rowValue (coefficient rowGauge16) k X = 0) :
    offDiagonalFunctional X = 0 := by
  unfold offDiagonalFunctional
  rw [gauge_functional_zero X hGauge, x24_24_vanishes_on_gauge X hGauge, sub_zero]

/-- **R8(a), decomposition and gauge invariance (`functional_eq_x24_24_add_gauge_invariant`)**:
`f(X) = X_{24, 24} + g(X)`, where both `X_{24, 24}` and the off-diagonal functional `g`
vanish on the CPTP gauge and are therefore gauge-invariant. -/
theorem functional_eq_x24_24_add_gauge_invariant :
    (∀ X : CoordVec, functional X = x24_24 X + offDiagonalFunctional X) ∧
    (∀ X : CoordVec,
      (∀ k < 16384, rowValue (coefficient rowGauge16) k X = 0) →
      x24_24 X = 0 ∧ offDiagonalFunctional X = 0) ∧
    (∀ X X' : CoordVec,
      (∀ k < 16384, rowValue (coefficient rowGauge16) k (X - X') = 0) →
      x24_24 X = x24_24 X' ∧
        offDiagonalFunctional X = offDiagonalFunctional X' ∧
        functional X = functional X') := by
  refine ⟨fun X => by unfold offDiagonalFunctional; ring,
    fun X hG => ⟨x24_24_vanishes_on_gauge X hG, offDiagonalFunctional_vanishes_on_gauge X hG⟩,
    fun X X' hG => ?_⟩
  have hx := x24_24_vanishes_on_gauge (X - X') hG
  have hg := offDiagonalFunctional_vanishes_on_gauge (X - X') hG
  have hf := gauge_functional_zero (X - X') hG
  have hx' : x24_24 X = x24_24 X' := sub_eq_zero.mp (by simpa [x24_24] using hx)
  have hg' : offDiagonalFunctional X = offDiagonalFunctional X' := by
    rw [offDiagonalFunctional_sub] at hg
    exact sub_eq_zero.mp hg
  have hf' : functional X = functional X' := by
    rw [functional_sub] at hf
    exact sub_eq_zero.mp hf
  exact ⟨hx', hg', hf'⟩

/-! ## Section 4: R8(b) — Solution-Space Dimension `126` and Admissible-Functional Dimension `199` -/

theorem rowValue_add (row : Nat → Coord → Int) (k : Nat) (X Y : CoordVec) :
    rowValue row k (X + Y) = rowValue row k X + rowValue row k Y := by
  simp [rowValue, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem rowValue_zero (row : Nat → Coord → Int) (k : Nat) :
    rowValue row k 0 = 0 := by
  simp [rowValue]

theorem rowValue_smul (row : Nat → Coord → Int) (k : Nat) (r : ℝ) (X : CoordVec) :
    rowValue row k (r • X) = r * rowValue row k X := by
  simp [rowValue, Pi.smul_apply, Finset.mul_sum, mul_left_comm]

/-- Solution space of system (a) (`AB`-causal equations) in `ℝ^325`. -/
def solAB : Submodule ℝ CoordVec where
  carrier := { X | ∀ k < 1088, rowValue (coefficient rowAB) k X = 0 }
  add_mem' {X Y} hX hY k hk := by rw [rowValue_add, hX k hk, hY k hk, add_zero]
  zero_mem' k _ := rowValue_zero _ k
  smul_mem' r {X} hX k hk := by rw [rowValue_smul, hX k hk, mul_zero]

/-- Solution space of system (b) (`BA`-causal equations) in `ℝ^325`. -/
def solBA : Submodule ℝ CoordVec where
  carrier := { X | ∀ k < 1088, rowValue (coefficient rowBA) k X = 0 }
  add_mem' {X Y} hX hY k hk := by rw [rowValue_add, hX k hk, hY k hk, add_zero]
  zero_mem' k _ := rowValue_zero _ k
  smul_mem' r {X} hX k hk := by rw [rowValue_smul, hX k hk, mul_zero]

/-- Solution space of system (c) (`16 Λ_A Λ_B` CPTP gauge equations) in `ℝ^325`. -/
def solGauge : Submodule ℝ CoordVec where
  carrier := { X | ∀ k < 16384, rowValue (coefficient rowGauge16) k X = 0 }
  add_mem' {X Y} hX hY k hk := by rw [rowValue_add, hX k hk, hY k hk, add_zero]
  zero_mem' k _ := rowValue_zero _ k
  smul_mem' r {X} hX k hk := by rw [rowValue_smul, hX k hk, mul_zero]

/-- Row vector of a constraint system in `ℝ^325`. -/
def rowVec (row : Nat → Coord → Int) (k : Nat) : CoordVec :=
  fun c => (row k c : ℝ)

/-- Row space of system (a) (`AB`-causal) in `ℝ^325`. -/
def rowSpaceAB : Submodule ℝ CoordVec :=
  Submodule.span ℝ (Set.range (fun k : Fin 1088 => rowVec (coefficient rowAB) k.val))

/-- Row space of system (b) (`BA`-causal) in `ℝ^325`. -/
def rowSpaceBA : Submodule ℝ CoordVec :=
  Submodule.span ℝ (Set.range (fun k : Fin 1088 => rowVec (coefficient rowBA) k.val))

/-- Row space of system (c) (CPTP gauge) in `ℝ^325`. -/
def rowSpaceGauge : Submodule ℝ CoordVec :=
  Submodule.span ℝ (Set.range (fun k : Fin 16384 => rowVec (coefficient rowGauge16) k.val))

/-- Space of admissible linear functionals on `ℝ^325` satisfying properties (a)–(c)
of Lemma 9 (`lem:exact-obstruction`), i.e., vanishing on `solAB`, `solBA`, and `solGauge`. -/
def AdmissibleFunctionals : Submodule ℝ (CoordVec →ₗ[ℝ] ℝ) where
  carrier := { φ | (∀ X ∈ solAB, φ X = 0) ∧ (∀ X ∈ solBA, φ X = 0) ∧ (∀ X ∈ solGauge, φ X = 0) }
  add_mem' {φ ψ} hφ hψ :=
    ⟨fun X hX => by simp [hφ.1 X hX, hψ.1 X hX],
     fun X hX => by simp [hφ.2.1 X hX, hψ.2.1 X hX],
     fun X hX => by simp [hφ.2.2 X hX, hψ.2.2 X hX]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  smul_mem' r {φ} hφ :=
    ⟨fun X hX => by simp [hφ.1 X hX],
     fun X hX => by simp [hφ.2.1 X hX],
     fun X hX => by simp [hφ.2.2 X hX]⟩

/-- The published witness functional `f` as a linear map `CoordVec →ₗ[ℝ] ℝ`. -/
def functionalLinear : CoordVec →ₗ[ℝ] ℝ where
  toFun := functional
  map_add' := functional_add
  map_smul' r X := by simp [functional, Pi.smul_apply, Finset.mul_sum, mul_left_comm]

theorem functionalLinear_mem_admissible : functionalLinear ∈ AdmissibleFunctionals :=
  ⟨fun X hX => ab_functional_zero X hX,
   fun X hX => ba_functional_zero X hX,
   fun X hX => gauge_functional_zero X hX⟩

/-- Standard dot-product linear equivalence between `ℝ^325` and its dual `CoordVec →ₗ[ℝ] ℝ`. -/
def toDualEquiv : CoordVec ≃ₗ[ℝ] (CoordVec →ₗ[ℝ] ℝ) where
  toFun w :=
    { toFun := fun X => ∑ c : Coord, w c * X c
      map_add' := fun X Y => by simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r X => by simp [Pi.smul_apply, Finset.mul_sum, mul_left_comm] }
  map_add' u v := by
    apply LinearMap.ext; intro X
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r u := by
    apply LinearMap.ext; intro X
    simp [Pi.smul_apply, Finset.mul_sum, mul_assoc]
  invFun φ := fun c => φ (Pi.single c 1)
  left_inv w := by
    funext c
    simp [Pi.single_apply]
  right_inv φ := by
    apply LinearMap.ext; intro X
    change (∑ c : Coord, φ (Pi.single c 1) * X c) = φ X
    have hX : X = ∑ c : Coord, X c • Pi.single c (1 : ℝ) := by
      funext d
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hX]
    rw [map_sum]
    apply Finset.sum_congr rfl; intro c _
    rw [map_smul, smul_eq_mul, mul_comm]

/-- Coordinate representation of `AdmissibleFunctionals` inside `ℝ^325`. -/
def AdmissibleVectors : Submodule ℝ CoordVec :=
  AdmissibleFunctionals.comap toDualEquiv.toLinearMap

theorem admissibleVectors_eq_map :
    AdmissibleVectors = AdmissibleFunctionals.map toDualEquiv.symm.toLinearMap := by
  ext w
  simp only [AdmissibleVectors, Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · intro hw
    exact ⟨toDualEquiv w, hw, toDualEquiv.symm_apply_apply w⟩
  · rintro ⟨φ, hφ, rfl⟩
    simpa using hφ

theorem finrank_admissibleVectors_eq :
    Module.finrank ℝ AdmissibleVectors = Module.finrank ℝ AdmissibleFunctionals := by
  rw [admissibleVectors_eq_map]
  exact (LinearEquiv.finrank_eq (toDualEquiv.symm.submoduleMap AdmissibleFunctionals)).symm

theorem admissibleVectors_ortho_sup (w : CoordVec) (hw : w ∈ AdmissibleVectors)
    {X : CoordVec} (hX : X ∈ solAB ⊔ solBA ⊔ solGauge) :
    ∑ c : Coord, w c * X c = 0 := by
  let kerW : Submodule ℝ CoordVec := LinearMap.ker (toDualEquiv w)
  have hAB : solAB ≤ kerW := hw.1
  have hBA : solBA ≤ kerW := hw.2.1
  have hG : solGauge ≤ kerW := hw.2.2
  have hsup : solAB ⊔ solBA ⊔ solGauge ≤ kerW := sup_le (sup_le hAB hBA) hG
  exact hsup hX

theorem inf_sol_admissibleVectors_eq_bot :
    (solAB ⊔ solBA ⊔ solGauge) ⊓ AdmissibleVectors = ⊥ := by
  rw [eq_bot_iff]
  intro X ⟨hXsol, hXadm⟩
  rw [Submodule.mem_bot]
  have hsq : ∑ c : Coord, X c * X c = 0 := admissibleVectors_ortho_sup X hXadm hXsol
  funext c
  have hle : X c * X c ≤ ∑ d : Coord, X d * X d :=
    Finset.single_le_sum (fun d _ => mul_self_nonneg (X d)) (Finset.mem_univ c)
  rw [hsq] at hle
  exact mul_self_eq_zero.mp (le_antisymm hle (mul_self_nonneg (X c)))

theorem finrank_sol_add_admissible_le_325 :
    Module.finrank ℝ ↥(solAB ⊔ solBA ⊔ solGauge) +
      Module.finrank ℝ ↥AdmissibleFunctionals ≤ 325 := by
  rw [← finrank_admissibleVectors_eq]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (solAB ⊔ solBA ⊔ solGauge) AdmissibleVectors
  rw [inf_sol_admissibleVectors_eq_bot, finrank_bot, add_zero] at h
  rw [← h]
  have hle := Submodule.finrank_le ((solAB ⊔ solBA ⊔ solGauge) ⊔ AdmissibleVectors)
  simpa [Module.finrank_pi_fintype] using hle

/-! ### Fast List / `GenTree` / Column-Index Helpers for Kernel Verification -/

def listAt {α : Type} (default : α) : List α → Nat → α
  | [], _ => default
  | x :: _, 0 => x
  | _ :: rest, k + 1 => listAt default rest k

private theorem listAt_mem {α : Type} (default : α) :
    ∀ (xs : List α) {k : Nat}, k < xs.length → listAt default xs k ∈ xs
  | [], _, hk => by simp at hk
  | _ :: _, 0, _ => by simp [listAt]
  | _ :: rest, k + 1, hk => by
    have hk' : k < rest.length := by simp at hk; omega
    exact List.mem_cons_of_mem _ (listAt_mem default rest hk')

def allIdxAux {α : Type} (p : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x :: rest => p i x && allIdxAux p (i + 1) rest

def allIdx {α : Type} (xs : List α) (p : Nat → α → Bool) : Bool :=
  allIdxAux p 0 xs

private theorem allIdxAux_sound {α : Type} (default : α) (p : Nat → α → Bool) :
    ∀ (base : Nat) (xs : List α),
      allIdxAux p base xs = true →
      ∀ k < xs.length, p (base + k) (listAt default xs k) = true
  | _, [], _, _, hk => by simp at hk
  | base, x :: rest, h, 0, _ => by
    simp only [allIdxAux, Bool.and_eq_true] at h
    simpa [listAt] using h.1
  | base, _ :: rest, h, k + 1, hk => by
    simp only [allIdxAux, Bool.and_eq_true] at h
    have hk' : k < rest.length := by simp at hk; omega
    have ih := allIdxAux_sound default p (base + 1) rest h.2 k hk'
    have hadd : base + 1 + k = base + (k + 1) := by omega
    simpa [listAt, hadd] using ih

private theorem allIdx_sound {α : Type} (default : α) (xs : List α) (p : Nat → α → Bool)
    (h : allIdx xs p = true) {k : Nat} (hk : k < xs.length) :
    p k (listAt default xs k) = true := by
  simpa using allIdxAux_sound default p 0 xs h k hk

def sparseNatAt (v : List (Nat × Int)) (c : Nat) : Int :=
  (v.map (fun cw => if c = cw.1 then cw.2 else 0)).sum

def sparseNatRealVec (v : List (Nat × Int)) : CoordVec :=
  fun c => (sparseNatAt v c.val : ℝ)

private theorem sum_swap_sparse (rp v : List (Nat × Int)) :
    (rp.map (fun cw => cw.2 * sparseNatAt v cw.1)).sum =
      (v.map (fun dv => dv.2 * (rp.map (fun cw => if dv.1 = cw.1 then cw.2 else 0)).sum)).sum := by
  induction rp with
  | nil => simp
  | cons cw rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    clear ih
    induction v with
    | nil => simp [sparseNatAt]
    | cons dv vrest ihv =>
      simp only [sparseNatAt, List.map_cons, List.sum_cons] at ihv ⊢
      have hlin : cw.2 * ((if cw.1 = dv.1 then dv.2 else 0) +
            (vrest.map (fun x => if cw.1 = x.1 then x.2 else 0)).sum) +
          (dv.2 * (rest.map (fun x => if dv.1 = x.1 then x.2 else 0)).sum +
            (vrest.map (fun d => d.2 * (rest.map (fun x => if d.1 = x.1 then x.2 else 0)).sum)).sum) =
          (cw.2 * (if cw.1 = dv.1 then dv.2 else 0) +
            dv.2 * (rest.map (fun x => if dv.1 = x.1 then x.2 else 0)).sum) +
          (cw.2 * (vrest.map (fun x => if cw.1 = x.1 then x.2 else 0)).sum +
            (vrest.map (fun d => d.2 * (rest.map (fun x => if d.1 = x.1 then x.2 else 0)).sum)).sum) := by
        ring
      rw [hlin, ihv]
      congr 1
      by_cases h : cw.1 = dv.1
      · simp only [h, ↓reduceIte]; ring
      · have h' : dv.1 ≠ cw.1 := Ne.symm h
        simp only [h, h', ↓reduceIte]; ring

abbrev PairListTree := GenTree (List (Nat × Int))

def emptyPairListTree (d : Nat) : PairListTree := genTreeConst [] d

def pairListTreePush : Nat → PairListTree → Nat → (Nat × Int) → PairListTree
  | 0, .leaf xs, _, item => .leaf (item :: xs)
  | d + 1, .branch l r, idx, item =>
    if idx % 2 == 0 then .branch (pairListTreePush d l (idx / 2) item) r
    else .branch l (pairListTreePush d r (idx / 2) item)
  | _, t, _, _ => t

theorem pairListTreePush_wf : ∀ (d : Nat) (t : PairListTree) (idx : Nat) (item : Nat × Int),
    GenTreeWF d t → GenTreeWF d (pairListTreePush d t idx item)
  | 0, .leaf _, _, _, _ => trivial
  | d + 1, .branch l r, idx, item, ⟨hl, hr⟩ => by
    simp only [pairListTreePush]
    split_ifs
    · exact ⟨pairListTreePush_wf d l _ _ hl, hr⟩
    · exact ⟨hl, pairListTreePush_wf d r _ _ hr⟩

theorem pairListTreeGet_push : ∀ (d : Nat) (t : PairListTree) {idx q : Nat} (item : Nat × Int),
    GenTreeWF d t → idx < 2 ^ d → q < 2 ^ d →
    genTreeGet [] d (pairListTreePush d t idx item) q =
      if q = idx then item :: genTreeGet [] d t q else genTreeGet [] d t q
  | 0, .leaf xs, idx, q, item, _, hidx, hq => by
    have h1 : q = idx := by omega
    simp [genTreeGet, pairListTreePush, h1]
  | d + 1, .branch l r, idx, q, item, ⟨hl, hr⟩, hidx, hq => by
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have hidx2 : idx / 2 < 2 ^ d := by omega
    have hq2 : q / 2 < 2 ^ d := by omega
    simp only [pairListTreePush]
    by_cases hi : (idx % 2 == 0) = true
    · rw [if_pos hi]
      simp only [genTreeGet]
      by_cases hqm : (q % 2 == 0) = true
      · simp only [hqm, ↓reduceIte, pairListTreeGet_push d l item hl hidx2 hq2]
        have heq : (q = idx) ↔ (q / 2 = idx / 2) := by
          simp only [beq_iff_eq] at hi hqm; omega
        simp [heq]
      · have hqmf : (q % 2 == 0) = false := Bool.eq_false_iff.mpr hqm
        simp only [hqmf, Bool.false_eq_true, ↓reduceIte]
        have hne : q ≠ idx := by simp only [beq_iff_eq] at hi hqm; omega
        simp [hne]
    · rw [if_neg hi]
      simp only [genTreeGet]
      by_cases hqm : (q % 2 == 0) = true
      · simp only [hqm, ↓reduceIte]
        have hne : q ≠ idx := by simp only [beq_iff_eq] at hi hqm; omega
        simp [hne]
      · have hqmf : (q % 2 == 0) = false := Bool.eq_false_iff.mpr hqm
        simp only [hqmf, Bool.false_eq_true, ↓reduceIte,
          pairListTreeGet_push d r item hr hidx2 hq2]
        have heq : (q = idx) ↔ (q / 2 = idx / 2) := by
          simp only [beq_iff_eq] at hi hqm; omega
        simp [heq]

def insertVecIntoCols (colTree : PairListTree) (vecIdx : Nat) (v : List (Nat × Int)) : PairListTree :=
  v.foldl (fun ct cw => pairListTreePush 9 ct cw.1 (vecIdx, cw.2)) colTree

def buildColIndexAux : List (List (Nat × Int)) → Nat → PairListTree → PairListTree
  | [], _, ct => ct
  | v :: rest, idx, ct => buildColIndexAux rest (idx + 1) (insertVecIntoCols ct idx v)

def buildColIndex (vecs : List (List (Nat × Int))) : PairListTree :=
  buildColIndexAux vecs 0 (emptyPairListTree 9)

private theorem insertVecIntoCols_wf (colTree : PairListTree) (vecIdx : Nat)
    (v : List (Nat × Int)) (hwf : GenTreeWF 9 colTree) :
    GenTreeWF 9 (insertVecIntoCols colTree vecIdx v) := by
  induction v generalizing colTree with
  | nil => exact hwf
  | cons cw rest ih =>
    exact ih _ (pairListTreePush_wf 9 colTree cw.1 (vecIdx, cw.2) hwf)

private theorem insertVecIntoCols_bnd (colTree : PairListTree) (vecIdx bnd : Nat)
    (v : List (Nat × Int)) (hwf : GenTreeWF 9 colTree)
    (hcoords : ∀ cw ∈ v, cw.1 < 512) (hvi : vecIdx < bnd)
    (hbnd : ∀ q < 512, ∀ iv ∈ genTreeGet [] 9 colTree q, iv.1 < bnd) :
    ∀ q < 512, ∀ iv ∈ genTreeGet [] 9 (insertVecIntoCols colTree vecIdx v) q, iv.1 < bnd := by
  induction v generalizing colTree with
  | nil => exact hbnd
  | cons cw rest ih =>
    have hcw : cw.1 < 512 := hcoords cw (by simp)
    have hrest : ∀ x ∈ rest, x.1 < 512 := fun x hx => hcoords x (by simp [hx])
    apply ih _ (pairListTreePush_wf 9 colTree cw.1 (vecIdx, cw.2) hwf) hrest
    intro q hq iv hiv
    rw [pairListTreeGet_push 9 colTree _ hwf hcw hq] at hiv
    split_ifs at hiv
    · simp only [List.mem_cons] at hiv
      rcases hiv with rfl | hm
      · exact hvi
      · exact hbnd q hq iv hm
    · exact hbnd q hq iv hiv

private theorem insertVecIntoCols_sum (colTree : PairListTree) (vecIdx : Nat)
    (v : List (Nat × Int)) (hwf : GenTreeWF 9 colTree)
    (hcoords : ∀ cw ∈ v, cw.1 < 512) {q : Nat} (hq : q < 512) (idx : Nat) :
    ((genTreeGet [] 9 (insertVecIntoCols colTree vecIdx v) q).map
      (fun iv => if idx = iv.1 then iv.2 else 0)).sum =
    ((genTreeGet [] 9 colTree q).map
      (fun iv => if idx = iv.1 then iv.2 else 0)).sum +
      (if idx = vecIdx then sparseNatAt v q else 0) := by
  induction v generalizing colTree with
  | nil => simp [insertVecIntoCols, sparseNatAt]
  | cons cw rest ih =>
    have hcw : cw.1 < 512 := hcoords cw (by simp)
    have hrest : ∀ x ∈ rest, x.1 < 512 := fun x hx => hcoords x (by simp [hx])
    simp only [insertVecIntoCols, List.foldl_cons, sparseNatAt, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih _ (pairListTreePush_wf 9 colTree cw.1 (vecIdx, cw.2) hwf) hrest,
      pairListTreeGet_push 9 colTree _ hwf hcw hq]
    ((by_cases h1 : q = cw.1 <;> by_cases h2 : idx = vecIdx) <;>
      simp only [h1, h2, ↓reduceIte, List.map_cons, List.sum_cons]) <;> omega

private theorem buildColIndexAux_wf :
    ∀ (vecs : List (List (Nat × Int))) (base : Nat) (ct : PairListTree),
      GenTreeWF 9 ct → GenTreeWF 9 (buildColIndexAux vecs base ct)
  | [], _, _, hwf => hwf
  | v :: rest, base, ct, hwf =>
    buildColIndexAux_wf rest (base + 1) _ (insertVecIntoCols_wf ct base v hwf)

private theorem buildColIndexAux_bnd :
    ∀ (vecs : List (List (Nat × Int))) (base bnd : Nat) (ct : PairListTree),
      GenTreeWF 9 ct →
      (∀ v ∈ vecs, ∀ cw ∈ v, cw.1 < 512) →
      base + vecs.length ≤ bnd →
      (∀ q < 512, ∀ iv ∈ genTreeGet [] 9 ct q, iv.1 < bnd) →
      ∀ q < 512, ∀ iv ∈ genTreeGet [] 9 (buildColIndexAux vecs base ct) q, iv.1 < bnd
  | [], _, _, _, _, _, _, hbnd => hbnd
  | v :: rest, base, bnd, ct, hwf, hcoords, hlen, hbnd => by
    have hv : ∀ cw ∈ v, cw.1 < 512 := hcoords v (by simp)
    have hrest : ∀ u ∈ rest, ∀ cw ∈ u, cw.1 < 512 := fun u hu => hcoords u (by simp [hu])
    have hbase : base < bnd := by simp at hlen; omega
    have hlen' : (base + 1) + rest.length ≤ bnd := by simp at hlen; omega
    exact buildColIndexAux_bnd rest (base + 1) bnd _
      (insertVecIntoCols_wf ct base v hwf) hrest hlen'
      (insertVecIntoCols_bnd ct base bnd v hwf hv hbase hbnd)

private theorem buildColIndexAux_sum :
    ∀ (vecs : List (List (Nat × Int))) (base : Nat) (ct : PairListTree),
      GenTreeWF 9 ct →
      (∀ v ∈ vecs, ∀ cw ∈ v, cw.1 < 512) →
      ∀ {q : Nat}, q < 512 → ∀ (idx : Nat),
        ((genTreeGet [] 9 (buildColIndexAux vecs base ct) q).map
          (fun iv => if idx = iv.1 then iv.2 else 0)).sum =
        ((genTreeGet [] 9 ct q).map
          (fun iv => if idx = iv.1 then iv.2 else 0)).sum +
          (if base ≤ idx then sparseNatAt (listAt [] vecs (idx - base)) q else 0)
  | [], base, ct, _, _, _, _, idx => by
    simp [buildColIndexAux, listAt, sparseNatAt]
  | v :: rest, base, ct, hwf, hcoords, q, hq, idx => by
    have hv : ∀ cw ∈ v, cw.1 < 512 := hcoords v (by simp)
    have hrest : ∀ u ∈ rest, ∀ cw ∈ u, cw.1 < 512 := fun u hu => hcoords u (by simp [hu])
    simp only [buildColIndexAux]
    rw [buildColIndexAux_sum rest (base + 1) _ (insertVecIntoCols_wf ct base v hwf) hrest hq idx,
      insertVecIntoCols_sum ct base v hwf hv hq idx]
    by_cases hlt : idx < base
    · have h1 : ¬(base ≤ idx) := by omega
      have h2 : ¬(base + 1 ≤ idx) := by omega
      have h3 : idx ≠ base := by omega
      simp [h1, h2, h3]
    · by_cases heq : idx = base
      · subst heq
        have h2 : ¬(idx + 1 ≤ idx) := by omega
        simp [h2, listAt]
      · have h1 : base ≤ idx := by omega
        have h2 : base + 1 ≤ idx := by omega
        obtain ⟨m, hm⟩ : ∃ m, idx - base = m + 1 := ⟨idx - (base + 1), by omega⟩
        have hm' : idx - (base + 1) = m := by omega
        simp only [heq, ↓reduceIte, h1, h2, hm, hm', listAt]
        omega

theorem buildColIndex_spec (vecs : List (List (Nat × Int)))
    (hlen : vecs.length ≤ 128)
    (hcoords : ∀ v ∈ vecs, ∀ cw ∈ v, cw.1 < 512) :
    (∀ q < 512, ∀ iv ∈ genTreeGet [] 9 (buildColIndex vecs) q, iv.1 < 128) ∧
    (∀ q < 512, ∀ idx : Nat,
      ((genTreeGet [] 9 (buildColIndex vecs) q).map
        (fun iv => if idx = iv.1 then iv.2 else 0)).sum =
      sparseNatAt (listAt [] vecs idx) q) := by
  have hbnd := buildColIndexAux_bnd vecs 0 128 (emptyPairListTree 9)
    (genTreeWF_const [] 9) hcoords (by omega)
    (fun q _ iv hiv => by simp [emptyPairListTree, genTreeGet_const] at hiv)
  refine ⟨hbnd, fun q hq idx => ?_⟩
  have hsum := buildColIndexAux_sum vecs 0 (emptyPairListTree 9)
    (genTreeWF_const [] 9) hcoords hq idx
  simpa [buildColIndex, emptyPairListTree, genTreeGet_const] using hsum

def evalRowAgainstColIndex (colTree : PairListTree) (rp : List (Nat × Int)) : IntTree :=
  rp.foldl (fun acc cw =>
    (genTreeGet [] 9 colTree cw.1).foldl
      (fun acc2 iv => intTreeAdd 7 acc2 iv.1 (cw.2 * iv.2)) acc)
    (zeroIntTree 7)

private theorem innerFold_wf (ivs : List (Nat × Int)) (w : Int) (acc : IntTree)
    (hwf : GenTreeWF 7 acc) :
    GenTreeWF 7 (ivs.foldl (fun acc2 iv => intTreeAdd 7 acc2 iv.1 (w * iv.2)) acc) := by
  induction ivs generalizing acc with
  | nil => exact hwf
  | cons iv rest ih => exact ih _ (intTreeAdd_wf 7 acc iv.1 (w * iv.2) hwf)

private theorem innerFold_get (ivs : List (Nat × Int)) (w : Int) (acc : IntTree)
    (hwf : GenTreeWF 7 acc) (hbnd : ∀ iv ∈ ivs, iv.1 < 128) {idx : Nat} (hidx : idx < 128) :
    intTreeGet 7 (ivs.foldl (fun acc2 iv => intTreeAdd 7 acc2 iv.1 (w * iv.2)) acc) idx =
      intTreeGet 7 acc idx + w * (ivs.map (fun iv => if idx = iv.1 then iv.2 else 0)).sum := by
  induction ivs generalizing acc with
  | nil => simp
  | cons iv rest ih =>
    have hiv : iv.1 < 128 := hbnd iv (by simp)
    have hrest : ∀ x ∈ rest, x.1 < 128 := fun x hx => hbnd x (by simp [hx])
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih _ (intTreeAdd_wf 7 acc iv.1 (w * iv.2) hwf) hrest,
      intTreeGet_add 7 acc (w * iv.2) hwf (by omega) (by omega)]
    by_cases h : idx = iv.1
    · simp [h]; ring
    · simp [h]

theorem evalRowAgainstColIndex_get (vecs : List (List (Nat × Int)))
    (hlen : vecs.length ≤ 128)
    (hcoords : ∀ v ∈ vecs, ∀ cw ∈ v, cw.1 < 512)
    (rp : List (Nat × Int)) (hrp : ∀ cw ∈ rp, cw.1 < 512)
    {idx : Nat} (hidx : idx < 128) :
    intTreeGet 7 (evalRowAgainstColIndex (buildColIndex vecs) rp) idx =
      (rp.map (fun cw => cw.2 * sparseNatAt (listAt [] vecs idx) cw.1)).sum := by
  rcases buildColIndex_spec vecs hlen hcoords with ⟨hbnd, hsum⟩
  unfold evalRowAgainstColIndex
  suffices h : ∀ (acc : IntTree), GenTreeWF 7 acc →
      intTreeGet 7 (rp.foldl (fun a cw =>
        (genTreeGet [] 9 (buildColIndex vecs) cw.1).foldl
          (fun acc2 iv => intTreeAdd 7 acc2 iv.1 (cw.2 * iv.2)) a) acc) idx =
      intTreeGet 7 acc idx + (rp.map (fun cw => cw.2 * sparseNatAt (listAt [] vecs idx) cw.1)).sum by
    rw [h (zeroIntTree 7) (genTreeWF_const 0 7), intTreeGet_zero, zero_add]
  induction rp with
  | nil => intro acc _; simp
  | cons cw rest ih =>
    intro acc hwf
    have hcw : cw.1 < 512 := hrp cw (by simp)
    have hrest : ∀ x ∈ rest, x.1 < 512 := fun x hx => hrp x (by simp [hx])
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    let ivs := genTreeGet [] 9 (buildColIndex vecs) cw.1
    rw [ih hrest (ivs.foldl (fun acc2 iv => intTreeAdd 7 acc2 iv.1 (cw.2 * iv.2)) acc)
        (innerFold_wf ivs cw.2 acc hwf),
      innerFold_get ivs cw.2 acc hwf (hbnd cw.1 hcw) hidx,
      hsum cw.1 hcw idx]
    ring

theorem rowValue_sparseNatRealVec (terms : List ((Nat × Nat) × Int))
    (row : Nat → Nat → Nat → Int) (k : Nat)
    (ht : ∀ c : Coord,
      evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2) terms = coefficient row k c)
    (v : List (Nat × Int)) (hv : ∀ dv ∈ v, dv.1 < 325) :
    rowValue (coefficient row) k (sparseNatRealVec v) =
      (((rawNatPairs terms).map (fun cw => cw.2 * sparseNatAt v cw.1)).sum : ℝ) := by
  rw [sum_swap_sparse]
  unfold rowValue sparseNatRealVec sparseNatAt
  induction v with
  | nil => simp
  | cons dv rest ih =>
    have hdv : dv.1 < 325 := hv dv (by simp)
    have hrest : ∀ x ∈ rest, x.1 < 325 := fun x hx => hv x (by simp [hx])
    simp only [List.map_cons, List.sum_cons, Int.cast_add, mul_add, Finset.sum_add_distrib]
    rw [ih hrest]
    congr 1
    let c0 : Coord := ⟨dv.1, hdv⟩
    have hc0 (c : Coord) : (c.val = dv.1) ↔ (c = c0) :=
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp_rw [hc0]
    have hsingle : (∑ c : Coord,
        (coefficient row k c : ℝ) * ((if c = c0 then dv.2 else 0 : Int) : ℝ)) =
        (dv.2 : ℝ) * (coefficient row k c0 : ℝ) := by
      rw [Finset.sum_eq_single c0]
      · simp [mul_comm]
      · intro c _ hne; simp [hne]
      · simp
    rw [hsingle, ← ht c0, ← rawNatPairs_sum terms c0, Int.cast_mul]

def pairListTreeBeq : Nat → PairListTree → PairListTree → Bool
  | 0, .leaf xs, .leaf ys => xs == ys
  | d + 1, .branch l1 r1, .branch l2 r2 =>
    pairListTreeBeq d l1 l2 && pairListTreeBeq d r1 r2
  | _, _, _ => false

private theorem pairListTreeBeq_eq :
    ∀ (d : Nat) (t1 t2 : PairListTree), pairListTreeBeq d t1 t2 = true → t1 = t2
  | 0, .leaf xs, .leaf ys, h => by
    simp only [pairListTreeBeq, beq_iff_eq] at h; exact congrArg GenTree.leaf h
  | 0, .leaf _, .branch _ _, h => by simp [pairListTreeBeq] at h
  | 0, .branch _ _, _, h => by simp [pairListTreeBeq] at h
  | d + 1, .branch l1 r1, .branch l2 r2, h => by
    simp only [pairListTreeBeq, Bool.and_eq_true] at h
    rw [pairListTreeBeq_eq d l1 l2 h.1, pairListTreeBeq_eq d r1 r2 h.2]
  | _ + 1, .leaf _, _, h => by simp [pairListTreeBeq] at h
  | _ + 1, .branch _ _, .leaf _, h => by simp [pairListTreeBeq] at h

private def checkPrimalSystem (rowCount : Nat) (termsFn : Nat → List ((Nat × Nat) × Int))
    (vecs : List (List (Nat × Int))) (colTree : PairListTree) : Bool :=
  (vecs.length ≤ 128) &&
  vecs.all (fun v => v.all (fun cw => cw.1 < 325)) &&
  pairListTreeBeq 9 colTree (buildColIndex vecs) &&
  ((List.range rowCount).all (fun k =>
     let rp := rawNatPairs (termsFn k)
     rp.isEmpty || intTreeBeq 7 (evalRowAgainstColIndex colTree rp) (zeroIntTree 7)))

private theorem checkPrimalSystem_sound (rowCount : Nat)
    (termsFn : Nat → List ((Nat × Nat) × Int))
    (row : Nat → Nat → Nat → Int)
    (ht : ∀ k c, evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2) (termsFn k) =
      coefficient row k c)
    (vecs : List (List (Nat × Int))) (colTree : PairListTree)
    (hok : checkPrimalSystem rowCount termsFn vecs colTree = true)
    {idx : Nat} (hidx : idx < vecs.length)
    {k : Nat} (hk : k < rowCount) :
    rowValue (coefficient row) k (sparseNatRealVec (listAt [] vecs idx)) = 0 := by
  unfold checkPrimalSystem at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  rcases hok with ⟨⟨⟨hlen, hcoords325⟩, hct_beq⟩, hrows⟩
  have hct : colTree = buildColIndex vecs := pairListTreeBeq_eq 9 _ _ hct_beq
  subst hct
  have hcoords512 : ∀ v ∈ vecs, ∀ cw ∈ v, cw.1 < 512 :=
    fun v hv cw hcw => Nat.lt_trans (hcoords325 v hv cw hcw) (by decide)
  have hv325 : ∀ dv ∈ listAt [] vecs idx, dv.1 < 325 :=
    hcoords325 _ (listAt_mem [] vecs hidx)
  rw [rowValue_sparseNatRealVec (termsFn k) row k (ht k) _ hv325]
  have hrk := hrows k (List.mem_range.mpr hk)
  rw [Bool.or_eq_true] at hrk
  rcases hrk with hemp | hbeq
  · rw [List.isEmpty_iff.mp hemp]; simp
  · have hidx128 : idx < 128 := Nat.lt_of_lt_of_le hidx hlen
    have hrp512 : ∀ cw ∈ rawNatPairs (termsFn k), cw.1 < 512 :=
      fun cw hcw => Nat.lt_trans (rawNatPairs_lt_325 _ cw hcw) (by decide)
    have hget := evalRowAgainstColIndex_get vecs hlen hcoords512 _ hrp512 hidx128
    have hz := intTreeBeq_sound 7 _ _ hbeq idx hidx128
    rw [intTreeGet_zero] at hz
    rw [← hget, hz]
    simp

/-! ### Part 1 of R8(b): `126` Linearly Independent Solution Vectors in `solAB ⊔ solBA` -/

private def primalABNatList_0 : List (List (Nat × Int)) := [
  [(2, 1), (27, 1)],
  [(6, 1), (31, 1)],
  [(10, 1), (35, 1)],
  [(14, 1), (39, 1)],
  [(18, 1), (43, 1)],
  [(51, 1), (74, 1)],
  [(55, 1), (78, 1)],
  [(59, 1), (82, 1)],
  [(63, 1), (86, 1)],
  [(96, 1), (117, 1)],
  [(100, 1), (121, 1)],
  [(104, 1), (125, 1)],
  [(108, 1), (129, 1)],
  [(137, 1), (156, 1)],
  [(141, 1), (160, 1)],
  [(145, 1), (164, 1)],
  [(174, 1), (191, 1)],
  [(178, 1), (195, 1)],
  [(182, 1), (199, 1)],
  [(207, 1), (222, 1)],
  [(211, 1), (226, 1)],
  [(236, 1), (249, 1)]
]

private def primalABNatList_1 : List (List (Nat × Int)) := [
  [(240, 1), (253, 1)],
  [(261, 1), (272, 1)],
  [(280, 1), (289, 1)],
  [(282, 1), (291, 1)],
  [(0, -1), (25, -1), (310, 1)],
  [(4, -1), (29, -1), (311, 1)],
  [(8, -1), (33, -1), (312, 1)],
  [(12, -1), (37, -1), (313, 1)],
  [(0, 1), (25, 1), (315, 1)],
  [(98, -1), (119, -1), (316, 1)],
  [(8, 1), (33, 1), (317, 1)],
  [(172, -1), (189, -1), (319, 1)],
  [(176, -1), (193, -1), (320, 1)],
  [(172, 1), (189, 1), (322, 1)],
  [(0, -1), (25, -1), (49, 1), (72, 1)],
  [(4, -1), (29, -1), (53, 1), (76, 1)],
  [(8, -1), (33, -1), (57, 1), (80, 1)],
  [(12, -1), (37, -1), (61, 1), (84, 1)],
  [(16, -1), (41, -1), (65, 1), (88, 1)],
  [(0, 1), (25, 1), (94, 1), (115, 1)],
  [(8, 1), (33, 1), (102, 1), (123, 1)],
  [(0, 1), (25, 1), (135, 1), (154, 1)]
]

private def primalABNatList_2 : List (List (Nat × Int)) := [
  [(98, -1), (119, -1), (139, 1), (158, 1)],
  [(8, 1), (33, 1), (143, 1), (162, 1)],
  [(106, -1), (127, -1), (147, 1), (166, 1)],
  [(172, -1), (189, -1), (205, 1), (220, 1)],
  [(176, -1), (193, -1), (209, 1), (224, 1)],
  [(180, -1), (197, -1), (213, 1), (228, 1)],
  [(172, 1), (189, 1), (234, 1), (247, 1)],
  [(172, 1), (189, 1), (259, 1), (270, 1)],
  [(238, -1), (251, -1), (263, 1), (274, 1)],
  [(3, 1), (6, -1), (9, -1), (12, 1), (16, -1), (19, -1), (20, -1), (23, -1), (24, 2)],
  [(2, -1), (18, 1), (30, -1), (33, -1), (36, 1), (40, -1), (44, -1), (47, -1), (48, 2)],
  [(50, 1), (53, -1), (56, -1), (59, 1), (63, -1), (66, -1), (67, -1), (70, -1), (71, 2)],
  [(73, 1), (96, -1), (99, -1), (102, 1), (106, -1), (109, -1), (110, -1), (113, -1), (114, 2)],
  [(51, -1), (108, 1), (116, -1), (119, -1), (122, 1), (126, -1), (130, -1), (133, -1), (134, 2)],
  [(75, 1), (135, -2), (138, -1), (141, 1), (145, -1), (148, -1), (149, -1), (152, -1), (153, 2)],
  [(77, 1), (137, -1), (173, -1), (176, 1), (180, -1), (183, -1), (184, -1), (187, -1), (188, 2)],
  [(55, -1), (138, -1), (182, 1), (189, -2), (192, 1), (196, -1), (200, -1), (203, -1), (204, 2)],
  [(79, 1), (139, -1), (190, -1), (207, 1), (211, -1), (214, -1), (215, -1), (218, -1), (219, 2)],
  [(81, 1), (141, -1), (192, -1), (234, 2), (238, -1), (241, -1), (242, -1), (245, -1), (246, 2)],
  [(59, -1), (142, -1), (193, -1), (235, 1), (240, 1), (250, -1), (254, -1), (257, -1), (258, 2)],
  [(83, 1), (143, -1), (194, -1), (236, 1), (261, -1), (264, -1), (265, -1), (268, -1), (269, 2)],
  [(85, 1), (145, -1), (196, -1), (238, 1), (280, -2), (283, -1), (284, -1), (287, -1), (288, 2)]
]

private def primalABNatList_3 : List (List (Nat × Int)) := [
  [(63, -1), (146, -1), (197, -1), (239, 1), (281, -1), (282, 1), (292, -1), (295, -1), (296, 2)],
  [(0, -2), (12, -1), (25, -2), (37, -1), (89, 1), (149, -1), (200, -1), (242, 1), (284, -1), (305, -1), (314, 2)],
  [(0, 2), (16, -1), (25, 2), (41, -1), (49, -2), (55, 1), (65, 1), (75, -1), (81, 1), (85, -1), (89, -1), (92, -1), (93, 2)],
  [(4, 1), (29, 1), (53, -1), (106, -1), (127, -1), (136, -1), (137, 1), (147, 1), (159, 1), (163, -1), (167, -1), (170, -1), (171, 2)],
  [(8, 1), (33, 1), (57, -1), (140, -1), (174, 1), (180, -1), (197, -1), (213, 1), (221, 1), (225, -1), (229, -1), (232, -1), (233, 2)],
  [(12, 1), (37, 1), (61, -1), (144, -1), (178, 1), (237, 1), (238, -1), (251, -1), (263, 1), (271, -1), (275, -1), (278, -1), (279, 2)],
  [(54, 1), (60, -1), (64, 1), (68, -1), (98, -1), (119, -1), (155, -1), (165, -1), (169, 1), (177, 1), (181, -1), (185, 1), (252, 1), (256, -1), (290, -1), (294, 1), (300, 1)],
  [(4, 1), (29, 1), (53, -1), (59, 1), (63, -1), (90, -1), (106, -1), (127, -1), (137, 1), (147, 1), (151, -1), (176, -1), (180, 1), (201, 1), (240, -1), (244, 1), (282, 1), (286, -1), (306, 1)],
  [(8, 1), (33, 1), (53, -1), (59, 1), (63, -1), (106, -1), (127, -1), (137, 1), (147, 1), (150, -1), (151, -1), (176, -1), (180, 1), (240, -1), (243, 1), (244, 1), (282, 1), (285, -1), (286, -1), (318, 2)],
  [(6, -1), (37, -1), (41, 1), (45, -1), (55, 1), (58, 1), (69, -1), (138, -1), (145, 1), (172, -2), (175, -1), (182, -1), (186, 1), (192, 1), (196, -1), (200, 1), (203, -1), (227, -1), (231, 1), (251, 1), (280, 2), (293, 1), (301, 1)],
  [(7, -1), (8, 1), (13, 1), (17, -1), (21, 1), (33, 1), (57, -1), (77, 1), (91, -1), (137, 1), (163, 1), (173, -1), (174, 1), (176, -1), (183, -1), (184, -1), (187, 1), (197, -1), (202, 1), (213, 1), (217, -1), (250, -1), (281, 1), (285, -1), (307, 1)],
  [(7, -1), (13, 1), (17, -1), (21, 1), (57, -1), (77, 1), (137, 1), (151, -1), (163, 1), (173, -1), (174, 1), (176, -2), (183, -1), (184, -1), (187, 1), (193, -1), (197, -1), (213, 1), (217, -1), (244, 1), (250, -1), (281, 1), (285, -1), (286, -1), (321, 2)],
  [(0, -2), (6, -1), (25, -2), (37, -1), (41, 1), (45, -1), (55, 1), (58, 1), (61, 1), (65, -1), (69, -1), (75, -1), (97, 1), (103, -1), (107, 1), (111, -1), (135, -2), (141, 1), (148, 1), (149, 1), (152, -1), (168, -1), (172, -2), (175, -1), (178, -1), (186, 1), (192, 1), (196, -1), (200, 1), (203, -1), (227, -1), (231, 1), (251, 1), (255, 1), (263, -1), (267, 1), (280, 2), (297, 2)],
  [(0, 2), (6, 1), (25, 2), (37, 1), (41, -1), (45, 1), (55, -1), (58, -1), (61, -1), (65, 1), (69, 1), (75, 1), (97, -1), (103, 1), (107, -1), (111, 1), (135, 2), (141, -1), (148, -1), (149, -1), (152, 1), (168, 1), (172, 2), (175, 1), (178, 1), (186, -1), (192, -1), (196, 1), (200, -1), (203, 1), (227, 1), (231, -1), (251, -1), (255, -1), (263, 1), (267, -1), (280, -2), (304, 2)],
  [(4, -1), (7, -1), (8, 1), (13, 1), (17, -1), (21, 1), (29, -1), (33, 1), (53, 1), (57, -1), (62, 1), (66, -1), (77, 1), (91, -1), (96, -1), (102, 1), (127, 1), (131, -1), (136, -1), (147, -1), (150, 1), (159, 1), (167, 1), (170, -1), (173, -1), (174, 1), (176, -1), (179, -1), (184, -1), (187, 1), (197, -1), (202, 1), (213, 1), (217, -1), (243, -1), (250, -1), (273, -1), (277, 1), (281, 1), (298, 1)],
  [(8, 2), (33, 2), (50, -1), (56, 1), (59, 1), (62, 1), (63, -1), (67, 1), (70, -1), (77, 1), (87, 1), (91, -1), (96, -1), (102, 1), (127, 1), (131, -1), (142, -1), (146, 1), (173, -1), (176, -1), (179, -1), (184, -1), (187, 1), (197, -1), (198, -1), (202, 1), (235, 1), (239, -1), (240, -1), (250, -1), (254, 1), (257, -1), (273, -1), (277, 1), (281, 1), (282, 1), (292, -1), (295, 1), (299, -1), (302, 1)],
  [(0, -2), (16, 1), (25, -2), (41, 1), (49, 2), (55, -2), (61, -1), (65, -1), (69, 1), (81, 1), (85, -1), (89, 1), (97, -1), (103, 1), (107, -1), (111, 1), (141, 1), (145, -1), (152, -1), (172, 4), (178, 1), (182, 1), (186, -1), (189, 2), (192, -1), (196, 1), (200, -1), (234, -2), (238, 1), (241, -1), (242, -1), (245, 2), (251, -1), (263, 1), (267, -1), (280, -2), (283, 1), (284, 1), (287, -2), (305, -1), (323, 2)],
  [(0, -2), (12, 1), (16, 1), (25, -2), (37, 1), (41, 1), (49, 2), (55, -2), (61, -1), (65, -1), (69, 1), (81, 1), (85, -1), (89, 1), (92, -1), (97, -1), (103, 1), (107, -1), (111, 1), (141, 1), (145, -1), (172, 2), (178, 1), (182, 1), (186, -1), (192, -1), (196, 1), (200, -1), (203, 1), (234, -2), (238, 1), (241, -1), (242, -1), (245, 1), (251, -1), (263, 1), (267, -1), (280, -2), (283, 1), (284, 1), (287, -1), (305, -1), (308, 1)],
  [(0, -2), (6, 1), (16, 2), (25, -2), (37, 1), (41, 1), (45, 1), (49, 2), (55, -3), (58, -1), (61, -1), (65, -1), (69, 1), (75, 1), (89, 2), (97, -1), (103, 1), (107, -1), (111, 1), (141, 1), (145, -2), (148, -1), (149, -1), (152, -1), (168, 1), (172, 4), (175, 1), (178, 1), (182, 2), (186, -1), (192, -1), (196, 1), (200, -3), (203, 1), (227, 1), (231, -1), (234, -2), (238, 2), (245, 2), (251, -1), (255, -1), (263, 1), (267, -1), (280, -4), (287, -2), (305, -2), (324, 4)],
  [(6, 1), (12, 1), (16, 2), (37, 2), (41, 1), (45, 1), (49, 2), (55, -3), (58, -1), (61, -2), (65, -1), (69, 2), (75, 1), (81, 1), (85, -1), (89, 1), (92, -1), (97, -2), (103, 2), (107, -2), (111, 2), (135, 2), (145, -1), (148, -2), (149, -1), (152, 1), (168, 1), (172, 4), (175, 1), (178, 2), (182, 2), (186, -2), (192, -2), (196, 2), (200, -2), (203, 2), (227, 1), (231, -1), (234, -2), (238, 1), (242, -1), (245, 1), (251, -2), (255, -1), (263, 2), (267, -2), (280, -4), (284, 1), (287, -1), (305, -2), (309, 2)],
  [(4, -1), (7, -1), (8, 3), (13, 1), (17, -1), (21, 1), (29, -1), (33, 3), (50, -1), (53, 1), (56, 1), (57, -1), (59, 1), (62, 2), (63, -1), (66, -1), (67, 1), (70, -1), (77, 2), (87, 2), (91, -2), (96, -2), (102, 2), (127, 2), (131, -2), (136, -1), (142, -1), (146, 1), (147, -2), (150, 1), (159, 1), (167, 1), (170, -1), (173, -2), (174, 1), (176, -2), (179, -2), (184, -2), (187, 2), (197, -2), (198, -2), (202, 2), (213, 1), (217, -1), (235, 1), (239, -1), (243, -1), (250, -2), (254, 1), (257, -1), (273, -2), (277, 2), (281, 2), (292, -1), (295, 1), (299, -2), (303, 2)]
]

def primalABNatList : List (List (Nat × Int)) := primalABNatList_0 ++ primalABNatList_1 ++ primalABNatList_2 ++ primalABNatList_3

private def primalBANatList_0 : List (List (Nat × Int)) := [
  [(8, 1), (102, 1)],
  [(9, 1), (103, 1)],
  [(10, 1), (104, 1)],
  [(11, 1), (105, 1)],
  [(22, 1), (113, 1)],
  [(32, 1), (122, 1)],
  [(34, 1), (124, 1)],
  [(46, 1), (133, 1)],
  [(55, 1), (141, 1)],
  [(56, 1), (142, 1)],
  [(57, 1), (143, 1)],
  [(58, 1), (144, 1)],
  [(69, 1), (152, 1)],
  [(77, 1), (159, 1)],
  [(79, 1), (161, 1)],
  [(91, 1), (170, 1)],
  [(184, 1), (243, 1)],
  [(200, 1), (255, 1)],
  [(215, 1), (266, 1)],
  [(229, 1), (276, 1)]
]

private def primalBANatList_1 : List (List (Nat × Int)) := [
  [(0, -1), (94, -1), (280, 1)],
  [(1, -1), (95, -1), (281, 1)],
  [(2, -1), (96, -1), (282, 1)],
  [(3, -1), (97, -1), (283, 1)],
  [(26, -1), (116, -1), (290, 1)],
  [(49, -1), (135, -1), (297, 1)],
  [(50, -1), (136, -1), (298, 1)],
  [(0, -1), (94, -1), (172, 1), (234, 1)],
  [(1, -1), (95, -1), (173, 1), (235, 1)],
  [(2, -1), (96, -1), (174, 1), (236, 1)],
  [(3, -1), (97, -1), (175, 1), (237, 1)],
  [(20, -1), (111, -1), (186, 1), (245, 1)],
  [(26, -1), (116, -1), (190, 1), (248, 1)],
  [(44, -1), (131, -1), (202, 1), (257, 1)],
  [(49, -1), (135, -1), (205, 1), (259, 1)],
  [(50, -1), (136, -1), (206, 1), (260, 1)],
  [(67, -1), (150, -1), (217, 1), (268, 1)],
  [(89, -1), (168, -1), (231, 1), (278, 1)],
  [(1, 1), (44, -1), (50, -1), (56, 1), (67, 1), (77, 1), (87, 1), (91, -1), (95, 1), (131, -1), (146, 1), (173, -1), (184, -1), (198, -1), (202, 1), (239, -1), (295, 1), (299, -1), (312, 1)]
]

def primalBANatList : List (List (Nat × Int)) := primalBANatList_0 ++ primalBANatList_1

private def primalABColTree : PairListTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(84, -2), (83, -2), (82, -2), (79, 2), (78, -2), (68, 2), (67, -2), (43, 1), (41, 1), (36, -1), (30, 1), (26, -1)]) (.leaf [(72, -1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(72, 1)]) (.leaf [(34, 1)])) (.branch (.leaf [(85, -2), (84, -1), (83, -1), (82, -1), (79, -1), (78, 1), (75, 1), (62, -1), (60, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(65, 2)])) (.branch (.leaf [(14, 1)]) (.leaf []))) (.branch (.branch (.leaf [(86, -2), (81, -1), (80, -1), (56, -1), (9, 1)]) (.leaf [])) (.branch (.leaf [(48, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(85, 2), (84, 2), (83, 1), (82, 1), (68, -1), (53, -1), (40, -1)]) (.leaf [(23, 1)])) (.branch (.leaf [(71, -1)]) (.leaf []))) (.branch (.branch (.leaf [(38, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(54, 2)]) (.leaf [(79, 2)])) (.branch (.leaf [(86, -2), (81, -1), (80, -1), (77, -2), (76, -1), (74, -1), (73, -1), (59, 1), (48, -1), (34, -1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(81, -1), (74, -1), (73, -1), (63, 1), (22, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(86, 3), (81, 2), (80, 1), (76, 1), (74, 1), (70, 1), (45, 1), (42, 1), (38, -1), (32, 1), (28, -1)]) (.leaf [(64, -1)])) (.branch (.leaf [(86, -1), (80, -1), (69, -1)]) (.leaf []))) (.branch (.branch (.leaf [(36, 1)]) (.leaf [])) (.branch (.leaf [(85, -2), (84, -3), (83, -1), (82, -1), (79, -1), (78, 1), (75, 1), (67, -1), (60, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(54, -1)]) (.leaf [(66, 2)])) (.branch (.leaf [(85, 1), (84, 1), (79, 1), (78, -1)]) (.leaf []))) (.branch (.branch (.leaf [(11, 1)]) (.leaf [])) (.branch (.leaf [(70, -1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(53, 2)]) (.leaf [(85, -4), (84, -4), (83, -2), (82, -2), (79, -2), (78, 2), (75, 2), (65, -2), (24, 1)])) (.branch (.leaf [(85, 1), (84, -1), (82, -1), (79, 1), (78, -1), (58, -1)]) (.leaf []))) (.branch (.branch (.leaf [(40, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(86, 1), (81, 1), (55, -1)]) (.leaf [(28, 1)])) (.branch (.leaf [(86, -2), (81, -1), (80, -1), (77, -1), (76, -1), (59, -1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(86, -1), (80, -1), (73, 1), (69, 1), (37, -1), (27, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(72, -1)]) (.leaf [(84, 4)])) (.branch (.leaf [(85, 2), (84, 1), (83, 1), (82, 1), (79, 1), (78, -1), (75, -1), (65, -1), (60, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(54, 1)]) (.leaf [(86, -1), (81, -1), (66, -1)])) (.branch (.leaf [(15, 1)]) (.leaf []))) (.branch (.branch (.leaf [(10, 1)]) (.leaf [])) (.branch (.leaf [(49, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(53, -1)]) (.leaf [])) (.branch (.leaf [(85, -2), (84, -1), (79, -1), (78, 1), (58, -1)]) (.leaf []))) (.branch (.branch (.leaf [(39, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(83, 1)])) (.branch (.leaf [(74, 1), (73, 1), (70, -1), (59, -1), (49, -1)]) (.leaf []))) (.branch (.branch (.leaf [(57, -1)]) (.leaf [])) (.branch (.leaf [(77, 1), (74, 1), (73, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(85, 1), (83, 1), (71, 1), (67, -1), (53, 1), (39, -1), (29, -1)]) (.leaf [(64, -1)])) (.branch (.leaf [(70, -1)]) (.leaf []))) (.branch (.branch (.leaf [(37, 1)]) (.leaf [])) (.branch (.leaf [(60, 2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(54, -1)]) (.leaf [(72, 1)])) (.branch (.leaf [(85, 4), (84, 4), (83, 2), (82, 4), (79, 2), (78, -2), (75, -2), (51, 1), (50, 1), (47, -1), (35, 1), (33, -1)]) (.leaf []))) (.branch (.branch (.leaf [(57, 1), (12, 1)]) (.leaf [])) (.branch (.leaf [(64, 1), (21, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(85, 1), (83, 1), (82, 1), (67, -1), (65, -1)])) (.branch (.leaf [(13, 1)]) (.leaf []))) (.branch (.branch (.leaf [(85, -1), (83, -1), (68, -1)]) (.leaf [])) (.branch (.leaf [(47, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(72, -1)]) (.leaf [(31, 1)])) (.branch (.leaf [(59, 2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(72, 1)]) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(54, -1), (0, 1)]) (.leaf [(63, 2)])) (.branch (.leaf [(57, -1)]) (.leaf []))) (.branch (.branch (.leaf [(86, -1), (80, -1), (55, -1)]) (.leaf [(35, 1)])) (.branch (.leaf [(64, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(72, -1)])) (.branch (.leaf [(45, 1)]) (.leaf []))) (.branch (.branch (.leaf [(72, -1), (44, -1), (31, -1)]) (.leaf [])) (.branch (.leaf [(20, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(54, 1), (4, 1)]) (.leaf [(52, 1)])) (.branch (.leaf [(86, 1), (81, 1), (66, -1)]) (.leaf []))) (.branch (.branch (.leaf [(7, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(86, -1), (81, -1), (55, 1)]) (.leaf [(73, 1)])) (.branch (.leaf [(85, 2), (84, 1), (83, 1), (82, 1), (79, 1), (78, -1), (71, 1), (17, 1)]) (.leaf []))) (.branch (.branch (.leaf [(56, 2)]) (.leaf [])) (.branch (.leaf [(85, -1), (83, -1), (82, -1), (67, 1), (62, -1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(2, 1)]) (.leaf [])) (.branch (.leaf [(75, -1), (60, -1), (58, -1)]) (.leaf []))) (.branch (.branch (.leaf [(5, 1)]) (.leaf [])) (.branch (.leaf [(86, 2), (81, 1), (80, 1), (76, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(80, 1)])) (.branch (.leaf [(86, -1), (80, -1), (69, -1)]) (.leaf []))) (.branch (.branch (.leaf [(74, -1), (73, -1), (69, -1), (56, -1), (46, -1)]) (.leaf [])) (.branch (.leaf [(85, -2), (84, -2), (83, -2), (82, -2), (62, 2), (50, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(81, 1), (74, 1), (73, 1), (66, 1), (25, 1)])) (.branch (.leaf [(43, 1)]) (.leaf []))) (.branch (.branch (.leaf [(73, -1)]) (.leaf [])) (.branch (.leaf [(61, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(85, -1), (84, -1), (79, -1), (78, 1), (75, 1)]) (.leaf [(67, 2)])) (.branch (.leaf [(85, -2), (84, -1), (83, -1), (82, -1), (79, -1), (78, 1), (75, 1)]) (.leaf []))) (.branch (.branch (.leaf [(57, 1)]) (.leaf [])) (.branch (.leaf [(86, -2), (81, -1), (80, -1), (77, -1), (76, -1), (63, -1)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(85, 1), (84, 1), (79, 1), (78, -1), (75, -1), (53, -1), (1, 1)]) (.leaf [])) (.branch (.leaf [(57, 2)]) (.leaf []))) (.branch (.branch (.leaf [(86, -1), (81, -1), (55, -1)]) (.leaf [])) (.branch (.leaf [(86, -2), (81, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(72, 1)])) (.branch (.leaf [(46, 1)]) (.leaf []))) (.branch (.branch (.leaf [(86, 2), (81, 1), (80, 1), (56, 1), (42, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(71, -1)])) (.branch (.leaf [(86, 1), (80, 1), (74, -1)]) (.leaf []))) (.branch (.branch (.leaf [(8, 1)]) (.leaf [])) (.branch (.leaf [(61, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(72, 1)]) (.leaf [(26, 1)])) (.branch (.leaf [(85, 2), (84, 2), (83, 1), (82, 1), (75, -1), (60, 1), (18, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(62, 2)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(3, 1)]) (.leaf [(51, 1)])) (.branch (.leaf [(86, -1), (81, -1), (63, -1)]) (.leaf []))) (.branch (.branch (.leaf [(6, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(81, 1)])) (.branch (.leaf [(86, 1), (80, 1), (77, 1), (76, 1), (70, 1), (16, 1)]) (.leaf []))) (.branch (.branch (.leaf [(56, -1)]) (.leaf [])) (.branch (.leaf [(85, 1), (84, 2), (83, 1), (82, 1), (71, -1), (65, 1), (62, -1), (52, -1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(54, -1)]) (.leaf [(77, -1), (74, -1), (73, -1)])) (.branch (.leaf [(44, 1)]) (.leaf []))) (.branch (.branch (.leaf [(41, 1)]) (.leaf [])) (.branch (.leaf [(19, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(86, 2), (81, 1), (80, 1)]) (.leaf [(74, 2)])) (.branch (.leaf [(61, -1)]) (.leaf []))) (.branch (.branch (.leaf [(57, -1)]) (.leaf [])) (.branch (.leaf [(86, 1), (81, 1), (63, -1)]) (.leaf []))))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(86, -1), (81, -1), (63, -1)])) (.branch (.leaf [(12, 1)]) (.leaf []))) (.branch (.branch (.leaf [(85, -1), (84, -1), (83, -1), (82, -1), (79, 1), (78, -1), (68, 1), (40, 1)]) (.leaf [(77, 2)])) (.branch (.leaf [(77, -1), (63, -1), (48, -1), (34, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(86, 3), (81, 2), (80, 1), (76, 1), (74, 1), (70, 1), (54, -1), (45, 1), (42, 1), (38, -1), (32, 1), (28, -1)]) (.leaf [(24, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(85, -2), (84, -1), (83, -1), (82, -1), (79, -1), (78, 1)]) (.leaf [])) (.branch (.leaf [(70, -1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(86, -1), (80, -1), (77, -1), (76, -1)]) (.leaf [(86, -2), (81, -1), (80, -1)])) (.branch (.leaf [(85, -1), (84, -2), (83, -1), (82, -1), (75, 1), (65, -1), (58, -1), (15, 1)]) (.leaf []))) (.branch (.branch (.leaf [(85, 1), (83, 1), (82, 1), (68, 1), (62, 1)]) (.leaf [])) (.branch (.leaf [(48, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(85, 2), (84, 2), (83, 2), (82, 2), (68, -2), (36, 1)]) (.leaf [(85, -2), (84, -2), (83, -1), (82, -1), (67, -1)])) (.branch (.leaf [(72, 1)]) (.leaf []))) (.branch (.branch (.leaf [(56, -1)]) (.leaf [])) (.branch (.leaf [(83, -1), (82, -1), (62, -1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(53, -1)]) (.leaf [(64, -1)])) (.branch (.leaf [(77, 1), (76, 1), (74, 1), (73, 1), (69, 1), (59, -1), (13, 1)]) (.leaf []))) (.branch (.branch (.leaf [(56, 1)]) (.leaf [])) (.branch (.leaf [(73, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(85, 1), (84, 1), (83, 1), (82, 1), (79, -1), (78, 1), (75, 1), (68, -1), (40, -1)]) (.leaf [(78, 2)])) (.branch (.leaf [(72, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(70, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(84, -2), (83, -2), (82, -2), (79, 2), (78, -2), (68, 2), (67, -2), (43, 1), (41, 1), (36, -1), (30, 1), (26, -1)]) (.leaf [(86, 2), (81, 1), (80, 1), (77, 1), (76, 1), (66, -1)])) (.branch (.leaf [(58, 2)]) (.leaf []))) (.branch (.branch (.leaf [(85, 1), (84, 2), (83, 1), (82, 1), (68, -1), (67, 1)]) (.leaf [])) (.branch (.leaf [(86, -1), (80, -1), (77, -1), (76, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(86, -1), (80, -1), (77, -1), (76, -1), (70, -1), (38, 1)]) (.leaf [(29, 1)])) (.branch (.leaf [(72, 1)]) (.leaf []))) (.branch (.branch (.leaf [(10, 1)]) (.leaf [])) (.branch (.leaf [(21, 1)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(64, -1), (23, 1)])) (.branch (.leaf [(57, -1)]) (.leaf []))) (.branch (.branch (.leaf [(85, 2), (84, 1), (83, 1), (82, 1), (79, 1), (78, -1), (75, -1)]) (.leaf [])) (.branch (.leaf [(86, -2), (81, -1), (80, -1), (77, -1), (76, -1), (70, -1), (66, -1), (49, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(85, 2), (84, 1), (83, 1), (79, 1), (78, -1), (75, -1), (71, 1), (67, -1), (39, -1), (29, -1)]) (.leaf [(75, 1)])) (.branch (.leaf [(72, -1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(70, -1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(86, 1), (80, 1), (77, 1), (76, 1)]) (.leaf [(86, 2), (81, 1), (80, 1)])) (.branch (.leaf [(85, -1), (84, -1), (79, -1), (78, 1), (67, -1), (58, -1)]) (.leaf []))) (.branch (.branch (.leaf [(85, -1), (83, -1), (82, -1), (68, -1), (65, 1)]) (.leaf [])) (.branch (.leaf [(86, 1), (80, 1), (77, 1), (76, 1), (70, 1), (49, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(86, 1), (80, 1), (74, -1), (73, -1), (69, -1), (55, -1), (37, 1)]) (.leaf [(85, 2)])) (.branch (.leaf [(72, -1)]) (.leaf []))) (.branch (.branch (.leaf [(9, 1)]) (.leaf [])) (.branch (.leaf [(85, 1), (84, 2), (83, 1), (82, 2), (62, -1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(86, 1), (80, 1), (77, 1), (76, 1)]) (.leaf [(64, 2)])) (.branch (.leaf [(84, 1), (83, 1), (82, 1), (79, -1), (78, 1), (62, -1), (58, 1), (14, 1)]) (.leaf []))) (.branch (.branch (.leaf [(86, 2), (81, 1), (80, 1), (77, 1), (76, 1), (59, 1)]) (.leaf [])) (.branch (.leaf [(47, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(85, 1), (84, 1), (79, 1), (78, -1), (75, -1)]) (.leaf [(75, 1)])) (.branch (.leaf [(86, -2), (81, -1), (80, -1), (77, -1), (76, -1), (59, -1)]) (.leaf []))) (.branch (.branch (.leaf [(56, -1)]) (.leaf [])) (.branch (.leaf [(71, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(86, -1), (80, -1), (73, 1), (69, 1), (37, -1), (27, -1)]) (.leaf [(77, -1), (76, -1), (74, -1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(68, 2)]) (.leaf [])) (.branch (.leaf [(70, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(85, -2), (84, -1), (83, -1), (82, -1), (79, -1), (78, 1), (71, -1), (39, 1)]) (.leaf [(32, 1)])) (.branch (.leaf [(82, 2), (60, -2), (51, 1), (50, 1), (47, -1), (35, 1), (33, -1)]) (.leaf []))) (.branch (.branch (.leaf [(11, 1)]) (.leaf [])) (.branch (.leaf [(22, 1)]) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(53, 1)]) (.leaf [(51, 1)])) (.branch (.leaf [(86, -2), (81, -1), (80, -1)]) (.leaf []))) (.branch (.branch (.leaf [(86, 1), (81, 1), (55, -1)]) (.leaf [(82, 2)])) (.branch (.leaf [(17, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(2, 1)]) (.leaf [(25, 1)])) (.branch (.leaf [(77, 1), (76, 1), (69, -1)]) (.leaf []))) (.branch (.branch (.leaf [(56, -1)]) (.leaf [])) (.branch (.leaf [(85, 1), (84, 1), (79, 1), (78, -1), (75, -1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(53, -1)]) (.leaf [(71, -1)])) (.branch (.leaf [(86, -2), (80, -1), (74, 1), (73, 1), (69, 1), (46, 1)]) (.leaf []))) (.branch (.branch (.leaf [(64, 1)]) (.leaf [])) (.branch (.leaf [(61, -1), (20, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(57, -1), (5, 1)]) (.leaf [(76, 1)])) (.branch (.leaf [(86, -2), (81, -1), (80, -1)]) (.leaf []))) (.branch (.branch (.leaf [(41, 1)]) (.leaf [])) (.branch (.leaf [(86, -1), (80, -1), (74, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(85, -2), (84, -1), (83, -1), (82, -1), (79, -1), (78, 1)])) (.branch (.leaf [(61, -1), (44, 1)]) (.leaf []))) (.branch (.branch (.leaf [(85, 1), (84, 1), (79, 1), (78, -1), (68, -1), (58, 1)]) (.leaf [])) (.branch (.leaf [(85, 2), (84, 1), (83, 1), (79, 1), (78, -1), (75, -1), (60, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(4, 1)]) (.leaf [(86, -2), (81, -1)])) (.branch (.leaf [(69, 2)]) (.leaf []))) (.branch (.branch (.leaf [(85, -2), (84, -1), (83, -1), (82, -1), (79, -1), (78, 1)]) (.leaf [])) (.branch (.leaf [(86, 1), (81, 1), (63, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(0, 1)]) (.leaf [(83, 1), (82, 1), (65, -1)])) (.branch (.leaf [(72, -1)]) (.leaf []))) (.branch (.branch (.leaf [(86, -2), (81, -1), (80, -1), (76, -1)]) (.leaf [])) (.branch (.leaf [(61, 2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(86, 1), (81, 1), (74, 1), (73, 1), (63, -1), (55, 1), (7, 1)]) (.leaf [(30, 1)])) (.branch (.leaf [(86, 2), (81, 1), (80, 1), (77, 1), (76, 1), (59, -1)]) (.leaf []))) (.branch (.branch (.leaf [(42, 1)]) (.leaf [])) (.branch (.leaf [(85, -2), (84, -1), (83, -1), (82, -1), (79, -1), (78, 1), (75, 1), (71, -1), (52, -1)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(86, -1), (80, -1), (77, -1), (76, -1)]) (.leaf [(85, 2), (84, 1), (83, 1), (82, 1), (79, 1), (78, -1), (71, 1), (52, 1)])) (.branch (.leaf [(85, 2), (79, 2), (78, -2), (58, -2), (43, 1)]) (.leaf []))) (.branch (.branch (.leaf [(55, 2)]) (.leaf [])) (.branch (.leaf [(18, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(3, 1)]) (.leaf [(86, 1), (81, 1), (66, -1)])) (.branch (.leaf [(86, 1), (80, 1), (69, -1)]) (.leaf []))) (.branch (.branch (.leaf [(85, 2), (84, 1), (83, 1), (82, 1), (79, 1), (78, -1)]) (.leaf [])) (.branch (.leaf [(85, -1), (84, -1), (79, -1), (78, 1), (75, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(53, -1)]) (.leaf [(71, 2)])) (.branch (.leaf [(77, -1), (74, -1), (73, -1)]) (.leaf []))) (.branch (.branch (.leaf [(86, 2), (81, 1)]) (.leaf [])) (.branch (.leaf [(61, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(85, -3), (84, -3), (83, -2), (82, -2), (79, -1), (78, 1), (75, 1), (68, 1), (60, -1), (6, 1)]) (.leaf [(27, 1)])) (.branch (.leaf [(77, -1), (76, -1), (59, -1)]) (.leaf []))) (.branch (.branch (.leaf [(72, -1), (57, -1), (44, -1), (31, -1)]) (.leaf [])) (.branch (.leaf [(50, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(71, -1)])) (.branch (.leaf [(64, -1), (45, 1)]) (.leaf []))) (.branch (.branch (.leaf [(61, 1)]) (.leaf [])) (.branch (.leaf [(61, 1), (19, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(54, -1)]) (.leaf [(86, 2)])) (.branch (.leaf [(85, 1), (84, 1), (79, 1), (78, -1), (75, -1)]) (.leaf []))) (.branch (.branch (.leaf [(85, 2), (84, 1), (83, 1), (82, 1), (79, 1), (78, -1)]) (.leaf [])) (.branch (.leaf [(86, -1), (81, -1), (66, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(1, 1)]) (.leaf [(85, -1), (84, -2), (83, -1), (82, -2), (65, -1)])) (.branch (.leaf [(86, 1), (80, 1), (69, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(86, -1), (81, -1), (74, -1), (73, -1), (66, -1), (55, -1), (8, 1)]) (.leaf [(33, 1)])) (.branch (.leaf [(16, 1)]) (.leaf []))) (.branch (.branch (.leaf [(86, 2), (81, 1), (80, 1), (74, -1), (73, -1), (69, -1), (46, -1)]) (.leaf [])) (.branch (.leaf [(85, -1), (84, -1), (79, -1), (78, 1)]) (.leaf [])))))))))

private def primalBAColTree : PairListTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(27, -1), (20, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(5, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(29, -1), (22, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(11, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(0, 1)]) (.leaf [])) (.branch (.leaf [(35, -1), (26, -1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(17, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(37, -1)]) (.leaf []))) (.branch (.branch (.leaf [(2, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(20, 1)])) (.branch (.leaf [(12, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(38, 1), (9, 1)]) (.leaf [(38, 1)])) (.branch (.leaf [(38, -1), (16, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(32, 1)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(35, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(31, -1)]) (.leaf [(19, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(32, -1), (24, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(36, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(38, -1), (33, -1)]) (.leaf [])) (.branch (.leaf [(27, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(29, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(6, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(29, -1), (22, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(6, 1)]) (.leaf [(24, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(38, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(38, -1), (35, -1), (26, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(2, 1)]) (.leaf [(18, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(38, 1), (33, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(26, 1)])) (.branch (.leaf [(15, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(27, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(32, -1), (24, -1)]) (.leaf [(22, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(11, 1)]) (.leaf [])) (.branch (.leaf [(31, 1)]) (.leaf []))) (.branch (.branch (.leaf [(5, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(38, -1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(0, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(4, 1)]) (.leaf [(37, 1)])) (.branch (.leaf [(36, -1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(9, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(35, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(7, 1)]) (.leaf [])) (.branch (.leaf [(29, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(27, -1), (20, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(32, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(38, 1), (28, -1), (21, -1)]) (.leaf [(33, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(14, 1)]) (.leaf []))) (.branch (.branch (.leaf [(30, -1), (23, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(34, -1), (25, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(4, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(1, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(25, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(3, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(21, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(37, -1)]) (.leaf [])) (.branch (.leaf [(36, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(10, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(7, 1)]) (.leaf []))) (.branch (.branch (.leaf [(12, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(19, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(31, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(8, 1)]) (.leaf []))) (.branch (.branch (.leaf [(38, 1), (13, 1)]) (.leaf [])) (.branch (.leaf [(34, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(38, -1), (28, 1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(30, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(30, -1), (23, -1)]) (.leaf [(34, 1)])) (.branch (.leaf [(38, -1), (33, -1)]) (.leaf []))) (.branch (.branch (.leaf [(38, 1), (36, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(16, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(3, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(38, -1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(28, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(23, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(38, -1), (15, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(34, -1), (25, -1)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(38, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(1, 1)]) (.leaf [])) (.branch (.leaf [(37, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(38, 1)]) (.leaf [])) (.branch (.leaf [(18, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(8, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(10, 1)]) (.leaf []))) (.branch (.branch (.leaf [(14, 1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(30, 1)]) (.leaf []))) (.branch (.branch (.leaf [(31, -1)]) (.leaf [])) (.branch (.leaf [(38, -1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(13, 1)]) (.leaf []))) (.branch (.branch (.leaf [(38, 1), (28, -1), (21, -1)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(17, 1)]) (.leaf [])))))))))

private theorem primalAB_len : primalABNatList.length = 87 := by decide +kernel
private theorem primalBA_len : primalBANatList.length = 39 := by decide +kernel

private theorem primalAB_check_true :
    checkPrimalSystem 1088 abNatTerms primalABNatList primalABColTree = true := by
  decide +kernel

private theorem primalBA_check_true :
    checkPrimalSystem 1088 baNatTerms primalBANatList primalBAColTree = true := by
  decide +kernel

theorem primalAB_mem_solAB (idx : Fin 87) :
    sparseNatRealVec (listAt [] primalABNatList idx.val) ∈ solAB := by
  intro k hk
  exact checkPrimalSystem_sound 1088 abNatTerms rowAB evalNatTerms_ab
    primalABNatList primalABColTree primalAB_check_true (by rw [primalAB_len]; exact idx.isLt) hk

theorem primalBA_mem_solBA (idx : Fin 39) :
    sparseNatRealVec (listAt [] primalBANatList idx.val) ∈ solBA := by
  intro k hk
  exact checkPrimalSystem_sound 1088 baNatTerms rowBA evalNatTerms_ba
    primalBANatList primalBAColTree primalBA_check_true (by rw [primalBA_len]; exact idx.isLt) hk

def primal126Data (r : Fin 126) : List (Nat × Int) :=
  if r.val < 87 then listAt [] primalABNatList r.val
  else listAt [] primalBANatList (r.val - 87)

def primal126Vec (r : Fin 126) : CoordVec :=
  sparseNatRealVec (primal126Data r)

theorem primal126_mem_ab_sup_ba (r : Fin 126) : primal126Vec r ∈ solAB ⊔ solBA := by
  unfold primal126Vec primal126Data
  by_cases h : r.val < 87
  · rw [if_pos h]
    exact Submodule.mem_sup_left (primalAB_mem_solAB ⟨r.val, h⟩)
  · rw [if_neg h]
    exact Submodule.mem_sup_right (primalBA_mem_solBA ⟨r.val - 87, by omega⟩)

theorem primal126_mem_three_sup (r : Fin 126) :
    primal126Vec r ∈ solAB ⊔ solBA ⊔ solGauge :=
  Submodule.mem_sup_left (primal126_mem_ab_sup_ba r)

private def primalRightInvList_0 : List (List (Nat × Int)) := [
  [(27, 2)],
  [(31, 2)],
  [(35, 2)],
  [(14, 2)],
  [(18, 2), (30, 2)],
  [(74, 2)],
  [(78, 2)],
  [(82, 2)],
  [(86, 2)],
  [(2, -2), (27, 2), (30, 2), (62, 2), (73, 2), (96, 2)],
  [(100, 2)],
  [(10, -2), (35, 2), (104, 2)],
  [(51, 2), (74, -2), (108, 2)],
  [(156, 2)],
  [(3, -4), (6, -4), (16, 4), (19, -4), (31, 4), (55, -2), (65, 8), (75, -4), (78, 2), (81, 2), (88, -4), (93, -4), (97, 4), (138, 2), (141, 2), (148, -4)],
  [(3, 2), (6, 2), (16, -4), (19, 4), (31, -2), (65, -6), (75, 4), (85, 2), (88, 2), (93, 4), (97, -2), (145, 2), (148, 2)],
  [(191, 2)],
  [(61, 2), (84, -2), (178, 2)],
  [(6, -4), (19, 4), (31, 4), (65, 2), (75, 2), (88, -2), (138, 2), (182, 2)],
  [(139, 2), (158, -2), (207, 2)],
  [(139, -2), (158, 2), (211, 2)]
]

private def primalRightInvList_1 : List (List (Nat × Int)) := [
  [(7, -2), (83, -2), (140, -2), (174, -2), (191, 2), (236, 2)],
  [(59, 2), (62, 2), (70, 2), (73, 2), (82, -2), (106, 2), (147, 2), (240, 2)],
  [(83, 2), (261, 2)],
  [(0, 2), (3, 4), (6, -4), (16, -4), (19, 12), (25, -2), (31, 4), (65, -4), (75, 4), (85, 4), (93, 4), (97, -4), (138, 4), (172, 2), (189, -2), (280, 2)],
  [(2, 2), (7, 2), (27, -2), (30, -2), (62, -2), (63, 2), (70, -2), (73, -2), (86, -2), (106, -2), (140, 2), (147, -2), (174, 2), (191, -2), (282, 2)],
  [(310, 2)],
  [(4, -2), (50, 2), (66, 2), (73, 2), (76, -2), (87, 2), (90, -2), (106, 2), (136, -2), (147, 2)],
  [(66, 2), (70, -2), (73, -2), (87, -2), (106, -2), (147, -2), (312, 2)],
  [(3, -2), (12, -2), (19, -4), (61, -2), (75, 2), (92, -2), (97, 2), (149, 2)],
  [(0, 2), (16, 4), (19, -4), (49, 2), (65, 4), (75, -8), (93, -4), (94, -2), (135, -2), (149, -4), (310, 2)],
  [(54, -2), (98, -2), (158, -2)],
  [(8, 2), (50, 4), (53, 4), (57, 2), (62, -2), (66, 2), (70, -2), (73, 4), (76, -4), (83, -2), (87, 2), (90, -2), (102, -2), (106, 2), (136, -4), (143, -2), (147, 2), (151, -2), (312, 2)],
  [(319, 2)],
  [(53, -2), (70, 2), (76, 2), (137, -2), (151, 2), (156, 2), (176, -2), (209, -2)],
  [(3, -12), (6, -4), (16, 8), (19, -16), (31, 4), (65, 12), (75, -4), (81, 4), (88, -4), (92, -4), (93, -8), (97, 12), (148, -4), (172, 2), (205, 2), (234, -2), (259, -2), (319, 2)],
  [(72, 2)],
  [(76, 2)],
  [(80, 2)],
  [(84, 2)],
  [(88, 2)],
  [(0, -2), (25, 2), (94, 2)]
]

private def primalRightInvList_2 : List (List (Nat × Int)) := [
  [(8, -2), (30, -2), (33, 2), (62, -2), (73, -2), (102, 2)],
  [(16, -4), (19, 4), (49, -2), (65, -8), (72, 2), (75, 8), (88, 4), (93, 4), (135, 2), (148, 4)],
  [(158, 2)],
  [(7, 2), (57, -2), (80, 2), (83, 2), (140, 2), (143, 2)],
  [(53, 2), (62, -2), (70, -2), (73, -2), (76, -2), (106, -2)],
  [(220, 2)],
  [(209, 2)],
  [(7, 2), (50, -2), (66, -2), (73, -2), (87, -2), (106, -2), (136, 2), (137, 2), (140, 2), (147, -2), (156, -2), (180, -2)],
  [(3, 8), (6, 8), (16, -4), (19, 4), (31, -8), (65, -8), (81, -4), (88, 4), (93, 4), (97, -8), (138, -4), (148, 4), (172, -2), (189, 2), (234, 2)],
  [(205, -2), (220, 2), (259, 2)],
  [(3, 6), (16, -2), (19, 8), (61, 2), (65, -4), (75, 2), (81, -2), (84, -2), (85, 2), (88, 2), (93, 4), (97, -6), (148, 2), (238, -2)],
  [(19, -2)],
  [(30, -2)],
  [(62, -1), (66, -1), (70, -1)],
  [(73, 2)],
  [(51, -2), (74, 2)],
  [(16, -2), (19, 2), (65, -2), (75, 2), (93, 1)],
  [(7, -2), (53, -2), (62, 1), (66, 1), (70, 1), (76, 2), (137, -2), (156, 2)],
  [(6, 2), (19, -2), (31, -2), (75, -2), (93, -1), (138, -2)],
  [(139, -2), (158, 2)],
  [(3, -2), (16, 2), (19, -4), (65, 2), (81, 2), (93, -1), (97, 2)]
]

private def primalRightInvList_3 : List (List (Nat × Int)) := [
  [(50, -2), (53, -2), (59, -2), (62, 1), (66, -1), (70, -1), (73, -2), (76, 2), (82, 2), (87, -2), (106, -2), (136, 2), (147, -2)],
  [(83, 2)],
  [(3, 2), (16, -2), (19, 4), (65, -2), (85, 2), (93, 1), (97, -2)],
  [(50, 2), (53, 2), (62, -1), (63, -2), (66, 1), (70, 1), (73, 2), (76, -2), (86, 2), (87, 2), (106, 2), (136, -2), (147, 2)],
  [(75, -2), (93, -1), (149, -2)],
  [(93, 1)],
  [(50, 2), (62, 1), (66, 1), (70, 1), (73, 2), (87, 2), (106, 2), (136, -2), (147, 2)],
  [(140, -2)],
  [(3, -2), (19, -2), (61, -2), (84, 2), (97, 2)],
  [(54, 2)],
  [(90, -2)],
  [(50, -2), (53, -2), (62, 1), (66, -1), (70, 1), (73, -2), (76, 2), (87, -2), (90, 2), (106, -2), (136, 2), (147, -2)],
  [(6, -2), (16, 2), (31, 2), (65, 2)],
  [(7, -2), (50, -2), (53, -2), (73, -2), (76, 2), (87, -2), (106, -2), (136, 2), (147, -2), (151, 2)],
  [(50, 2), (53, 2), (62, -1), (66, 1), (70, -1), (73, 2), (76, -2), (87, 2), (106, 2), (136, -2), (147, 2), (151, -2)],
  [(3, -1), (19, -1), (49, 1), (65, 1), (72, -1), (75, -1), (88, -1), (97, 1), (148, -1), (205, 1), (220, -1), (297, 1)],
  [(49, 1), (65, 2), (72, -1), (88, -2), (205, 1), (220, -1), (297, 1)],
  [(62, 2), (66, -2), (70, 2), (73, 2), (106, 2), (147, 2)],
  [(62, 2), (73, 2), (106, 2), (147, 2)],
  [(3, 2), (16, -2), (19, 4), (65, -2), (92, 2), (93, 1), (97, -2)],
  [(75, 2), (92, -2), (148, 2)]
]

private def primalRightInvList_4 : List (List (Nat × Int)) := [
  [(3, -1), (16, 2), (19, -3), (65, 1), (75, 1), (88, 1), (93, 1), (97, 1), (148, 1)],
  [(75, -2), (93, -1), (148, -2)],
  [(62, -1), (66, 1), (70, -1), (73, -2), (106, -2), (147, -2)],
  [(8, 2), (30, 2), (33, -2)],
  [(9, 2), (19, -2)],
  [(10, 2), (35, -2)],
  [(11, 2)],
  [(22, 2)],
  [(32, 2)],
  [(34, 2)],
  [(46, 2)],
  [(3, 2), (6, 4), (19, -2), (31, -4), (55, 2), (65, -2), (78, -2), (88, 2), (97, -2), (138, -2), (148, 2)],
  [(56, 2), (62, -2), (70, -2), (73, -2), (87, -2), (106, -2), (147, -2)],
  [(7, -2), (57, 2), (80, -2), (140, -2)],
  [(6, 2), (19, -2), (31, -2), (58, 2)],
  [(3, -2), (6, -2), (16, 2), (19, -2), (31, 2), (65, 2), (69, 2), (97, 2)],
  [(7, 4), (53, 2), (62, -2), (70, -2), (73, -2), (76, -2), (77, 2), (87, -2), (106, -2), (137, 2), (147, -2), (156, -2)],
  [(79, 2), (139, 2), (158, -2)],
  [(7, -2), (50, -2), (53, -2), (62, 2), (66, -2), (70, 2), (76, 2), (91, 2), (136, 2), (151, 2)],
  [(7, -4), (53, -2), (62, 2), (70, 2), (73, 2), (76, 2), (87, 2), (106, 2), (137, -2), (147, 2), (156, 2), (184, 2)],
  [(6, 4), (16, 2), (19, -6), (31, -4), (75, -2), (88, 2), (138, -2), (148, 2), (149, -2), (200, 2)]
]

private def primalRightInvList_5 : List (List (Nat × Int)) := [
  [(139, -2), (158, 2), (215, 2)],
  [(140, -2), (229, 2)],
  [(0, -2), (3, 2), (6, 8), (19, -6), (25, 2), (31, -8), (65, -2), (75, -2), (88, 2), (97, -2), (138, -4), (148, 2), (172, -2), (189, 2)],
  [(1, -2), (7, 4), (53, 2), (62, -2), (66, -2), (76, -2), (137, 2), (156, -2), (173, -2)],
  [(2, -2), (7, -2), (27, 2), (30, 2), (140, -2), (174, -2), (191, 2)],
  [(3, -2), (6, 2), (19, -4), (31, -2), (175, -2)],
  [(26, -2), (139, 2), (158, -2), (190, -2)],
  [(3, 2), (19, 2), (49, -2), (65, -2), (72, 2), (75, 2), (88, 2), (97, -2), (148, 2), (205, -2), (220, 2)],
  [(50, -2), (62, -2), (70, -2), (73, -2), (87, -2), (106, -2), (147, -2), (206, -2)],
  [(3, -2), (6, -8), (19, 6), (31, 8), (65, 2), (75, 2), (88, -2), (97, 2), (138, 4), (148, -2), (172, 2), (189, -2)],
  [(7, -4), (53, -2), (62, 2), (70, 2), (73, 2), (76, 2), (87, 2), (106, 2), (137, -2), (147, 2), (156, 2), (173, 2)],
  [(7, 2), (140, 2), (174, 2), (191, -2)],
  [(6, -2), (19, 2), (31, 2), (175, 2)],
  [(19, 2), (20, -2)],
  [(139, -2), (158, 2), (190, 2)],
  [(30, 2), (44, -2), (66, 2), (70, -2), (73, -2), (87, -2), (106, -2), (147, -2)],
  [(205, 2), (220, -2)],
  [(206, 2)],
  [(62, 2), (67, -2), (70, 2), (73, 2), (87, 2), (106, 2), (147, 2)],
  [(16, 2), (19, -2), (88, 2), (89, -2), (148, 2), (149, -2)],
  [(66, -2), (70, 2), (73, 2), (87, 2), (106, 2), (147, 2)]
]

def primalRightInvList : List (List (Nat × Int)) := primalRightInvList_0 ++ primalRightInvList_1 ++ primalRightInvList_2 ++ primalRightInvList_3 ++ primalRightInvList_4 ++ primalRightInvList_5

private def primalRightInvColTree : PairListTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(107, -2), (41, -2), (30, 2), (24, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(92, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(9, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(124, 2), (104, 2), (99, 2), (84, 2), (82, -2), (75, 2), (65, -2), (62, 2), (58, -2), (52, -2), (50, -4), (43, -4), (35, 8), (30, 4), (24, -4), (15, -4), (14, 4)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(97, -2), (45, 2), (38, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(34, -2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(22, 2)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(87, 2), (42, -2), (32, 2)]) (.leaf [])) (.branch (.leaf [(102, 2), (77, -2), (76, 2), (74, 2), (69, -2), (66, -2), (63, 2), (49, 2), (32, -4), (27, -2)]) (.leaf []))) (.branch (.branch (.leaf [(112, 2), (79, -1), (78, -1), (43, 2), (36, 2)]) (.leaf [])) (.branch (.leaf [(104, 2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(11, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(24, 2)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(124, 2), (114, -2), (112, 2), (107, 2), (104, 2), (95, 2), (84, 1), (79, -2), (78, -1), (52, 2), (50, 4), (43, 4), (40, 2), (35, -4), (18, -2), (15, 2), (14, -4)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(96, 2)]) (.leaf [(32, 2), (28, 2)])) (.branch (.leaf [(103, 2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(27, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(10, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(118, -2)]) (.leaf [])) (.branch (.leaf [(124, 2), (114, -2), (112, 2), (107, 2), (104, 2), (95, 2), (85, -2), (84, 1), (83, 2), (78, -1), (52, 2), (50, 4), (43, 4), (35, -4), (15, 2), (14, -4)]) (.leaf []))) (.branch (.branch (.leaf [(71, 2), (52, -2), (39, 2), (17, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(49, -2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(29, -2)]) (.leaf [])) (.branch (.leaf [(116, 2), (109, -2), (106, -2), (97, -2), (70, -2), (49, 2), (45, 2), (25, 2), (21, -2)]) (.leaf []))) (.branch (.branch (.leaf [(115, 2), (108, -2), (103, 2), (102, 2), (100, -2), (77, -2), (76, 2), (74, 2), (66, -2), (63, 2), (59, 2), (46, -2), (37, 2), (34, 2), (32, -4), (27, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(120, -2)]) (.leaf [])) (.branch (.leaf [(114, 2), (107, -2), (50, -2), (35, 2), (24, 2)]) (.leaf []))) (.branch (.branch (.leaf [(12, 2)]) (.leaf [])) (.branch (.leaf [(21, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(115, 2), (108, -2), (103, 2), (100, -2), (59, 2), (49, -2), (34, 2), (13, 2)]) (.leaf []))) (.branch (.branch (.leaf [(83, -2), (82, 2), (35, -4), (29, -2)]) (.leaf [])) (.branch (.leaf [(121, -2), (112, 2), (79, -1), (78, -1), (51, 2), (47, 2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(109, -2), (25, 2), (9, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(125, -2), (120, 2), (108, -2), (102, -2), (86, 1), (80, -2), (77, 1), (74, -1), (69, 1), (66, 1), (63, -1), (59, 1), (55, -1), (49, -2), (32, 2), (28, 2), (27, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(93, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(31, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(4, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(63, 2), (22, -2), (7, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(113, -2), (102, -2), (77, 2), (76, -2), (74, -2), (69, 2), (66, 2), (63, -2), (49, -2), (32, 4), (27, 2)]) (.leaf [])) (.branch (.leaf [(17, 2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(89, 2), (11, -2)]) (.leaf [])) (.branch (.leaf [(114, 4), (107, -4), (104, -2), (95, -2), (60, -2), (50, -4), (24, 4), (18, 2), (14, 2)]) (.leaf []))) (.branch (.branch (.leaf [(57, 2), (12, -2), (5, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(125, 2), (123, 2), (120, -2), (115, 2), (113, -2), (103, 2), (100, -2), (96, -2), (86, -2), (81, 2), (80, 2), (77, 2), (76, -2), (74, -2), (69, 2), (66, 2), (63, -2), (49, -2), (46, -2), (32, 2), (28, -2), (27, 2), (25, -2), (22, 2)]) (.leaf [])) (.branch (.leaf [(50, 2), (35, -2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(111, -2)]) (.leaf [(25, 2)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(74, 2), (73, -2), (32, -2), (27, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(98, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(117, -2), (114, -8), (110, 2), (107, 8), (104, 4), (99, -2), (98, 2), (95, 4), (75, -2), (60, 2), (50, 8), (35, -4), (24, -4), (18, -4), (15, 2), (14, -4)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(125, 2), (123, 2), (120, -2), (115, 2), (113, -2), (103, 2), (102, 2), (100, -2), (96, -2), (86, -1), (80, 2), (77, -1), (74, 1), (69, 1), (66, 1), (63, -1), (59, 1), (55, -1), (46, -2), (34, 2), (32, -2), (28, -2), (25, -2), (22, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(42, 2), (32, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(91, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(66, 2), (25, -2), (8, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(72, 2), (31, -2)]) (.leaf [(30, 2), (26, 2)])) (.branch (.leaf [(18, 2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(3, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(95, -2), (14, 2), (6, 2)]) (.leaf [])) (.branch (.leaf [(122, 2), (113, -2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(94, 2)]) (.leaf [])) (.branch (.leaf [(116, 2), (109, -2), (25, 2), (21, -2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(52, -2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(120, 2), (109, 2), (87, 2), (54, -2), (42, -2), (25, -2), (9, 2), (4, 2)]) (.leaf [])) (.branch (.leaf [(119, 2), (111, -2), (105, 2), (101, -2), (61, 2), (44, 2), (31, -2), (20, 2), (19, -2)]) (.leaf []))) (.branch (.branch (.leaf [(41, 2), (30, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(123, 2), (115, 2), (113, -2), (108, -2), (103, 2), (102, 2), (100, -2), (96, -2), (86, -1), (81, 2), (80, 2), (77, -1), (74, 1), (69, 1), (66, -1), (63, 1), (59, 1), (55, -1), (46, -2), (42, -2), (32, -2), (25, -2), (22, 2), (9, 2)]) (.leaf [])) (.branch (.leaf [(119, 2), (111, -2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(108, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(114, 2), (112, -2), (107, -2), (99, 2), (95, -2), (84, 1), (82, -2), (79, 2), (78, 1), (75, 2), (65, -2), (62, 2), (58, -2), (52, -4), (50, -8), (43, -8), (35, 12), (30, 4), (24, -4), (18, 2), (15, -6), (14, 8)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(87, -2), (42, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(114, 2), (112, -2), (107, -2), (99, 2), (95, -2), (84, 1), (82, -2), (78, 1), (71, 2), (65, -2), (62, 2), (52, -6), (50, -8), (35, 12), (29, 2), (24, -4), (15, -2), (14, 4)]) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(15, 2)]) (.leaf []))) (.branch (.branch (.leaf [(62, 2), (52, -2), (50, -4), (35, 4), (14, 2)]) (.leaf [])) (.branch (.leaf [(48, 2), (34, -2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(112, -2), (79, 1), (78, 1), (43, -2), (30, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(88, 2)]) (.leaf [])) (.branch (.leaf [(115, -2), (108, 2), (103, -2), (100, 2), (59, -2), (49, 2), (34, -2)]) (.leaf []))) (.branch (.branch (.leaf [(125, 2), (123, 2), (120, -2), (115, 2), (113, -2), (103, 2), (100, -2), (96, -2), (86, -2), (81, 2), (80, 2), (77, 2), (76, -2), (74, -2), (69, 2), (66, 2), (63, -2), (56, 2), (49, -2), (46, -2), (42, -2), (32, 4), (28, -2), (27, 2), (25, -2), (22, 2), (9, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [(79, 1), (78, 1)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(107, 2), (41, 2), (24, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(124, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(97, 2), (45, -2), (32, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [(23, 2)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(99, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(106, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(124, -2), (104, -2), (67, -2), (30, -4), (29, 2)]) (.leaf []))) (.branch (.branch (.leaf [(65, 2), (52, 2), (24, 4), (15, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(115, -2), (108, 2), (103, -2), (102, -2), (100, 2), (77, 2), (76, -2), (74, -2), (66, 2), (63, -2), (59, -2), (46, 2), (34, -2), (32, 4)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(14, 2)]) (.leaf []))) (.branch (.branch (.leaf [(100, 2)]) (.leaf [])) (.branch (.leaf [(121, 2), (112, -2), (79, 1), (78, 1), (51, -2), (35, 2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(115, 2), (108, -2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(85, -1), (84, 1), (82, 1), (68, 1), (67, -1), (65, 1), (62, -1), (60, -1), (58, 1), (52, 4), (50, 4), (43, 4), (35, -8), (30, -4), (24, 4), (15, 4), (14, -4)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(71, -2), (52, 2), (29, -2), (17, 2)]) (.leaf [])) (.branch (.leaf [(114, -2), (107, 2), (50, 2), (24, -2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(114, -2), (112, 2), (110, -2), (107, 2), (99, -2), (95, 2), (84, -1), (82, 2), (78, -1), (71, -2), (65, 2), (62, -2), (52, 6), (50, 8), (35, -12), (29, -2), (24, 4), (15, 2), (14, -4)]) (.leaf [(51, 2), (35, -2)])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(123, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(89, -2), (11, 2), (2, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(124, -2), (118, 2), (117, 2), (114, 6), (112, 2), (110, -4), (107, -6), (104, -6), (99, -2), (98, -2), (95, -2), (88, -2), (84, -3), (82, 4), (78, -1), (71, -2), (65, 4), (62, -4), (60, -2), (58, 2), (53, -2), (52, 8), (50, 4), (43, 4), (35, -16), (30, -4), (29, -4), (24, 12), (18, 4), (15, 4), (14, -4)]) (.leaf [])) (.branch (.leaf [(125, 2), (123, 2), (120, -2), (115, 2), (113, -2), (103, 2), (100, -2), (96, -2), (86, -2), (81, 2), (80, 2), (77, 2), (76, -2), (74, -2), (69, 2), (66, 2), (63, -2), (49, -2), (32, 2), (28, -2), (27, 2), (25, -2), (22, 2)]) (.leaf []))) (.branch (.branch (.leaf [(64, 2), (45, 2), (32, -2), (23, 2), (21, -2)]) (.leaf [])) (.branch (.leaf [(20, 2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(57, -2), (12, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(90, 2)]) (.leaf [])) (.branch (.leaf [(119, -2), (111, 2), (105, -2), (101, 2), (61, -2), (20, -2), (19, 2)]) (.leaf []))) (.branch (.branch (.leaf [(114, 2), (112, 2), (107, -2), (104, -2), (85, -2), (84, 1), (83, 2), (78, -1), (67, -2), (60, -2), (58, 2), (52, 2), (43, 8), (35, -4), (30, -8), (29, 2), (24, 4), (18, 2), (15, 4), (14, -4)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(109, 2), (25, -2), (9, 2), (0, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf [(102, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(63, -2), (22, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(116, 2), (115, -4), (109, -2), (108, 4), (103, -4), (102, -2), (100, 4), (97, -2), (76, -2), (59, -2), (49, 2), (45, 2), (25, 2), (21, -2)]) (.leaf [])) (.branch (.leaf [(43, 2), (30, -2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(102, 2), (77, -2), (76, 2), (34, 2), (32, -2)]) (.leaf []))) (.branch (.branch (.leaf [(125, 2), (123, 2), (120, -2), (115, 2), (113, -2), (103, 2), (100, -2), (96, -2), (77, 2), (76, -2), (74, -2), (69, 2), (66, 2), (63, -2), (49, -2), (32, 2), (28, -2), (27, 2)]) (.leaf [])) (.branch (.leaf [(105, 2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(95, 2), (14, -2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(45, 2), (32, -2)]) (.leaf []))) (.branch (.branch (.leaf [(101, 2)]) (.leaf [])) (.branch (.leaf [(19, 2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf [(117, 2), (110, -2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(117, 2), (114, 8), (110, -2), (107, -8), (104, -4), (99, 2), (98, -2), (95, -4), (75, 2), (60, -2), (50, -8), (35, 4), (24, 4), (18, 4), (15, -2), (14, 4), (1, 2)]) (.leaf [])) (.branch (.leaf []) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))) (.branch (.branch (.branch (.leaf [(66, -2), (25, 2)]) (.leaf [(35, 2), (33, 2)])) (.branch (.leaf [(116, -2), (109, 2), (25, -2), (21, 2), (16, 2)]) (.leaf []))) (.branch (.branch (.leaf []) (.leaf [])) (.branch (.leaf []) (.leaf [])))))))))

private def checkPrimalRightInvBool : Bool :=
  (primalRightInvList.length == 126) &&
  primalRightInvList.all (fun u => u.all (fun cw => cw.1 < 325)) &&
  pairListTreeBeq 9 primalRightInvColTree (buildColIndex primalRightInvList) &&
  ((List.range 126).all (fun r =>
     let v := if r < 87 then listAt [] primalABNatList r else listAt [] primalBANatList (r - 87)
     v.all (fun cw => cw.1 < 325) &&
     intTreeBeq 7 (evalRowAgainstColIndex primalRightInvColTree v)
       (intTreeAdd 7 (zeroIntTree 7) r 2)))

private theorem checkPrimalRightInvBool_true : checkPrimalRightInvBool = true := by
  decide +kernel

private theorem dot_primal126_rightInv (r s : Fin 126) :
    ((listAt [] primalRightInvList s.val).map
      (fun cw => cw.2 * sparseNatAt (primal126Data r) cw.1)).sum =
      if r = s then 2 else 0 := by
  have hok := checkPrimalRightInvBool_true
  unfold checkPrimalRightInvBool at hok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨hlen, hu325⟩, hct_beq⟩, hrows⟩
  have hct : primalRightInvColTree = buildColIndex primalRightInvList :=
    pairListTreeBeq_eq 9 _ _ hct_beq
  have hlen128 : primalRightInvList.length ≤ 128 := by omega
  have hu512 : ∀ u ∈ primalRightInvList, ∀ cw ∈ u, cw.1 < 512 :=
    fun u hu cw hcw => Nat.lt_trans (hu325 u hu cw hcw) (by decide)
  rcases hrows r.val (List.mem_range.mpr r.isLt) with ⟨hv325, hbeq⟩
  rw [hct] at hbeq
  have hv512 : ∀ cw ∈ primal126Data r, cw.1 < 512 :=
    fun cw hcw => Nat.lt_trans (hv325 cw hcw) (by decide)
  have hs128 : s.val < 128 := by omega
  have hget := evalRowAgainstColIndex_get primalRightInvList hlen128 hu512
    (primal126Data r) hv512 hs128
  have hz := intTreeBeq_sound 7 _ _ hbeq s.val hs128
  rw [intTreeGet_add 7 (zeroIntTree 7) 2 (genTreeWF_const 0 7) (by omega) hs128,
    intTreeGet_zero, zero_add] at hz
  change intTreeGet 7 (evalRowAgainstColIndex (buildColIndex primalRightInvList) (primal126Data r)) s.val = _ at hz
  rw [hget] at hz
  have hsymm : ((primal126Data r).map
      (fun cw => cw.2 * sparseNatAt (listAt [] primalRightInvList s.val) cw.1)).sum =
      ((listAt [] primalRightInvList s.val).map
        (fun cw => cw.2 * sparseNatAt (primal126Data r) cw.1)).sum := by
    rw [sum_swap_sparse]
    rfl
  rw [← hsymm, hz]
  have heq : (s.val = r.val) ↔ (r = s) :=
    ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
  by_cases hrs : r = s <;> simp [heq, hrs]

theorem primal126_linearIndependent : LinearIndependent ℝ primal126Vec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have hcoord (c : Coord) : (∑ r : Fin 126, g r * (sparseNatAt (primal126Data r) c.val : ℝ)) = 0 := by
    simpa [primal126Vec, sparseNatRealVec, Finset.sum_apply] using congrFun hg c
  have hu325 : ∀ cw ∈ listAt [] primalRightInvList s.val, cw.1 < 325 := by
    have hok := checkPrimalRightInvBool_true
    unfold checkPrimalRightInvBool at hok
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.2 _ (listAt_mem [] primalRightInvList (by rw [hok.1.1.1]; exact s.isLt))
  have hexpand : ∀ (l : List (Nat × Int)), (∀ cw ∈ l, cw.1 < 325) →
      ∑ r : Fin 126, g r *
        (((l.map (fun cw => cw.2 * sparseNatAt (primal126Data r) cw.1)).sum : Int) : ℝ) = 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons cw rest ih =>
      have hcw : cw.1 < 325 := hl cw (by simp)
      have hrest : ∀ x ∈ rest, x.1 < 325 := fun x hx => hl x (by simp [hx])
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul,
        mul_add, Finset.sum_add_distrib]
      rw [ih hrest, add_zero]
      have h1 : (∑ r : Fin 126, g r * ((cw.2 : ℝ) * (sparseNatAt (primal126Data r) cw.1 : ℝ))) =
          (cw.2 : ℝ) * (∑ r : Fin 126, g r * (sparseNatAt (primal126Data r) (⟨cw.1, hcw⟩ : Coord).val : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r _; ring
      rw [h1, hcoord ⟨cw.1, hcw⟩, mul_zero]
  have hzero := hexpand (listAt [] primalRightInvList s.val) hu325
  simp_rw [dot_primal126_rightInv] at hzero
  simp only [Int.cast_ite, Int.cast_ofNat, Int.cast_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hzero
  linarith

theorem finrank_ab_ba_ge_126 : 126 ≤ Module.finrank ℝ ↥(solAB ⊔ solBA) := by
  let vSub : Fin 126 → ↥(solAB ⊔ solBA) := fun r => ⟨primal126Vec r, primal126_mem_ab_sup_ba r⟩
  have hli : LinearIndependent ℝ vSub :=
    LinearIndependent.of_comp (Submodule.subtype (solAB ⊔ solBA)) primal126_linearIndependent
  simpa using hli.fintype_card_le_finrank

theorem finrank_three_sol_ge_126 : 126 ≤ Module.finrank ℝ ↥(solAB ⊔ solBA ⊔ solGauge) :=
  le_trans finrank_ab_ba_ge_126 (Submodule.finrank_mono le_sup_left)

/-! ### Part 2 of R8(b): `199` Certified Admissible Functionals in `rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge` -/

def dual199WsTree : PairListTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(5, 1)]) (.leaf [(3, 2), (16, -2), (19, 4), (65, -2), (81, -2), (93, 1), (97, -2), (246, 1)])) (.branch (.leaf [(54, 1), (155, 1)]) (.leaf [(8, -1), (50, -2), (53, -2), (57, -1), (62, 1), (66, -1), (70, 1), (73, -2), (76, 2), (83, 1), (87, -1), (90, 1), (102, 1), (106, -1), (136, 2), (143, 1), (147, -1), (151, 1), (312, -1), (317, 1)]))) (.branch (.branch (.leaf [(73, 1), (110, 1)]) (.leaf [(1, 1), (7, -1), (50, 1), (63, -1), (66, 1), (70, 1), (73, 1), (86, 1), (87, 1), (106, 1), (136, -1), (137, -1), (147, 1), (156, 1), (173, 1), (281, 1)])) (.branch (.leaf [(7, 1), (30, -1), (44, 1), (50, 1), (53, 1), (62, -1), (73, 1), (76, -1), (87, 1), (106, 1), (136, -1), (147, 1), (151, -1), (202, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(18, -1), (30, -1), (43, 1)]) (.leaf [(83, 1), (264, 1)])) (.branch (.leaf [(62, 1), (179, 1)]) (.leaf []))) (.branch (.branch (.leaf [(51, -1), (74, 1), (126, 1)]) (.leaf [(87, 1), (299, 1)])) (.branch (.leaf [(140, -1), (225, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(4, -1), (29, 1)]) (.leaf [(50, -1), (53, -1), (59, -1), (66, -1), (73, -1), (76, 1), (82, 1), (87, -1), (106, -1), (136, 1), (147, -1), (254, 1)])) (.branch (.leaf [(54, 1), (165, 1)]) (.leaf []))) (.branch (.branch (.leaf [(118, 1)]) (.leaf [(26, 1), (54, 1), (139, -1), (158, 1), (190, 1), (290, 1)])) (.branch (.leaf [(216, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(62, 1), (66, 1), (70, 1), (71, 1)]) (.leaf [(83, -1), (261, -1), (272, 1)])) (.branch (.leaf [(53, -1), (59, -1), (76, 1), (82, 1), (137, -1), (156, 1), (176, -1), (193, 1)]) (.leaf []))) (.branch (.branch (.leaf [(51, 2), (74, -2), (134, 1)]) (.leaf [(7, 1), (50, 1), (53, 1), (73, 1), (76, -1), (87, 1), (106, 1), (136, -1), (147, 1), (151, -1), (307, 1)])) (.branch (.leaf [(7, 2), (50, 1), (53, 2), (59, 1), (62, -2), (76, -2), (82, -1), (136, -1), (137, 1), (156, -1), (173, -1), (235, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(7, 1), (21, 1)]) (.leaf [(7, -1), (50, -1), (53, -1), (59, -1), (62, 1), (70, -1), (73, -1), (76, 1), (82, 1), (87, -1), (106, -1), (136, 1), (147, -1), (250, 1)])) (.branch (.leaf [(79, -1), (139, -1), (158, 1), (161, 1)]) (.leaf [(3, 6), (6, 2), (16, -4), (19, 8), (31, -2), (65, -6), (75, 2), (81, -2), (88, 2), (92, 2), (93, 4), (97, -6), (148, 2), (172, -1), (205, -1), (234, 1), (259, 1), (319, -1), (322, 1)]))) (.branch (.branch (.leaf [(73, -2), (114, 1)]) (.leaf [(151, -1), (286, 1)])) (.branch (.leaf [(210, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(52, 1)]) (.leaf [(62, -1), (67, 1), (70, -1), (73, -1), (83, 1), (87, -1), (106, -1), (147, -1), (268, 1)])) (.branch (.leaf [(3, 1), (6, 1), (16, -1), (20, 1), (31, -1), (65, -1), (97, -1), (186, 1)]) (.leaf []))) (.branch (.branch (.leaf [(51, -1), (74, 1), (130, 1)]) (.leaf [(62, 1), (66, -1), (70, 1), (73, 2), (106, 2), (147, 2), (303, 1)])) (.branch (.leaf [(230, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(14, -1), (39, 1)]) (.leaf [(50, 2), (53, 2), (59, 2), (62, -1), (66, 1), (70, 1), (73, 2), (76, -2), (82, -2), (87, 2), (106, 2), (136, -2), (147, 2), (258, 1)])) (.branch (.leaf [(54, -1), (169, 1)]) (.leaf []))) (.branch (.branch (.leaf [(32, -1), (51, 1), (74, -1), (122, 1)]) (.leaf [(54, -1), (294, 1)])) (.branch (.leaf [(140, 1), (221, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(3, -1), (9, -1), (97, 1), (103, 1)]) (.leaf [(140, 1), (229, -1), (276, 1)])) (.branch (.leaf [(53, 1), (63, -1), (76, -1), (86, 1), (137, 1), (156, -1), (180, -1), (197, 1)]) (.leaf []))) (.branch (.branch (.leaf [(50, -1), (53, -1), (62, 1), (67, -1), (70, 1), (76, 1), (90, 1), (136, 1), (150, 1)]) (.leaf [(3, 1), (12, 1), (19, 2), (61, 1), (75, -1), (92, 1), (97, -1), (149, -1), (313, 1)])) (.branch (.leaf [(75, 1), (81, 1), (149, 1), (242, 1)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(15, 1)]) (.leaf [(139, 1), (158, -1), (190, -1), (248, 1)])) (.branch (.leaf [(7, -2), (50, -1), (53, -1), (76, 1), (77, -1), (136, 1), (137, -1), (156, 1), (159, 1)]) (.leaf [(53, 1), (70, -1), (76, -1), (137, 1), (151, -1), (156, -1), (176, 1), (209, 1), (320, 1)]))) (.branch (.branch (.leaf [(112, 1)]) (.leaf [(75, -1), (85, 1), (149, -1), (284, 1)])) (.branch (.leaf [(6, -2), (19, 2), (31, 2), (75, 2), (93, 1), (138, 2), (204, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(30, -1), (47, 1)]) (.leaf [(139, 1), (158, -1), (215, -1), (266, 1)])) (.branch (.leaf [(7, -2), (53, -1), (66, 1), (76, 1), (137, -1), (156, 1), (183, 1)]) (.leaf []))) (.branch (.branch (.leaf [(128, 1)]) (.leaf [(6, 1), (16, -1), (31, -1), (65, -1), (301, 1)])) (.branch (.leaf [(6, -1), (19, 1), (31, 1), (227, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(6, -1), (12, -1), (31, 1), (37, 1)]) (.leaf [(54, 1), (256, 1)])) (.branch (.leaf [(50, 1), (66, 1), (73, 1), (87, 1), (106, 1), (136, -1), (147, 1), (167, 1)]) (.leaf []))) (.branch (.branch (.leaf [(120, 1)]) (.leaf [(50, 1), (53, 1), (63, -1), (66, 1), (73, 1), (76, -1), (86, 1), (87, 1), (106, 1), (136, -1), (147, 1), (292, 1)])) (.branch (.leaf [(139, -1), (158, 1), (218, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(73, 1), (99, 1)]) (.leaf [(3, -3), (16, 1), (19, -4), (61, -1), (65, 2), (75, -1), (81, 1), (84, 1), (85, -1), (88, -1), (93, -2), (97, 3), (148, -1), (238, 1), (274, 1)])) (.branch (.leaf [(61, -1), (84, 1), (178, -1), (195, 1)]) (.leaf []))) (.branch (.branch (.leaf [(3, -1), (6, -1), (31, 1), (58, -1), (61, -1), (84, 1), (97, 1), (144, 1)]) (.leaf [(75, 2), (93, 1), (148, 2), (309, 1)])) (.branch (.leaf [(50, -1), (53, -1), (62, 1), (63, 1), (66, -1), (76, 1), (86, -1), (136, 1), (239, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(19, 2), (24, 1)]) (.leaf [(54, -1), (252, 1)])) (.branch (.leaf [(7, 1), (50, 1), (62, 1), (70, 1), (73, 1), (87, 1), (106, 1), (136, -1), (147, 1), (163, 1)]) (.leaf [(3, 2), (16, -4), (19, 6), (65, -2), (75, -2), (88, -2), (93, -2), (97, -2), (148, -2), (324, 1)]))) (.branch (.branch (.leaf [(26, -1), (51, -1), (74, 1), (116, 1)]) (.leaf [(3, -2), (16, 2), (19, -4), (65, 2), (85, -2), (93, -1), (97, 2), (288, 1)])) (.branch (.leaf [(50, 1), (66, 1), (73, 1), (87, 1), (106, 1), (136, -1), (137, -1), (147, 1), (156, 1), (180, 1), (213, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(54, -1), (64, 1)]) (.leaf [(205, 1), (220, -1), (259, -1), (270, 1)])) (.branch (.leaf [(7, 2), (53, 2), (62, -1), (66, -1), (70, -1), (76, -2), (137, 2), (156, -2), (188, 1)]) (.leaf []))) (.branch (.branch (.leaf [(132, 1)]) (.leaf [(16, 1), (19, -1), (75, -1), (88, 1), (149, -1), (305, 1)])) (.branch (.leaf [(140, -1), (232, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(6, 1), (16, -1), (31, -1), (41, 1)]) (.leaf [(262, 1)])) (.branch (.leaf [(50, -2), (62, -1), (66, -1), (70, -1), (73, -2), (87, -2), (106, -2), (136, 2), (147, -2), (171, 1)]) (.leaf []))) (.branch (.branch (.leaf [(34, -1), (124, 1)]) (.leaf [(50, -2), (53, -2), (62, 1), (63, 2), (66, -1), (70, -1), (73, -2), (76, 2), (86, -2), (87, -2), (106, -2), (136, 2), (147, -2), (296, 1)])) (.branch (.leaf [(223, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(3, 1), (19, 1), (97, -1), (107, 1)]) (.leaf [(3, -1), (16, -1), (61, -1), (84, 1), (88, -1), (89, 1), (97, 1), (148, -1), (149, 1), (278, 1)])) (.branch (.leaf [(6, 2), (19, -2), (31, -2), (65, -1), (75, -1), (88, 1), (138, -1), (182, -1), (199, 1)]) (.leaf []))) (.branch (.branch (.leaf [(16, 2), (19, -2), (65, 2), (75, -2), (93, -1), (153, 1)]) (.leaf [(0, -1), (16, -2), (19, 2), (49, -1), (65, -2), (75, 4), (93, 2), (94, 1), (135, 1), (149, 2), (310, -1), (315, 1)])) (.branch (.leaf [(151, 1), (244, 1)]) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(7, 1), (13, 1)]) (.leaf [(3, -4), (6, -4), (16, 2), (19, -2), (31, 4), (65, 4), (81, 2), (88, -2), (93, -2), (97, 4), (138, 2), (148, -2), (172, 1), (189, -1), (234, -1), (247, 1)])) (.branch (.leaf [(157, 1)]) (.leaf [(50, 2), (53, 2), (62, -1), (66, 1), (70, -1), (73, 2), (76, -2), (87, 2), (90, -2), (106, 2), (136, -2), (147, 2), (318, 1)]))) (.branch (.branch (.leaf [(3, -1), (20, -1), (97, 1), (111, 1)]) (.leaf [(3, 1), (6, -1), (19, 2), (31, 1), (75, -1), (85, 1), (148, -1), (175, 1), (283, 1)])) (.branch (.leaf [(75, -1), (92, 1), (138, -1), (203, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(6, -1), (19, 1), (31, 1), (45, 1)]) (.leaf [(83, 1), (265, 1)])) (.branch (.leaf [(54, 1), (181, 1)]) (.leaf []))) (.branch (.branch (.leaf [(62, -1), (73, -1), (106, -1), (127, 1)]) (.leaf [(54, -1), (300, 1)])) (.branch (.leaf [(139, 1), (158, -1), (211, -1), (226, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(30, 1), (36, 1)]) (.leaf [(6, -2), (19, 2), (31, 2), (65, 1), (75, 1), (88, -1), (138, 1), (148, -1), (149, 1), (200, -1), (255, 1)])) (.branch (.leaf [(53, -1), (62, 1), (70, 1), (73, 1), (76, 1), (106, 1), (166, 1)]) (.leaf []))) (.branch (.branch (.leaf [(51, -1), (74, 1), (98, -1), (119, 1)]) (.leaf [(2, -1), (7, -1), (27, 1), (30, 1), (62, 1), (63, -1), (70, 1), (73, 1), (86, 1), (106, 1), (140, -1), (147, 1), (174, -1), (191, 1), (282, -1), (291, 1)])) (.branch (.leaf [(7, -1), (62, -1), (67, 1), (70, -1), (73, -1), (87, -1), (106, -1), (147, -1), (217, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(1, -1), (95, 1)]) (.leaf [(62, 1), (273, 1)])) (.branch (.leaf [(83, 1), (194, 1)]) (.leaf []))) (.branch (.branch (.leaf [(50, -1), (53, -1), (56, -1), (59, -1), (62, 2), (76, 1), (82, 1), (136, 1), (142, 1)]) (.leaf [(75, -1), (92, 1), (148, -1), (308, 1)])) (.branch (.leaf [(3, 1), (6, 1), (31, -1), (61, 1), (84, -1), (97, -1), (175, -1), (237, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(19, -1), (23, 1)]) (.leaf [(3, 3), (6, 1), (16, -2), (19, 4), (31, -1), (65, -3), (75, 1), (81, -1), (85, 1), (88, 1), (93, 2), (97, -3), (148, 1), (238, -1), (251, 1)])) (.branch (.leaf [(7, -1), (57, 1), (80, -1), (83, -1), (140, -1), (143, -1), (162, 1)]) (.leaf [(3, -2), (16, 2), (19, -4), (65, 2), (92, -2), (93, -1), (97, 2), (323, 1)]))) (.branch (.branch (.leaf [(0, 1), (25, -1), (94, -1), (115, 1)]) (.leaf [(3, 2), (16, -1), (19, 3), (65, -2), (75, 1), (85, 1), (88, 1), (92, 1), (93, 2), (97, -2), (148, 1), (287, 1)])) (.branch (.leaf [(212, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(54, 1), (60, 1)]) (.leaf [(83, -2), (269, 1)])) (.branch (.leaf [(53, -1), (70, 1), (76, 1), (137, -1), (156, 1), (187, 1)]) (.leaf []))) (.branch (.branch (.leaf [(30, 1), (44, -1), (62, 1), (131, 1)]) (.leaf [(49, -1), (65, -2), (72, 1), (88, 2), (205, -1), (220, 1), (297, -1), (304, 1)])) (.branch (.leaf [(6, 1), (16, -1), (31, -1), (88, -1), (89, 1), (148, -1), (149, 1), (231, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(30, -1), (40, 1)]) (.leaf [(206, -1), (260, 1)])) (.branch (.leaf [(7, 1), (50, 2), (53, 1), (66, 1), (73, 1), (76, -1), (87, 1), (91, -1), (106, 1), (136, -2), (147, 1), (151, -1), (170, 1)]) (.leaf []))) (.branch (.branch (.leaf [(8, 1), (30, 1), (33, -1), (62, 1), (73, 1), (102, -1), (123, 1)]) (.leaf [(50, 1), (53, 1), (62, -1), (63, -1), (66, 1), (76, -1), (86, 1), (136, -1), (295, 1)])) (.branch (.leaf [(139, -1), (158, 1), (207, -1), (222, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(11, -1), (105, 1)]) (.leaf [(62, -1), (277, 1)])) (.branch (.leaf [(87, 1), (198, 1)]) (.leaf []))) (.branch (.branch (.leaf [(3, 1), (6, 1), (16, -2), (19, 2), (31, -1), (65, -3), (69, -1), (75, 2), (88, 1), (92, 1), (93, 2), (97, -1), (148, 1), (152, 1)]) (.leaf [(75, 2), (93, 1), (149, 2), (314, 1)])) (.branch (.leaf [(7, 2), (50, 1), (53, 2), (62, -1), (70, -1), (76, -2), (90, -1), (136, -1), (137, 1), (156, -1), (184, -1), (243, 1)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(7, -1), (17, 1)]) (.leaf [(7, 1), (83, 1), (140, 1), (174, 1), (191, -1), (236, -1), (249, 1)])) (.branch (.leaf [(3, 2), (6, 2), (16, -2), (19, 2), (31, -2), (55, 1), (65, -4), (75, 2), (78, -1), (81, -1), (88, 2), (93, 2), (97, -2), (138, -1), (141, -1), (148, 2), (160, 1)]) (.leaf [(50, -2), (53, -2), (62, 1), (66, -1), (70, 1), (73, -2), (76, 2), (87, -2), (106, -2), (136, 2), (147, -2), (151, 2), (321, 1)]))) (.branch (.branch (.leaf [(22, -1), (73, 1), (113, 1)]) (.leaf [(7, -1), (50, -1), (53, -1), (73, -1), (76, 1), (87, -1), (90, 1), (106, -1), (136, 1), (147, -1), (285, 1)])) (.branch (.leaf [(208, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(30, 2), (48, 1)]) (.leaf [(3, 1), (19, 1), (97, -1), (267, 1)])) (.branch (.leaf [(54, -1), (185, 1)]) (.leaf []))) (.branch (.branch (.leaf [(51, -1), (74, 1), (108, -1), (129, 1)]) (.leaf [(62, -1), (73, -1), (106, -1), (147, -1), (302, 1)])) (.branch (.leaf [(7, -1), (50, 1), (66, 1), (73, 1), (87, 1), (106, 1), (136, -1), (137, -1), (140, -1), (147, 1), (156, 1), (180, 1), (228, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(38, 1)]) (.leaf [(30, -1), (44, 1), (50, -1), (53, -1), (59, -1), (62, 1), (66, -1), (76, 1), (82, 1), (136, 1), (257, 1)])) (.branch (.leaf [(65, -1), (88, 1), (89, -1), (148, 1), (149, -1), (168, 1)]) (.leaf []))) (.branch (.branch (.leaf [(100, -1), (121, 1)]) (.leaf [(6, 1), (16, -1), (31, -1), (65, -1), (293, 1)])) (.branch (.leaf [(139, 2), (158, -2), (219, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(101, 1)]) (.leaf [(3, -1), (19, -1), (61, -1), (84, 1), (97, 1), (275, 1)])) (.branch (.leaf [(75, -1), (85, 1), (138, -1), (196, 1)]) (.leaf []))) (.branch (.branch (.leaf [(50, 1), (53, 1), (62, -1), (63, -1), (66, 1), (76, -1), (86, 1), (136, -1), (146, 1)]) (.leaf [(4, 1), (50, -1), (66, -1), (73, -1), (76, 1), (87, -1), (90, 1), (106, -1), (136, 1), (147, -1), (311, 1)])) (.branch (.leaf [(75, 1), (81, 1), (148, 1), (241, 1)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(28, 1)]) (.leaf [(59, -1), (62, -1), (70, -1), (73, -1), (82, 1), (106, -1), (147, -1), (240, -1), (253, 1)])) (.branch (.leaf [(3, -1), (6, -1), (16, 2), (19, -2), (31, 1), (65, 3), (75, -2), (85, -1), (88, -1), (93, -2), (97, 1), (145, -1), (148, -1), (164, 1)]) (.leaf []))) (.branch (.branch (.leaf [(2, 1), (27, -1), (30, -1), (62, -1), (73, -1), (96, -1), (117, 1)]) (.leaf [(0, -1), (3, -2), (6, 2), (16, 2), (19, -6), (25, 1), (31, -2), (65, 2), (75, -2), (85, -2), (93, -2), (97, 2), (138, -2), (172, -1), (189, 1), (280, -1), (289, 1)])) (.branch (.leaf [(139, -1), (158, 1), (214, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(54, 1), (68, 1)]) (.leaf [(3, -1), (19, -1), (61, -1), (84, 1), (97, 1), (271, 1)])) (.branch (.leaf [(75, 1), (81, 1), (138, 1), (192, 1)]) (.leaf []))) (.branch (.branch (.leaf [(46, -1), (51, -1), (74, 1), (133, 1)]) (.leaf [(90, 1), (306, 1)])) (.branch (.leaf [(140, 2), (233, 1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(42, 1)]) (.leaf [(3, -3), (16, 1), (19, -4), (65, 2), (75, -1), (81, 1), (85, -1), (88, -1), (93, -2), (97, 3), (148, -1), (238, 1), (263, 1)])) (.branch (.leaf [(54, -1), (177, 1)]) (.leaf []))) (.branch (.branch (.leaf [(10, 1), (35, -1), (104, -1), (125, 1)]) (.leaf [(50, 1), (66, 1), (87, 1), (206, 1), (298, 1)])) (.branch (.leaf [(209, -1), (224, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(73, 1), (109, 1)]) (.leaf [(3, 2), (19, 2), (61, 2), (84, -2), (97, -2), (279, 1)])) (.branch (.leaf [(90, 1), (201, 1)]) (.leaf []))) (.branch (.branch (.leaf [(16, 2), (19, -2), (49, 1), (65, 4), (72, -1), (75, -4), (88, -2), (93, -2), (135, -1), (148, -2), (154, 1)]) (.leaf [(54, 1), (98, 1), (158, 1), (316, 1)])) (.branch (.leaf [(3, -2), (16, 1), (19, -4), (20, 1), (65, 2), (75, -1), (81, 1), (88, -1), (92, -1), (93, -2), (97, 2), (148, -1), (245, 1)]) (.leaf []))))))))

def dual199Vec (s : Fin 199) : CoordVec :=
  sparseNatRealVec (genTreeGet [] 8 dual199WsTree s.val)

def abBasisRows : List Nat := [7, 9, 13, 14, 15, 16, 20, 25, 28, 38, 46, 48, 52, 54, 60, 66, 67, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 82, 86, 88, 89, 94, 102, 104, 106, 108, 110, 114, 118, 120, 122, 126, 135, 137, 138, 139, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 153, 159, 166, 170, 172, 174, 176, 180, 182, 184, 188, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 211, 212, 213, 214, 215, 217, 219, 220, 221, 223, 232, 234, 236, 238, 240, 242, 244, 246, 248, 250, 252, 254, 264, 265, 266, 267, 268, 269, 270, 271, 272, 274, 276, 278, 280, 281, 284, 298, 300, 302, 304, 306, 308, 310, 312, 314, 316, 318, 330, 331, 332, 333, 334, 335, 338, 342, 344, 345, 346, 347, 350, 364, 366, 370, 374, 376, 378, 382, 396, 397, 398, 399, 400, 404, 406, 408, 409, 411, 412, 430, 432, 434, 436, 438, 440, 444, 462, 463, 466, 470, 472, 473, 474, 475, 478, 498, 502, 504, 506, 510, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 562, 564, 566, 568, 570, 572, 594, 595, 596, 597, 600, 601, 603, 628, 630, 632, 660, 661, 662, 663, 664, 665, 668, 669, 694, 696, 726, 727, 729, 731, 792, 793, 828, 1026, 1027, 1028, 1034, 1036, 1042, 1043, 1046, 1054, 1060, 1061]
def baBasisRows : List Nat := [7, 9, 13, 14, 15, 16, 20, 25, 28, 38, 46, 48, 52, 54, 60, 66, 67, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 82, 86, 88, 89, 94, 102, 104, 106, 108, 110, 114, 118, 120, 122, 126, 135, 137, 138, 139, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 153, 159, 166, 170, 172, 174, 176, 180, 182, 184, 188, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 211, 212, 213, 214, 215, 217, 219, 220, 221, 223, 232, 234, 236, 238, 240, 242, 244, 246, 248, 250, 252, 254, 264, 265, 266, 267, 268, 269, 270, 271, 272, 274, 276, 278, 280, 281, 284, 298, 300, 302, 304, 306, 308, 310, 312, 314, 316, 318, 330, 331, 332, 333, 334, 335, 338, 342, 344, 345, 346, 347, 350, 364, 366, 370, 374, 376, 378, 382, 396, 397, 398, 399, 400, 404, 406, 408, 409, 411, 412, 430, 432, 434, 436, 438, 440, 444, 462, 463, 466, 470, 472, 473, 474, 475, 478, 498, 502, 504, 506, 510, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 562, 564, 566, 568, 570, 572, 594, 595, 596, 597, 600, 601, 603, 628, 630, 632, 660, 661, 662, 663, 664, 665, 668, 669, 694, 696, 726, 727, 729, 731, 792, 793, 828, 1026, 1027, 1028, 1034, 1036, 1042, 1043, 1046, 1054, 1060, 1061]
def gaugeBasisRows : List Nat := [68, 80, 132, 140, 141, 143, 144, 152, 153, 155, 164, 165, 172, 176, 177, 184, 400, 408, 409, 411, 432, 433, 440, 521, 576, 577, 578, 584, 585, 665, 666, 688, 696, 704, 705, 706, 712, 713, 721, 728, 774, 913, 921, 922, 944, 952, 977, 984, 1032, 1057, 1073, 1075, 1090, 1092, 1100, 1102, 1164, 1167, 1188, 1189, 1196, 1295, 1347, 1379, 1440, 1441, 1473, 1553, 1561, 1562, 1576, 1584, 1592, 1600, 1601, 1602, 1608, 1609, 1617, 1624, 1633, 1952, 1960, 1985, 1992, 2064, 2081, 2208, 2245, 2272, 2276, 2369, 2402, 2403, 2497, 2501, 2532, 2600, 2625, 2633, 2641, 2648, 2649, 2657, 2724, 2769, 2776, 2777, 2788, 2885, 2918, 2919, 3013, 3105, 3236, 3237, 3240, 3244, 3269, 3300, 3304, 3354, 3364, 3365, 3372, 3393, 3397, 3401, 3411, 3426, 3427, 3428, 3434, 3435, 3489, 3521, 3529, 3554, 3555, 3624, 3649, 3657, 3665, 3672, 3673, 3681, 3777, 3785, 3809, 3870, 4033, 4041, 4065, 4145, 4160, 4161, 4176, 4210, 4272, 4273, 4280, 4289, 4386, 4644, 4656, 4664, 4673, 4677, 4680, 4681, 4689, 4696, 4705, 4712, 4713, 4784, 4792, 4801, 4808, 4809, 4817, 4824, 4833, 4840, 4841, 5168, 5169, 5172, 5180, 5185, 5189, 5193, 5201, 5475, 5676, 5680, 5688, 5697, 5704, 5705, 5713, 5720, 5729, 5736, 5737, 6209, 6213, 6217, 6242, 6243, 6244, 6337, 6368, 6721, 6725, 6729, 6753, 6758, 6759, 6849, 6857, 6881, 7233, 7237, 7241, 7266, 7267, 7268, 7274, 7275, 7740, 7745, 7753, 7777, 8388, 8400, 8408, 8420, 8913, 8920, 8929, 9313, 9316, 9425, 9442, 9444, 10468, 11361, 11362, 11364]

def abBasisPairsTree : PairListTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(7, 4), (163, 4), (167, 4), (171, 4)]) (.leaf [(205, 2), (220, -2)])) (.branch (.leaf [(107, 4), (111, 4)]) (.leaf [(12, 2), (16, 2), (37, -2), (41, -2)]))) (.branch (.branch (.leaf [(75, 4), (93, 2), (148, 4), (309, 2)]) (.leaf [(23, 4), (24, 2)])) (.branch (.leaf [(109, 4), (114, 2)]) (.leaf [(172, 2), (189, -2), (204, -2), (280, 2), (288, 2), (289, -2)])))) (.branch (.branch (.branch (.leaf [(50, 4), (66, 4), (87, 4), (298, 4)]) (.leaf [(230, 4)])) (.branch (.leaf [(87, 4), (299, 4)]) (.leaf [(75, 4), (93, 2), (149, 4), (314, 2)]))) (.branch (.branch (.leaf [(105, 4), (276, 4)]) (.leaf [(276, 4)])) (.branch (.leaf [(132, -2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(254, -2), (258, -1), (292, -2), (296, -1)]) (.leaf [(211, 2), (219, 1), (226, -2)])) (.branch (.leaf [(139, 2), (158, -2), (219, 1)]) (.leaf [(49, 2), (72, -2), (89, -4), (314, 2), (324, 1)]))) (.branch (.branch (.leaf [(87, 4), (91, 4), (298, 4), (307, 4)]) (.leaf [(265, 2), (269, 1)])) (.branch (.leaf [(174, 2), (191, -2), (217, 2), (233, -1)]) (.leaf [(172, 2), (186, 4), (189, 2), (204, 2), (205, 2), (220, 2), (234, -2), (245, -4), (247, -2), (259, -2), (270, -2), (319, 4), (322, -4), (323, -2)])))) (.branch (.branch (.branch (.leaf [(60, 4), (252, 4)]) (.leaf [(47, -2), (48, -1)])) (.branch (.leaf [(252, 4), (290, 4)]) (.leaf [(102, 2), (106, 2), (123, -2), (127, -2)]))) (.branch (.branch (.leaf [(163, 4), (171, 2), (285, 4), (318, 2)]) (.leaf [(4, 2), (29, -2)])) (.branch (.leaf [(22, 4)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(15, 4), (271, 4), (275, 4), (279, 4)]) (.leaf [(209, 2), (224, -2)])) (.branch (.leaf [(135, 2), (153, 2), (154, -2), (297, 2), (304, -2), (309, -2)]) (.leaf [(30, 4), (48, 2)]))) (.branch (.branch (.leaf [(83, 4), (264, 4)]) (.leaf [(187, 4), (188, 2), (250, 4), (258, 2)])) (.branch (.leaf [(241, 4), (246, 2), (283, 4), (288, 2)]) (.leaf [(12, 4), (23, 4), (37, 4), (61, 4), (84, 4), (238, 4), (242, 4), (246, 4), (251, 4), (263, 4), (274, 4), (287, 4), (313, 8), (314, 2), (323, 6)])))) (.branch (.branch (.branch (.leaf [(56, 4), (71, 2), (198, 4), (303, 2)]) (.leaf [(234, 2), (245, 4), (247, -2), (323, -2), (324, -1)])) (.branch (.leaf [(165, 4), (300, 4)]) (.leaf [(96, 2), (114, 1), (117, -2), (131, -2)]))) (.branch (.branch (.leaf [(85, 4), (93, 2), (284, 4), (314, 2)]) (.leaf [(0, 2), (25, -2)])) (.branch (.leaf [(256, -2), (294, -2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(110, 4), (114, 2)]) (.leaf [(218, 2), (219, 1)])) (.branch (.leaf [(143, 2), (162, -2), (269, 1)]) (.leaf [(55, 2), (78, -2), (93, -1), (200, -2), (284, 2), (288, 1)]))) (.branch (.branch (.leaf [(100, 2), (121, -2), (216, 2)]) (.leaf [(263, 2), (267, 2), (274, -2), (279, -1)])) (.branch (.leaf [(178, 2), (195, -2), (267, 2), (279, -1)]) (.leaf [(0, 2), (25, 2), (49, 2), (72, 2), (89, 4), (94, -2), (115, -2), (135, -2), (153, -2), (154, -2), (168, -4), (310, 4), (314, 2), (315, -4)])))) (.branch (.branch (.branch (.leaf [(68, 2), (300, 2)]) (.leaf [(239, 4), (295, 4)])) (.branch (.leaf [(159, 4), (170, 4)]) (.leaf [(135, 2), (153, 2), (154, -2), (168, -4), (324, 1)]))) (.branch (.branch (.leaf [(120, 4)]) (.leaf [(8, 2), (33, -2), (48, -1)])) (.branch (.leaf [(186, 4), (196, 4), (204, 2), (288, 2)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(13, 4), (250, 4), (254, 4), (258, 4)]) (.leaf [(207, 2), (218, 2), (222, -2)])) (.branch (.leaf [(126, 4), (134, 2), (181, 4), (185, 4)]) (.leaf [(26, 4)]))) (.branch (.branch (.leaf [(79, 4), (214, 4)]) (.leaf [(113, 4), (114, 2)])) (.branch (.leaf [(163, 4), (171, 2), (183, 4), (188, 2)]) (.leaf [(192, 4), (196, 4), (246, 2), (288, 2)])))) (.branch (.branch (.branch (.leaf [(54, 4), (165, 4)]) (.leaf [(227, 4), (231, 4)])) (.branch (.leaf [(128, 4)]) (.leaf [(94, 2), (115, -2)]))) (.branch (.branch (.leaf [(40, 4), (48, 2)]) (.leaf [(273, 4), (277, 4)])) (.branch (.leaf [(180, 2), (188, 1), (197, -2), (202, -2), (286, 2), (296, -1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(38, 4), (262, 4)]) (.leaf [(213, 2), (217, 2), (228, -2), (233, -1)])) (.branch (.leaf [(141, 2), (152, 2), (160, -2), (246, 1), (308, -2), (309, -1)]) (.leaf [(51, 2), (74, -2), (130, -2)]))) (.branch (.branch (.leaf [(97, 4), (168, 4), (283, 4), (288, 2), (309, 2)]) (.leaf [(261, 2), (269, 1), (272, -2)])) (.branch (.leaf [(176, 2), (187, 2), (193, -2), (244, 2), (258, -1), (321, -1)]) (.leaf [(180, 2), (188, 1), (197, 2), (202, 2), (213, 2), (217, 2), (228, 2), (233, 1), (257, -2), (258, -1), (268, -2), (269, -1), (286, 2), (295, -2), (321, 2)])))) (.branch (.branch (.branch (.leaf [(62, 4), (273, 4)]) (.leaf [(170, -2), (171, -1), (243, 2), (318, -1)])) (.branch (.leaf [(155, 4), (169, 4)]) (.leaf [(116, 4), (134, 2)]))) (.branch (.branch (.leaf [(271, 4), (279, 2), (283, 4), (287, 4), (288, 4), (309, 2), (323, 2), (324, 2)]) (.leaf [(6, 2), (24, 1), (31, -2), (45, -2)])) (.branch (.leaf [(112, 4)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(130, -2), (134, -1)]) (.leaf [(215, 2), (219, 1)])) (.branch (.leaf [(137, 2), (151, 2), (156, -2), (171, -1), (188, 1), (307, -2)]) (.leaf [(34, 4)]))) (.branch (.branch (.leaf [(90, 4), (306, 4)]) (.leaf [(259, 2), (270, -2)])) (.branch (.leaf [(172, 2), (186, 4), (189, -2), (204, -2), (324, -1)]) (.leaf [(98, 4), (112, 4), (119, 4), (134, 2), (139, 4), (158, 4), (185, 4), (219, 2), (294, 4), (316, 8)])))) (.branch (.branch (.branch (.leaf [(58, 4), (227, 4)]) (.leaf [(236, 2), (249, -2), (268, 2)])) (.branch (.leaf [(148, 4), (153, 2), (227, 4), (301, 4), (309, 2)]) (.leaf [(98, 2), (119, -2), (134, -1)]))) (.branch (.branch (.leaf [(126, 4), (134, 2)]) (.leaf [(2, 2), (27, -2), (44, -2)])) (.branch (.leaf [(192, 4), (203, 4), (246, 2), (323, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(242, 4), (246, 2), (284, 4), (288, 2)]) (.leaf [(223, 4)])) (.branch (.leaf [(18, 2), (43, -2), (48, -1)]) (.leaf [(58, 4), (69, 4), (305, 4), (309, 2), (314, 2), (324, 2)]))) (.branch (.branch (.leaf [(103, 4), (255, 4), (287, 4), (288, 2), (323, 2), (324, 2)]) (.leaf [(268, 2), (269, 1)])) (.branch (.leaf [(46, -2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(64, 4), (290, 4)]) (.leaf [(257, -2), (258, -1), (295, -2), (296, -1)])) (.branch (.leaf [(19, 4), (24, 2)]) (.leaf [(138, 4), (153, 2), (204, 2), (293, 4)]))) (.branch (.branch (.leaf [(124, 4)]) (.leaf [(10, 2), (35, -2), (46, -2)])) (.branch (.leaf [(244, 4), (286, 4)]) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(9, 4), (24, 2), (196, 4), (200, 4), (204, 4), (288, 2), (314, 2), (324, 2)]) (.leaf [(206, 4)])) (.branch (.leaf [(131, 4), (146, 4), (150, 4), (296, 2), (318, 2)]) (.leaf [(13, 4), (17, 4)]))) (.branch (.branch (.leaf [(77, 4), (91, 4), (183, 4), (307, 4)]) (.leaf [(70, 4), (71, 2), (254, 4), (258, 2)])) (.branch (.leaf [(148, 4), (153, 2), (168, 4), (309, 2)]) (.leaf [(173, 4), (188, 2), (281, 4), (296, 2)])))) (.branch (.branch (.branch (.leaf [(53, 2), (71, 1), (76, -2), (147, 2), (166, -2), (303, 1)]) (.leaf [(225, 4), (233, 2)])) (.branch (.leaf [(108, 2), (129, -2), (134, -1)]) (.leaf [(77, 4), (184, 4)]))) (.branch (.branch (.leaf [(16, 2), (24, 1), (41, -2), (45, -2)]) (.leaf [(271, 4), (279, 2)])) (.branch (.leaf [(169, -2), (185, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(30, 4), (48, 2), (146, 4), (296, 2), (299, 4), (303, 2)]) (.leaf [(212, 4)])) (.branch (.leaf [(140, 4), (233, 2)]) (.leaf [(50, 4), (67, 4)]))) (.branch (.branch (.leaf [(92, 4), (93, 2), (308, 4), (309, 2)]) (.leaf [(266, 2)])) (.branch (.leaf [(175, 4), (231, 4)]) (.leaf [(176, 4), (187, 4), (193, 4), (209, 4), (224, 4), (244, 4), (258, 2), (320, 8), (321, 2)])))) (.branch (.branch (.branch (.leaf [(61, 2), (84, -2), (263, 2), (274, -2)]) (.leaf [(133, -2), (134, -1)])) (.branch (.leaf [(273, 4), (298, 4), (302, 4), (303, 4)]) (.leaf [(103, 4), (107, 4)]))) (.branch (.branch (.leaf [(107, 4), (196, 4), (204, 2), (288, 2), (293, 4)]) (.leaf [(5, 4)])) (.branch (.leaf [(69, 4), (200, 4), (204, 2), (314, 2), (324, 2)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(44, -2), (48, -1)]) (.leaf [(210, 4)])) (.branch (.leaf [(136, 4), (171, 2), (298, 4), (303, 2)]) (.leaf [(32, 4)]))) (.branch (.branch (.leaf [(89, 4), (93, 2), (305, 4), (309, 2)]) (.leaf [(245, 4), (246, 2), (287, 4), (288, 2)])) (.branch (.leaf [(170, 4), (171, 2), (264, 4), (269, 2), (298, 4), (303, 2)]) (.leaf [(44, 2), (48, 1), (67, 2), (71, 1), (106, -2), (114, -1), (127, -2), (131, -2), (147, -2), (150, -2), (166, -2), (171, -1), (299, 2), (306, -2), (318, -2)])))) (.branch (.branch (.branch (.leaf [(57, 2), (80, -2), (213, 2), (228, -2)]) (.leaf [(235, 4), (257, 4)])) (.branch (.leaf [(146, 4), (198, 4), (296, 2), (303, 2)]) (.leaf [(97, 4), (111, 4)]))) (.branch (.branch (.leaf [(106, 2), (114, 1), (127, -2), (131, -2)]) (.leaf [(1, 4)])) (.branch (.leaf [(190, 4), (219, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(45, 4), (149, 4), (153, 2), (293, 4), (314, 2)]) (.leaf [(221, 4), (232, 4)])) (.branch (.leaf [(144, 4), (279, 2)]) (.leaf [(56, 4), (71, 2), (292, 4), (296, 2)]))) (.branch (.branch (.leaf [(101, 4), (230, 4)]) (.leaf [(264, 4), (269, 2)])) (.branch (.leaf [(179, 4), (277, 4)]) (.leaf [(4, 4), (29, 4), (53, 4), (71, 2), (76, 4), (90, 4), (167, 4), (311, 8), (318, 2)])))) (.branch (.branch (.branch (.leaf [(63, 2), (71, 1), (86, -2), (282, 2), (291, -2), (303, 1)]) (.leaf [(241, 4), (246, 2), (308, 4), (323, 2)])) (.branch (.leaf [(161, 4)]) (.leaf [(136, 4), (150, 4), (171, 2), (318, 2)]))) (.branch (.branch (.leaf [(122, 4), (133, 4)]) (.leaf [(9, 4), (24, 2)])) (.branch (.leaf [(198, 4), (202, 4), (217, 4), (303, 2), (321, 2)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(14, 2), (39, -2), (261, 2), (265, 2), (269, 2), (272, -2)]) (.leaf [(208, 4)])) (.branch (.leaf [(239, 4), (243, 4), (281, 4), (285, 4)]) (.leaf [(28, 4)]))) (.branch (.branch (.leaf [(81, 4), (92, 4), (241, 4), (308, 4)]) (.leaf [(152, 4), (153, 2), (255, 4), (323, 2), (324, 2)])) (.branch (.leaf [(165, 4), (169, 4), (214, 4), (219, 2)]) (.leaf [(8, 2), (22, 2), (33, 2), (48, 1), (57, 2), (80, 2), (102, -2), (113, -2), (123, -2), (143, -2), (162, -2), (180, 2), (184, 2), (188, 2), (197, 2), (213, 2), (228, 2), (243, -2), (269, -1), (286, 2), (295, -2), (312, 4), (317, -4), (318, -1), (321, 3)])))) (.branch (.branch (.branch (.leaf [(55, 2), (69, 2), (78, -2), (93, -1), (182, 2), (199, -2), (301, 2), (309, -1)]) (.leaf [(232, 4), (233, 2)])) (.branch (.leaf [(147, 2), (150, 2), (166, -2), (171, -1), (303, 1), (306, -2)]) (.leaf [(95, 4)]))) (.branch (.branch (.leaf [(63, 2), (71, 1), (86, -2), (90, -2), (110, 2), (114, 1), (292, -2), (318, 1)]) (.leaf [(278, 4), (279, 2)])) (.branch (.leaf [(181, 4), (294, 4)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(20, 4), (24, 2)]) (.leaf [(214, 4), (219, 2)])) (.branch (.leaf [(142, 4), (258, 2), (302, 4), (303, 2)]) (.leaf [(52, 4)]))) (.branch (.branch (.leaf [(99, 4), (114, 2), (201, 4), (286, 4), (318, 2), (321, 2)]) (.leaf [(262, 4)])) (.branch (.leaf [(177, 4), (256, 4)]) (.leaf [(203, 4), (204, 2), (238, 4), (246, 2), (251, 4), (263, 4), (267, 4), (274, 4), (279, 2), (287, 4), (323, 4)])))) (.branch (.branch (.branch (.leaf [(67, 2), (71, 1), (299, 2), (303, 1)]) (.leaf [(203, -2), (204, -1), (238, 2), (246, 1), (251, -2), (287, 2)])) (.branch (.leaf [(157, 4)]) (.leaf [(118, 4)]))) (.branch (.branch (.leaf [(116, 4), (134, 2), (290, 4), (300, 4)]) (.leaf [(7, 4), (21, 4)])) (.branch (.leaf [(151, 4), (201, 4), (318, 2), (321, 2)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(17, 4), (281, 4), (292, 4), (296, 4)]) (.leaf [(216, 2)])) (.branch (.leaf [(138, 4), (153, 2), (204, 2), (301, 4)]) (.leaf [(36, 4), (40, 4)]))) (.branch (.branch (.leaf [(85, 4), (93, 2), (283, 4), (309, 2)]) (.leaf [(260, 4)])) (.branch (.leaf [(173, 4), (188, 2), (202, 4), (321, 2)]) (.leaf [(16, 4), (24, 2), (41, 4), (45, 4), (65, 4), (88, 4), (93, 2), (149, 4), (153, 2), (305, 4), (314, 4)])))) (.branch (.branch (.branch (.leaf [(59, 2), (70, 2), (82, -2), (240, 2), (253, -2), (302, 2)]) (.leaf [(237, 4), (278, 4)])) (.branch (.leaf [(240, 2), (253, -2), (258, -1), (282, 2), (291, -2), (296, -1)]) (.leaf [(99, 4), (114, 2)]))) (.branch (.branch (.leaf [(111, 2), (145, 2), (153, 1), (164, -2), (168, -2), (288, 1), (293, -2), (324, 1)]) (.leaf [(3, 4), (20, 4)])) (.branch (.leaf [(194, 4), (269, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(49, 2), (65, 4), (72, -2), (88, -4), (297, 2), (304, -2)]) (.leaf [(229, 4), (233, 2)])) (.branch (.leaf [(42, 4)]) (.leaf [(73, 4), (110, 4)]))) (.branch (.branch (.leaf [(104, 2), (125, -2), (266, 2)]) (.leaf [(275, 4), (279, 2)])) (.branch (.leaf [(91, -2), (184, 2), (188, 1), (321, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(70, 2), (71, 1), (302, 2), (303, 1)]) (.leaf [(248, 4)])) (.branch (.leaf [(66, 4), (71, 2), (167, 4), (171, 2)]) (.leaf [(140, 4), (151, 4), (233, 2), (306, 4), (318, 2), (321, 2)]))) (.branch (.branch (.leaf [(17, 4), (21, 4)]) (.leaf [(11, 4), (22, 4)])) (.branch (.leaf [(203, 4), (204, 2), (267, 4), (301, 4), (323, 2)]) (.leaf []))))))))
def baBasisPairsTree : PairListTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(13, 4), (250, 4), (254, 4), (258, 4)]) (.leaf [(205, 2), (259, -2)])) (.branch (.leaf [(41, 4), (45, 4)]) (.leaf [(3, 2), (20, 2), (97, -2), (111, -2)]))) (.branch (.branch (.leaf [(192, 4), (203, 4), (246, 2), (323, 2)]) (.leaf [(19, 4), (24, 2)])) (.branch (.leaf [(47, 4), (48, 2)]) (.leaf [(49, 2), (135, -2), (153, -2), (310, 2), (314, 2), (315, -2)])))) (.branch (.branch (.branch (.leaf [(176, 4), (187, 4), (244, 4), (320, 4)]) (.leaf [(262, 4)])) (.branch (.leaf [(244, 4), (286, 4)]) (.leaf [(192, 4), (196, 4), (246, 2), (288, 2)]))) (.branch (.branch (.leaf [(39, 4), (272, 4)]) (.leaf [(272, 4)])) (.branch (.leaf [(128, -2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(163, -2), (171, -1), (285, -2), (318, -1)]) (.leaf [(215, 2), (219, 1), (266, -2)])) (.branch (.leaf [(190, 2), (219, 1), (248, -2)]) (.leaf [(172, 2), (234, -2), (238, -4), (288, 2), (324, 1)]))) (.branch (.branch (.leaf [(240, 4), (244, 4), (302, 4), (320, 4)]) (.leaf [(225, 2), (233, 1)])) (.branch (.leaf [(57, 2), (143, -2), (213, 2), (269, -1)]) (.leaf [(49, 2), (65, 4), (72, -2), (88, -4), (135, 2), (153, 2), (154, -2), (205, 2), (220, -2), (259, 2), (270, -2), (297, 4), (304, -4), (309, -2)])))) (.branch (.branch (.branch (.leaf [(155, 4), (169, 4)]) (.leaf [(109, -2), (114, -1)])) (.branch (.leaf [(169, 4), (316, 4)]) (.leaf [(27, 2), (44, 2), (117, -2), (131, -2)]))) (.branch (.branch (.leaf [(254, 4), (258, 2), (292, 4), (296, 2)]) (.leaf [(1, 2), (95, -2)])) (.branch (.leaf [(18, 4)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(15, 4), (271, 4), (275, 4), (279, 4)]) (.leaf [(206, 2), (260, -2)])) (.branch (.leaf [(189, 2), (204, 2), (247, -2), (319, 2), (322, -2), (323, -2)]) (.leaf [(99, 4), (114, 2)]))) (.branch (.branch (.leaf [(221, 4), (232, 4)]) (.leaf [(66, 4), (71, 2), (167, 4), (171, 2)])) (.branch (.leaf [(92, 4), (93, 2), (313, 4), (314, 2)]) (.leaf [(3, 4), (19, 4), (85, 4), (89, 4), (93, 4), (97, 4), (168, 4), (175, 4), (231, 4), (237, 4), (278, 4), (283, 8), (288, 2), (305, 4), (309, 6)])))) (.branch (.branch (.branch (.leaf [(137, 4), (151, 4), (188, 2), (321, 2)]) (.leaf [(72, 2), (88, 4), (154, -2), (309, -2), (324, -1)])) (.branch (.leaf [(256, 4), (294, 4)]) (.leaf [(33, 2), (48, 1), (123, -2), (127, -2)]))) (.branch (.branch (.leaf [(242, 4), (246, 2), (284, 4), (288, 2)]) (.leaf [(0, 2), (94, -2)])) (.branch (.leaf [(165, -2), (300, -2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(40, 4), (48, 2)]) (.leaf [(214, 2), (219, 1)])) (.branch (.leaf [(191, 2), (233, 1), (249, -2)]) (.leaf [(55, 2), (141, -2), (145, -2), (246, -1), (284, 2), (314, 1)]))) (.branch (.branch (.leaf [(34, 2), (124, -2), (212, 2)]) (.leaf [(227, 2), (231, 2), (278, -2), (279, -1)])) (.branch (.leaf [(58, 2), (144, -2), (227, 2), (279, -1)]) (.leaf [(0, 2), (25, -2), (94, 2), (115, -2), (172, 2), (189, -2), (204, -2), (234, 2), (238, 4), (247, -2), (251, -4), (280, 4), (288, 2), (289, -4)])))) (.branch (.branch (.branch (.leaf [(181, 2), (294, 2)]) (.leaf [(90, 4), (306, 4)])) (.branch (.leaf [(82, 4), (253, 4)]) (.leaf [(189, 2), (204, 2), (247, -2), (251, -4), (324, 1)]))) (.branch (.branch (.leaf [(120, 4)]) (.leaf [(2, 2), (96, -2), (114, -1)])) (.branch (.leaf [(65, 4), (149, 4), (153, 2), (314, 2)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(7, 4), (163, 4), (167, 4), (171, 4)]) (.leaf [(79, 2), (161, -2), (214, 2)])) (.branch (.leaf [(64, 4), (68, 4), (130, 4), (134, 2)]) (.leaf [(98, 4)]))) (.branch (.branch (.leaf [(207, 4), (218, 4)]) (.leaf [(43, 4), (48, 2)])) (.branch (.leaf [(70, 4), (71, 2), (254, 4), (258, 2)]) (.leaf [(75, 4), (93, 2), (149, 4), (314, 2)])))) (.branch (.branch (.branch (.leaf [(177, 4), (256, 4)]) (.leaf [(263, 4), (267, 4)])) (.branch (.leaf [(132, 4)]) (.leaf [(25, 2), (115, -2)]))) (.branch (.branch (.leaf [(110, 4), (114, 2)]) (.leaf [(273, 4), (277, 4)])) (.branch (.leaf [(67, 2), (71, 1), (147, -2), (150, -2), (299, 2), (318, -1)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(101, 4), (230, 4)]) (.leaf [(213, 2), (217, 2), (268, -2), (269, -1)])) (.branch (.leaf [(78, 2), (93, 1), (160, -2), (199, 2), (308, -2), (323, -1)]) (.leaf [(32, 2), (122, -2), (126, -2)]))) (.branch (.branch (.leaf [(37, 4), (251, 4), (313, 4), (314, 2), (323, 2)]) (.leaf [(229, 2), (233, 1), (276, -2)])) (.branch (.leaf [(50, 2), (66, 2), (87, 2), (136, -2), (171, -1), (303, -1)]) (.leaf [(67, 2), (71, 1), (147, 2), (150, 2), (166, -2), (171, -1), (213, 2), (217, 2), (228, -2), (233, -1), (268, 2), (269, 1), (299, 2), (303, 2), (306, -2)])))) (.branch (.branch (.branch (.leaf [(179, 4), (277, 4)]) (.leaf [(86, 2), (253, -2), (258, -1), (296, -1)])) (.branch (.leaf [(60, 4), (252, 4)]) (.leaf [(119, 4), (134, 2)]))) (.branch (.branch (.leaf [(275, 4), (279, 2), (305, 4), (309, 2), (313, 4), (314, 4), (323, 2), (324, 2)]) (.leaf [(9, 2), (24, 1), (103, -2), (107, -2)])) (.branch (.leaf [(42, 4)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(126, -2), (134, -1)]) (.leaf [(211, 2), (219, 1)])) (.branch (.leaf [(56, 2), (71, 1), (142, -2), (198, 2), (258, -1), (302, -2)]) (.leaf [(100, 4)]))) (.branch (.branch (.leaf [(239, 4), (295, 4)]) (.leaf [(220, 2), (270, -2)])) (.branch (.leaf [(49, 2), (65, 4), (135, -2), (153, -2), (324, -1)]) (.leaf [(26, 4), (42, 4), (64, 4), (116, 4), (134, 2), (190, 4), (219, 2), (248, 4), (290, 8), (300, 4)])))) (.branch (.branch (.branch (.leaf [(178, 4), (267, 4)]) (.leaf [(80, 2), (162, -2), (228, 2)])) (.branch (.leaf [(203, 4), (204, 2), (267, 4), (301, 4), (323, 2)]) (.leaf [(26, 2), (116, -2), (134, -1)]))) (.branch (.branch (.leaf [(130, 4), (134, 2)]) (.leaf [(8, 2), (102, -2), (106, -2)])) (.branch (.leaf [(75, 4), (93, 2), (148, 4), (309, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(85, 4), (93, 2), (284, 4), (314, 2)]) (.leaf [(223, 4)])) (.branch (.leaf [(22, 2), (113, -2), (114, -1)]) (.leaf [(178, 4), (182, 4), (287, 4), (288, 2), (323, 2), (324, 2)]))) (.branch (.branch (.leaf [(31, 4), (164, 4), (305, 4), (309, 2), (314, 2), (324, 2)]) (.leaf [(228, 2), (233, 1)])) (.branch (.leaf [(108, -2)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(185, 4), (316, 4)]) (.leaf [(166, -2), (171, -1), (306, -2), (318, -1)])) (.branch (.leaf [(23, 4), (24, 2)]) (.leaf [(138, 4), (153, 2), (204, 2), (293, 4)]))) (.branch (.branch (.leaf [(121, 4)]) (.leaf [(10, 2), (104, -2), (108, -2)])) (.branch (.leaf [(87, 4), (299, 4)]) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(6, 4), (24, 2), (145, 4), (149, 4), (153, 4), (288, 2), (314, 2), (324, 2)]) (.leaf [(209, 4)])) (.branch (.leaf [(127, 4), (197, 4), (201, 4), (296, 2), (318, 2)]) (.leaf [(7, 4), (21, 4)]))) (.branch (.branch (.leaf [(59, 4), (70, 4), (240, 4), (302, 4)]) (.leaf [(163, 4), (171, 2), (183, 4), (188, 2)])) (.branch (.leaf [(203, 4), (204, 2), (251, 4), (323, 2)]) (.leaf [(53, 4), (71, 2), (311, 4), (318, 2)])))) (.branch (.branch (.branch (.leaf [(173, 2), (188, 1), (202, 2), (235, -2), (257, -2), (321, 1)]) (.leaf [(265, 4), (269, 2)])) (.branch (.leaf [(46, 2), (133, -2), (134, -1)]) (.leaf [(59, 4), (63, 4)]))) (.branch (.branch (.leaf [(20, 2), (24, 1), (107, -2), (111, -2)]) (.leaf [(275, 4), (279, 2)])) (.branch (.leaf [(64, 2), (252, -2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(99, 4), (114, 2), (201, 4), (286, 4), (318, 2), (321, 2)]) (.leaf [(216, 4)])) (.branch (.leaf [(194, 4), (269, 2)]) (.leaf [(176, 4), (180, 4)]))) (.branch (.branch (.leaf [(241, 4), (246, 2), (308, 4), (323, 2)]) (.leaf [(226, 2)])) (.branch (.leaf [(61, 4), (263, 4)]) (.leaf [(50, 4), (66, 4), (87, 4), (136, 4), (171, 2), (206, 4), (260, 4), (298, 8), (303, 2)])))) (.branch (.branch (.branch (.leaf [(175, 2), (231, 2), (237, -2), (278, -2)]) (.leaf [(129, -2), (134, -1)])) (.branch (.leaf [(277, 4), (307, 4), (320, 4), (321, 4)]) (.leaf [(31, 4), (45, 4)]))) (.branch (.branch (.leaf [(45, 4), (149, 4), (153, 2), (293, 4), (314, 2)]) (.leaf [(5, 4)])) (.branch (.leaf [(145, 4), (153, 2), (182, 4), (288, 2), (324, 2)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(106, -2), (114, -1)]) (.leaf [(210, 4)])) (.branch (.leaf [(193, 4), (258, 2), (320, 4), (321, 2)]) (.leaf [(51, 4)]))) (.branch (.branch (.leaf [(238, 4), (246, 2), (287, 4), (323, 2)]) (.leaf [(88, 4), (93, 2), (305, 4), (314, 2)])) (.branch (.leaf [(232, 4), (233, 2), (253, 4), (258, 2), (320, 4), (321, 2)]) (.leaf [(44, -2), (48, -1), (106, 2), (114, 1), (127, -2), (131, -2), (180, 2), (188, 1), (197, -2), (202, -2), (257, -2), (258, -1), (286, 2), (295, -2), (296, -2)])))) (.branch (.branch (.branch (.leaf [(174, 2), (217, 2), (236, -2), (268, -2)]) (.leaf [(76, 4), (166, 4)])) (.branch (.leaf [(151, 4), (201, 4), (318, 2), (321, 2)]) (.leaf [(37, 4), (41, 4)]))) (.branch (.branch (.leaf [(44, 2), (48, 1), (127, -2), (131, -2)]) (.leaf [(4, 4)])) (.branch (.leaf [(139, 4), (219, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(107, 4), (196, 4), (204, 2), (288, 2), (293, 4)]) (.leaf [(83, 4), (264, 4)])) (.branch (.leaf [(195, 4), (279, 2)]) (.leaf [(137, 4), (188, 2), (285, 4), (318, 2)]))) (.branch (.branch (.leaf [(38, 4), (262, 4)]) (.leaf [(232, 4), (233, 2)])) (.branch (.leaf [(62, 4), (273, 4)]) (.leaf [(1, 4), (95, 4), (173, 4), (188, 2), (235, 4), (239, 4), (250, 4), (281, 8), (296, 2)])))) (.branch (.branch (.branch (.leaf [(184, 2), (188, 1), (243, -2), (312, 2), (317, -2), (321, 1)]) (.leaf [(92, 4), (93, 2), (308, 4), (309, 2)])) (.branch (.leaf [(222, 4)]) (.leaf [(193, 4), (197, 4), (258, 2), (296, 2)]))) (.branch (.branch (.leaf [(74, 4), (129, 4)]) (.leaf [(6, 4), (24, 2)])) (.branch (.leaf [(147, 4), (151, 4), (213, 4), (303, 2), (321, 2)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(11, 2), (105, -2), (225, 2), (229, 2), (233, 2), (276, -2)]) (.leaf [(157, 4)])) (.branch (.leaf [(86, 4), (90, 4), (292, 4), (311, 4)]) (.leaf [(28, 4)]))) (.branch (.branch (.leaf [(81, 4), (92, 4), (241, 4), (308, 4)]) (.leaf [(164, 4), (199, 4), (204, 2), (309, 2), (324, 2)])) (.branch (.leaf [(218, 4), (219, 2), (252, 4), (256, 4)]) (.leaf [(2, 2), (18, 2), (27, -2), (43, -2), (63, 2), (67, 2), (71, 2), (86, -2), (96, 2), (114, 1), (117, -2), (150, 2), (174, 2), (191, -2), (217, 2), (233, -1), (236, 2), (249, -2), (268, 2), (282, 4), (291, -4), (296, -1), (299, 2), (303, 3), (306, -2)])))) (.branch (.branch (.branch (.leaf [(55, 2), (69, 2), (141, -2), (152, -2), (182, 2), (246, -1), (301, 2), (323, -1)]) (.leaf [(264, 4), (269, 2)])) (.branch (.leaf [(197, 2), (202, 2), (257, -2), (258, -1), (295, -2), (321, 1)]) (.leaf [(29, 4)]))) (.branch (.branch (.leaf [(40, 2), (48, 1), (184, 2), (188, 1), (239, -2), (243, -2), (285, -2), (296, 1)]) (.leaf [(274, 4), (279, 2)])) (.branch (.leaf [(68, 4), (300, 4)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(16, 4), (24, 2)]) (.leaf [(218, 4), (219, 2)])) (.branch (.leaf [(156, 4), (171, 2), (307, 4), (321, 2)]) (.leaf [(118, 4)]))) (.branch (.branch (.leaf [(30, 4), (48, 2), (146, 4), (296, 2), (299, 4), (303, 2)]) (.leaf [(230, 4)])) (.branch (.leaf [(54, 4), (165, 4)]) (.leaf [(89, 4), (93, 2), (148, 4), (153, 2), (168, 4), (227, 4), (231, 4), (278, 4), (279, 2), (305, 4), (309, 4)])))) (.branch (.branch (.branch (.leaf [(180, 2), (188, 1), (286, 2), (321, 1)]) (.leaf [(89, 2), (93, 1), (148, -2), (153, -1), (168, -2), (305, 2)])) (.branch (.leaf [(208, 4)]) (.leaf [(52, 4)]))) (.branch (.branch (.leaf [(119, 4), (134, 2), (294, 4), (316, 4)]) (.leaf [(13, 4), (17, 4)])) (.branch (.leaf [(146, 4), (198, 4), (296, 2), (303, 2)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(21, 4), (285, 4), (311, 4), (318, 4)]) (.leaf [(212, 2)])) (.branch (.leaf [(138, 4), (153, 2), (204, 2), (301, 4)]) (.leaf [(73, 4), (110, 4)]))) (.branch (.branch (.leaf [(242, 4), (246, 2), (313, 4), (323, 2)]) (.leaf [(224, 4)])) (.branch (.leaf [(53, 4), (71, 2), (147, 4), (303, 2)]) (.leaf [(20, 4), (24, 2), (107, 4), (111, 4), (186, 4), (196, 4), (204, 2), (245, 4), (246, 2), (287, 4), (288, 4)])))) (.branch (.branch (.branch (.leaf [(77, 2), (91, 2), (159, -2), (170, -2), (183, 2), (307, 2)]) (.leaf [(84, 4), (274, 4)])) (.branch (.leaf [(91, 2), (170, -2), (171, -1), (312, 2), (317, -2), (318, -1)]) (.leaf [(30, 4), (48, 2)]))) (.branch (.branch (.leaf [(41, 2), (200, 2), (204, 1), (251, -2), (255, -2), (293, -2), (314, 1), (324, 1)]) (.leaf [(12, 4), (16, 4)])) (.branch (.leaf [(140, 4), (233, 2)]) (.leaf []))))) (.branch (.branch (.branch (.branch (.leaf [(172, 2), (186, 4), (234, -2), (245, -4), (319, 2), (322, -2)]) (.leaf [(261, 4), (269, 2)])) (.branch (.leaf [(112, 4)]) (.leaf [(36, 4), (40, 4)]))) (.branch (.branch (.leaf [(35, 2), (125, -2), (226, 2)]) (.leaf [(271, 4), (279, 2)])) (.branch (.leaf [(63, 2), (71, 1), (240, -2), (303, 1)]) (.leaf [])))) (.branch (.branch (.branch (.leaf [(183, 2), (188, 1), (307, 2), (321, 1)]) (.leaf [(158, 4)])) (.branch (.leaf [(187, 4), (188, 2), (250, 4), (258, 2)]) (.leaf [(194, 4), (198, 4), (269, 2), (295, 4), (296, 2), (303, 2)]))) (.branch (.branch (.leaf [(17, 4), (21, 4)]) (.leaf [(14, 4), (18, 4)])) (.branch (.leaf [(148, 4), (153, 2), (227, 4), (301, 4), (309, 2)]) (.leaf []))))))))
def gaugeBasisPairsTree : PairListTree := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(181, 4), (294, 4)]) (.leaf [(2, -2), (18, -2), (27, 2), (43, 2), (96, 6), (117, -6), (174, 2), (191, -2), (236, 2), (249, -2), (261, 2), (272, -2)])) (.branch (.leaf [(240, -4), (253, 4), (302, -4)]) (.leaf [(100, 8), (121, -8)]))) (.branch (.branch (.leaf [(265, 16), (269, 16)]) (.leaf [(277, -8)])) (.branch (.leaf [(281, 16), (296, 16)]) (.leaf [(12, 4), (23, 4), (37, 4), (61, 12), (84, -4), (275, -4)])))) (.branch (.branch (.branch (.leaf [(130, -4)]) (.leaf [(50, -4), (66, -4), (136, 12), (206, 4), (260, 4), (273, 4)])) (.branch (.leaf [(77, 8), (159, -8), (163, -8), (183, 8)]) (.leaf [(238, 12), (251, -4), (263, 4), (267, 4), (274, 4), (279, 4), (287, 12)]))) (.branch (.branch (.leaf [(0, 3), (16, 6), (20, 6), (24, 6), (25, 3), (41, 6), (49, 9), (65, 18), (72, -3), (88, -6), (94, -1), (111, -2), (115, -1), (135, -3), (153, -6), (154, 1), (172, 1), (186, 2), (189, 1), (205, 3), (220, -1), (234, 1), (245, 2), (247, 1), (259, 3), (270, -1), (280, 3), (284, 6), (288, 6), (289, 3), (297, 9), (304, -3), (310, 3), (314, 6), (315, -1), (319, 1), (322, 1)]) (.leaf [(267, 16)])) (.branch (.leaf [(16, -4), (24, -4), (41, 12), (45, 12), (65, 4), (88, 4), (305, 4)]) (.leaf [(32, 8), (122, -8), (126, -8)]))))) (.branch (.branch (.branch (.branch (.leaf [(305, -8), (309, -8), (314, -8), (324, -8)]) (.leaf [(16, 4), (24, 4), (41, 4), (45, 4), (65, 12), (88, -4), (305, -4)])) (.branch (.leaf [(83, 16), (264, 16)]) (.leaf [(101, 16)]))) (.branch (.branch (.leaf [(0, -3), (16, -6), (20, -6), (24, -6), (25, 9), (41, 18), (49, 3), (65, 6), (72, 3), (88, 6), (94, 1), (111, 2), (115, -3), (135, -1), (154, -1), (172, -1), (186, -2), (189, 3), (204, 6), (205, 1), (220, 1), (234, -1), (245, -2), (247, 3), (259, 1), (270, 1), (280, -3), (284, -6), (288, -6), (289, 9), (297, 3), (304, 3), (310, -3), (314, -6), (315, 1), (319, -1), (322, -1)]) (.leaf [(200, 8), (255, -8)])) (.branch (.leaf [(180, -4), (197, 12), (201, 12), (213, 4), (228, 4), (233, 4), (286, -4)]) (.leaf [(62, 16)])))) (.branch (.branch (.branch (.leaf [(196, 4), (204, 4)]) (.leaf [(183, 16)])) (.branch (.leaf [(40, 16)]) (.leaf [(177, 16)]))) (.branch (.branch (.leaf [(165, -4)]) (.leaf [(67, 4), (71, 4), (146, 4), (150, 4), (217, 12), (268, -4), (302, -4)])) (.branch (.leaf [(280, 4), (288, 4), (289, 4), (293, 4), (297, 12), (301, 12), (304, -4), (309, -4)]) (.leaf [(285, 8)])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(283, -4), (288, -4)]) (.leaf [(106, 4), (127, 4), (147, 12), (151, 12), (166, -4), (171, -4), (285, 4)])) (.branch (.leaf [(87, 16), (298, 16)]) (.leaf [(223, 16)]))) (.branch (.branch (.leaf [(293, -4), (301, 4), (310, 12), (314, 12), (315, -4), (319, 4), (322, 4), (323, 4)]) (.leaf [(192, 16), (203, 16)])) (.branch (.leaf [(1, -4), (17, -4), (95, 12), (173, 4), (235, 4), (250, 4)]) (.leaf [(238, 4), (251, 4), (263, 12), (267, 12), (274, -4), (279, -4), (287, 4)])))) (.branch (.branch (.branch (.leaf [(254, -4)]) (.leaf [(183, 16), (188, 16)])) (.branch (.leaf [(306, -4)]) (.leaf [(295, -4)]))) (.branch (.branch (.leaf [(211, 2), (226, -2)]) (.leaf [(112, 16)])) (.branch (.leaf [(180, 4), (197, 4), (201, 4), (213, 12), (228, -4), (233, -4), (286, 4)]) (.leaf [(63, 4), (86, -4), (292, -4)]))))) (.branch (.branch (.branch (.branch (.leaf [(271, -8)]) (.leaf [(7, 16)])) (.branch (.leaf [(89, 12), (168, -4), (227, 4), (231, 4), (278, 4), (279, 4), (305, 12)]) (.leaf [(50, 4), (66, 4), (136, 4), (206, 12), (260, -4), (273, -4)]))) (.branch (.branch (.leaf [(242, 16), (313, 16)]) (.leaf [(1, 4), (17, 4), (95, 4), (173, 12), (235, -4), (250, -4)])) (.branch (.leaf [(280, -4), (288, -4), (289, 12), (293, 12), (297, 4), (301, 4), (304, 4), (309, 4)]) (.leaf [(21, 8)])))) (.branch (.branch (.branch (.leaf [(26, 12), (64, 12), (116, -4), (190, 4), (248, 4), (252, 4)]) (.leaf [(216, 4)])) (.branch (.leaf [(106, 12), (127, -4), (147, 4), (151, 4), (166, 4), (171, 4), (285, 12)]) (.leaf [(70, 16)]))) (.branch (.branch (.leaf [(273, -8)]) (.leaf [(210, 16)])) (.branch (.leaf [(140, 16)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(126, -4)]) (.leaf [(137, 8), (156, -8)])) (.branch (.leaf [(108, -2), (129, 2)]) (.leaf [(0, 1), (16, 2), (20, 2), (24, 2), (25, 1), (41, 2), (49, -1), (65, -2), (72, 3), (88, 6), (94, 1), (111, 2), (115, 1), (135, -1), (153, -2), (154, 3), (172, 3), (186, 6), (189, 3), (205, -3), (220, 9), (234, -1), (245, -2), (247, -1), (259, 1), (270, -3), (280, 1), (284, 2), (288, 2), (289, 1), (297, -1), (304, 3), (310, 1), (314, 2), (315, 1), (319, 3), (322, -1)]))) (.branch (.branch (.leaf [(20, 12), (24, 12), (107, -4), (111, -4), (186, 4), (245, 4), (287, 4)]) (.leaf [(0, 3), (16, 6), (20, 6), (24, 6), (25, -1), (41, -2), (49, 1), (65, 2), (72, 1), (88, 2), (94, 3), (111, 6), (115, -1), (135, 1), (154, 1), (172, 9), (186, 18), (189, -3), (204, -6), (205, 3), (220, 3), (234, -3), (245, -6), (247, 1), (259, -1), (270, -1), (280, 3), (284, 6), (288, 6), (289, -1), (297, 1), (304, 1), (310, 3), (314, 6), (315, 3), (319, 9), (322, -3)])) (.branch (.leaf [(5, 16)]) (.leaf [(178, 8), (195, -8)])))) (.branch (.branch (.branch (.leaf [(305, -8), (314, -8)]) (.leaf [(19, 16), (24, 16)])) (.branch (.leaf [(264, -8)]) (.leaf [(239, 16), (295, 16)]))) (.branch (.branch (.leaf [(92, -8), (308, -8)]) (.leaf [(312, 8), (317, -8)])) (.branch (.leaf [(198, 16)]) (.leaf [(292, 8)]))))) (.branch (.branch (.branch (.branch (.leaf [(250, -8)]) (.leaf [(182, 8), (199, -8)])) (.branch (.leaf [(3, 12), (19, 12), (97, -4), (175, 4), (237, 4), (271, 4)]) (.leaf [(3, 4), (19, 4), (97, 4), (175, 12), (237, -4), (271, -4)]))) (.branch (.branch (.leaf [(299, 16)]) (.leaf [(99, 16)])) (.branch (.leaf [(293, 12), (301, 4), (310, -4), (314, -4), (315, 12), (319, 4), (322, 4), (323, 4)]) (.leaf [(181, 4)])))) (.branch (.branch (.branch (.leaf [(196, 4)]) (.leaf [(215, 2), (266, -2)])) (.branch (.leaf [(281, 16)]) (.leaf [(176, -4), (187, -4), (193, 12), (209, 4), (224, 4), (277, 4)]))) (.branch (.branch (.leaf [(252, -8)]) (.leaf [(232, -8)])) (.branch (.leaf [(138, 16)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(130, -4), (134, -4)]) (.leaf [(307, -8)])) (.branch (.leaf [(79, 8), (161, -8), (214, 8)]) (.leaf [(229, 8), (276, -8)]))) (.branch (.branch (.leaf [(110, 16), (114, 16)]) (.leaf [(9, 8), (103, -8)])) (.branch (.leaf [(26, -4), (64, -4), (116, 12), (190, 4), (248, 4), (252, 4)]) (.leaf [(0, 1), (16, 2), (20, 2), (24, 2), (25, 1), (41, 2), (49, -1), (65, -2), (72, 3), (88, 6), (94, 1), (111, 2), (115, 1), (135, -1), (153, -2), (154, 3), (172, -1), (186, -2), (189, -1), (205, 1), (220, -3), (234, 3), (245, 6), (247, 3), (259, -3), (270, 9), (280, 1), (284, 2), (288, 2), (289, 1), (297, -1), (304, 3), (310, 1), (314, 2), (315, 1), (319, -1), (322, 3)])))) (.branch (.branch (.branch (.leaf [(275, -8)]) (.leaf [(19, 16)])) (.branch (.leaf [(132, -4)]) (.leaf [(12, -4), (23, -4), (37, 12), (61, 4), (84, 4), (275, 4)]))) (.branch (.branch (.leaf [(214, 4)]) (.leaf [(20, 4), (24, 4), (107, 4), (111, 4), (186, 12), (245, -4), (287, -4)])) (.branch (.leaf [(42, 16)]) (.leaf [(107, 16)]))))) (.branch (.branch (.branch (.branch (.leaf [(313, -4), (323, -4)]) (.leaf [(3, -4), (19, -4), (97, 12), (175, 4), (237, 4), (271, 4)])) (.branch (.leaf [(73, 16), (109, 16)]) (.leaf [(36, 16), (47, 16)]))) (.branch (.branch (.leaf [(110, 16)]) (.leaf [(26, 4), (64, 4), (116, 4), (190, 12), (248, -4), (252, -4)])) (.branch (.leaf [(106, -4), (127, 12), (147, 4), (151, 4), (166, 4), (171, 4), (285, -4)]) (.leaf [(28, 16)])))) (.branch (.branch (.branch (.leaf [(149, 16), (153, 16)]) (.leaf [(256, -4)])) (.branch (.leaf [(16, 12), (24, 12), (41, -4), (45, -4), (65, 4), (88, 4), (305, 4)]) (.leaf [(14, 8), (39, -8)]))) (.branch (.branch (.leaf [(2, 6), (18, 6), (27, -6), (43, -6), (96, -2), (117, 2), (174, 2), (191, -2), (236, 2), (249, -2), (261, 2), (272, -2)]) (.leaf [(34, 8), (124, -8)])) (.branch (.leaf [(30, 16)]) (.leaf [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(68, 4), (300, 4)]) (.leaf [(145, 8), (164, -8)])) (.branch (.leaf [(308, 4)]) (.leaf [(2, 2), (18, 2), (27, -2), (43, -2), (96, 2), (117, -2), (174, 6), (191, -6), (236, -2), (249, 2), (261, -2), (272, 2)]))) (.branch (.branch (.leaf [(286, 4), (321, 4)]) (.leaf [(46, -2), (133, 2)])) (.branch (.leaf [(120, 16)]) (.leaf [(261, 8), (272, -8)])))) (.branch (.branch (.branch (.leaf [(167, -8)]) (.leaf [(155, 16)])) (.branch (.leaf [(241, -8), (308, -8)]) (.leaf [(176, 12), (187, 12), (193, -4), (209, 4), (224, 4), (277, 4)]))) (.branch (.branch (.leaf [(91, -4), (170, 4), (307, -4)]) (.leaf [(22, 8), (113, -8)])) (.branch (.leaf [(169, -8)]) (.leaf [(184, 4), (243, -4), (285, -4)]))))) (.branch (.branch (.branch (.branch (.leaf [(305, -8), (309, -8)]) (.leaf [(282, 8), (291, -8)])) (.branch (.leaf [(225, 4), (233, 4)]) (.leaf [(230, 16)]))) (.branch (.branch (.leaf [(284, 16)]) (.leaf [(56, 8), (142, -8)])) (.branch (.leaf [(20, -4), (24, -4), (107, 12), (111, 12), (186, 4), (245, 4), (287, 4)]) (.leaf [(179, 16)])))) (.branch (.branch (.branch (.leaf [(1, 12), (17, 12), (95, -4), (173, 4), (235, 4), (250, 4)]) (.leaf [(203, -4)])) (.branch (.leaf [(280, 12), (288, 12), (289, -4), (293, -4), (297, 4), (301, 4), (304, 4), (309, 4)]) (.leaf [(238, -4), (251, 12), (263, 4), (267, 4), (274, 4), (279, 4), (287, -4)]))) (.branch (.branch (.leaf [(298, -4)]) (.leaf [(207, 8), (218, 8), (222, -8)])) (.branch (.leaf [(0, -1), (16, -2), (20, -2), (24, -2), (25, -1), (41, -2), (49, -3), (65, -6), (72, 1), (88, 2), (94, 3), (111, 6), (115, 3), (135, 9), (154, -3), (172, 1), (186, 2), (189, 1), (204, 2), (205, 3), (220, -1), (234, 1), (245, 2), (247, 1), (259, 3), (270, -1), (280, -1), (284, -2), (288, -2), (289, -1), (297, -3), (304, 1), (310, -1), (314, -2), (315, 3), (319, 1), (322, 1)]) (.leaf [(293, 16)])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(283, -4)]) (.leaf [(98, 4), (119, 4), (139, 12), (158, -4), (169, -4), (185, 4)])) (.branch (.leaf [(75, 16), (148, 16)]) (.leaf [(11, 8), (105, -8)]))) (.branch (.branch (.leaf [(67, 12), (71, 12), (146, -4), (150, -4), (217, 4), (268, 4), (302, 4)]) (.leaf [(194, 16)])) (.branch (.leaf [(44, -4), (131, 12), (198, 4), (202, 4), (257, 4), (258, 4), (292, -4)]) (.leaf [(176, 4), (187, 4), (193, 4), (209, 12), (224, -4), (277, -4)])))) (.branch (.branch (.branch (.leaf [(313, -4)]) (.leaf [(0, -1), (16, -2), (20, -2), (24, -2), (25, -1), (41, -2), (49, 1), (65, 2), (72, -3), (88, -6), (94, 3), (111, 6), (115, 3), (135, -3), (154, 9), (172, 1), (186, 2), (189, 1), (204, 2), (205, -1), (220, 3), (234, 1), (245, 2), (247, 1), (259, -1), (270, 3), (280, -1), (284, -2), (288, -2), (289, -1), (297, 1), (304, -3), (310, -1), (314, -2), (315, 3), (319, 1), (322, 1)])) (.branch (.leaf [(0, -3), (16, -6), (20, -6), (24, -6), (25, 1), (41, 2), (49, -1), (65, -2), (72, -1), (88, -2), (94, 9), (111, 18), (115, -3), (135, 3), (153, 6), (154, 3), (172, 3), (186, 6), (189, -1), (205, 1), (220, 1), (234, 3), (245, 6), (247, -1), (259, 1), (270, 1), (280, -3), (284, -6), (288, -6), (289, 1), (297, -1), (304, -1), (310, -3), (314, -6), (315, 9), (319, 3), (322, 3)]) (.leaf [(13, 16)]))) (.branch (.branch (.leaf [(212, 4)]) (.leaf [(316, 16)])) (.branch (.leaf [(227, 16)]) (.leaf [(64, 8)]))))) (.branch (.branch (.branch (.branch (.leaf [(254, -4), (258, -4)]) (.leaf [(54, 16)])) (.branch (.leaf [(50, 12), (66, 12), (136, -4), (206, 4), (260, 4), (273, 4)]) (.leaf [(12, 12), (23, 12), (37, -4), (61, 4), (84, 4), (275, 4)]))) (.branch (.branch (.leaf [(265, 16)]) (.leaf [(44, 4), (131, 4), (198, 12), (202, 12), (257, -4), (258, -4), (292, 4)])) (.branch (.leaf [(4, -4), (21, -4), (29, 12), (53, 4), (76, 4), (167, 4)]) (.leaf [(17, 8)])))) (.branch (.branch (.branch (.leaf [(299, 16), (303, 16)]) (.leaf [(218, 4)])) (.branch (.leaf [(98, 12), (119, -4), (139, 4), (158, 4), (169, 4), (185, 12)]) (.leaf [(187, 16)]))) (.branch (.branch (.leaf [(148, -4)]) (.leaf [(10, 4), (35, -4), (104, -4), (125, 4)])) (.branch (.leaf [(6, 8), (31, -8)]) (.leaf []))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf [(163, -4)]) (.leaf [(146, 16)])) (.branch (.leaf [(85, 16), (283, 16)]) (.leaf [(221, 16), (232, 16)]))) (.branch (.branch (.leaf [(286, 4)]) (.leaf [(0, -1), (16, -2), (20, -2), (24, -2), (25, 3), (41, 6), (49, 1), (65, 2), (72, 1), (88, 2), (94, -1), (111, -2), (115, 3), (135, 1), (153, 2), (154, 1), (172, -3), (186, -6), (189, 9), (205, 3), (220, 3), (234, 1), (245, 2), (247, -3), (259, -1), (270, -1), (280, -1), (284, -2), (288, -2), (289, 3), (297, 1), (304, 1), (310, -1), (314, -2), (315, -1), (319, -3), (322, 1)])) (.branch (.leaf [(52, 16)]) (.leaf [(262, 16)])))) (.branch (.branch (.branch (.leaf [(305, -8)]) (.leaf [(66, 16), (71, 16)])) (.branch (.leaf [(109, -4)]) (.leaf [(47, -4)]))) (.branch (.branch (.leaf [(92, -8), (93, -8), (308, -8), (309, -8)]) (.leaf [(69, 8), (152, -8)])) (.branch (.leaf [(301, 16)]) (.leaf [(51, 8), (74, -8), (130, -8)]))))) (.branch (.branch (.branch (.branch (.leaf [(287, -8)]) (.leaf [(157, 16)])) (.branch (.leaf [(225, 4)]) (.leaf [(89, 4), (168, 4), (227, 12), (231, 12), (278, -4), (279, -4), (305, 4)]))) (.branch (.branch (.leaf [(149, 16)]) (.leaf [(201, 16)])) (.branch (.leaf [(67, -4), (71, -4), (146, 12), (150, 12), (217, 4), (268, 4), (302, 4)]) (.leaf [(68, 4)])))) (.branch (.branch (.branch (.leaf [(44, 12), (131, -4), (198, 4), (202, 4), (257, 4), (258, 4), (292, 12)]) (.leaf [(8, 6), (22, 6), (33, -2), (57, 2), (80, 2), (102, -6), (113, -6), (123, 2), (143, -2), (162, -2), (229, 2), (276, -2)])) (.branch (.leaf [(4, 12), (21, 12), (29, -4), (53, 4), (76, 4), (167, 4)]) (.leaf [(23, 16)]))) (.branch (.branch (.leaf [(302, -8)]) (.leaf [(208, 16)])) (.branch (.leaf [(151, 16)]) (.leaf [])))))) (.branch (.branch (.branch (.branch (.branch (.leaf [(167, -8), (171, -8)]) (.leaf [(18, 8), (43, -8)])) (.branch (.leaf [(81, 16), (92, 16), (241, 16), (308, 16)]) (.leaf [(58, 8), (144, -8)]))) (.branch (.branch (.leaf [(311, 16), (318, 16)]) (.leaf [(8, -2), (22, -2), (33, 6), (57, 2), (80, 2), (102, 2), (113, 2), (123, -6), (143, -2), (162, -2), (229, 2), (276, -2)])) (.branch (.leaf [(118, 16)]) (.leaf [(15, 16)])))) (.branch (.branch (.branch (.leaf [(128, -4)]) (.leaf [(66, 16)])) (.branch (.leaf [(180, 12), (197, -4), (201, -4), (213, 4), (228, 4), (233, 4), (286, 12)]) (.leaf [(60, 16)]))) (.branch (.branch (.leaf [(214, 4), (219, 4)]) (.leaf [(293, 4), (301, 12), (310, 4), (314, 4), (315, 4), (319, 12), (322, -4), (323, -4)])) (.branch (.leaf [(290, 16)]) (.leaf [(185, 8)]))))) (.branch (.branch (.branch (.branch (.leaf [(275, -8), (279, -8)]) (.leaf [(89, -4), (168, 12), (227, 4), (231, 4), (278, 4), (279, 4), (305, -4)])) (.branch (.leaf [(90, 16), (306, 16)]) (.leaf [(59, 8), (70, 8), (82, -8), (254, -8)]))) (.branch (.branch (.leaf [(311, 16)]) (.leaf [(244, 16), (320, 16)])) (.branch (.leaf [(98, -4), (119, 12), (139, 4), (158, 4), (169, 4), (185, -4)]) (.leaf [(45, 16)])))) (.branch (.branch (.branch (.leaf [(242, 16), (246, 16), (313, 16), (323, 16)]) (.leaf [(320, -4)])) (.branch (.leaf [(40, 16), (48, 16)]) (.leaf [(38, 16)]))) (.branch (.branch (.leaf [(55, 4), (78, -4), (141, -4), (145, -4), (160, 4), (164, 4), (182, 4), (199, -4)]) (.leaf [(8, 2), (22, 2), (33, 2), (57, 6), (80, -2), (102, -2), (113, -2), (123, -2), (143, -6), (162, 2), (229, -2), (276, 2)])) (.branch (.leaf [(4, 4), (21, 4), (29, 4), (53, 12), (76, -4), (167, -4)]) (.leaf []))))))))

def dual199ABCertsTree : GenTree (Int × List (Nat × Int)) := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(185, 1)])) (.leaf (4, [(11, -2), (15, -1), (32, -1), (35, -2), (37, 1), (41, 2), (42, -2), (49, -2), (68, 1), (94, 4), (97, 1), (100, 2), (183, 2), (200, 1), (208, 1), (220, -1), (231, -1)]))) (.branch (.leaf (4, [(18, 1), (90, 1), (99, -1), (139, 1)])) (.leaf (8, [(5, 2), (9, -1), (12, 4), (16, -2), (17, -8), (21, -2), (26, 2), (27, 2), (31, 4), (33, -1), (36, 2), (38, 2), (40, 1), (53, -4), (56, -1), (65, -1), (67, 1), (69, 5), (73, -2), (76, 2), (80, -1), (83, 6), (85, 2), (89, -2), (98, 1), (101, -2), (103, 1), (120, 1), (125, -2), (138, 2), (154, -4), (156, -1), (158, -2), (162, -1), (174, 2), (188, -2), (196, 1), (201, -2), (207, -4), (209, 1), (216, 2), (221, -1), (223, 2), (225, -1), (227, -2), (229, 2), (234, 2)])))) (.branch (.branch (.leaf (4, [(207, 1)])) (.leaf (4, [(0, -1), (5, -1), (8, 2), (27, -1), (33, -1), (38, -1), (51, -2), (53, 1), (70, -2), (73, -1), (80, 1), (83, 1), (95, 1), (98, 1), (111, -2), (161, 1), (181, 1), (201, 1), (207, 1), (209, 1), (221, -1), (223, 1), (225, 1), (229, -1)]))) (.branch (.leaf (4, [(5, -3), (7, 1), (8, 2), (12, -1), (17, 2), (26, -1), (27, -1), (31, -2), (53, 1), (63, -1), (69, -1), (73, 1), (80, 1), (83, -1), (89, 1), (103, 1), (161, 1), (187, 1), (196, -1), (201, 1), (207, 1), (223, -1), (225, -1), (229, -1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(78, -2), (196, -1)])) (.leaf (4, [(36, 1)]))) (.branch (.leaf (4, [(26, 1), (109, 1), (178, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(6, 2), (54, 1), (202, -2)])) (.leaf (4, [(80, 1)]))) (.branch (.leaf (4, [(73, -1), (145, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (2, [(184, -1)])) (.leaf (4, [(5, 1), (8, -2), (16, -1), (17, -2), (23, -2), (27, -1), (29, -2), (31, 2), (38, 1), (51, 2), (53, -1), (69, 1), (83, 1), (87, 2), (207, -1), (229, 1)]))) (.branch (.leaf (4, [(18, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(219, 1)])) (.leaf (4, [(18, 1), (59, 1), (72, -2), (84, -1), (117, 1), (194, 1), (218, -1)]))) (.branch (.leaf (2, [(135, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(16, 1), (26, 1), (27, 2), (31, 2), (80, -1), (89, -1), (201, -1)])) (.leaf (4, [(36, -1), (170, -2), (173, 1)]))) (.branch (.leaf (4, [(0, -1), (2, -1), (8, -2), (12, -1), (16, -1), (17, -2), (23, -2), (27, -2), (29, -2), (31, 2), (33, -1), (38, 1), (43, -1), (51, 2), (63, -1), (69, 1), (70, -2), (80, 1), (83, 2), (87, 2), (95, 1), (98, 1), (106, -2), (111, -2), (123, 1), (126, 1), (164, 1), (187, 1), (193, 1), (201, 1), (209, 1), (215, 1), (221, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (1, [(6, -1), (202, 1)])) (.leaf (4, [(0, 1), (5, -1), (12, -1), (16, 1), (17, 2), (27, 1), (33, 1), (53, 1), (69, -1), (73, 1), (83, -1), (95, -1), (98, -1), (111, 2), (207, 1), (209, -1), (223, -1), (229, -1)]))) (.branch (.leaf (4, [(7, 2), (8, 4), (9, 1), (12, 1), (17, 4), (20, 1), (23, 2), (26, -2), (27, -2), (29, 2), (31, -6), (33, 1), (38, -1), (51, -2), (56, 1), (63, -2), (67, -1), (69, -3), (70, 2), (73, 1), (83, -4), (85, -1), (87, -2), (89, 2), (98, -1), (101, 1), (111, 2), (149, 1), (154, 2), (156, 1), (158, 2), (161, 2), (173, -1), (187, 2), (196, -1), (201, 1), (205, -1), (209, -1), (221, 2), (223, -1), (225, -1)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(187, 1)])) (.leaf (4, [(2, 1), (5, 1), (8, -2), (17, -2), (23, -2), (26, 1), (27, 1), (29, -2), (31, 4), (38, 1), (51, 2), (53, -1), (63, 1), (69, 1), (80, -1), (83, 1), (87, 2), (89, -1), (161, -2), (187, -1), (193, -1), (201, -1), (207, -1), (229, 1)]))) (.branch (.leaf (4, [(34, -1), (72, -2), (93, 1), (139, 1)])) (.leaf (4, [(1, -2), (11, -6), (13, 2), (15, -4), (22, 2), (32, 2), (35, -2), (37, 4), (41, 4), (42, -6), (49, -4), (58, 2), (68, 4), (71, 2), (86, -2), (94, 8), (97, 2), (100, 4), (102, -1), (121, 2), (124, 2), (128, -1), (148, 1), (157, -2), (165, -2), (166, 1), (177, -2), (183, 6), (186, 4), (189, 2), (200, 4), (206, -2), (220, -4), (222, -2), (231, -2), (232, -1)])))) (.branch (.branch (.leaf (2, [(12, 1), (207, -1)])) (.leaf (4, [(43, 1), (123, -1), (215, -1)]))) (.branch (.leaf (4, [(133, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(203, 1)])) (.leaf (4, [(5, 1), (12, 1), (26, -1), (27, 1), (31, -2), (36, 1), (53, -1), (69, -1), (80, -1), (83, -1), (89, 1), (173, -1), (174, 2), (207, -1), (221, 1), (229, 1)]))) (.branch (.leaf (8, [(13, 2), (15, -1), (32, 1), (37, 1), (49, -2), (57, -2), (64, 2), (68, 1), (97, -1), (124, 2), (183, 2), (186, 4), (200, 1), (208, -1), (213, -2), (220, -1), (231, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(202, -1)])) (.leaf (4, [(5, -2), (12, -2), (16, -1), (26, 1), (31, 2), (53, 2), (69, 2), (80, 1), (83, 2), (89, -1), (201, 1), (207, 2), (221, -2), (229, -2)]))) (.branch (.leaf (4, [(144, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (2, [(3, -1), (168, 1), (170, 1)])) (.leaf (4, [(5, -2), (8, 4), (16, 1), (17, 4), (23, 4), (26, -1), (29, 4), (31, -6), (38, -2), (51, -4), (53, 2), (69, -2), (80, 1), (83, -2), (87, -4), (89, 1), (161, 2), (201, 1), (207, 2), (229, -2)]))) (.branch (.leaf (4, [(18, -1), (99, 1), (139, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(6, -2), (61, 1), (153, 2), (197, -1), (202, 2)])) (.leaf (4, [(18, -1), (54, 1), (66, -1), (99, 1), (113, 2), (115, 1), (139, -1)]))) (.branch (.leaf (4, [(73, 1), (141, 1), (147, -1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(11, 1), (64, -1), (183, -1), (189, -1), (213, 1), (217, 1)])) (.leaf (4, [(73, 1), (143, -1), (176, 1)]))) (.branch (.leaf (4, [(0, 1), (7, -1), (12, 1), (16, 1), (17, 2), (27, 2), (33, 1), (38, -1), (43, 1), (51, -2), (63, 1), (69, -1), (70, 2), (80, -1), (83, -2), (95, -1), (98, -1), (103, -1), (111, 2), (114, -2), (123, -1), (187, -1), (201, -1), (209, -1), (215, -1), (221, 1), (225, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(17, -2), (26, 1), (31, 2), (38, 1), (69, 1), (83, 2), (89, -1), (201, -1)])) (.leaf (8, [(11, -2), (13, -1), (14, -1), (25, 2), (32, -1), (39, -1), (41, 2), (42, -1), (49, -2), (52, 1), (57, -1), (64, 1), (71, -2), (94, 4), (97, 1), (100, 2), (118, -1), (127, 2), (157, -2), (160, -1), (172, -2), (183, 2), (192, 2), (208, -1), (213, -1), (222, 2), (226, 1), (228, 1), (235, -1)]))) (.branch (.leaf (4, [(14, 1), (35, 1), (39, 1), (41, -1), (52, -1), (100, -1), (208, 1)])) (.leaf (1, [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(4, 1), (175, -1), (177, -1)])) (.leaf (4, [(72, 2), (117, -1), (159, 1)]))) (.branch (.leaf (4, [(0, -2), (16, -2), (17, -2), (27, -2), (33, -2), (40, 1), (69, 2), (70, -2), (73, -1), (80, 1), (83, 2), (92, 1), (95, 2), (98, 2), (101, -1), (111, -2), (173, 1), (201, 1), (209, 1), (221, -1), (223, 1)])) (.leaf (8, [(0, 2), (2, 2), (16, 2), (17, 4), (27, 4), (33, 2), (43, 2), (63, 2), (69, -2), (70, 4), (73, 2), (80, -2), (83, -4), (95, -2), (98, -2), (106, 2), (111, 4), (123, -2), (126, -2), (132, 2), (161, -2), (164, -2), (187, -2), (193, -2), (201, -2), (209, -2), (215, -2), (221, 2), (223, -2), (233, 1)])))) (.branch (.branch (.leaf (4, [(122, 1)])) (.leaf (4, [(52, 1), (208, -1)]))) (.branch (.leaf (2, [(13, -1), (94, 1), (186, -2), (208, 1), (222, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(152, -2), (196, -1)])) (.leaf (2, [(72, 1), (134, -1), (169, 1)]))) (.branch (.leaf (4, [(0, -2), (16, -1), (17, -2), (27, -2), (33, -1), (69, 1), (70, -2), (73, -1), (80, 1), (83, 2), (95, 2), (98, 2), (111, -2), (201, 1), (209, 1), (221, -1), (223, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(82, 1)])) (.leaf (8, [(13, 2), (15, -1), (32, 1), (37, 1), (49, -2), (68, 1), (71, 2), (97, -1), (186, 4), (200, 1), (208, -1), (220, -1), (222, -2), (231, -1)]))) (.branch (.leaf (4, [(13, -1), (32, -1), (71, -1), (86, 1), (94, 1), (186, -2), (208, 1), (222, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (2, [(49, 1), (186, -1), (192, -1)])) (.leaf (4, [(18, 1), (54, -1), (66, 1), (99, -1), (113, -2), (115, -1), (116, -2), (139, 1)]))) (.branch (.leaf (4, [(5, -1), (12, -1), (27, -1), (53, 1), (80, 1), (83, 1), (95, 1), (201, 1), (207, 1), (221, -1), (229, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(60, 1)])) (.leaf (4, [(5, -1), (16, 1), (17, 2), (27, 1), (38, -1), (51, -2), (53, 1), (69, -1), (83, -1), (207, 1), (229, -1)]))) (.branch (.leaf (2, [(72, -1), (140, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(12, -1), (207, 1), (215, 1)])) (.leaf (8, [(1, 2), (11, 6), (15, 3), (22, -2), (25, -4), (32, -1), (35, 2), (37, -3), (39, -2), (41, -2), (42, 6), (49, 2), (58, -2), (68, -3), (86, 2), (94, -8), (97, -3), (100, -2), (118, 2), (121, -2), (127, -2), (155, 2), (172, 2), (177, 2), (183, -6), (189, -2), (200, -3), (206, 2), (208, -1), (220, 3), (226, -2), (231, 1), (235, 1)]))) (.branch (.leaf (2, [(25, -1), (108, -1), (172, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(11, 1), (13, -1), (22, -1), (25, -2), (32, -1), (57, 1), (64, -1), (77, 1), (86, 1), (118, 1), (127, -1), (172, 2), (183, -1), (186, -2), (208, 1), (213, 1), (226, -1)])) (.leaf (2, [(32, 1)]))) (.branch (.leaf (4, [(0, 1), (7, -1), (8, -2), (9, -1), (12, -1), (17, -2), (20, -1), (26, 1), (27, 2), (31, 2), (38, 1), (51, 2), (56, -1), (63, 1), (67, 1), (69, 2), (83, 2), (85, 1), (89, -1), (95, -1), (101, -1), (154, -2), (161, -1), (173, 1), (187, -1), (196, 1), (201, -1), (205, 1), (221, -1)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (2, [(94, 1)])) (.leaf (4, [(18, -1), (59, -1), (84, 1), (88, 1), (218, 1)]))) (.branch (.leaf (4, [(0, 1), (5, -1), (12, -1), (16, 1), (26, 1), (27, 1), (31, 2), (53, 1), (83, 1), (89, -1), (95, -1), (207, 1), (221, -1), (229, -1)])) (.leaf (2, [(1, 1), (11, -1), (22, -1), (32, -2), (49, -2), (57, -1), (64, 1), (71, -1), (86, 1), (94, 3), (121, -1), (183, 1), (189, -1), (206, 1), (208, 1), (213, -1), (222, 1), (231, -1)])))) (.branch (.branch (.leaf (4, [(6, 2), (194, -1), (202, -2), (218, 1)])) (.leaf (4, [(11, 2), (15, 1), (32, 1), (37, -1), (39, -2), (42, 2), (49, 2), (68, -1), (94, -4), (97, -1), (183, -2), (200, -1), (208, -1), (220, 1), (231, 1)]))) (.branch (.leaf (4, [(0, -1), (5, -1), (7, 1), (12, -1), (20, 1), (27, -1), (33, -1), (43, -1), (53, 1), (63, -1), (70, -2), (80, 1), (83, 1), (95, 1), (98, 1), (103, 1), (111, -2), (114, 1), (123, 1), (125, -1), (138, 1), (158, -1), (174, 1), (187, 1), (201, 1), (205, -1), (207, 1), (209, 1), (215, 1), (221, -1), (225, -1), (229, -1), (234, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(18, -1), (30, 1), (59, -1), (84, 1), (218, 1)])) (.leaf (2, [(128, 1), (166, -1)]))) (.branch (.leaf (4, [(0, 2), (16, 1), (17, 4), (26, -1), (27, 2), (31, -2), (33, 2), (69, -2), (70, 4), (73, 2), (80, -1), (83, -4), (89, 1), (95, -2), (98, -2), (111, 4), (201, -1), (209, -2), (221, 2), (223, -2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(112, -1)])) (.leaf (8, [(15, -1), (32, 1), (37, 1), (49, 2), (68, 1), (94, -2), (97, -1), (200, 1), (208, -3), (220, -1), (231, 1)]))) (.branch (.leaf (4, [(73, -1), (147, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (2, [(49, -1), (186, 1)])) (.leaf (4, [(171, 1)]))) (.branch (.leaf (4, [(5, 2), (12, 2), (16, -1), (26, -1), (31, -2), (53, -2), (80, -1), (83, -2), (89, 1), (201, -1), (207, -2), (221, 2), (229, 2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(62, 1), (198, -1)])) (.leaf (4, [(5, 2), (8, -4), (16, -1), (17, -4), (26, 1), (31, 2), (38, 2), (51, 4), (53, -2), (69, 2), (80, -1), (83, 2), (89, -1), (161, -2), (201, -1), (207, -2), (229, 2)]))) (.branch (.leaf (4, [(142, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(11, -1), (64, 1), (94, 1), (183, 1), (213, -1)])) (.leaf (8, [(11, 2), (15, 1), (25, -4), (32, -3), (37, 1), (49, -2), (57, 2), (64, -2), (68, -1), (71, 2), (97, 1), (118, 2), (127, -2), (172, 4), (179, 2), (183, -2), (200, -1), (208, 3), (213, 2), (220, 1), (222, -2), (226, -2), (231, -1)]))) (.branch (.leaf (4, [(1, -1), (13, 2), (15, -1), (19, -2), (22, 1), (32, 1), (37, 1), (39, 1), (42, -1), (52, -1), (57, 1), (64, -1), (68, 1), (71, 2), (86, -1), (94, -2), (121, 2), (186, 4), (189, 1), (200, 1), (204, 2), (206, -1), (208, -2), (213, 1), (220, -1), (222, -3)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(15, 1), (32, -1), (37, -1), (49, 2), (68, -1), (94, -2), (97, 1), (200, -1), (208, -1), (220, 1), (231, 1)])) (.leaf (4, [(15, -1), (32, 1), (37, 1), (49, -2), (68, 1), (94, 2), (97, -1), (180, -1), (208, 3), (210, 1), (231, -1), (236, -1)]))) (.branch (.leaf (4, [(43, -1), (123, 1), (126, 1), (215, 1)])) (.leaf (1, []))))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(63, -1), (187, 1), (193, 1)])) (.leaf (4, [(1, 2), (11, 4), (13, -4), (15, 3), (22, -2), (32, -3), (35, 2), (37, -3), (41, -2), (42, 4), (49, 2), (58, -2), (68, -3), (71, -2), (86, 2), (94, -2), (97, -1), (100, -2), (102, 2), (121, -2), (124, -2), (148, -2), (165, 2), (177, 2), (183, -4), (186, -8), (189, -2), (200, -3), (206, 2), (208, 3), (220, 3), (222, 4), (231, 1)]))) (.branch (.leaf (4, [(91, 1)])) (.leaf (4, [(5, -2), (12, -2), (16, 1), (17, 4), (26, -1), (31, -2), (38, -2), (53, 2), (69, -2), (80, 1), (83, -2), (89, 1), (201, 1), (207, 2), (229, -2)])))) (.branch (.branch (.leaf (4, [(183, -1), (213, 1)])) (.leaf (4, [(11, -1), (13, -1), (32, -2), (39, 1), (71, -1), (86, 1), (94, 2), (105, 1), (146, -1), (183, 1), (186, -2), (208, 1), (222, 1)]))) (.branch (.leaf (4, [(32, -1), (41, 1), (42, -1), (57, 1), (64, -1), (97, 1), (100, 1), (118, 1), (157, -1), (213, 1), (222, -1), (226, -1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(94, 1), (186, -2)])) (.leaf (4, [(36, 1), (168, 2), (173, -1)]))) (.branch (.leaf (4, [(18, 1), (54, -1), (66, 1), (99, -1), (113, -2), (139, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(8, 2), (12, 1), (20, -1), (26, -1), (31, -2), (53, -2), (65, -1), (69, -1), (85, 1), (89, 1), (161, 1), (205, 1), (207, -1), (221, 1)])) (.leaf (4, [(18, -1), (84, 1)]))) (.branch (.leaf (2, [(72, 1), (136, -1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(50, -1), (196, 1), (199, 1)])) (.leaf (4, [(13, -2), (15, 1), (22, -1), (32, -2), (37, -1), (42, 1), (46, 1), (58, -1), (64, 1), (68, -1), (71, -1), (86, 1), (94, 2), (121, -1), (177, 1), (186, -4), (200, -1), (206, 1), (208, 3), (213, -1), (217, -1), (220, 1), (222, 2)]))) (.branch (.leaf (4, [(5, -1), (12, -1), (17, -2), (26, 1), (27, 1), (31, 2), (53, 1), (69, 1), (83, 1), (89, -1), (207, 1), (221, -1), (229, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(6, 1), (202, -1), (214, -1)])) (.leaf (4, [(5, 1), (7, -1), (12, -1), (20, -1), (26, 1), (27, 1), (29, -2), (31, 2), (53, 1), (63, 1), (69, 1), (73, -1), (83, 1), (89, -1), (103, -1), (104, -2), (125, 1), (182, -2), (187, -1), (196, 1), (205, 1), (207, 1), (221, -1), (225, 1), (229, -1)]))) (.branch (.leaf (4, [(5, 1), (7, -1), (12, 1), (20, -1), (26, -1), (27, 1), (31, -2), (53, -1), (63, 1), (69, -1), (80, -1), (83, -1), (89, 1), (103, -1), (125, 1), (187, -1), (205, 1), (207, -1), (221, 1), (225, 1), (229, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(181, -1), (211, 1)])) (.leaf (4, [(26, 1)]))) (.branch (.leaf (4, [(36, 1), (119, 1), (173, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(8, -2), (9, -1), (12, -1), (17, -2), (20, -1), (23, -2), (26, 2), (27, 2), (29, -2), (31, 4), (38, 1), (51, 2), (69, 2), (75, 1), (83, 2), (85, 1), (87, 2), (89, -2), (161, -1), (196, 1), (201, -1), (221, -1)])) (.leaf (4, [(32, -1), (41, 1)]))) (.branch (.leaf (4, [(11, -1), (13, 1), (25, 2), (32, 1), (57, -1), (64, 1), (86, -1), (105, -1), (118, -1), (127, 1), (146, 1), (151, 1), (172, -2), (179, -1), (183, 1), (186, 2), (208, -1), (213, -1), (226, 1)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(94, -1), (160, 1)])) (.leaf (4, [(1, -1), (11, -3), (13, 1), (15, -2), (22, 1), (32, 1), (35, -1), (37, 2), (39, 1), (41, 1), (42, -3), (49, -2), (58, 1), (68, 2), (71, 1), (86, -1), (94, 4), (97, 1), (100, 1), (118, -1), (121, 1), (155, -2), (177, -1), (183, 3), (186, 2), (189, 1), (200, 2), (206, -1), (220, -2), (222, -1), (226, 1), (231, -1)]))) (.branch (.leaf (4, [(7, -1), (20, -1), (21, 2), (36, -1), (63, 1), (73, -1), (76, -2), (103, -1), (125, 1), (138, -2), (173, 1), (187, -1), (205, 1), (225, 1)])) (.leaf (4, [(11, 2), (15, 1), (32, 1), (37, -1), (41, -2), (42, 2), (49, 2), (68, -1), (94, -4), (97, -1), (100, -2), (157, 2), (183, -2), (200, -1), (208, -1), (220, 1), (231, 1)])))) (.branch (.branch (.leaf (2, [(180, 1), (210, -1)])) (.leaf (8, [(1, -2), (11, -4), (15, -3), (22, 2), (32, 1), (37, 3), (39, 2), (41, 2), (42, -6), (49, -2), (57, 2), (58, 2), (64, -2), (68, 3), (71, 2), (86, -2), (94, 6), (97, 3), (100, 2), (121, 2), (157, -2), (177, -2), (183, 4), (189, 2), (200, 3), (206, -2), (208, 1), (213, 2), (220, -3), (222, -2), (231, -1)]))) (.branch (.leaf (4, [(137, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(18, 1), (24, 1), (59, 1), (84, -1), (88, -1), (218, -1)])) (.leaf (2, [(36, -1), (173, 1)]))) (.branch (.leaf (4, [(0, -1), (2, -1), (16, -1), (17, -2), (27, -2), (33, -1), (63, -1), (69, 1), (70, -2), (73, -1), (80, 1), (83, 2), (95, 1), (98, 1), (111, -2), (161, 1), (164, 1), (187, 1), (193, 1), (201, 1), (209, 1), (221, -1), (223, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(5, 2), (8, -2), (20, 1), (26, 1), (31, 2), (65, 1), (69, 1), (85, -1), (89, -1), (161, -1), (196, 1), (205, -1), (221, -1)])) (.leaf (2, [(15, -1), (128, -1)]))) (.branch (.leaf (8, [(13, 2), (15, 1), (32, -1), (37, 1), (49, -2), (68, -1), (71, 2), (86, -2), (97, 1), (146, 2), (186, 4), (200, -1), (208, 1), (220, 1), (222, -2), (231, -1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(50, 1), (196, -1)])) (.leaf (4, [(129, -1), (167, 1)]))) (.branch (.leaf (4, [(0, 1), (5, -1), (12, -1), (16, 2), (17, 2), (27, 1), (33, 1), (40, -1), (53, 1), (69, -2), (73, 1), (83, -1), (95, -1), (98, -1), (101, 1), (111, 2), (173, -1), (207, 1), (209, -1), (223, -1), (229, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(8, -2), (12, -1), (20, 1), (26, 1), (31, 2), (53, 2), (65, 1), (69, 1), (85, -1), (89, -1), (161, -1), (188, 2), (196, 1), (205, -1), (207, 1), (216, -2), (221, -1)])) (.leaf (4, [(0, -1), (7, 1), (8, 2), (9, 1), (12, 1), (17, 2), (20, 1), (26, -1), (27, -2), (31, -2), (38, -1), (51, -2), (56, 1), (63, -1), (67, -1), (69, -2), (83, -2), (85, -1), (89, 1), (95, 1), (101, 1), (154, 2), (156, 1), (161, 1), (173, -1), (187, 1), (196, -1), (201, 1), (205, -1), (221, 1)]))) (.branch (.leaf (2, [(72, -1), (130, -1), (140, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(48, 1), (120, 1), (176, -1), (191, -1)])) (.leaf (4, [(26, -1), (178, 1)]))) (.branch (.leaf (4, [(9, -1), (80, 1), (85, 1), (196, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(11, -1), (13, 1), (15, -2), (22, 1), (32, 2), (37, 2), (41, 1), (42, -2), (46, -1), (49, -2), (58, 1), (64, -1), (68, 2), (71, 1), (86, -1), (94, 2), (100, 1), (157, -1), (163, 1), (177, -1), (183, 1), (186, 2), (200, 2), (206, -1), (213, 1), (217, 1), (220, -2), (222, -1), (231, -1)])) (.leaf (2, [(208, 1)]))) (.branch (.leaf (4, [(0, 2), (16, 2), (17, 4), (26, -1), (27, 2), (31, -2), (33, 2), (38, -1), (40, -1), (69, -3), (70, 2), (73, 1), (80, -1), (83, -4), (89, 1), (95, -2), (98, -2), (101, 1), (111, 2), (154, 2), (173, -1), (201, -1), (209, -2), (221, 2), (223, -1)])) (.leaf (1, [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(63, 1), (187, -1)])) (.leaf (4, [(7, 1), (20, 1), (36, 1), (63, -1), (73, 1), (103, 1), (104, 2), (125, -1), (150, -2), (173, -1), (174, 2), (187, 1), (205, -1), (225, -1)]))) (.branch (.leaf (4, [(1, -1), (11, -2), (13, 2), (15, -3), (22, 2), (32, 3), (35, -1), (37, 3), (39, 1), (41, 1), (42, -4), (46, -1), (49, -2), (52, -1), (57, 1), (58, 1), (64, -2), (68, 3), (71, 2), (74, -2), (86, -2), (94, 2), (97, 1), (100, 2), (121, 2), (157, -1), (163, 1), (177, -1), (183, 2), (186, 4), (189, 1), (200, 3), (204, 2), (206, -2), (208, -1), (213, 2), (217, 1), (220, -3), (222, -3), (231, -1)])) (.leaf (4, [(5, 2), (12, 2), (16, -1), (17, -4), (26, 1), (31, 2), (53, -2), (69, 2), (73, -2), (80, -1), (83, 2), (89, -1), (201, -1), (207, -2), (223, 2), (229, 2)])))) (.branch (.branch (.leaf (4, [(12, -1), (120, -1), (162, 1), (207, 1)])) (.leaf (4, [(0, -1), (5, 1), (12, 1), (16, -1), (17, -2), (27, -1), (38, 1), (53, -1), (56, 1), (69, 1), (83, 1), (95, 1), (207, -1), (229, 1)]))) (.branch (.leaf (4, [(131, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (2, [(196, 1)])) (.leaf (4, [(11, -1), (57, -1), (64, 1), (71, -1), (94, 1), (118, -1), (127, 1), (183, 1), (213, -1), (222, 1), (226, 1)]))) (.branch (.leaf (4, [(18, -1), (99, 1), (113, 2), (139, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(6, 1), (81, -1), (202, -1)])) (.leaf (4, [(5, 1), (12, 1), (26, -1), (27, -1), (53, -1), (69, -1), (83, -1), (89, 1), (207, -1), (221, 1), (229, 1)]))) (.branch (.leaf (4, [(0, -1), (5, -1), (12, -1), (27, -1), (33, -1), (43, -1), (53, 1), (70, -2), (73, -1), (80, 1), (83, 1), (95, 1), (98, 1), (111, -2), (114, 1), (123, 1), (138, -1), (158, -1), (174, 1), (201, 1), (207, 1), (209, 1), (215, 1), (221, -1), (229, -1), (234, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(10, 1), (171, -1)])) (.leaf (4, [(0, 1), (5, -2), (7, -1), (8, -2), (9, -1), (12, -1), (17, -2), (20, -1), (23, -2), (26, 1), (27, 2), (29, -2), (31, 4), (38, 1), (51, 2), (56, -1), (63, 1), (67, 1), (69, 2), (83, 2), (85, 1), (87, 2), (89, -1), (95, -1), (101, -1), (154, -2), (156, -1), (158, -2), (161, -1), (173, 1), (187, -1), (201, -1), (205, 1), (221, -1)]))) (.branch (.leaf (4, [(15, -1), (32, 1), (68, 1), (200, 1), (208, -1), (220, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(44, -1), (135, 1)])) (.leaf (8, [(13, 2), (15, -1), (32, 1), (37, 1), (49, -2), (68, 1), (97, -1), (186, 4), (200, 1), (208, -1), (220, -1), (231, -1)]))) (.branch (.leaf (1, [(72, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(45, 1), (144, -1)])) (.leaf (4, [(11, 1), (25, -2), (57, 1), (64, -1), (71, 1), (94, -1), (118, 1), (127, -1), (172, 2), (175, 1), (183, -1), (213, 1), (222, -1), (226, -1)]))) (.branch (.leaf (4, [(32, -1), (39, 1), (42, -1), (57, 1), (64, -1), (97, 1), (213, 1), (222, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(8, 2), (9, 1), (12, 1), (16, 1), (17, 2), (26, -1), (31, -2), (38, -1), (51, -2), (69, -2), (80, -1), (83, -2), (89, 1), (161, 1), (196, -1), (221, 1)])) (.leaf (8, [(5, 2), (12, 2), (16, -1), (17, -2), (38, 1), (53, -2), (69, 1), (80, -1), (95, -1), (184, 2), (201, -1), (207, -2), (221, 1), (229, 2), (237, 1)]))) (.branch (.leaf (4, [(32, 1), (35, 1), (41, -1)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(195, 1)])) (.leaf (4, [(5, 1), (12, 1), (23, -2), (26, -1), (27, -1), (53, -1), (69, -1), (83, -1), (89, 1), (207, -1), (221, 1), (229, 1)]))) (.branch (.leaf (4, [(1, 1), (11, 1), (13, -1), (15, 2), (22, -1), (32, -2), (37, -2), (39, -1), (42, 1), (49, 2), (55, -2), (57, -1), (64, 1), (68, -2), (71, -1), (86, 1), (94, -2), (121, -1), (183, -1), (186, -2), (189, -1), (200, -2), (206, 1), (220, 2), (222, 1), (231, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(5, -2), (8, 2), (12, 1), (20, -1), (26, -1), (31, -2), (65, -1), (69, -1), (85, 1), (89, 1), (161, 1), (182, 2), (196, -1), (205, 1), (207, -1), (212, -2), (221, 1)])) (.leaf (4, [(11, 2), (13, 2), (15, 1), (32, 1), (37, -1), (39, -2), (42, 2), (49, 2), (68, -1), (94, -6), (97, -1), (180, -2), (183, -2), (186, 4), (200, -1), (208, -3), (220, 1), (222, -2), (224, -2), (231, 1)]))) (.branch (.leaf (4, [(72, -2), (139, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(18, 1), (28, 2), (84, -1)])) (.leaf (4, [(11, 1), (25, -2), (57, 1), (64, -1), (71, 1), (94, -1), (118, 1), (127, -1), (172, 2), (177, 1), (183, -1), (213, 1), (222, -1), (226, -1)]))) (.branch (.leaf (4, [(32, 1), (35, 1), (41, -1), (42, 1), (57, -1), (64, 1), (97, -1), (100, -1), (213, -1), (222, 1), (226, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(6, 1), (110, 1), (153, -1), (202, -1)])) (.leaf (4, [(38, 1)]))) (.branch (.leaf (2, [(73, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(79, 1)])) (.leaf (8, [(1, 2), (11, 6), (15, 3), (22, -2), (32, -1), (35, 2), (37, -3), (39, -2), (41, -2), (42, 6), (49, 2), (58, -2), (68, -3), (86, 2), (94, -8), (97, -3), (100, -2), (118, 2), (121, -2), (127, -2), (155, 2), (172, 2), (177, 2), (183, -6), (189, -2), (200, -3), (206, 2), (208, -1), (220, 3), (226, -2), (231, 1), (235, 1)]))) (.branch (.leaf (4, [(18, -1), (54, 1), (66, -1), (99, 1), (107, 1), (113, 2), (115, 1), (116, 2), (139, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(47, -1), (110, -1), (169, 1), (190, 1)])) (.leaf (4, [(16, 1), (129, 1)]))) (.branch (.leaf (2, [(132, -1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(12, -1), (96, 1), (207, 1)])) (.leaf (2, [(11, -1), (25, 2), (57, -1), (64, 1), (71, -1), (94, 1), (118, -1), (127, 1), (172, -2), (183, 1), (213, -1), (222, 1), (226, 1)]))) (.branch (.leaf (4, [(38, 1), (73, 1), (123, 1), (223, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(15, 3), (32, -3), (37, -1), (49, 2), (68, -3), (94, -2), (97, 1), (200, -1), (208, -1), (220, 1), (231, 1)])) (.leaf (8, [(18, 2), (54, -1), (66, 1), (72, -2), (99, -2), (113, -4), (115, -1), (122, -1), (139, 2), (214, 2), (230, 1)]))) (.branch (.leaf (8, [(1, 2), (11, 6), (15, 3), (22, -2), (32, -1), (35, 2), (37, -3), (41, -4), (42, 6), (49, 2), (57, -2), (58, -2), (64, 2), (68, -3), (71, -2), (86, 2), (94, -8), (97, -3), (100, -4), (121, -2), (157, 2), (165, 2), (177, 2), (183, -4), (189, -2), (200, -3), (206, 2), (208, -1), (213, -2), (220, 3), (222, 2), (231, 1)])) (.leaf (1, [])))))))))
def dual199BACertsTree : GenTree (Int × List (Nat × Int)) := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(185, 1)])) (.leaf (2, [(11, -1), (13, -1), (32, -1), (35, -1), (41, 1), (42, -1), (49, -2), (57, 1), (64, -1), (97, 1), (100, 1), (124, -1), (160, 2), (192, 2), (208, 1), (213, 1)]))) (.branch (.leaf (4, [(24, 1), (54, 1), (59, 1), (66, -1), (84, -1), (88, -1), (99, 1), (107, 1), (113, 2), (115, 1), (116, 2), (139, -1), (218, -1)])) (.leaf (4, [(0, -2), (2, -1), (5, 4), (7, 1), (12, -1), (16, -2), (27, -4), (29, -2), (31, -2), (38, 1), (43, -1), (50, 2), (51, 2), (56, 1), (63, -2), (67, -1), (73, 1), (80, 2), (89, 1), (95, 2), (98, 1), (101, 1), (103, -2), (104, -2), (106, -4), (109, 1), (123, 1), (125, 1), (126, 1), (141, 1), (147, -1), (149, 2), (154, 2), (156, 2), (158, 4), (161, 1), (164, 1), (173, -1), (178, -1), (182, -2), (187, 2), (193, 1), (199, -2), (201, 2), (215, 1), (223, -1)])))) (.branch (.branch (.leaf (4, [(199, 1)])) (.leaf (8, [(5, -4), (7, 2), (8, 4), (9, -2), (16, 1), (17, 2), (20, -2), (27, 2), (31, -4), (33, 2), (38, -1), (40, -2), (50, -2), (69, -1), (75, 2), (80, 1), (83, -2), (85, 2), (95, -1), (101, 2), (103, 2), (106, 4), (154, 4), (161, 2), (173, -2), (184, 2), (193, -2), (196, 2), (199, 2), (201, -1), (209, -2), (221, 1), (225, -2), (237, 1)]))) (.branch (.leaf (4, [(0, 1), (2, 1), (5, -3), (7, -1), (16, 1), (20, -1), (27, 3), (31, 2), (50, -1), (53, 1), (56, -1), (63, 1), (67, 1), (69, 1), (80, -1), (83, 1), (89, -1), (95, -1), (101, -1), (103, 1), (106, 2), (109, -1), (149, -1), (154, -2), (156, -1), (158, -2), (161, -1), (164, -1), (173, 1), (178, 1), (187, -1), (199, 1), (201, -1), (205, 1), (215, -1), (221, -1), (229, -1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(120, -1), (162, 1), (215, -1)])) (.leaf (4, [(141, 1)]))) (.branch (.leaf (4, [(26, 1), (109, 1), (178, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(6, -2), (61, 1), (153, 2), (197, -1)])) (.leaf (4, [(126, 1)]))) (.branch (.leaf (4, [(119, -1), (168, 2)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(181, -1), (211, 1)])) (.leaf (4, [(0, -1), (5, 2), (7, 1), (9, 1), (16, -1), (20, 1), (27, -2), (33, -1), (40, 1), (50, 1), (56, 1), (63, -1), (67, -1), (85, -1), (92, 1), (95, 1), (98, 1), (103, -1), (106, -2), (149, 1), (154, 2), (156, 1), (158, 2), (187, 1), (196, -1), (199, -1), (201, 1), (205, -1)]))) (.branch (.leaf (4, [(107, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(203, 1)])) (.leaf (8, [(54, 1), (66, -1), (72, 2), (107, 2), (115, 1), (116, 4), (117, -2), (122, -1), (159, 2), (214, 2), (230, 1)]))) (.branch (.leaf (4, [(137, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(0, -1), (2, -1), (16, -1), (27, -2), (31, -2), (63, -1), (80, 1), (89, 1), (95, 1), (98, 1), (109, 1), (161, 1), (164, 1), (178, -1), (187, 1), (193, 1), (201, 1)])) (.leaf (4, [(141, -1), (143, -1), (147, 1), (176, 1)]))) (.branch (.leaf (4, [(0, -2), (7, 2), (8, 2), (16, -2), (27, -2), (31, -2), (33, -1), (40, 1), (56, 1), (63, -2), (67, -1), (69, 1), (75, 1), (80, 1), (92, 1), (95, 2), (98, 1), (149, 1), (154, 2), (156, 1), (158, 2), (161, 1), (187, 2), (201, 1), (205, -1), (225, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(61, -1), (153, -2), (197, 1)])) (.leaf (4, [(0, 1), (2, 1), (5, -2), (7, -1), (16, 1), (20, -1), (27, 2), (31, 2), (50, -1), (56, -1), (63, 1), (67, 1), (80, -1), (95, -1), (101, -1), (103, 1), (106, 2), (149, -1), (154, -2), (156, -1), (158, -2), (161, -1), (164, -1), (173, 1), (187, -1), (199, 1), (201, -1), (205, 1)]))) (.branch (.leaf (4, [(0, 3), (2, 1), (7, -4), (8, -4), (9, -1), (16, 3), (17, -2), (20, -1), (27, 6), (31, 6), (33, 1), (40, -1), (43, 1), (56, -2), (63, 3), (67, 2), (69, 1), (73, -1), (75, -1), (80, -2), (83, 2), (85, 1), (89, -2), (92, -1), (95, -3), (98, -1), (101, -1), (106, 2), (109, -2), (123, -1), (126, -1), (149, -2), (154, -4), (156, -2), (158, -4), (161, -3), (164, -1), (173, 1), (178, 2), (187, -3), (193, 1), (196, 1), (201, -3), (205, 2), (215, -1), (221, -1), (223, 1), (225, 2)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(193, 1)])) (.leaf (4, [(0, -1), (2, -1), (5, 2), (7, 1), (9, 1), (16, -2), (20, 1), (27, -4), (31, -2), (33, -1), (40, 1), (50, 1), (56, 1), (63, -1), (67, -1), (80, 1), (85, -1), (89, 1), (92, 1), (95, 2), (103, -1), (106, -2), (109, 1), (149, 1), (154, 2), (156, 1), (158, 2), (161, 1), (164, 1), (178, -1), (187, 1), (196, -1), (199, -1), (201, 2), (205, -1)]))) (.branch (.leaf (4, [(117, -1), (130, -2), (140, 2), (159, 1)])) (.leaf (2, [(1, 1), (11, -2), (13, -3), (22, -1), (32, -3), (35, -1), (37, -1), (41, 1), (42, -1), (49, -6), (57, 2), (58, -1), (64, -1), (68, -1), (71, -1), (86, 1), (97, 2), (100, 2), (118, 1), (121, -1), (124, -3), (128, -1), (160, 4), (165, 1), (177, 1), (192, 6), (200, -1), (206, 1), (208, 3), (213, 1), (217, -1), (220, 1), (222, 1)])))) (.branch (.branch (.leaf (2, [(50, 1), (199, -1)])) (.leaf (4, [(9, 1), (85, -1), (196, -1)]))) (.branch (.leaf (4, [(133, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(219, 1)])) (.leaf (4, [(0, 1), (5, 2), (7, -1), (8, -2), (16, 1), (27, 2), (31, 2), (50, 1), (63, 1), (80, -1), (89, -1), (95, -1), (98, -1), (103, -1), (109, -1), (114, 1), (126, -1), (138, -1), (141, 1), (147, -1), (158, -1), (161, -1), (174, 1), (178, 1), (187, -1), (199, -1), (201, -1), (225, 1), (234, 1)]))) (.branch (.leaf (8, [(11, -2), (13, -2), (15, 1), (32, -1), (37, -1), (49, -2), (57, 2), (68, -1), (97, 1), (124, -2), (189, 2), (192, 4), (200, -1), (208, 1), (217, -2), (220, 1), (231, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(54, 1), (61, 1), (153, 2), (197, -1)])) (.leaf (4, [(0, -1), (2, 1), (5, -4), (7, 2), (8, 4), (16, -1), (27, -2), (31, -2), (50, -2), (63, -1), (80, 1), (89, 1), (95, 1), (98, 1), (103, 2), (109, 1), (161, 1), (164, -1), (178, -1), (187, 1), (193, -1), (199, 2), (201, 1), (225, -2)]))) (.branch (.leaf (4, [(171, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(48, 1), (120, 1), (176, -1), (191, -1)])) (.leaf (4, [(0, 3), (2, 1), (5, -4), (7, -2), (9, -2), (16, 3), (20, -2), (27, 6), (31, 2), (33, 2), (40, -2), (50, -2), (56, -2), (63, 3), (67, 2), (80, -1), (85, 2), (89, -1), (92, -2), (95, -3), (98, -1), (103, 2), (106, 4), (109, -1), (149, -2), (154, -4), (156, -2), (158, -4), (161, -1), (164, -1), (178, 1), (187, -3), (193, -1), (196, 2), (199, 2), (201, -3), (205, 2)]))) (.branch (.leaf (4, [(54, -1), (59, -1), (66, 1), (84, 1), (88, 1), (99, -1), (107, -1), (113, -2), (115, -1), (116, -2), (139, 1), (218, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(6, 2), (61, -1), (153, -2), (197, 1), (202, -2)])) (.leaf (4, [(54, -1), (66, 1), (84, 1), (99, -1), (107, -1), (113, -2), (115, -1), (116, -2), (139, 1)]))) (.branch (.leaf (4, [(36, 1), (119, 1), (173, -1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (2, [(49, 1), (186, -1), (192, -1)])) (.leaf (4, [(119, 1), (170, -2)]))) (.branch (.leaf (4, [(0, 2), (7, -2), (8, -2), (16, 2), (27, 2), (31, 2), (33, 1), (40, -1), (56, -1), (63, 2), (67, 1), (69, -1), (75, -1), (80, -1), (95, -2), (98, -1), (149, -1), (156, -1), (158, -2), (161, -1), (187, -2), (201, -2), (205, 1), (209, -1), (221, 1), (225, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(0, -1), (2, -1), (16, -1), (27, -2), (31, -2), (63, -1), (80, 1), (89, 1), (95, 1), (98, 1), (103, -1), (106, -2), (109, 1), (114, -2), (126, 1), (149, 1), (156, 1), (158, 2), (161, 1), (164, 1), (178, -1), (187, 1), (193, 1), (201, 1)])) (.leaf (4, [(11, -1), (13, -1), (32, -1), (49, -2), (71, -1), (86, 1), (100, 1), (105, 1), (146, -1), (160, 2), (183, 1), (192, 2), (208, 1), (222, 1), (226, -1)]))) (.branch (.leaf (4, [(35, 1), (39, 1), (41, -1), (100, -1), (226, 1)])) (.leaf (1, [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(4, 1), (175, -1), (177, -1)])) (.leaf (4, [(72, -2), (117, 1), (159, -1)]))) (.branch (.leaf (4, [(0, -1), (2, -1), (7, 2), (12, -1), (16, -1), (23, -2), (27, -2), (29, -2), (38, 1), (43, -1), (51, 2), (56, 1), (63, -1), (67, -1), (73, 1), (75, 1), (80, 1), (87, 2), (95, 1), (101, 1), (106, -2), (123, 1), (126, 1), (149, 1), (154, 2), (156, 1), (158, 2), (161, 1), (164, 1), (173, -1), (187, 1), (193, -1), (201, 1), (205, -1), (215, 1), (223, -1), (225, -1)])) (.leaf (4, [(0, 2), (7, -2), (8, -2), (9, 1), (16, 2), (27, 2), (31, 2), (56, -1), (63, 2), (67, 1), (75, -1), (80, -2), (85, -1), (95, -2), (98, -1), (101, -1), (129, 1), (149, -1), (154, -2), (156, -1), (158, -2), (161, -1), (173, 1), (187, -2), (196, -1), (201, -1), (205, 1), (225, 1)])))) (.branch (.branch (.leaf (4, [(79, 1)])) (.leaf (4, [(14, 1), (226, -1)]))) (.branch (.leaf (2, [(57, -1), (160, 1), (189, -1), (217, 1), (222, 1), (226, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(96, 1), (215, -1)])) (.leaf (4, [(117, 1), (136, -2), (159, -1)]))) (.branch (.leaf (4, [(0, -1), (2, -1), (7, 2), (8, 2), (16, -1), (27, -2), (31, -2), (56, 1), (63, -1), (67, -1), (75, 1), (80, 1), (95, 1), (101, 1), (149, 1), (154, 2), (156, 1), (158, 2), (161, 2), (164, 1), (173, -1), (187, 1), (193, -1), (201, 1), (205, -1), (225, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(112, -1)])) (.leaf (4, [(11, -1), (57, 1), (71, 1), (124, -1), (189, 1), (217, -1), (222, -1)]))) (.branch (.leaf (4, [(57, -1), (71, -1), (118, -1), (127, 1), (160, 1), (189, -1), (217, 1), (222, 1), (226, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(11, 1), (64, -1), (183, -1), (189, -1), (213, 1), (217, 1)])) (.leaf (4, [(54, 1), (66, -1), (99, 1), (107, 1), (113, 2), (115, 1), (116, 2), (139, -1)]))) (.branch (.leaf (4, [(2, 1), (5, -2), (7, 1), (8, 2), (50, -1), (103, 1), (106, 2), (193, -1), (199, 1), (225, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(60, 1)])) (.leaf (4, [(0, 1), (5, -2), (7, -1), (9, -1), (16, 1), (20, -1), (27, 2), (33, 1), (40, -1), (50, -1), (63, 1), (67, 1), (85, 1), (95, -1), (98, -1), (103, 1), (106, 2), (149, -1), (156, -1), (158, -2), (187, -1), (196, 1), (199, 1), (201, -1), (205, 1), (209, -1)]))) (.branch (.leaf (4, [(117, -1), (139, 1), (159, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(50, -1), (196, 1), (199, 1)])) (.leaf (4, [(1, -1), (11, 1), (13, 3), (14, -1), (22, 1), (32, 3), (35, 1), (37, 1), (39, -1), (41, -1), (42, 1), (49, 6), (52, 1), (57, -1), (58, 1), (64, 1), (71, 2), (86, -2), (97, -1), (100, -1), (105, -1), (118, -1), (121, 1), (124, 2), (146, 1), (151, 1), (160, -4), (165, -1), (177, -1), (189, 1), (192, -6), (206, -1), (208, -3), (213, -1), (222, -2)]))) (.branch (.leaf (4, [(22, -1), (77, 1), (105, -1), (146, 1), (151, 1), (179, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(13, 1), (32, 1), (49, 2), (57, -1), (86, -1), (105, -1), (108, -2), (118, -1), (127, 1), (146, 1), (151, 1), (179, -1), (189, -1), (192, -2), (208, -1), (217, 1), (226, 1)])) (.leaf (2, [(118, 1)]))) (.branch (.leaf (4, [(0, -2), (7, 2), (8, 2), (9, 1), (16, -2), (20, 1), (27, -4), (31, -2), (33, -1), (38, 1), (40, 1), (43, -1), (56, 1), (63, -2), (67, -1), (73, 1), (80, 1), (85, -1), (89, 1), (95, 2), (98, 1), (106, -2), (109, 1), (123, 1), (126, 1), (149, 1), (156, 1), (158, 2), (161, 1), (178, -1), (187, 2), (196, -1), (201, 2), (205, -1), (209, 1), (215, 1), (223, -1), (225, -1)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (2, [(160, 1)])) (.leaf (4, [(54, -1), (66, 1), (107, -1), (113, -2), (115, -1), (116, -2)]))) (.branch (.leaf (4, [(0, -1), (2, 1), (5, -2), (7, 1), (8, 2), (16, -1), (27, -2), (31, -2), (50, -1), (63, -1), (80, 1), (89, 1), (95, 1), (98, 1), (103, 1), (106, 2), (109, 1), (161, 1), (164, -1), (178, -1), (187, 1), (199, 1), (201, 1), (225, -1)])) (.leaf (2, [(11, -2), (13, -1), (32, -1), (42, -1), (49, -2), (57, 1), (58, 1), (64, -1), (97, 1), (118, -1), (124, -1), (160, 3), (165, -1), (177, -1), (192, 2), (208, 1), (213, 1)])))) (.branch (.branch (.leaf (4, [(61, 1), (153, 2), (197, -1), (214, -2)])) (.leaf (2, [(11, 1), (13, 1), (14, -1), (32, 1), (39, -1), (42, 1), (49, 2), (52, 1), (57, -1), (64, 1), (97, -1), (124, 1), (160, -2), (192, -2), (208, -1), (213, -1)]))) (.branch (.leaf (4, [(5, -2), (8, 2), (9, -1), (20, -2), (27, 2), (31, -2), (50, -1), (75, 1), (85, 1), (106, 2), (125, 1), (161, 1), (196, 1), (199, 1), (205, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(54, -1), (66, 1), (107, -1), (115, -1), (116, -2)])) (.leaf (2, [(128, 1), (166, -1)]))) (.branch (.leaf (4, [(0, 3), (2, 1), (7, -4), (8, -4), (16, 3), (27, 6), (31, 6), (56, -2), (63, 3), (67, 2), (75, -2), (80, -3), (89, -1), (95, -3), (98, -1), (101, -2), (109, -1), (149, -2), (154, -4), (156, -2), (158, -4), (161, -3), (164, -1), (173, 2), (178, 1), (187, -3), (193, 1), (201, -3), (205, 2), (225, 2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(82, 1)])) (.leaf (4, [(11, 1), (160, -1), (165, 1), (226, -1)]))) (.branch (.leaf (4, [(119, -1), (173, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(11, -1), (64, 1), (189, 1), (217, -1)])) (.leaf (4, [(144, 1)]))) (.branch (.leaf (4, [(0, 1), (2, -1), (5, 4), (7, -2), (8, -4), (16, 1), (27, 2), (31, 2), (50, 2), (63, 1), (80, -1), (89, -1), (95, -1), (98, -1), (103, -2), (106, -4), (109, -1), (161, -1), (164, 1), (178, 1), (187, -1), (193, 1), (199, -2), (201, -1), (225, 2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(44, -1), (135, 1)])) (.leaf (4, [(0, -3), (2, -1), (5, 4), (7, 2), (9, 2), (16, -3), (20, 2), (27, -6), (31, -2), (33, -2), (40, 2), (50, 2), (56, 2), (63, -3), (67, -2), (80, 1), (85, -2), (89, 1), (95, 3), (98, 1), (103, -2), (106, -4), (109, 1), (149, 2), (156, 2), (158, 4), (161, 1), (164, 1), (178, -1), (187, 3), (193, 1), (196, -2), (199, -2), (201, 3), (205, -2), (209, 2)]))) (.branch (.leaf (4, [(142, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(49, -2), (160, 1), (192, 2)])) (.leaf (8, [(11, -2), (13, 2), (32, 2), (49, 4), (71, 2), (86, -2), (105, -2), (118, -2), (146, 2), (151, 2), (155, 2), (165, -2), (172, -2), (179, -2), (192, -4), (208, -2), (222, -2), (226, 2), (235, 1)]))) (.branch (.leaf (4, [(1, 1), (46, -1), (57, 1), (121, -1), (124, -1), (160, -2), (163, 1), (165, 1), (189, 1), (217, -1), (222, -1), (226, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(11, 1), (124, 1), (160, -1), (226, -1)])) (.leaf (2, [(11, -1), (124, -1), (160, 1), (180, -1), (224, -1), (226, 2)]))) (.branch (.leaf (4, [(9, -1), (80, 1), (85, 1), (196, 1)])) (.leaf (1, []))))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(63, -1), (187, 1), (193, 1)])) (.leaf (2, [(1, -1), (11, 1), (13, 2), (22, 1), (32, 2), (35, 1), (37, 1), (41, -1), (49, 4), (57, -2), (58, 1), (71, 1), (86, -1), (97, -1), (100, -1), (118, -1), (121, 1), (124, 2), (160, -1), (165, -1), (177, -1), (189, -1), (192, -4), (200, 1), (206, -1), (208, -2), (217, 2), (220, -1), (226, 1)]))) (.branch (.leaf (4, [(131, 1)])) (.leaf (4, [(0, 1), (2, 1), (5, -4), (16, 1), (27, 2), (31, 2), (50, -2), (63, 1), (80, -1), (89, -1), (95, -1), (98, -1), (103, 2), (106, 4), (109, -1), (149, -2), (156, -2), (158, -4), (161, -1), (164, -1), (178, 1), (187, -1), (193, -1), (199, 2), (201, -1)])))) (.branch (.branch (.leaf (2, [(192, -1)])) (.leaf (8, [(13, -1), (14, 1), (25, 2), (32, -1), (39, 1), (42, -1), (49, -2), (52, -1), (57, -1), (64, -1), (71, -2), (97, 1), (118, -3), (127, 2), (160, 3), (172, -2), (189, -2), (192, 2), (208, 1), (213, 1), (217, 2), (222, 2), (226, 1), (228, 1), (235, -1)]))) (.branch (.leaf (4, [(42, -1), (57, 1), (64, -1), (97, 1), (100, 1), (213, 1), (222, -1), (226, -1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(160, 1), (189, -1), (217, 1)])) (.leaf (4, [(141, 1), (145, 1), (147, -1)]))) (.branch (.leaf (4, [(28, 2), (54, 1), (66, -1), (84, -1), (99, 1), (107, 1), (113, 2), (115, 1), (116, 2), (139, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(5, 2), (8, -2), (20, 1), (31, 2), (50, 1), (65, 1), (69, 1), (85, -1), (89, -1), (109, -1), (161, -1), (178, 1), (199, -1), (205, -1), (221, -1)])) (.leaf (4, [(107, -1), (116, -2)]))) (.branch (.leaf (4, [(117, 1), (134, -2), (159, -1), (169, 2)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(12, -1), (207, 1), (215, 1)])) (.leaf (4, [(42, -1), (55, -2), (57, -2), (58, 1), (118, -1), (124, 1), (160, 2), (165, -1), (177, -1), (189, -2), (213, 1), (217, 2), (222, 1), (226, 2)]))) (.branch (.leaf (4, [(0, -1), (5, -2), (7, 1), (8, 2), (16, -1), (27, -2), (31, -2), (50, -1), (63, -1), (80, 1), (89, 1), (95, 1), (98, 1), (109, 1), (149, 1), (161, 1), (178, -1), (187, 1), (199, 1), (201, 1), (225, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(61, 1), (153, 2), (194, -1), (197, -1), (218, 1)])) (.leaf (8, [(5, -4), (7, 2), (8, 4), (9, -1), (21, -2), (31, -4), (33, 1), (40, -1), (50, -2), (53, -2), (56, -1), (65, -1), (67, 1), (69, -1), (76, 2), (80, 1), (85, 2), (89, 2), (98, 1), (103, 3), (109, 2), (119, -2), (120, 1), (125, -2), (138, 2), (156, -1), (158, -2), (161, 2), (162, -1), (174, 2), (178, -2), (188, -2), (193, -2), (196, 1), (199, 2), (209, -1), (215, 2), (216, 2), (221, 1), (225, -3), (227, -2), (234, 2)]))) (.branch (.leaf (4, [(0, 1), (5, 2), (8, -2), (16, 1), (20, 1), (27, 2), (31, 2), (50, 1), (63, 1), (80, -1), (89, -1), (95, -1), (98, -1), (109, -1), (114, 1), (125, -1), (126, -1), (138, 1), (158, -1), (161, -1), (174, 1), (178, 1), (187, -1), (193, -1), (199, -1), (201, -1), (205, -1), (234, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (2, [(184, -1)])) (.leaf (4, [(109, 1)]))) (.branch (.leaf (4, [(73, 1), (141, 1), (147, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(0, -3), (2, -1), (7, 2), (8, 2), (9, 1), (16, -3), (20, 1), (27, -6), (31, -4), (33, -2), (40, 1), (43, -1), (56, 1), (63, -3), (67, -1), (70, -2), (80, 2), (85, -1), (89, 2), (92, 1), (95, 3), (98, 2), (106, -2), (109, 2), (111, -2), (123, 1), (126, 1), (149, 1), (154, 2), (156, 1), (158, 2), (161, 2), (164, 1), (178, -2), (187, 3), (193, 1), (196, -1), (201, 3), (205, -1), (209, 1), (215, 1), (225, -1)])) (.leaf (4, [(118, -1), (157, 1)]))) (.branch (.leaf (4, [(13, -1), (25, -2), (32, -1), (49, -2), (57, 1), (86, 1), (105, 1), (118, 1), (127, -1), (146, -1), (151, -1), (172, 2), (179, 1), (189, 1), (192, 2), (208, 1), (217, -1), (226, -1)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(94, 1), (160, -1)])) (.leaf (4, [(1, 1), (11, -2), (13, -3), (14, 1), (22, -1), (32, -3), (35, -1), (37, -1), (39, 1), (41, 1), (42, -1), (49, -6), (52, -1), (57, 2), (58, -1), (64, -1), (71, -1), (86, 1), (97, 2), (100, 1), (118, 1), (121, -1), (124, -3), (160, 4), (165, 1), (177, 1), (192, 6), (206, 1), (208, 3), (213, 1), (217, -1), (222, 1)]))) (.branch (.leaf (4, [(7, 1), (20, 1), (103, 1), (104, 2), (119, -1), (125, -1), (141, -1), (147, 1), (150, -2), (174, 2), (193, -1), (205, -1), (225, -1)])) (.leaf (2, [(11, 1), (13, 1), (32, 1), (42, 1), (49, 2), (57, -1), (64, 1), (97, -1), (100, -1), (124, 1), (160, -2), (192, -2), (208, -1), (213, -1)])))) (.branch (.branch (.leaf (2, [(180, 1), (210, -1)])) (.leaf (4, [(1, 1), (11, -1), (13, -2), (14, 1), (22, -1), (32, -2), (39, 1), (42, -1), (49, -4), (52, -1), (57, 1), (58, -1), (64, -1), (71, -1), (86, 1), (97, 1), (100, 1), (118, 1), (121, -1), (124, -2), (160, 3), (165, 1), (177, 1), (189, -1), (192, 4), (206, 1), (208, 2), (213, 1), (222, 1)]))) (.branch (.leaf (2, [(135, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(54, 1), (66, -1), (90, 1), (107, 1), (113, 2), (115, 1), (116, 2)])) (.leaf (2, [(141, -1), (147, 1)]))) (.branch (.leaf (4, [(0, -2), (7, 2), (8, 2), (16, -1), (27, -2), (31, -2), (56, 1), (63, -2), (67, -1), (75, 1), (80, 1), (95, 2), (98, 1), (101, 1), (149, 1), (154, 2), (156, 1), (158, 2), (161, 1), (173, -1), (187, 2), (201, 1), (205, -1), (225, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(8, 2), (20, -1), (31, -2), (53, -2), (65, -1), (69, -1), (85, 1), (89, 1), (109, 1), (161, 1), (178, -1), (205, 1), (215, 1), (221, 1)])) (.leaf (4, [(102, -1), (128, -1), (148, 1), (166, 1), (232, -1)]))) (.branch (.leaf (8, [(11, -2), (57, 2), (71, 2), (127, -2), (155, 2), (165, -2), (172, 2), (189, 2), (217, -2), (222, -2), (235, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(12, 1), (215, -1)])) (.leaf (2, [(132, -1)]))) (.branch (.leaf (4, [(0, 1), (2, 1), (5, -2), (7, -1), (8, 2), (12, 1), (16, 1), (20, -1), (27, 2), (29, 2), (38, -1), (43, 1), (50, -1), (51, -2), (56, -1), (63, 1), (67, 1), (73, -1), (80, -1), (87, -2), (95, -1), (101, -1), (103, 1), (106, 4), (123, -1), (126, -1), (149, -1), (154, -2), (156, -1), (158, -2), (164, -1), (173, 1), (187, -1), (199, 1), (201, -1), (205, 1), (215, -1), (223, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(5, -2), (8, 2), (20, -1), (31, -2), (50, -1), (65, -1), (69, -1), (85, 1), (89, 1), (109, 1), (161, 1), (178, -1), (182, 2), (199, 1), (205, 1), (212, -2), (215, 1), (221, 1)])) (.leaf (4, [(0, 2), (7, -2), (8, -2), (9, -1), (16, 2), (20, -1), (27, 4), (31, 2), (33, 1), (40, -1), (43, 1), (56, -1), (63, 2), (67, 1), (73, -1), (80, -1), (85, 1), (89, -1), (95, -2), (98, -1), (106, 2), (109, -1), (123, -1), (126, -1), (149, -1), (156, -1), (158, -2), (161, -1), (178, 1), (187, -2), (196, 1), (201, -2), (205, 1), (209, -1), (215, -1), (223, 1), (225, 1)]))) (.branch (.leaf (4, [(34, -1), (93, 1), (117, -1), (139, 1), (159, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (2, [(3, -1), (168, 1), (170, 1)])) (.leaf (4, [(109, -1), (178, 1)]))) (.branch (.leaf (4, [(43, -1), (123, 1), (126, 1), (215, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(11, -2), (13, -1), (19, -2), (32, -1), (39, 1), (42, -1), (49, -2), (52, -1), (57, 2), (58, -1), (64, -1), (71, 1), (97, 1), (100, 1), (118, 1), (121, 1), (124, -3), (160, 2), (165, 1), (177, 1), (189, 1), (192, 2), (204, 2), (208, 1), (213, 1), (217, -1), (222, -1), (226, 1)])) (.leaf (2, [(226, 1)]))) (.branch (.leaf (4, [(0, 2), (2, 1), (7, -3), (8, -2), (12, 1), (16, 2), (27, 4), (31, 4), (38, -1), (43, 1), (51, -2), (56, -1), (63, 2), (67, 1), (73, -1), (75, -1), (80, -2), (89, -1), (95, -2), (98, -1), (101, -1), (106, 2), (109, -1), (123, -1), (126, -1), (149, -2), (154, -2), (156, -2), (158, -4), (161, -2), (164, -1), (173, 1), (178, 1), (187, -2), (193, 1), (201, -2), (205, 1), (215, -1), (223, 1), (225, 2)])) (.leaf (1, [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(63, 1), (193, -1)])) (.leaf (4, [(7, -1), (20, -1), (21, 2), (76, -2), (103, -1), (119, 1), (125, 1), (138, -2), (141, 1), (147, -1), (193, 1), (205, 1), (225, 1)]))) (.branch (.leaf (4, [(1, 1), (11, -2), (13, -2), (32, -2), (35, -1), (39, 1), (41, 1), (42, -2), (46, -1), (49, -4), (52, -1), (57, 3), (58, -1), (64, -2), (74, -2), (97, 2), (100, 2), (118, 2), (124, -4), (157, -1), (160, 2), (163, 1), (165, 2), (177, 1), (189, 1), (192, 4), (204, 2), (208, 2), (213, 2), (217, -1), (222, -1)])) (.leaf (4, [(0, -3), (2, -1), (5, 4), (7, 2), (16, -3), (20, 2), (27, -6), (31, -2), (50, 2), (56, 2), (63, -3), (67, -2), (80, 3), (89, 1), (95, 3), (98, 1), (101, 2), (103, -2), (106, -4), (109, 1), (149, 2), (154, 4), (156, 2), (158, 4), (161, 1), (164, 1), (173, -2), (178, -1), (187, 3), (193, 1), (199, -2), (201, 3), (205, -2)])))) (.branch (.branch (.leaf (4, [(50, -1), (78, -2), (199, 1)])) (.leaf (4, [(2, -1), (5, 2), (8, -2), (50, 1), (103, -1), (106, -2), (149, 1), (156, 1), (158, 2), (164, 1), (199, -1)]))) (.branch (.leaf (4, [(91, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (2, [(215, 1)])) (.leaf (4, [(13, -1), (32, -1), (49, -2), (71, -1), (86, 1), (160, 1), (192, 2), (208, 1), (222, 1)]))) (.branch (.leaf (4, [(30, 1), (54, -1), (59, -1), (66, 1), (84, 1), (99, -1), (107, -1), (113, -2), (115, -1), (116, -2), (139, 1), (218, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(61, 1), (110, 2), (197, -1)])) (.leaf (4, [(0, 1), (5, 2), (7, -1), (8, -2), (16, 1), (27, 2), (31, 2), (33, 1), (50, 1), (63, 1), (80, -1), (89, -1), (95, -1), (98, -1), (103, -1), (109, -1), (111, 2), (161, -1), (178, 1), (187, -1), (199, -1), (201, -1), (209, -1), (225, 1)]))) (.branch (.leaf (4, [(5, -2), (7, 1), (8, 2), (9, -1), (20, -1), (27, 2), (31, -2), (50, -1), (75, 1), (85, 1), (103, 1), (106, 2), (119, -1), (161, 1), (174, 2), (193, -1), (196, 1), (199, 1), (225, -1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(45, 1), (144, -1)])) (.leaf (4, [(0, -2), (5, -1), (7, 2), (8, 2), (9, 1), (16, -2), (20, 1), (27, -3), (31, -2), (33, -1), (40, 1), (43, -1), (53, 1), (56, 1), (63, -2), (67, -1), (73, 1), (80, 1), (83, -1), (85, -1), (89, 1), (92, 1), (95, 2), (98, 1), (106, -2), (109, 1), (123, 1), (126, 1), (149, 1), (154, 2), (156, 1), (158, 2), (161, 1), (178, -1), (187, 2), (196, -1), (201, 2), (205, -1), (223, -1), (225, -1), (229, -1)]))) (.branch (.leaf (4, [(124, -1), (155, -2), (165, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(62, 1), (198, -1)])) (.leaf (4, [(11, -1), (57, 1), (124, -1), (189, 1), (217, -1)]))) (.branch (.leaf (2, [(117, 1), (159, -1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(10, 1), (171, -1)])) (.leaf (4, [(13, 1), (32, 1), (49, 2), (71, 1), (86, -1), (105, -1), (146, 1), (151, 1), (160, -1), (177, 1), (179, -1), (192, -2), (208, -1), (222, -1)]))) (.branch (.leaf (4, [(14, 1), (32, -1), (39, 1), (42, -1), (52, -1), (57, 1), (64, -1), (97, 1), (208, 1), (213, 1), (222, -1), (226, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(0, 2), (7, -2), (8, -2), (9, -1), (16, 2), (20, -1), (27, 4), (31, 2), (33, 1), (40, -1), (43, 1), (56, -1), (63, 2), (67, 1), (80, -1), (85, 1), (89, -1), (95, -2), (98, -1), (106, 2), (109, -1), (126, -1), (149, -1), (156, -1), (158, -2), (161, -1), (178, 1), (187, -2), (196, 1), (201, -2), (205, 1), (209, -1), (215, -1), (225, 1)])) (.leaf (4, [(5, 2), (50, 1), (103, -1), (106, -2), (149, 1), (156, 1), (158, 2), (181, 1), (199, -1), (225, 1)]))) (.branch (.leaf (4, [(35, 1), (118, 1), (157, -1)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (4, [(195, 1)])) (.leaf (4, [(0, 1), (5, 2), (7, -1), (8, -2), (16, 1), (27, 2), (31, 2), (50, 1), (63, 1), (80, -1), (89, -1), (92, 1), (95, -1), (98, -1), (103, -1), (109, -1), (111, 2), (161, -1), (178, 1), (187, -1), (199, -1), (201, -1), (209, -1), (225, 1)]))) (.branch (.leaf (4, [(1, -1), (11, 2), (13, 1), (14, -1), (32, 1), (39, -1), (42, 1), (46, 1), (49, 2), (52, 1), (57, -1), (64, 1), (97, -1), (118, -1), (124, 3), (160, -2), (165, -1), (192, -2), (208, -1), (213, -1), (226, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(8, -2), (20, 1), (31, 2), (50, 1), (53, 2), (65, 1), (69, 1), (85, -1), (89, -1), (109, -1), (161, -1), (178, 1), (188, 2), (199, -1), (205, -1), (215, -1), (216, -2), (221, -1)])) (.leaf (4, [(11, 2), (13, 2), (14, -2), (32, 2), (39, -2), (42, 2), (49, 4), (52, 2), (64, 2), (97, -2), (124, 2), (160, -6), (180, -1), (189, 2), (192, -4), (200, -1), (208, -2), (210, 1), (213, -2), (217, -2), (220, 1), (222, -2), (226, -2), (236, -1)]))) (.branch (.leaf (4, [(117, -1), (140, 2), (159, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(107, 1), (115, 1), (116, 2)])) (.leaf (4, [(13, 1), (32, 1), (49, 2), (71, 1), (86, -1), (105, -1), (146, 1), (151, 1), (160, -1), (175, 1), (179, -1), (192, -2), (208, -1), (222, -1)]))) (.branch (.leaf (4, [(32, 1), (35, 1), (41, -1), (42, 1), (57, -1), (64, 1), (97, -1), (100, -1), (213, -1), (222, 1), (226, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(61, 1), (81, -2), (153, 2), (197, -1)])) (.leaf (4, [(156, 1)]))) (.branch (.leaf (2, [(119, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (4, [(122, 1)])) (.leaf (4, [(1, -1), (11, 1), (13, 3), (14, -1), (22, 1), (32, 3), (35, 1), (37, 1), (39, -1), (41, -1), (42, 1), (49, 6), (52, 1), (57, -1), (58, 1), (64, 1), (71, 2), (86, -2), (97, -1), (100, -1), (118, -1), (121, 1), (124, 2), (146, 1), (160, -4), (165, -1), (177, -1), (189, 1), (192, -6), (206, -1), (208, -3), (213, -1), (222, -2)]))) (.branch (.leaf (4, [(18, 1), (54, -1), (66, 1), (99, -1), (107, -1), (113, -2), (115, -1), (116, -2), (139, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(47, -1), (110, -1), (169, 1), (190, 1)])) (.leaf (8, [(106, 2), (132, 2), (233, 1)]))) (.branch (.leaf (4, [(129, -1), (167, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (4, [(50, -1), (152, -2), (199, 1)])) (.leaf (2, [(13, -1), (32, -1), (49, -2), (71, -1), (86, 1), (105, 1), (146, -1), (151, -1), (160, 1), (179, 1), (192, 2), (208, 1), (222, 1)]))) (.branch (.leaf (4, [(0, 1), (7, -1), (16, 1), (20, -1), (27, 2), (56, -1), (63, 1), (67, 1), (80, -1), (85, 1), (95, -1), (101, -1), (154, -2), (173, 1), (187, -1), (201, -1), (205, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (2, [(11, 1), (102, 1), (118, -1), (124, 1), (148, -1), (160, -1), (226, -1)])) (.leaf (4, [(54, 1), (59, 1), (66, -1), (84, -1), (99, 1), (107, 1), (113, 2), (115, 1), (116, 2), (139, -1), (159, 1), (194, 1), (218, -1)]))) (.branch (.leaf (8, [(1, -2), (11, 2), (13, 4), (15, -1), (22, 2), (32, 5), (35, 2), (37, 1), (41, -2), (42, 2), (49, 10), (57, -2), (58, 2), (64, 2), (68, 1), (71, 2), (86, -2), (97, -3), (100, -4), (118, -2), (121, 2), (124, 4), (160, -8), (165, -2), (177, -2), (189, 2), (192, -8), (200, 1), (206, -2), (208, -5), (213, -2), (220, -1), (222, -2), (231, 1)])) (.leaf (1, [])))))))))
def dual199GaugeCertsTree : GenTree (Int × List (Nat × Int)) := .branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (16, [(98, 1)])) (.leaf (16, [(9, 2), (14, 4), (19, -2), (21, -4), (31, 1), (44, -1), (50, -2), (51, -2), (65, -8), (71, -2), (74, 2), (81, -4), (94, -2), (136, -2), (142, -2), (146, 2)]))) (.branch (.leaf (16, [(141, 1), (145, 1)])) (.leaf (16, [(17, 4), (57, -4), (68, -1), (72, 1), (77, -2), (78, -2), (79, 1), (82, 2), (83, -8), (84, 4), (91, 2), (92, -1), (109, 2), (123, 2), (127, -4), (132, -1), (144, 2), (151, 1), (155, -2), (177, 2), (178, -2), (191, -2), (220, 1), (232, 1), (248, 2)])))) (.branch (.branch (.leaf (16, [(46, 1), (78, 1), (83, 4)])) (.leaf (16, [(25, 1), (57, 4), (68, 1), (77, 1), (78, 1), (83, 4), (90, 1), (92, 1), (123, -1), (130, -2), (132, 1), (140, -1), (144, -1), (172, 1), (220, 1), (237, -2), (242, -2), (244, -4), (248, -2)]))) (.branch (.leaf (16, [(17, -2), (27, 1), (57, 4), (68, 1), (77, 1), (78, 1), (83, 4), (91, -1), (92, 1), (109, -1), (114, -1), (123, -2), (126, -1), (127, 2), (132, 1), (140, 1), (144, -1), (151, -1), (173, 1), (232, -1), (242, -2), (248, -2)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(126, -1), (135, -2)])) (.leaf (16, [(72, 1)]))) (.branch (.leaf (16, [(232, 1), (233, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (8, [(2, -2), (16, 2), (243, -1)])) (.leaf (16, [(42, 1), (57, 4), (68, 1)]))) (.branch (.leaf (16, [(75, 4), (124, -1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (16, [(91, -1), (109, 1), (236, 2)])) (.leaf (16, [(17, 2), (57, -4), (68, -1), (77, -1), (78, -1), (83, -4), (91, 1), (92, -1), (109, 1), (123, 1), (127, -2), (132, -1), (144, 1), (207, -2), (220, 1), (248, 2)]))) (.branch (.leaf (16, [(56, -4), (141, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(103, 1)])) (.leaf (16, [(28, 1), (93, 1), (111, 1), (113, 2), (119, 1), (133, -2), (141, 1), (174, 1), (245, -2)]))) (.branch (.leaf (4, [(156, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(147, 1), (220, 1), (232, 1)])) (.leaf (16, [(72, -1), (82, -2), (225, -2)]))) (.branch (.leaf (16, [(17, 2), (20, 4), (91, 1), (109, 1), (127, -2), (130, -2), (207, -2), (209, -1), (218, 1), (220, 1), (221, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(6, -1), (16, -1), (243, 1)])) (.leaf (16, [(17, -2), (57, 4), (68, 1), (77, 1), (78, 1), (83, 4), (91, -1), (92, 1), (109, -1), (123, -2), (127, 2), (132, 1), (134, -2), (140, 1), (144, -1), (151, -1), (248, -2)]))) (.branch (.leaf (16, [(10, 2), (17, -4), (20, -4), (25, 1), (77, 1), (91, -2), (100, 1), (109, -2), (127, 4), (130, 2), (140, 2), (144, -1), (151, -1), (172, -2), (207, 2), (220, -1), (232, -2)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (16, [(140, 1), (236, 2)])) (.leaf (16, [(10, -2), (17, 2), (20, 4), (57, -4), (68, -1), (77, -1), (78, -1), (83, -4), (91, 1), (92, -1), (109, 1), (123, 1), (127, -2), (132, -1), (140, -1), (144, 1), (151, 1), (207, -2), (232, 1), (248, 2)]))) (.branch (.leaf (16, [(54, 4), (70, -2), (93, 1), (111, 1), (113, 2), (133, -2)])) (.leaf (128, [(9, 64), (11, -32), (19, -32), (24, -36), (26, 36), (30, 9), (34, -16), (40, -8), (43, -9), (48, 16), (51, -64), (65, -128), (69, 16), (71, -16), (74, 48), (81, -32), (85, 8), (94, -16), (105, -16), (112, 16), (121, 8), (125, 32), (136, -64), (142, -48), (146, 32), (149, -8), (150, -16), (162, -32), (163, -16), (182, 32), (194, 24), (230, 8)])))) (.branch (.branch (.leaf (16, [(38, 1), (46, -1), (78, -2), (83, -8)])) (.leaf (16, [(35, 4), (123, -1)]))) (.branch (.leaf (16, [(188, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(99, 1)])) (.leaf (16, [(37, 2), (57, -4), (59, 2), (68, -1), (72, 1), (78, -1), (82, 2), (83, -4), (92, -1), (107, 1), (123, 1), (132, -1), (147, -1), (151, 1), (184, -1), (220, -1), (232, -1), (248, 2)]))) (.branch (.leaf (16, [(34, 1), (74, 1), (94, -1), (125, 2), (136, -1), (142, -1), (150, -1), (182, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (8, [(243, -1)])) (.leaf (16, [(29, 1), (42, -1), (78, 2), (83, 8), (92, 2), (123, -2), (132, 2), (151, -1), (220, 1), (232, 1), (248, -4)]))) (.branch (.leaf (16, [(201, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (8, [(222, -1)])) (.leaf (16, [(13, -4), (17, -4), (20, -4), (57, 8), (68, 2), (77, 2), (78, 2), (83, 8), (91, -2), (92, 2), (109, -2), (123, -2), (127, 4), (132, 2), (144, -2), (151, -1), (207, 4), (220, -1), (232, -1), (248, -4)]))) (.branch (.leaf (16, [(113, -2), (141, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (8, [(2, 2), (16, -2), (240, -1), (243, 1)])) (.leaf (16, [(0, 4), (141, -1), (234, -4)]))) (.branch (.leaf (16, [(124, 1), (186, 2), (195, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(74, -1), (142, 1), (150, 1), (166, -2)])) (.leaf (16, [(124, 1), (198, -2)]))) (.branch (.leaf (16, [(17, -2), (35, 4), (87, -1), (91, -1), (104, 1), (109, -1), (127, 2), (130, 2), (171, -1), (242, -2), (244, -4)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(17, 2), (37, -1), (77, -1), (79, 1), (84, 4), (91, 1), (107, 1), (109, 1), (127, -2), (131, -1), (144, 1), (147, 1), (220, 1), (232, 1)])) (.leaf (16, [(21, -4), (43, -1), (50, -2), (61, -4), (65, -4), (69, -1), (74, 1), (142, -1), (150, 1), (205, 1), (219, -1), (224, 1)]))) (.branch (.leaf (16, [(21, 4), (43, 1), (44, 1), (50, 2), (61, 4), (65, 4), (69, 1), (71, 1), (81, 2)])) (.leaf (1, [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (16, [(231, 1)])) (.leaf (16, [(28, 1), (58, 2), (93, -1), (102, 1), (111, -1), (113, -2), (133, 2), (174, -2)]))) (.branch (.leaf (16, [(3, 4), (17, 2), (77, -1), (80, -2), (91, 1), (109, 1), (127, -2), (130, -2), (140, -2), (144, 1), (151, 1), (152, 1)])) (.leaf (16, [(17, -2), (91, -1), (109, -1), (123, -1), (127, 2), (130, 2), (159, -4), (209, 1), (220, -1), (221, -1), (229, 1)])))) (.branch (.branch (.leaf (16, [(180, 1)])) (.leaf (16, [(5, 4), (41, 1), (43, -1), (61, -4), (67, 1), (69, -1)]))) (.branch (.leaf (8, [(9, 1), (19, -1), (24, 2), (26, -2), (50, 1), (51, -1), (61, 4), (69, 1), (122, 1), (125, -2), (150, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(126, -1), (211, -4)])) (.leaf (16, [(93, -1), (111, -1), (113, -2), (133, 2), (154, -8)]))) (.branch (.leaf (16, [(17, 2), (91, 1), (109, 1), (127, -2), (130, -2), (140, -2), (151, 1), (152, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(23, -1)])) (.leaf (16, [(94, -1), (115, 1), (125, 2), (136, -1), (146, 1), (150, -1)]))) (.branch (.leaf (16, [(117, 1), (125, -2), (150, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (16, [(125, -2), (205, -1), (214, 1), (219, 1)])) (.leaf (16, [(141, 1), (158, -4)]))) (.branch (.leaf (16, [(17, -2), (57, 4), (68, 1), (77, 1), (78, 1), (83, 4), (92, 1), (123, -1), (132, 1), (144, -1), (248, -2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(97, 1)])) (.leaf (16, [(17, -2), (57, 4), (68, 1), (77, 1), (78, 1), (83, 4), (91, -1), (92, 1), (109, -1), (123, -1), (127, 2), (132, 1), (144, -1), (244, -4), (248, -2)]))) (.branch (.leaf (16, [(93, 1), (111, 1), (113, 2), (133, -2), (157, 4)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(78, 1), (83, 4), (170, 1)])) (.leaf (16, [(5, -4), (9, -4), (11, 2), (15, 2), (19, 2), (50, -2), (51, 4), (65, 4), (67, -1), (69, -1), (71, 1), (74, -3), (81, 2), (112, -1), (136, 3), (142, 3), (146, -1), (205, 1), (208, 2), (214, 1), (217, 1), (224, -2), (228, -1)]))) (.branch (.leaf (16, [(22, 2), (205, 1), (214, 1), (224, -2), (226, -2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(22, 2), (74, -1), (125, -2), (142, 1), (150, 1), (199, -2), (205, 1), (214, 1), (224, -2)])) (.leaf (8, [(50, 1), (51, -1), (69, 1)]))) (.branch (.leaf (16, [(17, 2), (77, -1), (91, 1), (109, 1), (127, -2), (144, 1), (210, 1), (212, 4), (232, 1), (242, 2), (244, 4)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (16, [(146, 1), (150, 1)])) (.leaf (16, [(58, -2), (141, -1)]))) (.branch (.leaf (16, [(3, -4), (57, 4), (68, 1), (77, 1), (78, 1), (83, 4), (92, 1), (123, -1), (132, 1), (140, 1), (144, -1), (151, -1), (220, 1), (232, 1), (248, -2)])) (.leaf (8, [(8, -1), (9, -1), (18, 1), (19, -1), (50, -2), (51, 2), (69, -1), (74, 1), (94, -3), (112, -1), (142, -1), (146, 2)])))) (.branch (.branch (.leaf (16, [(16, 4), (28, -1), (102, 1), (243, -2), (245, 2)])) (.leaf (8, [(4, -2), (5, -2), (9, -1), (19, 1), (50, -1), (51, 1), (67, -1), (74, -1), (94, 1), (136, 1), (142, 1), (146, -1)]))) (.branch (.leaf (16, [(35, -4), (57, 4), (68, 1), (77, 1), (78, 1), (83, 4), (87, 1), (92, 1), (116, 1), (123, -1), (130, -2), (132, 1), (144, -1), (248, -2)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(141, -1), (245, 2)])) (.leaf (128, [(24, 28), (26, -28), (30, -7), (43, 7), (48, -8), (121, -8), (162, 16), (163, 16), (194, -24), (230, 8)]))) (.branch (.leaf (16, [(17, -4), (91, -2), (109, -2), (127, 4), (130, 4), (140, 2), (148, 1), (151, -1), (152, -1), (220, -1), (232, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(86, -1)])) (.leaf (16, [(43, -1), (61, -4), (69, -1), (94, 2), (112, 1), (136, -1), (146, -1)]))) (.branch (.leaf (16, [(124, -1), (186, -2)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (16, [(94, -1), (112, 1), (125, 2), (146, 1), (150, -1), (239, -1)])) (.leaf (16, [(227, 1)]))) (.branch (.leaf (16, [(7, -2), (17, 2), (57, -8), (68, -2), (77, -2), (78, -2), (83, -8), (92, -2), (123, 2), (132, -2), (144, 2), (151, 1), (220, -1), (232, -1), (248, 4)])) (.leaf (1, [])))) (.branch (.branch (.leaf (8, [(190, -1)])) (.leaf (16, [(17, 4), (57, -8), (68, -2), (77, -2), (78, -2), (83, -8), (90, -1), (91, 2), (92, -2), (96, 1), (109, 2), (123, 2), (127, -4), (132, -2), (144, 2), (151, 1), (220, -1), (232, 1), (242, 4), (244, 8), (248, 4)]))) (.branch (.leaf (16, [(196, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(74, 1), (142, -1), (246, 1)])) (.leaf (16, [(15, 2), (43, 1), (61, 4), (74, -1), (76, 2), (94, -2), (112, -1), (136, 1), (142, 1), (143, 1), (146, 1), (203, -1), (205, 1), (214, 1), (224, -2)]))) (.branch (.leaf (16, [(19, 2), (61, -4), (69, -1), (94, 1), (112, 1), (122, -1), (125, 4), (136, -2), (138, -2), (150, -2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(9, -2), (19, 2), (30, 1), (43, -1), (50, -2), (51, 2), (61, -8), (69, -2), (94, 2), (136, 2), (146, -2)])) (.leaf (128, [(4, -32), (5, 32), (9, 32), (18, -32), (24, -20), (26, 20), (30, -11), (34, 16), (40, 8), (41, 16), (43, 27), (48, -16), (50, 32), (51, -32), (61, 128), (69, 32), (85, 8), (89, 8), (105, -16), (115, -8), (120, 8), (121, 8), (149, 8), (150, 16), (194, -8), (230, -8), (246, 16)]))) (.branch (.leaf (16, [(123, 1), (159, 4), (175, 1)])) (.leaf (1, []))))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (16, [(140, 1), (213, 1)])) (.leaf (128, [(9, -32), (11, 32), (14, 32), (21, -32), (24, -12), (26, 12), (30, 3), (34, 16), (36, 8), (40, 16), (43, -3), (48, -8), (51, 32), (61, 64), (65, 64), (71, 16), (74, -32), (81, 32), (85, -16), (105, 16), (106, 8), (112, -16), (115, 8), (121, 8), (122, 16), (125, -64), (136, 48), (142, 32), (146, -16), (149, 16), (150, 32), (162, 16), (163, -16), (182, -32), (183, -16), (194, -8), (230, -8)]))) (.branch (.leaf (16, [(139, 1)])) (.leaf (16, [(17, -4), (39, 1), (47, -1), (57, 8), (68, 2), (77, 2), (78, 2), (79, -2), (83, 8), (84, -8), (91, -2), (92, 2), (109, -2), (123, -2), (127, 4), (132, 2), (144, -2), (151, -1), (220, -1), (232, -1), (248, -4)])))) (.branch (.branch (.leaf (16, [(34, -1), (74, -1), (105, 1), (142, 1), (146, 1), (246, -1)])) (.leaf (16, [(67, 1), (69, -1), (74, 1), (125, -2), (150, 1), (202, 1)]))) (.branch (.leaf (16, [(50, -2), (61, -4), (65, -4), (69, -1), (122, -1), (153, -4)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(125, -2), (150, 1), (239, 1)])) (.leaf (16, [(45, 1), (72, 1), (82, 2)]))) (.branch (.leaf (16, [(141, 1), (234, 4)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(78, -1), (83, -4), (92, -1), (110, 1), (232, -1), (248, 2)])) (.leaf (16, [(1, 4), (141, -1), (235, -4)]))) (.branch (.leaf (16, [(52, -8), (93, -1), (111, -1), (113, -2), (133, 2)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (16, [(126, 1), (206, 1), (211, 4)])) (.leaf (16, [(19, -2), (43, 1), (61, 8), (69, 1), (94, -1), (112, -1), (122, 1), (125, -4), (136, 2), (150, 2), (168, -2)]))) (.branch (.leaf (16, [(7, 2), (78, 1), (83, 4), (91, 1), (92, 2), (109, 1), (110, 1), (127, -2), (132, -1), (220, 1), (232, 1), (248, -2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(16, 4), (93, -1), (111, 1), (243, -2), (247, 2)])) (.leaf (16, [(62, -2), (78, 1), (83, 4), (92, 1), (123, -1), (124, -1), (126, 1), (132, 1), (135, 2), (137, -2), (140, -1), (193, -2), (220, 1), (232, 1), (242, -2), (244, -4), (248, -2)]))) (.branch (.leaf (16, [(37, 1), (57, -4), (68, -1), (78, -1), (83, -4), (92, -1), (123, 1), (132, -1), (140, -1), (147, -1), (151, 1), (184, 1), (220, -1), (232, -1), (248, 2)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(25, -1), (100, 1), (237, 2)])) (.leaf (16, [(60, -2), (232, 1)]))) (.branch (.leaf (16, [(72, 1), (82, 2), (165, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(17, 2), (20, 4), (77, -1), (91, 1), (109, 1), (127, -2), (144, 1), (151, 1), (169, -2), (207, -2), (220, 1), (232, 2)])) (.leaf (16, [(50, -2), (69, -1)]))) (.branch (.leaf (16, [(12, 2), (22, -2), (74, 2), (125, 2), (150, -1), (202, -2), (205, -1), (214, -1), (224, 2)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (16, [(150, -1), (219, 1)])) (.leaf (16, [(5, 4), (9, 4), (11, -2), (19, -2), (50, 2), (51, -4), (65, -4), (67, 1), (69, 1), (71, -1), (74, 3), (81, -2), (94, -1), (112, 1), (125, 2), (136, -4), (142, -3), (146, 2), (150, -1), (208, -1), (217, 1)]))) (.branch (.leaf (16, [(72, -1), (82, -2), (124, -1), (140, -1), (155, -2), (167, -2), (191, 4), (198, 2)])) (.leaf (8, [(9, -1), (14, -2), (19, 1), (21, 2), (50, 1), (51, 1), (65, 4), (74, -1), (94, 1), (136, 1), (142, 1), (146, -1)])))) (.branch (.branch (.leaf (128, [(4, 32), (5, -32), (18, 16), (19, -16), (24, 20), (26, -20), (30, 11), (34, -16), (36, -8), (40, -16), (41, -16), (43, -11), (48, 8), (85, -16), (89, -8), (94, -16), (105, 16), (106, 8), (108, 8), (112, 16), (121, 8), (146, 16), (150, -16), (194, 8), (230, 8), (239, -16), (246, -16), (249, -16)])) (.leaf (16, [(5, 4), (9, 4), (11, -2), (19, -2), (50, 2), (51, -4), (65, -4), (67, 1), (69, 1), (74, 2), (112, 1), (136, -3), (142, -2), (146, 1)]))) (.branch (.leaf (4, [(53, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(141, 1), (215, 1)])) (.leaf (16, [(32, 1), (45, -1), (72, -2), (82, -4)]))) (.branch (.leaf (16, [(17, 2), (91, 1), (109, 1), (127, -2), (130, -2), (220, 1), (221, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(27, -1), (101, 1), (126, 1), (232, 1), (242, 2)])) (.leaf (64, [(24, -4), (26, 4), (30, 1), (43, -1), (48, -4), (149, -4), (162, -4), (163, -4), (194, 12), (230, 4)]))) (.branch (.leaf (16, [(43, 1), (61, 4), (76, 1), (94, -2), (112, -1), (117, -1), (125, 2), (136, 1), (146, 1), (150, -1), (203, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (16, [(88, 1), (126, -1)])) (.leaf (16, [(60, 2), (77, 1), (144, 1), (204, -2)]))) (.branch (.leaf (16, [(17, -2), (49, 4), (57, 4), (68, 1), (77, 2), (78, 1), (83, 4), (91, -1), (92, 1), (109, -1), (123, -2), (127, 2), (132, 1), (134, -2), (140, 1), (144, -2), (151, -1), (248, -2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(78, 1), (83, 4), (126, 1), (155, 2), (167, -2), (177, -2), (232, 1)])) (.leaf (16, [(17, -2), (77, 1), (91, -1), (109, -1), (127, 2), (144, -1), (212, -4), (232, -1), (242, -2), (244, -4)]))) (.branch (.leaf (16, [(93, 1), (111, 1), (113, 2), (133, -2), (157, 4), (185, -2)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (8, [(197, -1)])) (.leaf (16, [(160, -2), (232, -1)]))) (.branch (.leaf (16, [(57, 4), (68, 1), (114, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(9, 4), (19, -2), (50, 2), (51, -4), (61, 4), (65, -4), (69, 2), (74, 1), (94, -1), (112, 1), (125, 2), (136, -4), (142, -1), (146, 2), (150, -1), (179, -2)])) (.leaf (8, [(9, 1), (18, -1), (43, 1), (50, 1), (51, -1), (61, 4), (69, 1)]))) (.branch (.leaf (16, [(17, -4), (77, 1), (79, -1), (84, -4), (91, -2), (109, -2), (127, 4), (130, 2), (140, 2), (144, -1), (151, -1), (220, -1), (232, -1), (241, -4), (248, -2)])) (.leaf (1, [])))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf (16, [(140, -1), (237, 2)])) (.leaf (16, [(62, -2), (72, 1), (82, 2), (124, 1), (128, -2), (140, 1), (193, 4), (225, 2)]))) (.branch (.leaf (16, [(9, 4), (50, 2), (51, -4), (63, 4), (65, -4), (69, 2), (71, -1), (74, 2), (81, -2), (112, 2), (122, -1), (125, 4), (129, 2), (136, -6), (138, -2), (142, -2), (146, 2), (150, -2)])) (.leaf (16, [(17, 4), (33, 4), (35, -4), (57, -8), (68, -2), (77, -2), (78, -2), (83, -8), (91, 2), (92, -2), (109, 2), (123, 4), (127, -4), (132, -2), (144, 2), (151, 1), (220, 1), (232, 1), (248, 4)])))) (.branch (.branch (.leaf (16, [(78, 1), (83, 4), (177, -2)])) (.leaf (16, [(17, 2), (57, -4), (68, -1), (77, -1), (78, -1), (79, 1), (83, -4), (84, 4), (91, 1), (92, -1), (109, 1), (123, 1), (127, -2), (132, -1), (140, -1), (144, 1), (151, 1), (248, 4)]))) (.branch (.leaf (16, [(187, 1)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(88, -1), (95, 1), (126, 2)])) (.leaf (16, [(74, 1), (142, -1), (176, 1)]))) (.branch (.leaf (16, [(141, -1), (247, 2)])) (.leaf (1, [])))) (.branch (.branch (.leaf (8, [(16, 2), (66, 4), (243, -1)])) (.leaf (16, [(59, -2), (78, -1), (83, -4), (92, -1), (123, 1), (132, -1), (232, -1), (248, 2)]))) (.branch (.leaf (16, [(35, -4), (57, 4), (68, 1), (73, -4), (75, 4), (77, 1), (78, 1), (83, 4), (87, 2), (92, 1), (104, 1), (116, -1), (123, -1), (124, -1), (130, -2), (132, 1), (140, -1), (144, -1), (248, -2)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (16, [(223, 1)])) (.leaf (16, [(13, 4), (17, 2), (27, 2), (77, -1), (91, 1), (101, 1), (109, 1), (126, -1), (127, -2), (144, 1), (173, -1), (207, -2), (220, 1), (232, 1), (242, -2)]))) (.branch (.leaf (16, [(43, -1), (61, -4), (76, -1), (94, 1), (112, 1), (136, -2), (143, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (8, [(192, -1)])) (.leaf (16, [(94, -1), (125, 2), (136, -1), (146, 1), (150, -1), (249, 1)]))) (.branch (.leaf (8, [(54, -2), (55, 2), (93, -1), (111, -1), (113, -2), (133, 2)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(200, 1)])) (.leaf (16, [(74, -1), (142, 1), (205, 1), (214, 1), (224, -2)]))) (.branch (.leaf (16, [(5, 4), (26, 4), (61, -4), (67, 1), (69, -1), (122, -1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(17, -2), (77, 1), (91, -1), (109, -1), (127, 2), (131, 1), (144, -1), (232, -1), (242, -2), (244, -4)])) (.leaf (16, [(17, 2), (47, 1), (57, -4), (68, -1), (77, -1), (78, -1), (79, 1), (83, -4), (84, 4), (91, 2), (92, -1), (109, 1), (123, 1), (127, -1), (132, -1), (144, 1), (236, -2), (248, 2)]))) (.branch (.leaf (16, [(50, 2), (69, 1), (71, 1)])) (.leaf (1, []))))))) (.branch (.branch (.branch (.branch (.branch (.leaf (16, [(238, 1)])) (.leaf (16, [(20, 4), (59, -2), (64, 4), (78, -1), (83, -4), (92, -1), (123, 1), (132, -1), (207, -2), (232, -1), (248, 2)]))) (.branch (.leaf (16, [(5, -4), (9, -4), (19, 2), (50, -4), (51, 4), (61, -4), (67, -1), (69, -2), (74, -1), (94, 1), (112, -1), (125, -2), (129, -2), (136, 4), (142, 1), (146, -2), (150, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (16, [(62, 2), (78, -1), (83, -4), (126, -1), (128, -2), (135, -2), (232, -1)])) (.leaf (64, [(4, -32), (9, -16), (18, -8), (19, 24), (24, -20), (26, 20), (30, -3), (34, 8), (36, 4), (40, 8), (41, 8), (43, 3), (48, -4), (50, -16), (51, 16), (61, -32), (67, -8), (69, -8), (74, -8), (94, 16), (112, -8), (115, -4), (122, -8), (125, 16), (136, 8), (142, 8), (146, -16), (149, 4), (162, -4), (163, 4), (182, 8), (183, 4), (194, -4), (230, -4), (239, 8)]))) (.branch (.leaf (16, [(54, 4), (93, 1), (111, 1), (113, 2), (133, -2)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(141, 1), (235, 4)])) (.leaf (16, [(12, -2), (22, 2), (74, -1), (142, 1), (205, 1), (214, 1), (224, -2)]))) (.branch (.leaf (16, [(50, 2), (61, 4), (65, 4), (69, 1), (71, 1), (81, 2), (122, 1), (153, 4), (164, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (8, [(16, 2), (161, 4), (243, -1)])) (.leaf (16, [(79, 1)]))) (.branch (.leaf (8, [(73, 2), (75, -2), (124, 1)])) (.leaf (1, [])))))) (.branch (.branch (.branch (.branch (.leaf (16, [(118, 1)])) (.leaf (16, [(5, -4), (9, -4), (11, 2), (19, 2), (50, -2), (51, 4), (65, 4), (67, -1), (69, -1), (71, 1), (74, -3), (81, 2), (112, -1), (136, 3), (142, 3), (146, -1), (176, -1), (208, 1), (228, 1)]))) (.branch (.leaf (16, [(141, -1), (216, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (4, [(189, 1)])) (.leaf (16, [(68, 1), (77, 1), (204, 1)]))) (.branch (.leaf (16, [(160, 2), (209, 1), (218, 1), (229, -2)])) (.leaf (1, []))))) (.branch (.branch (.branch (.leaf (16, [(78, 1)])) (.leaf (8, [(15, -1), (22, -1), (74, 1), (142, -1), (205, -1), (214, -1), (224, 2)]))) (.branch (.leaf (16, [(79, 1), (84, 4), (171, 1)])) (.leaf (1, [])))) (.branch (.branch (.leaf (128, [(9, -16), (19, 16), (24, -4), (26, 4), (30, 1), (43, -1), (48, 8), (50, -32), (51, 32), (61, -64), (69, -32), (89, 8), (94, 16), (108, 8), (115, 8), (120, -16), (121, -8), (136, 16), (146, -16), (149, 16), (194, -8), (230, -8)])) (.leaf (16, [(93, 2), (111, 1), (113, 2), (133, -1), (141, 1), (181, 1), (247, -2)]))) (.branch (.leaf (16, [(9, -4), (11, 2), (19, 2), (34, 2), (51, 4), (65, 8), (69, -1), (71, 1), (74, -2), (81, 2), (105, 1), (112, -1), (136, 3), (142, 2), (146, -2), (182, -1)])) (.leaf (1, [])))))))))

def mapBasisComb (basisRows : List Nat) (idxComb : List (Nat × Int)) : List (Nat × Int) :=
  idxComb.map (fun bc => (listAt 0 basisRows bc.1, bc.2))

private def checkBasisPairsTree (bound : Nat) (termsFn : Nat → List ((Nat × Nat) × Int))
    (basisRows : List Nat) (bpTree : PairListTree) : Bool :=
  (basisRows.length ≤ 256) &&
  allIdx basisRows (fun i rk =>
    (rk < bound) &&
    (let bp := genTreeGet [] 8 bpTree i
     bp.all (fun cw => cw.1 < 325) &&
     intTreeBeq 9 (addScaledPairsNatTree (zeroIntTree 9) 1 bp)
       (addScaledPairsNatTree (zeroIntTree 9) 1 (rawNatPairs (termsFn rk)))))

private theorem checkBasisPairsTree_sound (bound : Nat)
    (termsFn : Nat → List ((Nat × Nat) × Int))
    (row : Nat → Nat → Nat → Int)
    (ht : ∀ k c, evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2) (termsFn k) =
      coefficient row k c)
    (basisRows : List Nat) (bpTree : PairListTree)
    (hok : checkBasisPairsTree bound termsFn basisRows bpTree = true)
    {i : Nat} (hi : i < basisRows.length) :
    listAt 0 basisRows i < bound ∧
    (∀ cw ∈ genTreeGet [] 8 bpTree i, cw.1 < 325) ∧
    (∀ c : Coord, ((genTreeGet [] 8 bpTree i).map (fun cw => if c.val = cw.1 then cw.2 else 0)).sum =
      coefficient row (listAt 0 basisRows i) c) := by
  unfold checkBasisPairsTree at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have hi_ok := allIdx_sound 0 basisRows _ hok.2 hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hi_ok
  rcases hi_ok with ⟨hrk, hbp325, hbeq⟩
  refine ⟨hrk, hbp325, fun c => ?_⟩
  have hc512 : c.val < 512 := Nat.lt_trans c.isLt (by decide)
  have heq := intTreeBeq_sound 9 _ _ hbeq c.val hc512
  have hbp512 : ∀ cw ∈ genTreeGet [] 8 bpTree i, cw.1 < 512 :=
    fun cw hcw => Nat.lt_trans (hbp325 cw hcw) (by decide)
  have hrp512 : ∀ cw ∈ rawNatPairs (termsFn (listAt 0 basisRows i)), cw.1 < 512 :=
    fun cw hcw => Nat.lt_trans (rawNatPairs_lt_325 _ cw hcw) (by decide)
  rw [intTreeGet_addScaledPairsNatTree (zeroIntTree 9) 1 _
      (genTreeWF_const 0 9) hbp512 hc512,
    intTreeGet_addScaledPairsNatTree (zeroIntTree 9) 1 _
      (genTreeWF_const 0 9) hrp512 hc512,
    intTreeGet_zero, zero_add, one_mul, one_mul, rawNatPairs_sum, ht] at heq
  omega

private def checkDualCertsTree (basisLen : Nat) (bpTree wsTree : PairListTree)
    (certsTree : GenTree (Int × List (Nat × Int))) : Bool :=
  (List.range 199).all (fun s =>
    let w := genTreeGet [] 8 wsTree s
    let cert := genTreeGet (1, []) 8 certsTree s
    (cert.1 > 0) &&
    w.all (fun cw => cw.1 < 325) &&
    cert.2.all (fun bc => bc.1 < basisLen) &&
    (let lhs := cert.2.foldl
       (fun acc bc => addScaledPairsNatTree acc bc.2 (genTreeGet [] 8 bpTree bc.1))
       (zeroIntTree 9)
     let rhs := addScaledPairsNatTree (zeroIntTree 9) cert.1 w
     intTreeBeq 9 lhs rhs))

private theorem checkDualCertsTree_sound (bound : Nat)
    (termsFn : Nat → List ((Nat × Nat) × Int))
    (row : Nat → Nat → Nat → Int)
    (ht : ∀ k c, evalNatTerms (choiCoefficient (coordinate c).1 (coordinate c).2) (termsFn k) =
      coefficient row k c)
    (basisRows : List Nat) (bpTree wsTree : PairListTree)
    (certsTree : GenTree (Int × List (Nat × Int)))
    (hbp : checkBasisPairsTree bound termsFn basisRows bpTree = true)
    (hcerts : checkDualCertsTree basisRows.length bpTree wsTree certsTree = true)
    (s : Fin 199) :
    let cert := genTreeGet (1, []) 8 certsTree s.val
    let comb := mapBasisComb basisRows cert.2
    0 < cert.1 ∧
    (∀ kc ∈ comb, kc.1 < bound) ∧
    (∀ c : Coord, combinedCoefficient comb (coefficient row) c =
      cert.1 * sparseNatAt (genTreeGet [] 8 wsTree s.val) c.val) := by
  unfold checkDualCertsTree at hcerts
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcerts
  rcases hcerts s.val (List.mem_range.mpr s.isLt) with ⟨⟨⟨hpos, hw325⟩, hbc_lt⟩, hbeq⟩
  let cert := genTreeGet (1, []) 8 certsTree s.val
  refine ⟨hpos, ?_, fun c => ?_⟩
  · intro kc hkc
    unfold mapBasisComb at hkc
    rw [List.mem_map] at hkc
    rcases hkc with ⟨bc, hbc, rfl⟩
    exact (checkBasisPairsTree_sound bound termsFn row ht basisRows bpTree hbp (hbc_lt bc hbc)).1
  · have hc512 : c.val < 512 := Nat.lt_trans c.isLt (by decide)
    have heq := intTreeBeq_sound 9 _ _ hbeq c.val hc512
    have hw512 : ∀ cw ∈ genTreeGet [] 8 wsTree s.val, cw.1 < 512 :=
      fun cw hcw => Nat.lt_trans (hw325 cw hcw) (by decide)
    rw [intTreeGet_addScaledPairsNatTree (zeroIntTree 9) cert.1 _
      (genTreeWF_const 0 9) hw512 hc512, intTreeGet_zero, zero_add] at heq
    suffices hlhs : ∀ (l : List (Nat × Int)), (∀ bc ∈ l, bc.1 < basisRows.length) →
        ∀ (acc : IntTree), GenTreeWF 9 acc →
        intTreeGet 9
          (l.foldl (fun a bc => addScaledPairsNatTree a bc.2 (genTreeGet [] 8 bpTree bc.1)) acc)
          c.val =
        intTreeGet 9 acc c.val + combinedCoefficient (mapBasisComb basisRows l) (coefficient row) c by
      have hl := hlhs cert.2 hbc_lt (zeroIntTree 9) (genTreeWF_const 0 9)
      rw [intTreeGet_zero, zero_add] at hl
      rw [← hl, heq]
      rfl
    intro l hl_lt
    induction l with
    | nil => intro acc _; simp [mapBasisComb, combinedCoefficient]
    | cons bc rest ih =>
      intro acc hwf
      have hbc1 : bc.1 < basisRows.length := hl_lt bc (by simp)
      have hrest : ∀ x ∈ rest, x.1 < basisRows.length := fun x hx => hl_lt x (by simp [hx])
      rcases checkBasisPairsTree_sound bound termsFn row ht basisRows bpTree hbp hbc1 with
        ⟨_, hbp325, hbp_sum⟩
      have hbp512 : ∀ cw ∈ genTreeGet [] 8 bpTree bc.1, cw.1 < 512 :=
        fun cw hcw => Nat.lt_trans (hbp325 cw hcw) (by decide)
      have hcc : combinedCoefficient (mapBasisComb basisRows (bc :: rest)) (coefficient row) c =
          bc.2 * coefficient row (listAt 0 basisRows bc.1) c +
            combinedCoefficient (mapBasisComb basisRows rest) (coefficient row) c := by
        simp [mapBasisComb, combinedCoefficient]
      simp only [List.foldl_cons]
      rw [ih hrest _ (addScaledPairsNatTree_wf acc bc.2 _ hwf),
        intTreeGet_addScaledPairsNatTree acc bc.2 _ hwf hbp512 hc512,
        hbp_sum c, hcc]
      omega

private theorem ab_basis_true :
    checkBasisPairsTree 1088 abNatTerms abBasisRows abBasisPairsTree = true := by
  decide +kernel

private theorem ba_basis_true :
    checkBasisPairsTree 1088 baNatTerms baBasisRows baBasisPairsTree = true := by
  decide +kernel

private theorem gauge_basis_true :
    checkBasisPairsTree 16384 gaugeNatTerms gaugeBasisRows gaugeBasisPairsTree = true := by
  decide +kernel

private theorem dual199_ab_true :
    checkDualCertsTree abBasisRows.length abBasisPairsTree dual199WsTree dual199ABCertsTree = true := by
  decide +kernel

private theorem dual199_ba_true :
    checkDualCertsTree baBasisRows.length baBasisPairsTree dual199WsTree dual199BACertsTree = true := by
  decide +kernel

private theorem dual199_gauge_true :
    checkDualCertsTree gaugeBasisRows.length gaugeBasisPairsTree dual199WsTree dual199GaugeCertsTree = true := by
  decide +kernel

private theorem mem_rowSpace_of_cert {bound : Nat} (row : Nat → Coord → Int)
    (w : List (Nat × Int)) (scale : Int) (comb : List (Nat × Int))
    (hpos : 0 < scale) (hbound : ∀ kc ∈ comb, kc.1 < bound)
    (hcoeff : ∀ c : Coord, combinedCoefficient comb row c = scale * sparseNatAt w c.val) :
    sparseNatRealVec w ∈ Submodule.span ℝ (Set.range (fun k : Fin bound => rowVec row k.val)) := by
  let S := Submodule.span ℝ (Set.range (fun k : Fin bound => rowVec row k.val))
  have hsum_mem : ∀ (l : List (Nat × Int)), (∀ kc ∈ l, kc.1 < bound) →
      (fun c : Coord => (combinedCoefficient l row c : ℝ)) ∈ S := by
    intro l hl
    induction l with
    | nil =>
      have hz : (fun c : Coord => (combinedCoefficient [] row c : ℝ)) = 0 := by
        funext c; simp [combinedCoefficient]
      rw [hz]; exact Submodule.zero_mem S
    | cons kc rest ih =>
      have hkc : kc.1 < bound := hl kc (by simp)
      have hrest : ∀ t ∈ rest, t.1 < bound := fun t ht => hl t (by simp [ht])
      have hsplit : (fun c : Coord => (combinedCoefficient (kc :: rest) row c : ℝ)) =
          (kc.2 : ℝ) • rowVec row kc.1 + (fun c : Coord => (combinedCoefficient rest row c : ℝ)) := by
        funext c
        simp [combinedCoefficient, rowVec, Int.cast_add, Int.cast_mul]
      rw [hsplit]
      exact Submodule.add_mem S
        (Submodule.smul_mem S (kc.2 : ℝ) (Submodule.subset_span ⟨⟨kc.1, hkc⟩, rfl⟩))
        (ih hrest)
  have hmem := hsum_mem comb hbound
  have hsne : (scale : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have hscale : sparseNatRealVec w =
      ((scale : ℝ)⁻¹) • (fun c : Coord => (combinedCoefficient comb row c : ℝ)) := by
    funext c
    simp only [sparseNatRealVec, Pi.smul_apply, smul_eq_mul, hcoeff c, Int.cast_mul]
    field_simp [hsne]
  rw [hscale]
  exact Submodule.smul_mem S _ hmem

theorem dual199_mem_row_intersection (s : Fin 199) :
    dual199Vec s ∈ rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge := by
  rcases checkDualCertsTree_sound 1088 abNatTerms rowAB evalNatTerms_ab
    abBasisRows abBasisPairsTree dual199WsTree dual199ABCertsTree
    ab_basis_true dual199_ab_true s with ⟨hpA, hbA, hcA⟩
  rcases checkDualCertsTree_sound 1088 baNatTerms rowBA evalNatTerms_ba
    baBasisRows baBasisPairsTree dual199WsTree dual199BACertsTree
    ba_basis_true dual199_ba_true s with ⟨hpB, hbB, hcB⟩
  rcases checkDualCertsTree_sound 16384 gaugeNatTerms rowGauge16 evalNatTerms_gauge
    gaugeBasisRows gaugeBasisPairsTree dual199WsTree dual199GaugeCertsTree
    gauge_basis_true dual199_gauge_true s with ⟨hpG, hbG, hcG⟩
  exact ⟨⟨mem_rowSpace_of_cert (coefficient rowAB) _ _ _ hpA hbA hcA,
          mem_rowSpace_of_cert (coefficient rowBA) _ _ _ hpB hbB hcB⟩,
         mem_rowSpace_of_cert (coefficient rowGauge16) _ _ _ hpG hbG hcG⟩

theorem rowSpace_ortho {bound : Nat} (row : Nat → Coord → Int)
    {w : CoordVec}
    (hw : w ∈ Submodule.span ℝ (Set.range (fun k : Fin bound => rowVec row k.val)))
    {X : CoordVec} (hX : ∀ k < bound, rowValue row k X = 0) :
    ∑ c : Coord, w c * X c = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨k, rfl⟩
    exact hX k.val k.isLt
  · simp
  · intro u v _ _ hu hv
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, hu, hv]
  · intro r u _ hu
    simp [Pi.smul_apply, mul_assoc, ← Finset.mul_sum, hu]

theorem row_intersection_le_admissibleVectors :
    rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge ≤ AdmissibleVectors := by
  rintro w ⟨⟨hwA, hwB⟩, hwG⟩
  exact ⟨fun X hX => rowSpace_ortho (coefficient rowAB) hwA hX,
         fun X hX => rowSpace_ortho (coefficient rowBA) hwB hX,
         fun X hX => rowSpace_ortho (coefficient rowGauge16) hwG hX⟩

def free199List : List Nat := [5, 13, 15, 17, 21, 23, 24, 28, 29, 36, 37, 38, 39, 40, 41, 42, 43, 45, 47, 48, 52, 60, 64, 68, 71, 95, 99, 101, 103, 105, 107, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 142, 144, 146, 150, 152, 153, 154, 155, 157, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 177, 179, 181, 183, 185, 186, 187, 188, 192, 193, 194, 195, 196, 197, 198, 199, 201, 202, 203, 204, 208, 210, 212, 213, 214, 216, 217, 218, 219, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232, 233, 235, 237, 239, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 260, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 281, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 311, 313, 314, 315, 316, 317, 318, 320, 321, 322, 323, 324]

def free199Coord (t : Fin 199) : Coord :=
  ⟨listAt 0 free199List t.val % 325, Nat.mod_lt _ (by decide)⟩

private def checkDual199SubmatrixBool : Bool :=
  (free199List.length == 199) &&
  free199List.all (· < 325) &&
  (List.range 199).all (fun s =>
    let w := genTreeGet [] 8 dual199WsTree s
    w.all (fun cw => cw.1 < 325) &&
    (let wt := addScaledPairsNatTree (zeroIntTree 9) 1 w
     allIdx free199List (fun t fc =>
       intTreeGet 9 wt fc == (if s == t then 1 else 0))))

private theorem checkDual199SubmatrixBool_true : checkDual199SubmatrixBool = true := by
  decide +kernel

private theorem dual199_identity_submatrix (s t : Fin 199) :
    sparseNatAt (genTreeGet [] 8 dual199WsTree s.val) (free199Coord t).val =
      if s = t then 1 else 0 := by
  have hok := checkDual199SubmatrixBool_true
  unfold checkDual199SubmatrixBool at hok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨hflen, hf325⟩, hall⟩
  have ht : t.val < free199List.length := by rw [hflen]; exact t.isLt
  rcases hall s.val (List.mem_range.mpr s.isLt) with ⟨hw325, ht_all⟩
  have hst := allIdx_sound 0 free199List _ ht_all ht
  simp only [beq_iff_eq] at hst
  have hfc325 : listAt 0 free199List t.val < 325 := hf325 _ (listAt_mem 0 free199List ht)
  have hfc_eq : (free199Coord t).val = listAt 0 free199List t.val :=
    Nat.mod_eq_of_lt hfc325
  have hw512 : ∀ cw ∈ genTreeGet [] 8 dual199WsTree s.val, cw.1 < 512 :=
    fun cw hcw => Nat.lt_trans (hw325 cw hcw) (by decide)
  have hfc512 : listAt 0 free199List t.val < 512 := Nat.lt_trans hfc325 (by decide)
  rw [intTreeGet_addScaledPairsNatTree (zeroIntTree 9) 1 _
    (genTreeWF_const 0 9) hw512 hfc512, intTreeGet_zero, zero_add, one_mul] at hst
  rw [hfc_eq]
  change ((genTreeGet [] 8 dual199WsTree s.val).map
    (fun cw => if listAt 0 free199List t.val = cw.1 then cw.2 else 0)).sum = _
  rw [hst]
  have heq : (s.val = t.val) ↔ (s = t) :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  by_cases h : s = t <;> simp [heq, h]

theorem dual199_linearIndependent : LinearIndependent ℝ dual199Vec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg t
  have h := congrFun hg (free199Coord t)
  simp only [dual199Vec, sparseNatRealVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply, dual199_identity_submatrix] at h
  simpa [mul_ite] using h

theorem finrank_row_intersection_ge_199 :
    199 ≤ Module.finrank ℝ ↥(rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge) := by
  let wSub : Fin 199 → ↥(rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge) :=
    fun s => ⟨dual199Vec s, dual199_mem_row_intersection s⟩
  have hli : LinearIndependent ℝ wSub :=
    LinearIndependent.of_comp
      (Submodule.subtype (rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge))
      dual199_linearIndependent
  simpa using hli.fintype_card_le_finrank

theorem finrank_admissibleFunctionals_ge_199 :
    199 ≤ Module.finrank ℝ ↥AdmissibleFunctionals := by
  rw [← finrank_admissibleVectors_eq]
  exact le_trans finrank_row_intersection_ge_199
    (Submodule.finrank_mono row_intersection_le_admissibleVectors)

/-- **R8(b), exact solution-space dimension (`three_systems_solution_dim_126`)**:
the solutions of the three homogeneous systems (a) `AB`-causal, (b) `BA`-causal, and
(c) CPTP gauge in `ℝ^325` span a subspace of exact dimension `126`. -/
theorem three_systems_solution_dim_126 :
    Module.finrank ℝ ↥(solAB ⊔ solBA ⊔ solGauge) = 126 := by
  have hsum := finrank_sol_add_admissible_le_325
  have h1 := finrank_three_sol_ge_126
  have h2 := finrank_admissibleFunctionals_ge_199
  omega

/-- **R8(b), exact admissible-functional dimension (`admissible_functionals_dim_199`)**:
the linear functionals on `ℝ^325` satisfying properties (a)–(c) of Lemma 9
(`lem:exact-obstruction`) form a space of exact dimension `325 - 126 = 199`. -/
theorem admissible_functionals_dim_199 :
    Module.finrank ℝ ↥AdmissibleFunctionals = 199 := by
  have hsum := finrank_sol_add_admissible_le_325
  have h1 := finrank_three_sol_ge_126
  have h2 := finrank_admissibleFunctionals_ge_199
  omega

/-- The `AB`-causal and `BA`-causal solution spaces alone already span the `126`-dimensional
joint solution space (`solGauge ≤ solAB ⊔ solBA`). -/
theorem ab_ba_solution_dim_126 :
    Module.finrank ℝ ↥(solAB ⊔ solBA) = 126 ∧ solGauge ≤ solAB ⊔ solBA := by
  have hle : Module.finrank ℝ ↥(solAB ⊔ solBA) ≤
      Module.finrank ℝ ↥(solAB ⊔ solBA ⊔ solGauge) := Submodule.finrank_mono le_sup_left
  rw [three_systems_solution_dim_126] at hle
  have heq : Module.finrank ℝ ↥(solAB ⊔ solBA) = 126 :=
    le_antisymm hle finrank_ab_ba_ge_126
  have hsub : solAB ⊔ solBA = solAB ⊔ solBA ⊔ solGauge :=
    Submodule.eq_of_le_of_finrank_eq le_sup_left
      (heq.trans three_systems_solution_dim_126.symm)
  refine ⟨heq, ?_⟩
  calc
    solGauge ≤ solAB ⊔ solBA ⊔ solGauge := le_sup_right
    _ = solAB ⊔ solBA := hsub.symm

/-- Exact duality characterization (`sec:functional-proof`): a linear functional on `ℝ^325`
vanishes on `solAB`, `solBA`, and `solGauge` if and only if its coefficient vector lies in
`rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge`, which has exact dimension `199`. -/
theorem admissible_row_intersection_dim_199 :
    Module.finrank ℝ ↥(rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge) = 199 ∧
      AdmissibleVectors = rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge := by
  have hadm : Module.finrank ℝ ↥AdmissibleVectors = 199 := by
    rw [finrank_admissibleVectors_eq, admissible_functionals_dim_199]
  have hle : Module.finrank ℝ ↥(rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge) ≤ 199 := by
    rw [← hadm]
    exact Submodule.finrank_mono row_intersection_le_admissibleVectors
  have heq : Module.finrank ℝ ↥(rowSpaceAB ⊓ rowSpaceBA ⊓ rowSpaceGauge) = 199 :=
    le_antisymm hle finrank_row_intersection_ge_199
  exact ⟨heq, (Submodule.eq_of_le_of_finrank_eq row_intersection_le_admissibleVectors
    (heq.trans hadm.symm)).symm⟩

end
end ICO.ExactQubitNamedLemmas

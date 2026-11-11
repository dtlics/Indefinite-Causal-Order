import ICO.C6OperationalDecision
import ICO.C6PhysicalCosts

/-! # Section 5.4 & 5.5: The Label Cache, Proposition `prop:cache`, and Lemma `lem:reference-invariant`

This module provides the explicit standalone formalization of:
1. **Definition `def:cache` (`eq:c6-cache`, `eq:covariance`)**: the explicit one-call label-cache
   instrument `(ℛ_{Δ, ν}, ℬ_ν)` on counter `ν` and symmetric pair space
   `ℋ_ν = Sym^ν(ℂ^d ⊗ ℂ^d)`, its exact label-rotation covariance, complementary effect traces
   `Tr ℛ_{Δ, ν}(X) = Tr(P_ν X)` and `Tr ℬ_ν(X) = Tr((1 - P_ν) X)`, and semantic bridges to both
   `ICO.C6GradedCache` / `uniformRun` / `ICO.C6CacheOutputComparisonAfter.density` and direct
   unpadded `BudgetQueryTree.Tree` execution.
2. **Proposition `prop:cache` (`eq:eps-cache`)**: the single-experiment trace-distance bound
   `TD(ρ, ρ^{cache}) ≤ ε_rec + ε_2 + ε_3 + ε_4 + ε_5` at both the purified sequential protocol
   level and the adaptive `BudgetQueryTree.Tree` mixed-input level, for arbitrary relative basis
   `H : Matrix.unitaryGroup A ℂ` (covering `H = 1` for `(Δ_U, Δ_U)` and any `H` for `(Δ_U, Δ_{UH})`),
   together with 1-based index identities matching `eq:eps-cache` term for term.
3. **Lemma `lem:reference-invariant` and Reference-Cache Comparison**: common label-rotation
   invariance (`T^{⊗ ν}`) of the reference cache (with depolarizing `Ω` in place of `Δ` in every
   retrieval) at every step and every counter value `ν`, for both sequential runs and arbitrary
   adaptive `BudgetQueryTree.Tree` strategies with budget `q ≤ d`, plus the standalone distance
   bound `TD(ρ^{cache}, τ_ref) ≤ 3 q (q - 1) / d`.
-/

namespace ICO.C6LabelCache

open Matrix QIT MeasureTheory
open ICO.BudgetQueryTree ICO.BudgetContinuity ICO.C6Decision
open ICO.C6BosonicPolar ICO.C6CacheMap ICO.C6CacheDecode ICO.C6CacheQueryBound
open ICO.C6CacheReference ICO.C6CacheReferenceStep ICO.C6GradedCache
open ICO.C6SectorChannel ICO.MHSymmetric ICO.MHSectorCovariance
open ICO.MHCreationCovariance ICO.C6MatrixCovariance ICO.C6LabelSymmetry
open ICO.RecordingCopyIdentity ICO.InstrumentCompression ICO.SequentialIsometry
open ICO.ClassicalDilation (channelKraus channelKraus_map)
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048
set_option Elab.async false

@[simp] private theorem isometryChannel_apply {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (F : Matrix b a ℂ) (hF : F.conjTranspose * F = 1)
    (X : CMatrix a) :
    (isometryChannel F hF).map X = F * X * F.conjTranspose :=
  conjugate_apply F X

@[simp] private theorem star_if {α : Type*} [Star α] (P : Prop) [Decidable P] (x y : α) :
    star (if P then x else y) = if P then star x else star y :=
  apply_ite star P x y

@[simp] private theorem starRingEnd_if (P : Prop) [Decidable P] (x y : ℂ) :
    (starRingEnd ℂ) (if P then x else y) = if P then (starRingEnd ℂ) x else (starRingEnd ℂ) y :=
  apply_ite (starRingEnd ℂ) P x y

private theorem inclusion_sandwich_apply {I : Type*} [Fintype I] [DecidableEq I]
    {H : I → Type*} [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    (r s₁ s₂ : I) (Z : CMatrix (H r)) (c₁ : H s₁) (c₂ : H s₂) :
    (inclusion (H := H) r * Z * (inclusion (H := H) r).conjTranspose) ⟨s₁, c₁⟩ ⟨s₂, c₂⟩ =
      if h₁ : s₁ = r then
        if h₂ : s₂ = r then Z (h₁ ▸ c₁) (h₂ ▸ c₂) else 0
      else 0 := by
  by_cases h₁ : s₁ = r
  · subst s₁
    by_cases h₂ : s₂ = r
    · subst s₂
      simp [inclusion, basisEmbedding, Matrix.mul_apply,
        Matrix.submatrix_apply, Matrix.one_apply]
    · simp [inclusion, basisEmbedding, Matrix.mul_apply,
        Matrix.submatrix_apply, Matrix.one_apply, h₂, Ne.symm h₂]
  · simp [inclusion, basisEmbedding, Matrix.mul_apply,
      Matrix.submatrix_apply, Matrix.one_apply, h₁]

private theorem conjugate_inclusion_apply {I : Type*} [Fintype I] [DecidableEq I]
    {H : I → Type*} [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    (r s₁ s₂ : I) (Z : CMatrix (H r)) (c₁ : H s₁) (c₂ : H s₂) :
    (conjugate (inclusion (H := H) r) Z) ⟨s₁, c₁⟩ ⟨s₂, c₂⟩ =
      if h₁ : s₁ = r then
        if h₂ : s₂ = r then Z (h₁ ▸ c₁) (h₂ ▸ c₂) else 0
      else 0 := by
  rw [conjugate_apply]
  exact inclusion_sandwich_apply r s₁ s₂ Z c₁ c₂

private theorem conjugate_embed_apply {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    [Fintype M] [DecidableEq M] (Q : ℕ) (r s₁ s₂ : Fin (Q + 1))
    (Z : CMatrix (Cache (A := A) (M := M) r.val))
    (c₁ : Cache (A := A) (M := M) s₁.val) (c₂ : Cache (A := A) (M := M) s₂.val) :
    (conjugate (embed (A := A) (M := M) Q r) Z) ⟨s₁, c₁⟩ ⟨s₂, c₂⟩ =
      if h₁ : s₁ = r then
        if h₂ : s₂ = r then Z (h₁ ▸ c₁) (h₂ ▸ c₂) else 0
      else 0 := by
  rw [conjugate_apply, embed]
  exact inclusion_sandwich_apply (H := fun s : Fin (Q + 1) => Cache (A := A) (M := M) s.val)
    r s₁ s₂ Z c₁ c₂

/-! ## 1. Explicit Label Cache of Definition `def:cache` (`eq:c6-cache`, `eq:covariance`) -/

section DefCache

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The unnormalized bosonic pair-creation operator `E_ν` of Definition `def:cache`,
mapping query plus `ν` symmetric pairs (`Sector ν`) to query plus `ν + 1` symmetric pairs. -/
def rawPairCreator (ν : ℕ) : Matrix (Sector (A := A) (ν + 1)) (Sector (A := A) ν) ℂ :=
  ICO.MHERecordingApprox.symmetricInsertion (α := A) ν

/-- The polar-normalized bosonic pair-creation isometry `F_ν = E_ν (E_ν† E_ν)^{-1/2}`
of Definition `def:cache`. -/
def polarPairCreator (ν : ℕ) : Matrix (Sector (A := A) (ν + 1)) (Sector (A := A) ν) ℂ :=
  leftPolar (A := A) ν

theorem polarPairCreator_eq_polar (ν : ℕ) :
    polarPairCreator (A := A) ν = ICO.C6Polar.polar (rawPairCreator (A := A) ν) := rfl

theorem polarPairCreator_isometry [Nonempty A] {ν : ℕ} (hν : ν < Fintype.card A) :
    (polarPairCreator (A := A) ν).conjTranspose * polarPairCreator (A := A) ν = 1 :=
  leftPolar_isometry hν

/-- The stored-image recognition projector `P_ν` of Definition `def:cache`:
`P_0 = 0` and `P_{ν + 1} = F_ν F_ν†`. -/
def pairImageProj : (ν : ℕ) → CMatrix (Sector (A := A) ν)
  | 0 => 0
  | ν + 1 => polarPairCreator (A := A) ν * (polarPairCreator (A := A) ν).conjTranspose

@[simp] theorem pairImageProj_zero : pairImageProj (A := A) 0 = 0 := rfl

@[simp] theorem pairImageProj_succ (ν : ℕ) :
    pairImageProj (A := A) (ν + 1) =
      polarPairCreator (A := A) ν * (polarPairCreator (A := A) ν).conjTranspose := rfl

theorem pairImageProj_adjoint (ν : ℕ) :
    (pairImageProj (A := A) ν).conjTranspose = pairImageProj (A := A) ν := by
  cases ν with
  | zero => simp [pairImageProj]
  | succ m => exact image_adjoint (polarPairCreator m)

theorem pairImageProj_idem [Nonempty A] {ν : ℕ} (hν : ∀ m, ν = m + 1 → m < Fintype.card A) :
    pairImageProj (A := A) ν * pairImageProj (A := A) ν = pairImageProj (A := A) ν := by
  cases ν with
  | zero => simp [pairImageProj]
  | succ m =>
    exact image_sq (polarPairCreator m) (polarPairCreator_isometry (hν m rfl))

theorem complement_pairImageProj_idem [Nonempty A] {ν : ℕ}
    (hν : ∀ m, ν = m + 1 → m < Fintype.card A) :
    (1 - pairImageProj (A := A) ν) * (1 - pairImageProj (A := A) ν) =
      1 - pairImageProj (A := A) ν := by
  have h := pairImageProj_idem (A := A) hν
  noncomm_ring [h]

/-- Common label rotation `I_query ⊗ T^{⊗ ν}` on query plus `ν` stored pairs
(rotating the `ν` stored labels by `T` and leaving the query and the `ν` stored images fixed). -/
def storedSectorRotation (T : Matrix.unitaryGroup A ℂ) (ν : ℕ) :
    Matrix.unitaryGroup (Sector (A := A) ν) ℂ :=
  outputRotation T 1 ν

/-- Incoming query-plus-labels rotation `T_query ⊗ T^{⊗ ν}` on query plus `ν` stored pairs. -/
def inputSectorRotation (T : Matrix.unitaryGroup A ℂ) (ν : ℕ) :
    Matrix.unitaryGroup (Sector (A := A) ν) ℂ :=
  inputRotation T 1 ν

theorem storedSectorRotation_matrix (T : Matrix.unitaryGroup A ℂ) (ν : ℕ) :
    (storedSectorRotation T ν : CMatrix (Sector (A := A) ν)) =
      Matrix.kronecker (1 : CMatrix A) (occupationRotation (leftEdgeUnitary T 1) ν) := by
  simp [storedSectorRotation, outputRotation, tensorUnitary, symmetricRotation]

theorem inputSectorRotation_matrix (T : Matrix.unitaryGroup A ℂ) (ν : ℕ) :
    (inputSectorRotation T ν : CMatrix (Sector (A := A) ν)) =
      Matrix.kronecker (T : CMatrix A) (occupationRotation (leftEdgeUnitary T 1) ν) := by
  simp [inputSectorRotation, inputRotation, tensorUnitary, symmetricRotation]

/-- Exact label-rotation covariance `eq:covariance` of `F_ν`:
`(I ⊗ T^{⊗(ν+1)}) F_ν = F_ν (T ⊗ T^{⊗ ν})`. -/
theorem polarPairCreator_covariance [Nonempty A] (T : Matrix.unitaryGroup A ℂ) {ν : ℕ}
    (hν : ν < Fintype.card A) :
    (storedSectorRotation T (ν + 1) : CMatrix (Sector (A := A) (ν + 1))) *
        polarPairCreator (A := A) ν =
      polarPairCreator (A := A) ν *
        (inputSectorRotation T ν : CMatrix (Sector (A := A) ν)) :=
  leftPolar_covariance T 1 hν

/-- Consequence of `eq:covariance`: `P_ν` commutes with `I ⊗ T^{⊗ ν}` for all `ν ≤ d`. -/
theorem pairImageProj_commutes [Nonempty A] (T : Matrix.unitaryGroup A ℂ) {ν : ℕ}
    (hν : ∀ m, ν = m + 1 → m < Fintype.card A) :
    (storedSectorRotation T ν : CMatrix (Sector (A := A) ν)) * pairImageProj (A := A) ν =
      pairImageProj (A := A) ν * (storedSectorRotation T ν : CMatrix (Sector (A := A) ν)) := by
  cases ν with
  | zero => simp [pairImageProj]
  | succ m => exact leftPolar_image_covariance T 1 (hν m rfl)

/-- Dephasing channel `Δ_V` on the query system `A` in the orthonormal basis of columns of `V`. -/
def dephaseChannel (V : Matrix.unitaryGroup A ℂ) : Channel A A where
  map := MatrixMap.ofKraus (ICO.SwitchObservable.basisProjection (V : CMatrix A))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by
      simpa only [MatrixMap.krausAdjoint, Matrix.mul_one] using
        ICO.SwitchObservable.hidden_basis_kraus_complete (V : CMatrix A) V.property.1 V.property.2)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

/-- The retrieval operation `ℛ_{Δ, ν}` of `eq:c6-cache` in Definition `def:cache`:
zero at `ν = 0`, and `F_{ν-1} (Δ ⊗ id)(F_{ν-1}† X F_{ν-1}) F_{ν-1}†` for `ν ≥ 1`. -/
def labelCacheRetrieval (Δ : Channel A A) :
    (ν : ℕ) → MatrixMap (Sector (A := A) ν) (Sector (A := A) ν)
  | 0 => 0
  | m + 1 =>
    retrieval (polarPairCreator (A := A) m)
      (Δ.prod (Channel.idChannel (TensorPowerProfile (A × A) m)))

@[simp] theorem labelCacheRetrieval_zero (Δ : Channel A A) :
    labelCacheRetrieval (A := A) Δ 0 = 0 := rfl

theorem labelCacheRetrieval_succ_apply (Δ : Channel A A) (m : ℕ)
    (X : CMatrix (Sector (A := A) (m + 1))) :
    labelCacheRetrieval Δ (m + 1) X =
      polarPairCreator m *
        (Δ.prod (Channel.idChannel (TensorPowerProfile (A × A) m))).map
          ((polarPairCreator m).conjTranspose * X * polarPairCreator m) *
        (polarPairCreator m).conjTranspose :=
  retrieval_apply _ _ X

/-- Explicit maximally-mixed-label insertion `(I / d) ⊗ Tr_{query}(Y)` used in `ℬ_ν` (`eq:c6-cache`). -/
def freshLabelState (ν : ℕ) (Y : CMatrix (Sector (A := A) ν)) : CMatrix (Sector (A := A) ν) :=
  Matrix.kronecker (((Fintype.card A : ℂ)⁻¹) • (1 : CMatrix A)) (partialTraceA Y)

theorem freshLabelState_eq_withMemory [Nonempty A] (ν : ℕ) (Y : CMatrix (Sector (A := A) ν)) :
    freshLabelState (A := A) ν Y =
      (ICO.RecordingDepolarizing.withMemory (α := A)
        (μ := TensorPowerProfile (A × A) ν)).map Y := by
  ext ⟨a₁, p₁⟩ ⟨a₂, p₂⟩
  change _ = MatrixMap.kron (ICO.RecordingDepolarizing.depolarizing (α := A)).map
    (Channel.idChannel (TensorPowerProfile (A × A) ν)).map Y (a₁, p₁) (a₂, p₂)
  rw [MatrixMap.kron_idChannel_apply_slice, ICO.RecordingDepolarizing.depolarizing_entry]
  by_cases ha : a₁ = a₂
  · subst a₂
    simp [freshLabelState, partialTraceA, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.smul_apply, Matrix.trace, Matrix.diag_apply]
  · simp [freshLabelState, Matrix.kronecker, Matrix.kroneckerMap_apply, ha]

/-- The birth operation `ℬ_ν` of `eq:c6-cache` in Definition `def:cache`:
`F_ν [ (I / d) ⊗ Tr_{query}((I - P_ν) X (I - P_ν)) ] F_ν†`, raising the counter from `ν` to `ν + 1`. -/
def labelCacheBirth [Nonempty A] (ν : ℕ) :
    MatrixMap (Sector (A := A) ν) (Sector (A := A) (ν + 1)) :=
  (conjugate (polarPairCreator (A := A) ν)).comp
    ((ICO.RecordingDepolarizing.withMemory (α := A)
        (μ := TensorPowerProfile (A × A) ν)).map.comp
      (conjugate (1 - pairImageProj (A := A) ν)))

theorem labelCacheBirth_zero [Nonempty A] (X : CMatrix (Sector (A := A) 0)) :
    labelCacheBirth (A := A) 0 X =
      conjugate (polarPairCreator (A := A) 0)
        ((ICO.RecordingDepolarizing.withMemory (α := A)
            (μ := TensorPowerProfile (A × A) 0)).map X) := by
  have h : conjugate (1 - pairImageProj (A := A) 0) X = X := by
    simp [conjugate_apply, pairImageProj_zero]
  change conjugate (polarPairCreator (A := A) 0)
      ((ICO.RecordingDepolarizing.withMemory (α := A)
          (μ := TensorPowerProfile (A × A) 0)).map
        (conjugate (1 - pairImageProj (A := A) 0) X)) = _
  rw [h]

theorem labelCacheBirth_apply [Nonempty A] (ν : ℕ) (X : CMatrix (Sector (A := A) ν)) :
    labelCacheBirth (A := A) ν X =
      polarPairCreator ν *
        freshLabelState ν
          ((1 - pairImageProj ν) * X * (1 - pairImageProj ν)) *
        (polarPairCreator ν).conjTranspose := by
  simp only [labelCacheBirth, LinearMap.comp_apply, conjugate_apply,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, pairImageProj_adjoint,
    freshLabelState_eq_withMemory]

theorem labelCacheRetrieval_cp (Δ : Channel A A) (ν : ℕ) :
    MatrixMap.IsCompletelyPositive (labelCacheRetrieval (A := A) Δ ν) := by
  cases ν with
  | zero =>
    change (MatrixMap.choi (0 : MatrixMap (Sector (A := A) 0) (Sector (A := A) 0))).PosSemidef
    have h0 : MatrixMap.choi (0 : MatrixMap (Sector (A := A) 0) (Sector (A := A) 0)) = 0 := by
      ext i j; simp [MatrixMap.choi]
    rw [h0]
    exact Matrix.PosSemidef.zero
  | succ m =>
    exact retrieval_cp _ _

theorem labelCacheBirth_cp [Nonempty A] (ν : ℕ) :
    MatrixMap.IsCompletelyPositive (labelCacheBirth (A := A) ν) :=
  MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _)
    (MatrixMap.isCompletelyPositive_comp _ _
      (ICO.RecordingDepolarizing.withMemory (α := A)
        (μ := TensorPowerProfile (A × A) ν)).completelyPositive
      (conjugate_cp _))

/-- Complementary retrieval trace law `Tr ℛ_{Δ, ν}(X) = Tr(P_ν X)` of Definition `def:cache`. -/
theorem labelCacheRetrieval_trace [Nonempty A] (Δ : Channel A A) {ν : ℕ}
    (hν : ∀ m, ν = m + 1 → m < Fintype.card A)
    (X : CMatrix (Sector (A := A) ν)) :
    (labelCacheRetrieval Δ ν X).trace = (pairImageProj ν * X).trace := by
  cases ν with
  | zero => simp [labelCacheRetrieval, pairImageProj]
  | succ m =>
    exact retrieval_trace (polarPairCreator m) (polarPairCreator_isometry (hν m rfl)) _ X

/-- Complementary birth trace law `Tr ℬ_ν(X) = Tr((1 - P_ν) X)` of Definition `def:cache`. -/
theorem labelCacheBirth_trace [Nonempty A] {ν : ℕ} (hν : ν < Fintype.card A)
    (X : CMatrix (Sector (A := A) ν)) :
    (labelCacheBirth ν X).trace = ((1 - pairImageProj ν) * X).trace := by
  change (conjugate (polarPairCreator ν)
    ((ICO.RecordingDepolarizing.withMemory (α := A) (μ := TensorPowerProfile (A × A) ν)).map
      (conjugate (1 - pairImageProj ν) X))).trace = _
  rw [conjugate_trace_of_isometry _ (polarPairCreator_isometry hν),
    (ICO.RecordingDepolarizing.withMemory (α := A)
      (μ := TensorPowerProfile (A × A) ν)).tracePreserving,
    conjugate_trace, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    pairImageProj_adjoint, complement_pairImageProj_idem (fun m hm => by omega)]

/-- The hidden state space of the label cache up to budget `Q`:
a hidden classical counter `ν ∈ {0, ..., Q}` and a symmetric state in `ℋ_ν`. -/
abbrev CacheHidden (A : Type*) [Fintype A] [DecidableEq A] (Q : ℕ) :=
  Σ r : Fin (Q + 1), TensorPowerProfile (A × A) r.val

/-- The unique empty profile on `0` pairs. -/
def emptyPairProfile : TensorPowerProfile (A × A) 0 :=
  (ICO.MHOccupationCounts.occupationMultiset (a := A × A) 0).symm (Sym.mk 0 rfl)

theorem emptyPairProfile_unique (p q : TensorPowerProfile (A × A) 0) : p = q := by
  apply Subtype.ext
  funext z
  have hp := QIT.tensorPowerTypeProfile_sum_of_mem_profiles 0 p.property
  have hq := QIT.tensorPowerTypeProfile_sum_of_mem_profiles 0 q.property
  have hpz := Finset.single_le_sum (fun y _ => Nat.zero_le (p.val y)) (Finset.mem_univ z)
  have hqz := Finset.single_le_sum (fun y _ => Nat.zero_le (q.val y)) (Finset.mem_univ z)
  rw [hp] at hpz
  rw [hq] at hqz
  exact (Nat.eq_zero_of_le_zero hpz).trans (Nat.eq_zero_of_le_zero hqz).symm

/-- Initial hidden state `ν = 0` of the label cache (`|0, ∅⟩⟨0, ∅|`). -/
def cacheHiddenVacuum (Q : ℕ) : CacheHidden A Q :=
  ⟨⟨0, Nat.zero_lt_succ Q⟩, emptyPairProfile (A := A)⟩

def cacheHiddenInitialMatrix (Q : ℕ) : CMatrix (CacheHidden A Q) :=
  rankOneMatrix (fun r : CacheHidden A Q => if r = cacheHiddenVacuum (A := A) Q then 1 else 0)

theorem cacheHiddenInitialMatrix_pos (Q : ℕ) :
    (cacheHiddenInitialMatrix (A := A) Q).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem cacheHiddenInitialMatrix_trace (Q : ℕ) :
    (cacheHiddenInitialMatrix (A := A) Q).trace = 1 := by
  simp [cacheHiddenInitialMatrix, rankOneMatrix, Matrix.trace, Matrix.diag_apply,
    Matrix.vecMulVec_apply]

/-- Canonical reindexing between `(hidden cache, query)` and the counter-graded sector sum. -/
def hiddenQueryEquiv (Q : ℕ) :
    CacheHidden A Q × A ≃ Σ r : Fin (Q + 1), Sector (A := A) r.val where
  toFun x := ⟨x.1.1, (x.2, x.1.2)⟩
  invFun y := (⟨y.1, y.2.2⟩, y.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem hiddenQueryEquiv_apply (Q : ℕ) (x : CacheHidden A Q × A) :
    hiddenQueryEquiv (A := A) Q x = ⟨x.1.1, (x.2, x.1.2)⟩ := rfl

@[simp] theorem hiddenQueryEquiv_symm_apply (Q : ℕ)
    (y : Σ r : Fin (Q + 1), Sector (A := A) r.val) :
    (hiddenQueryEquiv (A := A) Q).symm y = (⟨y.1, y.2.2⟩, y.2.1) := rfl

/-- Local one-call CPTP channel from counter `r : Fin (Q + 1)` into the counter-graded cache,
implementing `ℛ_{Δ, ν} + ℬ_ν` of Definition `def:cache` for every active counter `ν < Q ≤ d`
(and extending by the identity on the terminal boundary `ν = Q`, which is never reached before
any of the at most `Q` calls of a budget-`Q` strategy). -/
def labelCacheSectorStep [Nonempty A] (Q : ℕ) (hQ : Q ≤ Fintype.card A) (Δ : Channel A A)
    (r : Fin (Q + 1)) :
    Channel (Sector (A := A) r.val) (Σ s : Fin (Q + 1) , Sector (A := A) s.val) :=
  if hr : r.val < Q then
    let sSucc : Fin (Q + 1) := ⟨r.val + 1, Nat.succ_lt_succ hr⟩
    let embSame := inclusion (H := fun s : Fin (Q + 1) => Sector (A := A) s.val) r
    let embNext := inclusion (H := fun s : Fin (Q + 1) => Sector (A := A) s.val) sSucc
    let map := (conjugate embSame).comp (labelCacheRetrieval (A := A) Δ r.val) +
      (conjugate embNext).comp (labelCacheBirth (A := A) r.val)
    have hcp : MatrixMap.IsCompletelyPositive map :=
      cp_add
        (MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _) (labelCacheRetrieval_cp Δ r.val))
        (MatrixMap.isCompletelyPositive_comp _ _ (conjugate_cp _) (labelCacheBirth_cp r.val))
    { map := map
      completelyPositive := hcp
      tracePreserving := by
        intro X
        have hlt : r.val < Fintype.card A := Nat.lt_of_lt_of_le hr hQ
        change ((conjugate embSame (labelCacheRetrieval Δ r.val X)) +
          (conjugate embNext (labelCacheBirth r.val X))).trace = X.trace
        rw [Matrix.trace_add,
          conjugate_trace_of_isometry embSame (inclusion_gram r),
          conjugate_trace_of_isometry embNext (inclusion_gram sSucc),
          labelCacheRetrieval_trace Δ (fun m hm => by omega),
          labelCacheBirth_trace hlt,
          ← Matrix.trace_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
      mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ hcp }
  else
    isometryChannel
      (inclusion (H := fun s : Fin (Q + 1) => Sector (A := A) s.val) r)
      (inclusion_gram r)

theorem labelCacheSectorStep_lt_map [Nonempty A] (Q : ℕ) (hQ : Q ≤ Fintype.card A)
    (Δ : Channel A A) (r : Fin (Q + 1)) (hr : r.val < Q)
    (Z : CMatrix (Sector (A := A) r.val)) :
    (labelCacheSectorStep (A := A) Q hQ Δ r).map Z =
      conjugate (inclusion (H := fun s : Fin (Q + 1) => Sector (A := A) s.val) r)
        (labelCacheRetrieval (A := A) Δ r.val Z) +
      conjugate (inclusion (H := fun s : Fin (Q + 1) => Sector (A := A) s.val)
          ⟨r.val + 1, Nat.succ_lt_succ hr⟩)
        (labelCacheBirth (A := A) r.val Z) := by
  simp only [labelCacheSectorStep, dif_pos hr, LinearMap.add_apply, LinearMap.comp_apply]

theorem labelCacheSectorStep_not_lt_map [Nonempty A] (Q : ℕ) (hQ : Q ≤ Fintype.card A)
    (Δ : Channel A A) (r : Fin (Q + 1)) (hr : ¬ r.val < Q)
    (Z : CMatrix (Sector (A := A) r.val)) :
    (labelCacheSectorStep (A := A) Q hQ Δ r).map Z =
      conjugate (inclusion (H := fun s : Fin (Q + 1) => Sector (A := A) s.val) r) Z := by
  simp only [labelCacheSectorStep, dif_neg hr, isometryChannel]

/-- Explicit one-call label-cache channel on `CacheHidden A Q × A` from Definition `def:cache`. -/
def labelCacheCall [Nonempty A] (Q : ℕ) (hQ : Q ≤ Fintype.card A) (Δ : Channel A A) :
    Channel (CacheHidden A Q × A) (CacheHidden A Q × A) :=
  (ICO.C6ReindexChannel.channel (hiddenQueryEquiv (A := A) Q)).comp
    ((sectorChannel (labelCacheSectorStep (A := A) Q hQ Δ)).comp
      (ICO.C6ReindexChannel.channel (hiddenQueryEquiv (A := A) Q).symm))

/-- Explicit one-call reference-cache channel on `CacheHidden A Q × A`
(replacing `Δ` by completely depolarizing `Ω` in every retrieval, as in Section 5.5). -/
def referenceCacheCall [Nonempty A] (Q : ℕ) (hQ : Q ≤ Fintype.card A) :
    Channel (CacheHidden A Q × A) (CacheHidden A Q × A) :=
  labelCacheCall (A := A) Q hQ (ICO.RecordingDepolarizing.depolarizing (α := A))

end DefCache

/-! ## 2. Semantic Bridges: `C6GradedCache`, `uniformRun`, and Direct `BudgetQueryTree` Execution -/

section Bridges

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Lift a matrix on `B → C` by tensoring on the left with `1_R` on a hidden register `R`. -/
def liftEnvOp (R : Type) [Fintype R] [DecidableEq R] {B C : Type}
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (W : Matrix C B ℂ) : Matrix (R × C) (R × B) ℂ :=
  Matrix.kronecker (1 : CMatrix R) W

theorem liftEnvOp_isometry (R : Type) [Fintype R] [DecidableEq R] {B C : Type}
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (W : Matrix C B ℂ) (hW : W.conjTranspose * W = 1) :
    (liftEnvOp R W).conjTranspose * liftEnvOp R W = 1 := by
  simp only [liftEnvOp, Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hW, Matrix.one_kronecker_one]

theorem liftEnvOp_mul (R : Type) [Fintype R] [DecidableEq R] {B C D : Type}
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (V : Matrix D C ℂ) (W : Matrix C B ℂ) :
    liftEnvOp R (V * W) = liftEnvOp R V * liftEnvOp R W := by
  simp only [liftEnvOp, Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Lift a stateful call `Ψ : Channel (R × A₀) (R × A₀)` across strategy memory `M`. -/
def liftEnvCall {R A₀ : Type} [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    (M : Type) [Fintype M] [DecidableEq M]
    (Ψ : Channel (R × A₀) (R × A₀)) : Channel (R × (A₀ × M)) (R × (A₀ × M)) :=
  (ICO.C6ReindexChannel.channel (Equiv.prodAssoc R A₀ M).symm).comp
    ((Ψ.prod (Channel.idChannel M)).comp
      (ICO.C6ReindexChannel.channel (Equiv.prodAssoc R A₀ M)))

theorem liftEnvCall_apply {R A₀ M : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M]
    (Ψ : Channel (R × A₀) (R × A₀)) (X : CMatrix (R × (A₀ × M)))
    (r₁ r₂ : R) (a₁ a₂ : A₀) (m₁ m₂ : M) :
    (liftEnvCall M Ψ).map X (r₁, (a₁, m₁)) (r₂, (a₂, m₂)) =
      Ψ.map (Matrix.of (fun u₁ u₂ : R × A₀ => X (u₁.1, (u₁.2, m₁)) (u₂.1, (u₂.2, m₂))))
        (r₁, a₁) (r₂, a₂) := by
  dsimp only [liftEnvCall, Channel.comp, LinearMap.comp_apply]
  rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply]
  change MatrixMap.kron Ψ.map (Channel.idChannel M).map
    (X.submatrix (Equiv.prodAssoc R A₀ M) (Equiv.prodAssoc R A₀ M))
    ((r₁, a₁), m₁) ((r₂, a₂), m₂) = _
  rw [MatrixMap.kron_idChannel_apply_slice]
  rfl

theorem liftEnvCall_labelCacheCall_apply [Nonempty A] {M : Type} [Fintype M] [DecidableEq M]
    (Q : ℕ) (hQ : Q ≤ Fintype.card A) (Δ : Channel A A)
    (X : CMatrix (CacheHidden A Q × (A × M)))
    (s₁ s₂ : Fin (Q + 1)) (p₁ : TensorPowerProfile (A × A) s₁.val)
    (p₂ : TensorPowerProfile (A × A) s₂.val) (a₁ a₂ : A) (m₁ m₂ : M) :
    (liftEnvCall M (labelCacheCall (A := A) Q hQ Δ)).map X
      (⟨s₁, p₁⟩, (a₁, m₁)) (⟨s₂, p₂⟩, (a₂, m₂)) =
      ((sectorChannel (labelCacheSectorStep (A := A) Q hQ Δ)).map
        (Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          X (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂)))))
        ⟨s₁, (a₁, p₁)⟩ ⟨s₂, (a₂, p₂)⟩ := by
  rw [liftEnvCall_apply]
  dsimp only [labelCacheCall, Channel.comp, LinearMap.comp_apply]
  rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply, Matrix.submatrix_apply,
    hiddenQueryEquiv_apply, hiddenQueryEquiv_apply]
  suffices hmat :
      (Matrix.of (fun u₁ u₂ : CacheHidden A Q × A =>
        X (u₁.1, (u₁.2, m₁)) (u₂.1, (u₂.2, m₂)))).submatrix
        (hiddenQueryEquiv (A := A) Q).symm (hiddenQueryEquiv (A := A) Q).symm =
      Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
        X (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂))) by
    rw [hmat]
  ext ⟨t₁, a₁', p₁'⟩ ⟨t₂, a₂', p₂'⟩
  rfl

/-- Lift a single Kraus operator on `R × A₀` across strategy memory `M`. -/
def liftEnvKraus {R A₀ : Type} [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    (M : Type) [Fintype M] [DecidableEq M]
    (G : CMatrix (R × A₀)) : CMatrix (R × (A₀ × M)) :=
  (Matrix.kronecker G (1 : CMatrix M)).submatrix
    (Equiv.prodAssoc R A₀ M).symm (Equiv.prodAssoc R A₀ M).symm

theorem liftEnvCall_kraus_apply {R A₀ M : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M]
    (Ψ : Channel (R × A₀) (R × A₀)) (X : CMatrix (R × (A₀ × M))) :
    (liftEnvCall M Ψ).map X =
      ∑ k, liftEnvKraus M (ICO.BudgetPreparation.kraus Ψ k) * X *
        (liftEnvKraus M (ICO.BudgetPreparation.kraus Ψ k)).conjTranspose := by
  have hk : Ψ.map = MatrixMap.ofKraus (ICO.BudgetPreparation.kraus Ψ) :=
    (ICO.BudgetPreparation.kraus_map Ψ).symm
  apply Matrix.ext
  rintro ⟨r₁, a₁, m₁⟩ ⟨r₂, a₂, m₂⟩
  rw [liftEnvCall_apply, hk]
  simp only [liftEnvKraus, MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.conjTranspose_submatrix, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Equiv.prodAssoc_symm_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  apply Finset.sum_congr rfl
  intro r'' _
  apply Finset.sum_congr rfl
  intro a'' _
  rw [Finset.sum_eq_single m₂]
  · simp only [ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro r' _
    apply Finset.sum_congr rfl
    intro a' _
    rw [Finset.sum_eq_single m₁]
    · simp
    · intro m' _ hne; rw [if_neg hne.symm]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro m' _ hne; simp [hne]
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- Direct operational execution of an adaptive `BudgetQueryTree.Tree` against any stateful
environment `(Φ₀, Φ₁)` with hidden state space `R`, tracing out `R` at termination. -/
def runStatefulTree {R A₀ M O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀))
    {q : ℕ} {B : Type} [Fintype B] [DecidableEq B]
    (tree : BudgetQueryTree.Tree (A₀ × M) O q B) : MatrixMap (R × B) O := by
  induction tree with
  | stop after => exact after.map.comp (Channel.traceOutLeft R _).map
  | query b _ ih => exact ih.comp (liftEnvCall M (if b then Φ₁ else Φ₀)).map
  | node I _ ih => exact ∑ l, (ih l).comp (singleMap (liftEnvOp R (I.op l)))

@[simp] private theorem runStatefulTree_stop {R A₀ M O B : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀))
    {q : ℕ} (after : Channel B O) :
    runStatefulTree (M := M) Φ₀ Φ₁ (BudgetQueryTree.Tree.stop (q := q) after) =
      after.map.comp (Channel.traceOutLeft R B).map := rfl

@[simp] private theorem runStatefulTree_query {R A₀ M O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀)) {q : ℕ} (b : Bool)
    (after : BudgetQueryTree.Tree (A₀ × M) O q (A₀ × M)) :
    runStatefulTree Φ₀ Φ₁ (BudgetQueryTree.Tree.query b after) =
      (runStatefulTree Φ₀ Φ₁ after).comp (liftEnvCall M (if b then Φ₁ else Φ₀)).map := rfl

@[simp] private theorem runStatefulTree_node {R A₀ M O B C J : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]
    (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀)) {q : ℕ}
    (I : Instrument B C J) (next : J → BudgetQueryTree.Tree (A₀ × M) O q C) :
    runStatefulTree Φ₀ Φ₁ (BudgetQueryTree.Tree.node I next) =
      ∑ l, (runStatefulTree Φ₀ Φ₁ (next l)).comp (singleMap (liftEnvOp R (I.op l))) := rfl

/-- Direct unpadded output state `ρ^{cache}` of an adaptive strategy `tree` with mixed input `ρ`
interacting with the explicit label cache of Definition `def:cache`, using `Δ_I` for calls to box `A`
(`b = false`) and `Δ_H` for calls to box `B` (`b = true`). -/
def treeLabelCacheDensity [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A × M) O q B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ) (hqd : q ≤ Fintype.card A) : CMatrix O :=
  runStatefulTree
    (labelCacheCall (A := A) q hqd (dephaseChannel 1))
    (labelCacheCall (A := A) q hqd (dephaseChannel H))
    tree
    (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) q) ρ.matrix)

/-- Same-basis specialization (`H = 1`, `Δ_I` on both boxes) of `treeLabelCacheDensity`. -/
def treeSameLabelCacheDensity [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A × M) O q B) (ρ : State B)
    (hqd : q ≤ Fintype.card A) : CMatrix O :=
  treeLabelCacheDensity tree ρ 1 hqd

/-- Direct unpadded output state `τ_q` of an adaptive strategy `tree` with mixed input `ρ`
interacting with the basis-independent reference cache (depolarizing `Ω` in every retrieval). -/
def treeReferenceCacheDensity [Nonempty A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A × M) O q B) (ρ : State B)
    (hqd : q ≤ Fintype.card A) : CMatrix O :=
  runStatefulTree
    (referenceCacheCall (A := A) q hqd)
    (referenceCacheCall (A := A) q hqd)
    tree
    (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) q) ρ.matrix)

section ExactGradedBridge

variable [Nontrivial A] {M : Type} [Fintype M] [DecidableEq M]

/-- Canonical equivalence between `CacheHidden A Q × (A × M)` and `Graded (A := A) Q M`. -/
def hiddenGradedEquiv (Q : ℕ) (M : Type) :
    CacheHidden A Q × (A × M) ≃ Graded (A := A) Q M where
  toFun x := ⟨x.1.1, ((x.2.1, x.1.2), x.2.2)⟩
  invFun y := (⟨y.1, y.2.1.2⟩, (y.2.1.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Nontrivial A] in
@[simp] theorem hiddenGradedEquiv_apply (Q : ℕ) (M : Type)
    (x : CacheHidden A Q × (A × M)) :
    hiddenGradedEquiv (A := A) Q M x = ⟨x.1.1, ((x.2.1, x.1.2), x.2.2)⟩ := rfl

omit [Nontrivial A] in
@[simp] theorem hiddenGradedEquiv_symm_apply (Q : ℕ) (M : Type)
    (y : Graded (A := A) Q M) :
    (hiddenGradedEquiv (A := A) Q M).symm y = (⟨y.1, y.2.1.2⟩, (y.2.1.1, y.2.2)) := rfl

theorem dephaseChannel_prod_eq_basisChannel (V : Matrix.unitaryGroup A ℂ) (n : ℕ)
    (X : CMatrix (Cache (A := A) (M := M) n)) :
    (basisChannel V n).map X =
      MatrixMap.kron
        ((dephaseChannel V).prod (Channel.idChannel (TensorPowerProfile (A × A) n))).map
        (Channel.idChannel M).map X := by
  rw [ICO.C6CacheReference.basis_apply]
  ext ⟨⟨a₁, p₁⟩, m₁⟩ ⟨⟨a₂, p₂⟩, m₂⟩
  rw [MatrixMap.kron_idChannel_apply_slice]
  change (ICO.C6BasisDephase.basisMap V (ICO.C6MemoryDecode.cacheHead n X))
      (a₁, (p₁, m₁)) (a₂, (p₂, m₂)) =
    MatrixMap.kron (dephaseChannel V).map
      (Channel.idChannel (TensorPowerProfile (A × A) n)).map
      (fun s₁ s₂ => X (s₁, m₁) (s₂, m₂)) (a₁, p₁) (a₂, p₂)
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp only [ICO.C6BasisDephase.basisMap, ICO.AllChannelDilation.oracleMap,
    dephaseChannel, MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ICO.C6MemoryDecode.cacheHead, Matrix.submatrix_apply,
    Equiv.prodAssoc_symm_apply, Prod.mk.injEq, ite_and]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  apply Finset.sum_congr rfl
  intro y₂ _
  rw [Finset.sum_eq_single p₂]
  · simp only [ite_true]
    rw [Finset.sum_eq_single m₂]
    · simp only [ite_true]
      congr 1
      apply Finset.sum_congr rfl
      intro y₁ _
      rw [Finset.sum_eq_single p₁]
      · simp only [ite_true]
        rw [Finset.sum_eq_single m₁]
        · simp
        · intro m' _ hne; rw [if_neg hne.symm]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · intro p' _ hne; simp [hne.symm]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intro m' _ hne; simp [hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro p' _ hne; simp [hne]
  · intro h; exact (h (Finset.mem_univ _)).elim

theorem uniformChannel_eq_withMemory_kron (n : ℕ)
    (X : CMatrix (Cache (A := A) (M := M) n)) :
    (uniformChannel n).map X =
      MatrixMap.kron
        (ICO.RecordingDepolarizing.withMemory (α := A)
          (μ := TensorPowerProfile (A × A) n)).map
        (Channel.idChannel M).map X := by
  rw [ICO.C6CacheReference.uniform_apply]
  ext ⟨⟨a₁, p₁⟩, m₁⟩ ⟨⟨a₂, p₂⟩, m₂⟩
  rw [MatrixMap.kron_idChannel_apply_slice]
  change MatrixMap.kron (ICO.RecordingDepolarizing.depolarizing (α := A)).map
      (Channel.idChannel (SideMemory (A := A) (M := M) n)).map
      (ICO.C6MemoryDecode.cacheHead n X) (a₁, (p₁, m₁)) (a₂, (p₂, m₂)) =
    MatrixMap.kron (ICO.RecordingDepolarizing.depolarizing (α := A)).map
      (Channel.idChannel (TensorPowerProfile (A × A) n)).map
      (fun s₁ s₂ => X (s₁, m₁) (s₂, m₂)) (a₁, p₁) (a₂, p₂)
  rw [MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_apply_slice]
  rfl

omit [Nontrivial A] in
private theorem kronecker_one_conjugate_eq_kron {S₁ S₂ : Type}
    [Fintype S₁] [DecidableEq S₁] [Fintype S₂] [DecidableEq S₂]
    (F : Matrix S₂ S₁ ℂ) (Y : CMatrix (S₁ × M)) :
    Matrix.kronecker F (1 : CMatrix M) * Y *
      (Matrix.kronecker F (1 : CMatrix M)).conjTranspose =
    MatrixMap.kron (conjugate F) (Channel.idChannel M).map Y := by
  ext ⟨s₁, m₁⟩ ⟨s₂, m₂⟩
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp only [conjugate_apply, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  apply Finset.sum_congr rfl
  intro t₂ _
  rw [Finset.sum_eq_single m₂]
  · simp only [ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro t₁ _
    rw [Finset.sum_eq_single m₁]
    · simp
    · intro m' _ hne; rw [if_neg hne.symm]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro m' _ hne; simp [hne]
  · intro h; exact (h (Finset.mem_univ _)).elim

omit [Nontrivial A] in
theorem memoryPolar_conjugate_eq_kron (n : ℕ)
    (Y : CMatrix (Cache (A := A) (M := M) n)) :
    memoryPolar n * Y * (memoryPolar n).conjTranspose =
      MatrixMap.kron (conjugate (polarPairCreator (A := A) n))
        (Channel.idChannel M).map Y :=
  kronecker_one_conjugate_eq_kron (polarPairCreator (A := A) n) Y

omit [Nontrivial A] in
theorem memoryPolar_adj_conjugate_eq_kron (n : ℕ)
    (X : CMatrix (Cache (A := A) (M := M) (n + 1))) :
    (memoryPolar n).conjTranspose * X * memoryPolar n =
      MatrixMap.kron (conjugate (polarPairCreator (A := A) n).conjTranspose)
        (Channel.idChannel M).map X := by
  have hadj : (memoryPolar (A := A) (M := M) n).conjTranspose =
      Matrix.kronecker (polarPairCreator (A := A) n).conjTranspose (1 : CMatrix M) := by
    simp [memoryPolar, polarPairCreator, Matrix.kronecker, Matrix.conjTranspose_kronecker]
  have h := kronecker_one_conjugate_eq_kron (M := M) (polarPairCreator (A := A) n).conjTranspose X
  rw [← hadj, Matrix.conjTranspose_conjTranspose] at h
  exact h

omit [Nontrivial A] in
theorem complement_memoryPolar_eq_kron (n : ℕ)
    (X : CMatrix (Cache (A := A) (M := M) (n + 1))) :
    (1 - image (memoryPolar n)) * X * (1 - image (memoryPolar n)) =
      MatrixMap.kron (conjugate (1 - pairImageProj (A := A) (n + 1)))
        (Channel.idChannel M).map X := by
  have himg : image (memoryPolar (A := A) (M := M) n) =
      Matrix.kronecker (pairImageProj (A := A) (n + 1)) (1 : CMatrix M) := by
    simp only [image, memoryPolar, polarPairCreator, pairImageProj_succ, Matrix.kronecker,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have hsub : (1 : CMatrix (Cache (A := A) (M := M) (n + 1))) - image (memoryPolar n) =
      Matrix.kronecker (1 - pairImageProj (A := A) (n + 1)) (1 : CMatrix M) := by
    rw [himg, ← Matrix.one_kronecker_one (α := ℂ) (m := Sector (A := A) (n + 1)) (n := M)]
    ext ⟨s₁, m₁⟩ ⟨s₂, m₂⟩
    by_cases hs : s₁ = s₂ <;> by_cases hm : m₁ = m₂ <;>
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hs, hm]
  have hadj : (Matrix.kronecker (1 - pairImageProj (A := A) (n + 1)) (1 : CMatrix M)).conjTranspose =
      Matrix.kronecker (1 - pairImageProj (A := A) (n + 1)) (1 : CMatrix M) := by
    simp [Matrix.kronecker, Matrix.conjTranspose_kronecker]
  rw [hsub, ← kronecker_one_conjugate_eq_kron (1 - pairImageProj (A := A) (n + 1)) X, hadj]

private theorem localQuery_zero_map (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A)
    (D : Option (Matrix.unitaryGroup A ℂ)) (hr : 0 < Q + 1)
    (B : CMatrix (Cache (A := A) (M := M) 0)) :
    (ICO.C6GradedCache.localQuery (A := A) (M := M) Q hpos hQ D ⟨0, hr⟩).map B =
      conjugate (embed (A := A) (M := M) Q ⟨1, Nat.succ_lt_succ hpos⟩)
        (conjugate (memoryPolar (A := A) (M := M) 0)
          ((uniformChannel (A := A) (M := M) 0).map B)) := by
  dsimp only [ICO.C6GradedCache.localQuery, vacuumStep, Channel.comp,
    LinearMap.comp_apply, isometryChannel]
  rfl

/-- Lifting the explicit Definition `def:cache` one-call channel `labelCacheCall` across `M`
and reindexing to `Graded Q M` agrees identically with `ICO.C6GradedCache.query Q hpos hQ (some V)`. -/
theorem labelCacheCall_eq_gradedQuery (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A)
    (V : Matrix.unitaryGroup A ℂ) :
    (ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M).symm).comp
      ((liftEnvCall M (labelCacheCall (A := A) Q hQ.le (dephaseChannel V))).comp
        (ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M))) =
      ICO.C6GradedCache.query (A := A) (M := M) Q hpos hQ (some V) := by
  apply ICO.BudgetPreparation.channel_eq_of_map_eq
  ext X ⟨s₁, ⟨a₁, p₁⟩, m₁⟩ ⟨s₂, ⟨a₂, p₂⟩, m₂⟩
  have hL :
      (((ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M).symm).comp
        ((liftEnvCall M (labelCacheCall (A := A) Q hQ.le (dephaseChannel V))).comp
          (ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M)))).map X)
        ⟨s₁, (a₁, p₁), m₁⟩ ⟨s₂, (a₂, p₂), m₂⟩ =
      ((sectorChannel (labelCacheSectorStep (A := A) Q hQ.le (dephaseChannel V))).map
        (Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          X ⟨u₁.1, u₁.2, m₁⟩ ⟨u₂.1, u₂.2, m₂⟩))) ⟨s₁, (a₁, p₁)⟩ ⟨s₂, (a₂, p₂)⟩ := by
    dsimp only [Channel.comp, LinearMap.comp_apply]
    rw [ICO.C6ReindexChannel.apply, Matrix.submatrix_apply,
      hiddenGradedEquiv_symm_apply, hiddenGradedEquiv_symm_apply,
      liftEnvCall_labelCacheCall_apply]
    suffices hmat :
        Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          ((ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M)).map X)
            (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂))) =
        Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          X ⟨u₁.1, u₁.2, m₁⟩ ⟨u₂.1, u₂.2, m₂⟩) by
      rw [hmat]
    rw [ICO.C6ReindexChannel.apply]
    ext ⟨t₁, a₁', p₁'⟩ ⟨t₂, a₂', p₂'⟩
    rfl
  rw [hL, sector_apply, ICO.C6GradedCache.query, sector_apply]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  have hslice :
      (inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r).conjTranspose *
        Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          X ⟨u₁.1, u₁.2, m₁⟩ ⟨u₂.1, u₂.2, m₂⟩) *
        inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r =
      Matrix.of (fun x₁ x₂ => (((inclusion (H := fun t : Fin (Q + 1) => Cache (A := A) (M := M) t.val) r).conjTranspose * X *
        inclusion (H := fun t : Fin (Q + 1) => Cache (A := A) (M := M) t.val) r :
          CMatrix (Cache (A := A) (M := M) r.val)) (x₁, m₁) (x₂, m₂))) := by
    rw [inclusion, inclusion, basisEmbedding_compression, basisEmbedding_compression]
    rfl
  rw [hslice]
  rcases r with ⟨r, hr⟩
  set B : CMatrix (Cache (A := A) (M := M) r) :=
    (inclusion (H := fun t : Fin (Q + 1) => Cache (A := A) (M := M) t.val) ⟨r, hr⟩).conjTranspose *
      X * inclusion (H := fun t : Fin (Q + 1) => Cache (A := A) (M := M) t.val) ⟨r, hr⟩
  cases r with
  | zero =>
    rw [labelCacheSectorStep_lt_map Q hQ.le _ ⟨0, hr⟩ hpos, localQuery_zero_map]
    simp only [labelCacheRetrieval_zero, LinearMap.zero_apply, map_zero, zero_add]
    have hb : labelCacheBirth (A := A) 0 (Matrix.of (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂))) =
        Matrix.of (fun y₁ y₂ => (conjugate (memoryPolar (A := A) (M := M) 0)
          ((uniformChannel (A := A) (M := M) 0).map B)) (y₁, m₁) (y₂, m₂)) := by
      ext y₁ y₂
      rw [labelCacheBirth_zero]
      simp only [Matrix.of_apply]
      rw [conjugate_apply (memoryPolar (A := A) (M := M) 0),
        memoryPolar_conjugate_eq_kron, uniformChannel_eq_withMemory_kron]
      simp_rw [MatrixMap.kron_idChannel_apply_slice]
      suffices hin :
          Matrix.of (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂)) =
          (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂)) by
        rw [hin]
      rfl
    rw [hb, conjugate_inclusion_apply, conjugate_embed_apply]
    by_cases h1 : s₁ = ⟨1, Nat.succ_lt_succ hpos⟩
    · subst s₁
      by_cases h2 : s₂ = ⟨1, Nat.succ_lt_succ hpos⟩
      · subst s₂; rfl
      · simp [h2]
    · simp [h1]
  | succ n =>
    by_cases hn : n + 1 < Q
    · simp only [labelCacheSectorStep, ICO.C6GradedCache.localQuery, dif_pos hn, cacheStep,
        cacheChannel, Channel.comp, isometryChannel, LinearMap.add_apply, LinearMap.comp_apply]
      rw [ICO.C6GradedCacheReference.sum_cache_apply]
      have hret : labelCacheRetrieval (A := A) (dephaseChannel V) (n + 1)
          (Matrix.of (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂))) =
          Matrix.of (fun y₁ y₂ => (retrieval (memoryPolar n) (basisChannel V n) B)
            (y₁, m₁) (y₂, m₂)) := by
        ext y₁ y₂
        simp only [Matrix.of_apply]
        rw [retrieval_apply, memoryPolar_conjugate_eq_kron, dephaseChannel_prod_eq_basisChannel,
          memoryPolar_adj_conjugate_eq_kron]
        simp_rw [MatrixMap.kron_idChannel_apply_slice]
        rfl
      have hbir : labelCacheBirth (A := A) (n + 1)
          (Matrix.of (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂))) =
          Matrix.of (fun y₁ y₂ => (birth (memoryPolar n) (memoryPolar (n + 1)) (uniformChannel (n + 1)) B)
            (y₁, m₁) (y₂, m₂)) := by
        ext y₁ y₂
        simp only [Matrix.of_apply]
        rw [birth_apply, memoryPolar_conjugate_eq_kron, uniformChannel_eq_withMemory_kron,
          complement_memoryPolar_eq_kron]
        simp_rw [MatrixMap.kron_idChannel_apply_slice]
        rfl
      rw [hret, hbir, Matrix.add_apply, Matrix.add_apply]
      congr 1
      · rw [conjugate_inclusion_apply, conjugate_embed_apply]
        by_cases h1 : s₁ = ⟨n + 1, hr⟩
        · subst s₁
          by_cases h2 : s₂ = ⟨n + 1, hr⟩
          · subst s₂; rfl
          · simp [h2]
        · simp [h1]
      · rw [conjugate_inclusion_apply, conjugate_embed_apply]
        by_cases h1 : s₁ = ⟨n + 2, Nat.succ_lt_succ hn⟩
        · subst s₁
          by_cases h2 : s₂ = ⟨n + 2, Nat.succ_lt_succ hn⟩
          · subst s₂; rfl
          · simp [h2]
        · simp [h1]
    · simp only [labelCacheSectorStep, ICO.C6GradedCache.localQuery, dif_neg hn, isometryChannel]
      rw [conjugate_inclusion_apply, conjugate_embed_apply]
      by_cases h1 : s₁ = ⟨n + 1, hr⟩
      · subst s₁
        by_cases h2 : s₂ = ⟨n + 1, hr⟩
        · subst s₂; rfl
        · simp [h2]
      · simp [h1]

/-- Lifting `referenceCacheCall` across `M` and reindexing to `Graded Q M` agrees identically
with `ICO.C6GradedCache.query Q hpos hQ none`. -/
theorem referenceCacheCall_eq_gradedQuery (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A) :
    (ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M).symm).comp
      ((liftEnvCall M (referenceCacheCall (A := A) Q hQ.le)).comp
        (ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M))) =
      ICO.C6GradedCache.query (A := A) (M := M) Q hpos hQ none := by
  apply ICO.BudgetPreparation.channel_eq_of_map_eq
  ext X ⟨s₁, ⟨a₁, p₁⟩, m₁⟩ ⟨s₂, ⟨a₂, p₂⟩, m₂⟩
  have hL :
      (((ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M).symm).comp
        ((liftEnvCall M (referenceCacheCall (A := A) Q hQ.le)).comp
          (ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M)))).map X)
        ⟨s₁, (a₁, p₁), m₁⟩ ⟨s₂, (a₂, p₂), m₂⟩ =
      ((sectorChannel (labelCacheSectorStep (A := A) Q hQ.le
          (ICO.RecordingDepolarizing.depolarizing (α := A)))).map
        (Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          X ⟨u₁.1, u₁.2, m₁⟩ ⟨u₂.1, u₂.2, m₂⟩))) ⟨s₁, (a₁, p₁)⟩ ⟨s₂, (a₂, p₂)⟩ := by
    dsimp only [Channel.comp, LinearMap.comp_apply, referenceCacheCall]
    rw [ICO.C6ReindexChannel.apply, Matrix.submatrix_apply,
      hiddenGradedEquiv_symm_apply, hiddenGradedEquiv_symm_apply,
      liftEnvCall_labelCacheCall_apply]
    suffices hmat :
        Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          ((ICO.C6ReindexChannel.channel (hiddenGradedEquiv (A := A) Q M)).map X)
            (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂))) =
        Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          X ⟨u₁.1, u₁.2, m₁⟩ ⟨u₂.1, u₂.2, m₂⟩) by
      rw [hmat]
    rw [ICO.C6ReindexChannel.apply]
    ext ⟨t₁, a₁', p₁'⟩ ⟨t₂, a₂', p₂'⟩
    rfl
  rw [hL, sector_apply, ICO.C6GradedCache.query, sector_apply]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  have hslice :
      (inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r).conjTranspose *
        Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          X ⟨u₁.1, u₁.2, m₁⟩ ⟨u₂.1, u₂.2, m₂⟩) *
        inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r =
      Matrix.of (fun x₁ x₂ => (((inclusion (H := fun t : Fin (Q + 1) => Cache (A := A) (M := M) t.val) r).conjTranspose * X *
        inclusion (H := fun t : Fin (Q + 1) => Cache (A := A) (M := M) t.val) r :
          CMatrix (Cache (A := A) (M := M) r.val)) (x₁, m₁) (x₂, m₂))) := by
    rw [inclusion, inclusion, basisEmbedding_compression, basisEmbedding_compression]
    rfl
  rw [hslice]
  rcases r with ⟨r, hr⟩
  set B : CMatrix (Cache (A := A) (M := M) r) :=
    (inclusion (H := fun t : Fin (Q + 1) => Cache (A := A) (M := M) t.val) ⟨r, hr⟩).conjTranspose *
      X * inclusion (H := fun t : Fin (Q + 1) => Cache (A := A) (M := M) t.val) ⟨r, hr⟩
  cases r with
  | zero =>
    rw [labelCacheSectorStep_lt_map Q hQ.le _ ⟨0, hr⟩ hpos, localQuery_zero_map]
    simp only [labelCacheRetrieval_zero, LinearMap.zero_apply, map_zero, zero_add]
    have hb : labelCacheBirth (A := A) 0 (Matrix.of (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂))) =
        Matrix.of (fun y₁ y₂ => (conjugate (memoryPolar (A := A) (M := M) 0)
          ((uniformChannel (A := A) (M := M) 0).map B)) (y₁, m₁) (y₂, m₂)) := by
      ext y₁ y₂
      rw [labelCacheBirth_zero]
      simp only [Matrix.of_apply]
      rw [conjugate_apply (memoryPolar (A := A) (M := M) 0),
        memoryPolar_conjugate_eq_kron, uniformChannel_eq_withMemory_kron]
      simp_rw [MatrixMap.kron_idChannel_apply_slice]
      suffices hin :
          Matrix.of (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂)) =
          (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂)) by
        rw [hin]
      rfl
    rw [hb, conjugate_inclusion_apply, conjugate_embed_apply]
    by_cases h1 : s₁ = ⟨1, Nat.succ_lt_succ hpos⟩
    · subst s₁
      by_cases h2 : s₂ = ⟨1, Nat.succ_lt_succ hpos⟩
      · subst s₂; rfl
      · simp [h2]
    · simp [h1]
  | succ n =>
    by_cases hn : n + 1 < Q
    · simp only [labelCacheSectorStep, ICO.C6GradedCache.localQuery, dif_pos hn, referenceStep,
        cacheChannel, Channel.comp, isometryChannel, LinearMap.add_apply, LinearMap.comp_apply]
      rw [ICO.C6GradedCacheReference.sum_cache_apply]
      have hret : labelCacheRetrieval (A := A)
          (ICO.RecordingDepolarizing.depolarizing (α := A)) (n + 1)
          (Matrix.of (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂))) =
          Matrix.of (fun y₁ y₂ => (retrieval (memoryPolar n) (uniformChannel n) B)
            (y₁, m₁) (y₂, m₂)) := by
        ext y₁ y₂
        simp only [Matrix.of_apply]
        rw [retrieval_apply, memoryPolar_conjugate_eq_kron, uniformChannel_eq_withMemory_kron,
          memoryPolar_adj_conjugate_eq_kron]
        simp_rw [MatrixMap.kron_idChannel_apply_slice]
        rfl
      have hbir : labelCacheBirth (A := A) (n + 1)
          (Matrix.of (fun x₁ x₂ => B (x₁, m₁) (x₂, m₂))) =
          Matrix.of (fun y₁ y₂ => (birth (memoryPolar n) (memoryPolar (n + 1)) (uniformChannel (n + 1)) B)
            (y₁, m₁) (y₂, m₂)) := by
        ext y₁ y₂
        simp only [Matrix.of_apply]
        rw [birth_apply, memoryPolar_conjugate_eq_kron, uniformChannel_eq_withMemory_kron,
          complement_memoryPolar_eq_kron]
        simp_rw [MatrixMap.kron_idChannel_apply_slice]
        rfl
      rw [hret, hbir, Matrix.add_apply, Matrix.add_apply]
      congr 1
      · rw [conjugate_inclusion_apply, conjugate_embed_apply]
        by_cases h1 : s₁ = ⟨n + 1, hr⟩
        · subst s₁
          by_cases h2 : s₂ = ⟨n + 1, hr⟩
          · subst s₂; rfl
          · simp [h2]
        · simp [h1]
      · rw [conjugate_inclusion_apply, conjugate_embed_apply]
        by_cases h1 : s₁ = ⟨n + 2, Nat.succ_lt_succ hn⟩
        · subst s₁
          by_cases h2 : s₂ = ⟨n + 2, Nat.succ_lt_succ hn⟩
          · subst s₂; rfl
          · simp [h2]
        · simp [h1]
    · simp only [labelCacheSectorStep, ICO.C6GradedCache.localQuery, dif_neg hn, isometryChannel]
      rw [conjugate_inclusion_apply, conjugate_embed_apply]
      by_cases h1 : s₁ = ⟨n + 1, hr⟩
      · subst s₁
        by_cases h2 : s₂ = ⟨n + 1, hr⟩
        · subst s₂; rfl
        · simp [h2]
      · simp [h1]

end ExactGradedBridge

/-! ### Tagged Choice-Channel, `uniformRun`, and Sequential Protocol Bridges -/

section StatefulCompiler

/-- Pinch the `Bool` box-selection tag and apply `Φ₀` (`b = false`) or `Φ₁` (`b = true`) on `R × A₀`. -/
def choiceEnvCall {R A₀ : Type} [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀)) :
    Channel (R × (A₀ × Bool)) (R × (A₀ × Bool)) :=
  let e : R × (A₀ × Bool) ≃ Σ _ : Bool, R × A₀ :=
    { toFun := fun x => ⟨x.2.2, (x.1, x.2.1)⟩
      invFun := fun y => (y.2.1, (y.2.2, y.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let loc : Bool → Channel (R × A₀) (Σ _ : Bool, R × A₀) := fun b =>
    (isometryChannel (inclusion (H := fun _ : Bool => R × A₀) b) (inclusion_gram b)).comp
      (if b then Φ₁ else Φ₀)
  (ICO.C6ReindexChannel.channel e).comp
    ((sectorChannel loc).comp (ICO.C6ReindexChannel.channel e.symm))

/-- Explicit entrywise formula for `choiceEnvCall`, keeping `Φ₀` and `Φ₁` opaque. -/
theorem choiceEnvCall_apply {R A₀ : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀))
    (Y : CMatrix (R × (A₀ × Bool))) (r₁ r₂ : R) (a₁ a₂ : A₀) (b₁ b₂ : Bool) :
    (choiceEnvCall Φ₀ Φ₁).map Y (r₁, (a₁, b₁)) (r₂, (a₂, b₂)) =
      if b₁ = b₂ then
        ((if b₁ then Φ₁ else Φ₀).map
          (Matrix.of (fun u₁ u₂ : R × A₀ => Y (u₁.1, (u₁.2, b₁)) (u₂.1, (u₂.2, b₁)))))
          (r₁, a₁) (r₂, a₂)
      else 0 := by
  simp only [choiceEnvCall, Channel.comp, LinearMap.comp_apply, ICO.C6ReindexChannel.apply,
    sector_apply, isometryChannel_apply, Matrix.submatrix_apply, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk, Fintype.sum_bool, Matrix.add_apply]
  rw [inclusion_sandwich_apply, inclusion_sandwich_apply]
  have hcomp (b : Bool) :
      (inclusion (H := fun _ : Bool => R × A₀) b).conjTranspose *
        Y.submatrix (fun y : Σ _ : Bool, R × A₀ => (y.2.1, y.2.2, y.1))
          (fun y : Σ _ : Bool, R × A₀ => (y.2.1, y.2.2, y.1)) *
        inclusion b =
      Matrix.of (fun u₁ u₂ : R × A₀ => Y (u₁.1, (u₁.2, b)) (u₂.1, (u₂.2, b))) := by
    rw [inclusion, basisEmbedding_compression]
    rfl
  rw [hcomp true, hcomp false]
  cases b₁ <;> cases b₂ <;> simp

/-- Canonical equivalence between `CacheHidden A Q × ((A × Bool) × M)` and `Graded Q (Bool × M)`. -/
def hiddenChoiceGradedEquiv [Nontrivial A] (Q : ℕ) (M : Type) :
    CacheHidden A Q × ((A × Bool) × M) ≃ Graded (A := A) Q (Bool × M) where
  toFun x := ⟨x.1.1, ((x.2.1.1, x.1.2), (x.2.1.2, x.2.2))⟩
  invFun y := (⟨y.1, y.2.1.2⟩, ((y.2.1.1, y.2.2.1), y.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem hiddenChoiceGradedEquiv_symm_apply [Nontrivial A] (Q : ℕ) (M : Type)
    (y : Graded (A := A) Q (Bool × M)) :
    (hiddenChoiceGradedEquiv (A := A) Q M).symm y =
      (⟨y.1, y.2.1.2⟩, ((y.2.1.1, y.2.2.1), y.2.2.2)) := rfl

private theorem choiceEmbed_sandwich_apply [Nontrivial A] {M : Type} [Fintype M] [DecidableEq M]
    (Q : ℕ) (b b₁ b₂ : Bool) (Z : CMatrix (Graded (A := A) Q M))
    (s₁ s₂ : Fin (Q + 1)) (c₁ : Sector (A := A) s₁.val) (c₂ : Sector (A := A) s₂.val)
    (m₁ m₂ : M) :
    ((ICO.C6ChoiceCache.choiceEmbed (A := A) (M := M) Q b * Z *
      (ICO.C6ChoiceCache.choiceEmbed (A := A) (M := M) Q b).conjTranspose :
        CMatrix (Graded (A := A) Q (Bool × M)))
        ⟨s₁, c₁, (b₁, m₁)⟩ ⟨s₂, c₂, (b₂, m₂)⟩) =
      if b₁ = b ∧ b₂ = b then Z ⟨s₁, c₁, m₁⟩ ⟨s₂, c₂, m₂⟩ else 0 := by
  have he : ICO.C6ChoiceCache.choiceEmbed (A := A) (M := M) Q b =
      (inclusion (H := fun _ : Bool => Graded (A := A) Q M) b).submatrix
        (ICO.C6ChoiceCache.choiceEquiv Q).symm (Equiv.refl _) := by
    ext o x
    simp only [ICO.C6ChoiceCache.choiceEmbed, ICO.C6ChoiceCache.choiceInjection,
      inclusion, basisEmbedding, Matrix.submatrix_apply, Matrix.one_apply, Equiv.refl_apply]
    by_cases h : o = (ICO.C6ChoiceCache.choiceEquiv Q) ⟨b, x⟩
    · subst h; simp
    · have h2 : (ICO.C6ChoiceCache.choiceEquiv Q).symm o ≠ ⟨b, x⟩ :=
        fun hs => h ((ICO.C6ChoiceCache.choiceEquiv Q).symm_apply_eq.mp hs)
      simp [h, h2]
  have hs : ((inclusion (H := fun _ : Bool => Graded (A := A) Q M) b * Z *
        (inclusion (H := fun _ : Bool => Graded (A := A) Q M) b).conjTranspose).submatrix
          (ICO.C6ChoiceCache.choiceEquiv Q).symm (ICO.C6ChoiceCache.choiceEquiv Q).symm) =
      ICO.C6ChoiceCache.choiceEmbed (A := A) (M := M) Q b * Z *
        (ICO.C6ChoiceCache.choiceEmbed (A := A) (M := M) Q b).conjTranspose := by
    rw [← Matrix.submatrix_mul_equiv (inclusion b * Z) (inclusion b).conjTranspose
        (ICO.C6ChoiceCache.choiceEquiv Q).symm (Equiv.refl _)
        (ICO.C6ChoiceCache.choiceEquiv Q).symm,
      ← Matrix.submatrix_mul_equiv (inclusion b) Z
        (ICO.C6ChoiceCache.choiceEquiv Q).symm (Equiv.refl _) (Equiv.refl _),
      ← Matrix.conjTranspose_submatrix, ← he]
    rfl
  rw [← hs, Matrix.submatrix_apply]
  dsimp only [ICO.C6ChoiceCache.choiceEquiv, Equiv.coe_fn_symm_mk]
  rw [inclusion_sandwich_apply]
  by_cases h1 : b₁ = b
  · subst b₁
    by_cases h2 : b₂ = b
    · subst b₂; simp
    · simp [h2]
  · simp [h1]

theorem choiceEnvCall_eq_choiceCache [Nontrivial A] {M : Type} [Fintype M] [DecidableEq M]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A) (H : Matrix.unitaryGroup A ℂ) :
    (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q M).symm).comp
      ((liftEnvCall M (choiceEnvCall
          (labelCacheCall (A := A) Q hQ.le (dephaseChannel 1))
          (labelCacheCall (A := A) Q hQ.le (dephaseChannel H)))).comp
        (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q M))) =
      ICO.C6ChoiceCache.query (A := A) (M := M) Q hpos hQ
        (fun b => some (ICO.C6ActualResidualWeight.outcomeBasis H b)) := by
  apply ICO.BudgetPreparation.channel_eq_of_map_eq
  ext X ⟨s₁, ⟨a₁, p₁⟩, ⟨b₁, m₁⟩⟩ ⟨s₂, ⟨a₂, p₂⟩, ⟨b₂, m₂⟩⟩
  rw [ICO.C6ChoiceCache.query_apply]
  simp only [Matrix.sum_apply, Fintype.sum_bool, choiceEmbed_sandwich_apply]
  have h1 := congrArg (fun C => C.map (ICO.C6ChoiceCache.choiceBlock Q false X)
      ⟨s₁, (a₁, p₁), m₁⟩ ⟨s₂, (a₂, p₂), m₂⟩)
    (labelCacheCall_eq_gradedQuery (A := A) (M := M) Q hpos hQ 1)
  have hH := congrArg (fun C => C.map (ICO.C6ChoiceCache.choiceBlock Q true X)
      ⟨s₁, (a₁, p₁), m₁⟩ ⟨s₂, (a₂, p₂), m₂⟩)
    (labelCacheCall_eq_gradedQuery (A := A) (M := M) Q hpos hQ H)
  dsimp only [Channel.comp, LinearMap.comp_apply] at h1 hH ⊢
  rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply, Matrix.submatrix_apply,
    hiddenGradedEquiv_symm_apply, hiddenGradedEquiv_symm_apply, liftEnvCall_apply] at h1 hH
  rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply, Matrix.submatrix_apply,
    hiddenChoiceGradedEquiv_symm_apply, hiddenChoiceGradedEquiv_symm_apply,
    liftEnvCall_apply, choiceEnvCall_apply]
  have hm (b : Bool) :
      Matrix.of (fun u₁ u₂ : CacheHidden A Q × A =>
        (Matrix.of (fun v₁ v₂ : CacheHidden A Q × (A × Bool) =>
          (X.submatrix (hiddenChoiceGradedEquiv (A := A) Q M)
            (hiddenChoiceGradedEquiv (A := A) Q M))
            (v₁.1, (v₁.2, m₁)) (v₂.1, (v₂.2, m₂))))
          (u₁.1, (u₁.2, b)) (u₂.1, (u₂.2, b))) =
      Matrix.of (fun u₁ u₂ : CacheHidden A Q × A =>
        ((ICO.C6ChoiceCache.choiceBlock Q b X).submatrix
          (hiddenGradedEquiv (A := A) Q M) (hiddenGradedEquiv (A := A) Q M))
          (u₁.1, (u₁.2, m₁)) (u₂.1, (u₂.2, m₂))) := by
    ext ⟨⟨t₁, p₁'⟩, a₁'⟩ ⟨⟨t₂, p₂'⟩, a₂'⟩
    rfl
  cases b₁ <;> cases b₂
  · simp only [ite_true, Bool.false_eq_true, ite_false, and_self, zero_add,
      ICO.C6ActualResidualWeight.outcomeBasis]
    rw [hm false]
    exact h1
  · simp
  · simp
  · simp only [ite_true, Bool.true_eq_false, ite_false, and_self, add_zero,
      ICO.C6ActualResidualWeight.outcomeBasis]
    rw [hm true]
    exact hH

theorem choiceEnvCall_eq_referenceChoiceCache [Nontrivial A] {M : Type} [Fintype M] [DecidableEq M]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A) :
    (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q M).symm).comp
      ((liftEnvCall M (choiceEnvCall
          (referenceCacheCall (A := A) Q hQ.le)
          (referenceCacheCall (A := A) Q hQ.le))).comp
        (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q M))) =
      ICO.C6ChoiceCache.query (A := A) (M := M) Q hpos hQ (fun _ => none) := by
  apply ICO.BudgetPreparation.channel_eq_of_map_eq
  ext X ⟨s₁, ⟨a₁, p₁⟩, ⟨b₁, m₁⟩⟩ ⟨s₂, ⟨a₂, p₂⟩, ⟨b₂, m₂⟩⟩
  rw [ICO.C6ChoiceCache.query_apply]
  simp only [Matrix.sum_apply, Fintype.sum_bool, choiceEmbed_sandwich_apply]
  have hRef0 := congrArg (fun C => C.map (ICO.C6ChoiceCache.choiceBlock Q false X)
      ⟨s₁, (a₁, p₁), m₁⟩ ⟨s₂, (a₂, p₂), m₂⟩)
    (referenceCacheCall_eq_gradedQuery (A := A) (M := M) Q hpos hQ)
  have hRef1 := congrArg (fun C => C.map (ICO.C6ChoiceCache.choiceBlock Q true X)
      ⟨s₁, (a₁, p₁), m₁⟩ ⟨s₂, (a₂, p₂), m₂⟩)
    (referenceCacheCall_eq_gradedQuery (A := A) (M := M) Q hpos hQ)
  dsimp only [Channel.comp, LinearMap.comp_apply] at hRef0 hRef1 ⊢
  rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply, Matrix.submatrix_apply,
    hiddenGradedEquiv_symm_apply, hiddenGradedEquiv_symm_apply, liftEnvCall_apply] at hRef0 hRef1
  rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply, Matrix.submatrix_apply,
    hiddenChoiceGradedEquiv_symm_apply, hiddenChoiceGradedEquiv_symm_apply,
    liftEnvCall_apply, choiceEnvCall_apply]
  have hm (b : Bool) :
      Matrix.of (fun u₁ u₂ : CacheHidden A Q × A =>
        (Matrix.of (fun v₁ v₂ : CacheHidden A Q × (A × Bool) =>
          (X.submatrix (hiddenChoiceGradedEquiv (A := A) Q M)
            (hiddenChoiceGradedEquiv (A := A) Q M))
            (v₁.1, (v₁.2, m₁)) (v₂.1, (v₂.2, m₂))))
          (u₁.1, (u₁.2, b)) (u₂.1, (u₂.2, b))) =
      Matrix.of (fun u₁ u₂ : CacheHidden A Q × A =>
        ((ICO.C6ChoiceCache.choiceBlock Q b X).submatrix
          (hiddenGradedEquiv (A := A) Q M) (hiddenGradedEquiv (A := A) Q M))
          (u₁.1, (u₁.2, m₁)) (u₂.1, (u₂.2, m₂))) := by
    ext ⟨⟨t₁, p₁'⟩, a₁'⟩ ⟨⟨t₂, p₂'⟩, a₂'⟩
    rfl
  cases b₁ <;> cases b₂
  · simp only [ite_true, Bool.false_eq_true, ite_false, and_self, zero_add]
    rw [hm false]
    exact hRef0
  · simp
  · simp
  · simp only [ite_true, Bool.true_eq_false, ite_false, and_self, add_zero]
    rw [hm true]
    exact hRef1

theorem liftEnvOp_submatrix_eq_known [Nontrivial A] {M N : Type}
    [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (Q : ℕ) (K : Matrix (A × (Bool × N)) (A × (Bool × M)) ℂ) :
    (liftEnvOp (CacheHidden A Q)
      (K.submatrix (Equiv.prodAssoc A Bool N) (Equiv.prodAssoc A Bool M))).submatrix
      (hiddenChoiceGradedEquiv (A := A) Q N).symm
      (hiddenChoiceGradedEquiv (A := A) Q M).symm =
    known Q K := by
  ext ⟨r₁, ⟨a₁, p₁⟩, ⟨b₁, m₁⟩⟩ ⟨r₂, ⟨a₂, p₂⟩, ⟨b₂, m₂⟩⟩
  by_cases hr : r₁ = r₂
  · subst r₂
    simp [liftEnvOp, hiddenChoiceGradedEquiv, known, ICO.C6CacheKnownOperation.externalLift,
      ICO.C6CacheKnownOperation.externalEquiv, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
  · rw [known, Matrix.blockDiagonal'_apply_ne _ _ _ hr]
    simp [liftEnvOp, hiddenChoiceGradedEquiv, Matrix.kronecker, Matrix.kroneckerMap_apply, hr]

/-- Explicit one-step stage of a hidden-cache choice call followed by known strategy operation `K`. -/
def statefulChoiceStep {R : Type} [Fintype R] [DecidableEq R] {M N : Type}
    [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (Φ₀ Φ₁ : Channel (R × A) (R × A))
    (K : Matrix (A × (Bool × N)) (A × (Bool × M)) ℂ) (hK : K.conjTranspose * K = 1) :
    Channel (R × ((A × Bool) × M)) (R × ((A × Bool) × N)) :=
  let K' : Matrix ((A × Bool) × N) ((A × Bool) × M) ℂ :=
    K.submatrix (Equiv.prodAssoc A Bool N) (Equiv.prodAssoc A Bool M)
  have hK' : K'.conjTranspose * K' = 1 := by
    dsimp [K']
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc A Bool N), hK]
    exact Matrix.submatrix_one_equiv _
  (isometryChannel (liftEnvOp R K') (liftEnvOp_isometry R K' hK')).comp
    (liftEnvCall M (choiceEnvCall Φ₀ Φ₁))

/-- Explicit Definition `def:cache` stages on `Graded (A := A) Q (Bool × μ i)`. -/
def labelCacheStages [Nontrivial A] {μ : ℕ → Type} [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    (Q : ℕ) (hQ : Q ≤ Fintype.card A) (H : Matrix.unitaryGroup A ℂ)
    (K : ∀ i, Matrix (A × (Bool × μ (i + 1))) (A × (Bool × μ i)) ℂ)
    (hK : ∀ i, (K i).conjTranspose * K i = 1) (i : ℕ) :
    Channel (Graded (A := A) Q (Bool × μ i)) (Graded (A := A) Q (Bool × μ (i + 1))) :=
  (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q (μ (i + 1))).symm).comp
    ((statefulChoiceStep
        (labelCacheCall (A := A) Q hQ (dephaseChannel 1))
        (labelCacheCall (A := A) Q hQ (dephaseChannel H))
        (K i) (hK i)).comp
      (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q (μ i))))

/-- Explicit reference-cache stages on `Graded (A := A) Q (Bool × μ i)`. -/
def referenceCacheStages [Nontrivial A]
    {μ : ℕ → Type} [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    (Q : ℕ) (hQ : Q ≤ Fintype.card A)
    (K : ∀ i, Matrix (A × (Bool × μ (i + 1))) (A × (Bool × μ i)) ℂ)
    (hK : ∀ i, (K i).conjTranspose * K i = 1) (i : ℕ) :
    Channel (Graded (A := A) Q (Bool × μ i)) (Graded (A := A) Q (Bool × μ (i + 1))) :=
  (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q (μ (i + 1))).symm).comp
    ((statefulChoiceStep
        (referenceCacheCall (A := A) Q hQ)
        (referenceCacheCall (A := A) Q hQ)
        (K i) (hK i)).comp
      (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q (μ i))))

theorem statefulChoiceStep_label_eq_choiceStep [Nontrivial A] {M N : Type}
    [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A) (H : Matrix.unitaryGroup A ℂ)
    (K : Matrix (A × (Bool × N)) (A × (Bool × M)) ℂ) (hK : K.conjTranspose * K = 1) :
    (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q N).symm).comp
      ((statefulChoiceStep
          (labelCacheCall (A := A) Q hQ.le (dephaseChannel 1))
          (labelCacheCall (A := A) Q hQ.le (dephaseChannel H))
          K hK).comp
        (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q M))) =
      ICO.C6CacheTrajectoryAfter.choiceStep Q hpos hQ
        (fun b => some (ICO.C6ActualResidualWeight.outcomeBasis H b)) K hK := by
  apply ICO.BudgetPreparation.channel_eq_of_map_eq
  ext X o p
  have hq := congrArg (fun C => C.map X)
    (choiceEnvCall_eq_choiceCache (A := A) (M := M) Q hpos hQ H)
  simp only [Channel.comp, LinearMap.comp_apply, ICO.C6ReindexChannel.apply] at hq
  simp only [statefulChoiceStep, ICO.C6CacheTrajectoryAfter.choiceStep,
    Channel.comp, LinearMap.comp_apply, ICO.C6ReindexChannel.apply, isometryChannel_apply]
  set Z := (liftEnvCall M (choiceEnvCall
    (labelCacheCall (A := A) Q hQ.le (dephaseChannel 1))
    (labelCacheCall (A := A) Q hQ.le (dephaseChannel H)))).map
      (X.submatrix (hiddenChoiceGradedEquiv (A := A) Q M)
        (hiddenChoiceGradedEquiv (A := A) Q M))
  have hZ : Z = ((ICO.C6ChoiceCache.query (A := A) (M := M) Q hpos hQ
      (fun b => some (ICO.C6ActualResidualWeight.outcomeBasis H b))).map X).submatrix
        (hiddenChoiceGradedEquiv (A := A) Q M)
        (hiddenChoiceGradedEquiv (A := A) Q M) := by
    rw [← hq]
    simp [Matrix.submatrix_submatrix]
  rw [hZ, ← Matrix.submatrix_mul_equiv _ _ _
    (hiddenChoiceGradedEquiv (A := A) Q M).symm,
    ← Matrix.submatrix_mul_equiv _ _ _
    (hiddenChoiceGradedEquiv (A := A) Q M).symm]
  simp only [← Matrix.conjTranspose_submatrix, Matrix.submatrix_submatrix,
    Function.comp_def, Equiv.apply_symm_apply, liftEnvOp_submatrix_eq_known]
  rfl

theorem statefulChoiceStep_reference_eq_choiceStep [Nontrivial A] {M N : Type}
    [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A)
    (K : Matrix (A × (Bool × N)) (A × (Bool × M)) ℂ) (hK : K.conjTranspose * K = 1) :
    (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q N).symm).comp
      ((statefulChoiceStep
          (referenceCacheCall (A := A) Q hQ.le)
          (referenceCacheCall (A := A) Q hQ.le)
          K hK).comp
        (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q M))) =
      ICO.C6CacheTrajectoryAfter.choiceStep Q hpos hQ (fun _ => none) K hK := by
  apply ICO.BudgetPreparation.channel_eq_of_map_eq
  ext X o p
  have hq := congrArg (fun C => C.map X)
    (choiceEnvCall_eq_referenceChoiceCache (A := A) (M := M) Q hpos hQ)
  simp only [Channel.comp, LinearMap.comp_apply, ICO.C6ReindexChannel.apply] at hq
  simp only [statefulChoiceStep, ICO.C6CacheTrajectoryAfter.choiceStep,
    Channel.comp, LinearMap.comp_apply, ICO.C6ReindexChannel.apply, isometryChannel_apply]
  set Z := (liftEnvCall M (choiceEnvCall
    (referenceCacheCall (A := A) Q hQ.le)
    (referenceCacheCall (A := A) Q hQ.le))).map
      (X.submatrix (hiddenChoiceGradedEquiv (A := A) Q M)
        (hiddenChoiceGradedEquiv (A := A) Q M))
  have hZ : Z = ((ICO.C6ChoiceCache.query (A := A) (M := M) Q hpos hQ
      (fun _ => none)).map X).submatrix
        (hiddenChoiceGradedEquiv (A := A) Q M)
        (hiddenChoiceGradedEquiv (A := A) Q M) := by
    rw [← hq]
    simp [Matrix.submatrix_submatrix]
  rw [hZ, ← Matrix.submatrix_mul_equiv _ _ _
    (hiddenChoiceGradedEquiv (A := A) Q M).symm,
    ← Matrix.submatrix_mul_equiv _ _ _
    (hiddenChoiceGradedEquiv (A := A) Q M).symm]
  simp only [← Matrix.conjTranspose_submatrix, Matrix.submatrix_submatrix,
    Function.comp_def, Equiv.apply_symm_apply, liftEnvOp_submatrix_eq_known]
  rfl

theorem labelCacheStages_eq_afterStages [Nontrivial A]
    {μ : ℕ → Type} [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A) (H : Matrix.unitaryGroup A ℂ)
    (K : ∀ i, Matrix (A × (Bool × μ (i + 1))) (A × (Bool × μ i)) ℂ)
    (hK : ∀ i, (K i).conjTranspose * K i = 1) (i : ℕ) :
    labelCacheStages Q hQ.le H K hK i =
      ICO.C6CacheTrajectoryAfter.stages Q hpos hQ
        (fun _ b => some (ICO.C6ActualResidualWeight.outcomeBasis H b)) K hK i :=
  statefulChoiceStep_label_eq_choiceStep Q hpos hQ H (K i) (hK i)

theorem referenceCacheStages_eq_afterStages [Nontrivial A]
    {μ : ℕ → Type} [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A)
    (K : ∀ i, Matrix (A × (Bool × μ (i + 1))) (A × (Bool × μ i)) ℂ)
    (hK : ∀ i, (K i).conjTranspose * K i = 1) (i : ℕ) :
    referenceCacheStages Q hQ.le K hK i =
      ICO.C6CacheTrajectoryAfter.stages Q hpos hQ (fun _ _ => none) K hK i :=
  statefulChoiceStep_reference_eq_choiceStep Q hpos hQ (K i) (hK i)

/-- **Definition `def:cache` bridge (`uniformRun_eq_labelCache_run`)**:
erasing the private outcome/birth-flag history from `uniformRun` equals running the strategy
directly against the explicit label-cache device `labelCacheStages` of Definition `def:cache`. -/
theorem uniformRun_eq_labelCache_run [Nontrivial A]
    {μ : ℕ → Type} [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A) (H : Matrix.unitaryGroup A ℂ)
    (K : ∀ i, Matrix (A × (Bool × μ (i + 1))) (A × (Bool × μ i)) ℂ)
    (hK : ∀ i, (K i).conjTranspose * K i = 1)
    (X : CMatrix (Cache (A := A) (M := Bool × μ 0) 0)) (n : ℕ) :
    ICO.C6ClassicalHistoryRun.erase (H := fun i => Graded (A := A) Q (Bool × μ i)) n
        (ICO.C6WeightedHistory.uniformRun Q hpos hQ H K X n) =
      ICO.C6ChannelTrajectory.run (labelCacheStages Q hQ.le H K hK)
        (ICO.C6CacheTrajectory.initial Q X) n := by
  rw [ICO.C6WeightedHistory.uniform_erase Q hpos hQ H K hK X n]
  have hs : ICO.C6CacheTrajectoryAfter.stages Q hpos hQ
      (fun _ b => some (ICO.C6ActualResidualWeight.outcomeBasis H b)) K hK =
      labelCacheStages Q hQ.le H K hK :=
    funext (fun i => (labelCacheStages_eq_afterStages Q hpos hQ H K hK i).symm)
  rw [hs]

/-- Sequential-protocol output state `ρ^{cache}` produced by running `tail` against the explicit
Definition `def:cache` label cache and tracing out the cache register. -/
def protocolLabelCacheDensity [Nontrivial A] {M O : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A × Bool) × M → ℂ)
    (n : ℕ) (hQ : n ≤ Fintype.card A) :
    CMatrix ((A × Bool) × tail.tailMemory n) :=
  (ICO.C6CacheVisibleOutput.output n).map
    (ICO.C6ChannelTrajectory.run
      (labelCacheStages n hQ H
        (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
        (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i)))
      (ICO.C6CacheTrajectory.initial n (ICO.C6RawWeightedEndpoint.cacheInput tail v)) n)

/-- Sequential-protocol output state `τ_n` produced by running `tail` against the explicit
basis-independent reference cache (`Ω` in every retrieval) and tracing out the cache register. -/
def protocolReferenceCacheDensity [Nontrivial A] {M O : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (v : (A × Bool) × M → ℂ) (n : ℕ) (hQ : n ≤ Fintype.card A) :
    CMatrix ((A × Bool) × tail.tailMemory n) :=
  (ICO.C6CacheVisibleOutput.output n).map
    (ICO.C6ChannelTrajectory.run
      (referenceCacheStages n hQ
        (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
        (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i)))
      (ICO.C6CacheTrajectory.initial n (ICO.C6RawWeightedEndpoint.cacheInput tail v)) n)

/-- **Definition `def:cache` bridge (`cacheDensity_eq_labelCache_output`)**:
`ICO.C6CacheOutputComparisonAfter.density` (the uniform cache output `ρ^{cache}`) equals
`protocolLabelCacheDensity`, the output of running `tail` against the explicit label cache of
Definition `def:cache`. -/
theorem cacheDensity_eq_labelCache_output [Nontrivial A] {M O : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A × Bool) × M → ℂ)
    (n : ℕ) (hpos : 0 < n) (hQ : n < Fintype.card A) :
    ICO.C6CacheOutputComparisonAfter.density n hpos hQ
        (fun _ b => some (ICO.C6ActualResidualWeight.outcomeBasis H b))
        (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
        (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i))
        (ICO.C6RawWeightedEndpoint.cacheInput tail v) n
        (ICO.C6CacheVisibleOutput.output n).map =
      protocolLabelCacheDensity tail H v n hQ.le := by
  dsimp only [ICO.C6CacheOutputComparisonAfter.density, protocolLabelCacheDensity]
  have hs : ICO.C6CacheTrajectoryAfter.stages n hpos hQ
      (fun _ b => some (ICO.C6ActualResidualWeight.outcomeBasis H b))
      (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
      (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i)) =
      labelCacheStages n hQ.le H
        (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
        (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i)) :=
    funext (fun i => (labelCacheStages_eq_afterStages n hpos hQ H _ _ i).symm)
  rw [hs]

theorem referenceDensity_eq_referenceCache_output [Nontrivial A] {M O : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (v : (A × Bool) × M → ℂ)
    (n : ℕ) (hpos : 0 < n) (hQ : n < Fintype.card A) :
    ICO.C6CacheOutputComparisonAfter.density n hpos hQ
        (fun _ _ => none)
        (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
        (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i))
        (ICO.C6RawWeightedEndpoint.cacheInput tail v) n
        (ICO.C6CacheVisibleOutput.output n).map =
      protocolReferenceCacheDensity tail v n hQ.le := by
  dsimp only [ICO.C6CacheOutputComparisonAfter.density, protocolReferenceCacheDensity]
  have hs : ICO.C6CacheTrajectoryAfter.stages n hpos hQ
      (fun _ _ => none)
      (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
      (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i)) =
      referenceCacheStages n hQ.le
        (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
        (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i)) :=
    funext (fun i => (referenceCacheStages_eq_afterStages n hpos hQ _ _ i).symm)
  rw [hs]

/-- Note on naming: `ICO.C6RawWeightedEndpoint.cacheDensity` denotes the *weighted* history state
`ρ^w` (`eq:appA:weighted-state`), which is within `n (n - 1) / (4 d)` of the uniform label-cache
state `ρ^{cache}` (`protocolLabelCacheDensity`) of Definition `def:cache`. -/
theorem weighted_cacheDensity_labelCache_distance [Nontrivial A] {M O : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A × Bool) × M → ℂ) (hv : ‖WithLp.toLp 2 v‖ = 1)
    (n : ℕ) (hpos : 0 < n) (hQ : n < Fintype.card A) :
    normalizedTraceDistance
        (ICO.C6RawWeightedEndpoint.cacheDensity tail H v n hpos hQ)
        (protocolLabelCacheDensity tail H v n hQ.le) ≤
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) / (4 * (Fintype.card A : ℝ)) := by
  rw [← cacheDensity_eq_labelCache_output tail H v n hpos hQ]
  exact ICO.C6WeightedHistoryOutput.unit_mass_uniform_distance n hpos hQ H
    (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
    (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i))
    (ICO.C6RawWeightedEndpoint.cacheInput tail v)
    (ICO.C6SharedPairBound.cacheInput_pos tail v)
    (ICO.C6SharedPairBound.cacheInput_trace tail v hv) n
    (ICO.C6CacheVisibleOutput.output n).map
    (ICO.C6CacheVisibleOutput.output n).traceNonincreasingCP_map

/-! ### Exact Unpadded `BudgetQueryTree` ↔ Compiled `Protocol` Equivalence -/

/-- Operational execution of a `SequentialIsometry.Protocol` against a stateful environment `Ψ`
with hidden state space `R`, tracing out `R` at termination. -/
def runStatefulProtocol {R A₀ O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype O] [DecidableEq O]
    (Ψ : Channel (R × A₀) (R × A₀))
    {q : ℕ} {B : Type} [Fintype B] [DecidableEq B]
    (p : Protocol A₀ B O q) : MatrixMap (R × B) O := by
  induction p with
  | stop post hpost =>
      exact (erasureChannel post hpost).map.comp (Channel.traceOutLeft R _).map
  | query pre _ _ ih =>
      exact ih.comp ((liftEnvCall _ Ψ).map.comp (singleMap (liftEnvOp R pre)))

@[simp] private theorem runStatefulProtocol_stop {R A₀ O B E : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]
    (Ψ : Channel (R × A₀) (R × A₀)) (post : Matrix (O × E) B ℂ)
    (hpost : post.conjTranspose * post = 1) :
    runStatefulProtocol (A₀ := A₀) Ψ (Protocol.stop post hpost) =
      (erasureChannel post hpost).map.comp (Channel.traceOutLeft R B).map := rfl

@[simp] private theorem runStatefulProtocol_query {R A₀ O B M : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] [Fintype M] [DecidableEq M] {q : ℕ}
    (Ψ : Channel (R × A₀) (R × A₀)) (pre : Matrix (A₀ × M) B ℂ)
    (hpre : pre.conjTranspose * pre = 1) (after : Protocol A₀ (A₀ × M) O q) :
    runStatefulProtocol Ψ (Protocol.query pre hpre after) =
      (runStatefulProtocol Ψ after).comp ((liftEnvCall M Ψ).map.comp (singleMap (liftEnvOp R pre))) := rfl

theorem runStatefulProtocol_ending {R A₀ B O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (Ψ : Channel (R × A₀) (R × A₀)) (p : Protocol A₀ B O 0) :
    runStatefulProtocol Ψ p =
      (erasureChannel p.ending.post p.ending.isometry).map.comp
        (Channel.traceOutLeft R B).map := by
  cases p
  rfl

theorem runStatefulProtocol_heading_query {R A₀ B O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    {q : ℕ} (Ψ : Channel (R × A₀) (R × A₀)) (p : Protocol A₀ B O (q + 1)) :
    runStatefulProtocol Ψ p =
      (runStatefulProtocol Ψ p.heading.tail).comp
        ((liftEnvCall p.heading.M Ψ).map.comp (singleMap (liftEnvOp R p.heading.pre))) := by
  cases p
  rfl

/-- Stateful `tailEvolution` recurrence matching `Protocol.tailEvolution` with hidden register `R`. -/
def runStatefulTail {R A₀ M O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    {q : ℕ} (p : Protocol A₀ (A₀ × M) O q)
    (Ψ : Channel (R × A₀) (R × A₀)) (X : CMatrix (R × (A₀ × M))) :
    (t : ℕ) → CMatrix (R × (A₀ × p.tailMemory t))
  | 0 => X
  | t + 1 =>
      liftEnvOp R (p.tailKnown t) *
        (liftEnvCall (p.tailMemory t) Ψ).map (runStatefulTail p Ψ X t) *
        (liftEnvOp R (p.tailKnown t)).conjTranspose

theorem runStatefulTail_query_succ {R A₀ M N O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M]
    [Fintype N] [DecidableEq N] [Fintype O] [DecidableEq O] {q : ℕ}
    (pre : Matrix (A₀ × N) (A₀ × M) ℂ) (hpre : pre.conjTranspose * pre = 1)
    (after : Protocol A₀ (A₀ × N) O q) (Ψ : Channel (R × A₀) (R × A₀))
    (X : CMatrix (R × (A₀ × M))) (t : ℕ) :
    runStatefulTail (Protocol.query pre hpre after) Ψ X (t + 1) =
      runStatefulTail after Ψ
        (liftEnvOp R pre * (liftEnvCall M Ψ).map X * (liftEnvOp R pre).conjTranspose) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change liftEnvOp R (after.tailKnown t) *
      (liftEnvCall (after.tailMemory t) Ψ).map
        (runStatefulTail (Protocol.query pre hpre after) Ψ X (t + 1)) *
      (liftEnvOp R (after.tailKnown t)).conjTranspose = _
    rw [ih]
    rfl

theorem runStatefulTail_output {R A₀ M O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    {q : ℕ} (p : Protocol A₀ (A₀ × M) O q) (Ψ : Channel (R × A₀) (R × A₀))
    (X : CMatrix (R × (A₀ × M))) :
    p.terminalChannel.map ((Channel.traceOutLeft R _).map (runStatefulTail p Ψ X (q + 1))) =
      runStatefulProtocol Ψ p ((liftEnvCall M Ψ).map X) := by
  induction q generalizing M with
  | zero =>
    cases p with
    | stop post hpost =>
      change (erasureChannel post hpost).map
        ((Channel.traceOutLeft R (A₀ × M)).map
          (liftEnvOp R (1 : CMatrix (A₀ × M)) * (liftEnvCall M Ψ).map X *
            (liftEnvOp R (1 : CMatrix (A₀ × M))).conjTranspose)) = _
      have h1 : liftEnvOp R (1 : CMatrix (A₀ × M)) = 1 := Matrix.one_kronecker_one
      simp [h1]
  | succ q ih =>
    cases p with
    | query pre hpre after =>
      rw [runStatefulTail_query_succ]
      change after.terminalChannel.map ((Channel.traceOutLeft R _).map
        (runStatefulTail after Ψ
          (liftEnvOp R pre * (liftEnvCall M Ψ).map X * (liftEnvOp R pre).conjTranspose) (q + 1))) = _
      rw [ih]
      simp [singleMap_apply]

theorem runStatefulProtocol_heading {R A₀ B O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    {q : ℕ} (p : Protocol A₀ B O (q + 1)) (Ψ : Channel (R × A₀) (R × A₀))
    (X : CMatrix (R × B)) :
    p.heading.tail.terminalChannel.map
      ((Channel.traceOutLeft R _).map
        (runStatefulTail p.heading.tail Ψ
          (liftEnvOp R p.heading.pre * X * (liftEnvOp R p.heading.pre).conjTranspose) (q + 1))) =
      runStatefulProtocol Ψ p X := by
  rw [runStatefulTail_output, runStatefulProtocol_heading_query Ψ p]
  simp [singleMap_apply]

theorem partialTraceA_liftEnvOp {R B C : Type} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (W : Matrix C B ℂ) (X : CMatrix (R × B)) :
    partialTraceA (liftEnvOp R W * X * (liftEnvOp R W).conjTranspose) =
      W * partialTraceA X * W.conjTranspose :=
  ICO.C6CacheVisible.partialTraceA_known W X

theorem runStatefulProtocol_precompose {R A₀ B C O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O] {q : ℕ}
    (p : Protocol A₀ B O q) (W : Matrix B C ℂ) (hW : W.conjTranspose * W = 1)
    (Ψ : Channel (R × A₀) (R × A₀)) :
    runStatefulProtocol Ψ (p.precompose W hW) =
      (runStatefulProtocol Ψ p).comp (singleMap (liftEnvOp R W)) := by
  cases p with
  | stop post hpost =>
    ext X o₁ o₂
    simp only [Protocol.precompose, runStatefulProtocol_stop, LinearMap.comp_apply,
      Channel.traceOutLeft_map, singleMap_apply, erasureChannel]
    rw [partialTraceA_liftEnvOp, ← singleMap_apply W, ← LinearMap.comp_apply,
      ← ofKraus_right_mul]
    rfl
  | query pre hpre after =>
    ext X o₁ o₂
    simp only [Protocol.precompose, runStatefulProtocol_query, LinearMap.comp_apply,
      liftEnvOp_mul, singleMap_mul]

theorem singleMap_liftEnvOp_slice {R B C : Type} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (W : Matrix C B ℂ) (X : CMatrix (R × B)) (r₁ r₂ : R) :
    (fun c₁ c₂ => singleMap (liftEnvOp R W) X (r₁, c₁) (r₂, c₂)) =
      singleMap W (fun b₁ b₂ => X (r₁, b₁) (r₂, b₂)) := by
  ext c₁ c₂
  simp only [singleMap_apply, liftEnvOp, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single r₂]
  · simp only [ite_true, one_mul]
    apply Finset.sum_congr rfl; intro b₂ _
    congr 1
    rw [Finset.sum_eq_single r₁]
    · simp only [ite_true, one_mul]
    · intro s _ hne; simp [Ne.symm hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro s _ hne; simp [hne]
  · intro h; exact (h (Finset.mem_univ _)).elim

private theorem liftEnvOp_permutation_sandwich {R B C : Type} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (e : B ≃ C) (Y : CMatrix (R × B)) :
    liftEnvOp R (permutation e) * Y * (liftEnvOp R (permutation e)).conjTranspose =
      Y.submatrix (Prod.map id e.symm) (Prod.map id e.symm) := by
  have he : liftEnvOp R (permutation e) = permutation (Equiv.prodCongr (Equiv.refl R) e) := by
    ext ⟨r₁, x₁⟩ ⟨r₂, x₂⟩
    by_cases hr : r₁ = r₂
    · subst r₂
      simp [liftEnvOp, permutation, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    · simp [liftEnvOp, permutation, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Prod.mk.injEq, hr]
  rw [he, permutation_sandwich]
  rfl

theorem controlled_stateful_block {R A₀ J : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype J] [DecidableEq J]
    {Bs Ms : J → Type} [∀ j, Fintype (Bs j)] [∀ j, DecidableEq (Bs j)]
    [∀ j, Fintype (Ms j)] [∀ j, DecidableEq (Ms j)]
    (W : (j : J) → Matrix (A₀ × Ms j) (Bs j) ℂ)
    (Ψ : Channel (R × A₀) (R × A₀))
    (X : CMatrix (R × ((j : J) × Bs j))) (j : J) :
    (liftEnvOp R (permutation (ICO.ControlledIsometry.distrib A₀ Ms)) *
      (liftEnvCall ((k : J) × Ms k) Ψ).map
        (liftEnvOp R (ICO.ControlledIsometry.controlled W) * X *
          (liftEnvOp R (ICO.ControlledIsometry.controlled W)).conjTranspose) *
      (liftEnvOp R (permutation (ICO.ControlledIsometry.distrib A₀ Ms))).conjTranspose).submatrix
        (Prod.map id (Sigma.mk j)) (Prod.map id (Sigma.mk j)) =
    (liftEnvCall (Ms j) Ψ).map
      (liftEnvOp R (W j) *
        X.submatrix (Prod.map id (Sigma.mk j)) (Prod.map id (Sigma.mk j)) *
        (liftEnvOp R (W j)).conjTranspose) := by
  rw [liftEnvOp_permutation_sandwich]
  ext ⟨r₁, a₁, m₁⟩ ⟨r₂, a₂, m₂⟩
  simp only [Matrix.submatrix_apply, Prod.map_apply, id_eq,
    ICO.ControlledIsometry.distrib, Equiv.coe_fn_symm_mk]
  rw [liftEnvCall_apply, liftEnvCall_apply]
  suffices hmat :
      Matrix.of (fun u₁ u₂ : R × A₀ =>
        (liftEnvOp R (ICO.ControlledIsometry.controlled W) * X *
          (liftEnvOp R (ICO.ControlledIsometry.controlled W)).conjTranspose)
          (u₁.1, (u₁.2, ⟨j, m₁⟩)) (u₂.1, (u₂.2, ⟨j, m₂⟩))) =
      Matrix.of (fun u₁ u₂ : R × A₀ =>
        (liftEnvOp R (W j) *
          X.submatrix (Prod.map id (Sigma.mk j)) (Prod.map id (Sigma.mk j)) *
          (liftEnvOp R (W j)).conjTranspose)
          (u₁.1, (u₁.2, m₁)) (u₂.1, (u₂.2, m₂))) by
    rw [hmat]
  ext ⟨r', a'⟩ ⟨r'', a''⟩
  rw [Matrix.of_apply, Matrix.of_apply]
  have h1 := congrFun (congrFun (singleMap_liftEnvOp_slice
    (ICO.ControlledIsometry.controlled W) X r' r'') (a', ⟨j, m₁⟩)) (a'', ⟨j, m₂⟩)
  have h2 := congrFun (congrFun (singleMap_liftEnvOp_slice (W j)
    (X.submatrix (Prod.map id (Sigma.mk j)) (Prod.map id (Sigma.mk j))) r' r'')
    (a', m₁)) (a'', m₂)
  simp only [singleMap_apply] at h1 h2
  rw [h1, h2]
  exact ICO.ControlledIsometry.controlled_sandwich_block W
    (fun b₁ b₂ => X (r', b₁) (r'', b₂)) j a' a'' m₁ m₂

theorem runStatefulProtocol_controlled {R A₀ O J : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    {Bs : J → Type} [∀ j, Fintype (Bs j)] [∀ j, DecidableEq (Bs j)] {q : ℕ}
    (p : (j : J) → Protocol A₀ (Bs j) O q) (Ψ : Channel (R × A₀) (R × A₀))
    (X : CMatrix (R × ((j : J) × Bs j))) :
    runStatefulProtocol Ψ (Protocol.controlled p) X =
      ∑ j, runStatefulProtocol Ψ (p j)
        (X.submatrix (Prod.map id (Sigma.mk j)) (Prod.map id (Sigma.mk j))) := by
  induction q generalizing Bs with
  | zero =>
    change MatrixMap.ofKraus (erasedKraus
        (ICO.ControlledIsometry.controlled (fun j => (p j).ending.post)))
      (partialTraceA X) = _
    rw [erasedKraus_apply, ICO.ControlledIsometry.controlled_erasure]
    apply Finset.sum_congr rfl
    intro j _
    rw [runStatefulProtocol_ending Ψ (p j)]
    simp only [LinearMap.comp_apply, Channel.traceOutLeft_map, erasureChannel]
    rw [erasedKraus_apply]
    rfl
  | succ q ih =>
    change runStatefulProtocol Ψ
      ((Protocol.controlled (fun j => (p j).heading.tail)).precompose
        (permutation (ICO.ControlledIsometry.distrib A₀ (fun j => (p j).heading.M)))
        (permutation_isometry _))
      ((liftEnvCall _ Ψ).map
        (singleMap (liftEnvOp R (ICO.ControlledIsometry.controlled (fun j => (p j).heading.pre))) X)) = _
    rw [runStatefulProtocol_precompose]
    simp only [LinearMap.comp_apply, singleMap_apply]
    rw [ih]
    apply Finset.sum_congr rfl
    intro j _
    rw [controlled_stateful_block, runStatefulProtocol_heading_query Ψ (p j)]
    simp only [LinearMap.comp_apply, singleMap_apply]

theorem runStatefulProtocol_instrumentQuery {R A₀ B M O J : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype B] [DecidableEq B]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    {q : ℕ} (instrument : Instrument B (A₀ × M) J)
    (tail : J → Protocol A₀ (A₀ × M) O q) (Ψ : Channel (R × A₀) (R × A₀))
    (X : CMatrix (R × B)) :
    runStatefulProtocol Ψ (Protocol.instrumentQuery instrument tail) X =
      ∑ j, runStatefulProtocol Ψ (tail j)
        ((liftEnvCall M Ψ).map (singleMap (liftEnvOp R (instrument.op j)) X)) := by
  change runStatefulProtocol Ψ
    ((Protocol.controlled tail).precompose
      (permutation (ICO.ControlledIsometry.distrib A₀ (fun _ : J => M)))
      (permutation_isometry _))
    ((liftEnvCall ((_ : J) × M) Ψ).map
      (singleMap (liftEnvOp R (instrumentStack instrument)) X)) = _
  rw [runStatefulProtocol_precompose]
  simp only [LinearMap.comp_apply, singleMap_apply]
  rw [runStatefulProtocol_controlled]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [liftEnvOp_permutation_sandwich]
  ext ⟨r₁, a₁, m₁⟩ ⟨r₂, a₂, m₂⟩
  simp only [Matrix.submatrix_apply, Prod.map_apply, id_eq,
    ICO.ControlledIsometry.distrib, Equiv.coe_fn_symm_mk]
  rw [liftEnvCall_apply, liftEnvCall_apply]
  suffices hmat :
      Matrix.of (fun u₁ u₂ : R × A₀ =>
        (liftEnvOp R (instrumentStack instrument) * X *
          (liftEnvOp R (instrumentStack instrument)).conjTranspose)
          (u₁.1, (u₁.2, ⟨j, m₁⟩)) (u₂.1, (u₂.2, ⟨j, m₂⟩))) =
      Matrix.of (fun u₁ u₂ : R × A₀ =>
        (liftEnvOp R (instrument.op j) * X *
          (liftEnvOp R (instrument.op j)).conjTranspose)
          (u₁.1, (u₁.2, m₁)) (u₂.1, (u₂.2, m₂))) by
    rw [hmat]
  ext ⟨r', a'⟩ ⟨r'', a''⟩
  rw [Matrix.of_apply, Matrix.of_apply]
  have h1 := congrFun (congrFun (singleMap_liftEnvOp_slice
    (instrumentStack instrument) X r' r'') (a', ⟨j, m₁⟩)) (a'', ⟨j, m₂⟩)
  have h2 := congrFun (congrFun (singleMap_liftEnvOp_slice
    (instrument.op j) X r' r'') (a', m₁)) (a'', m₂)
  simp only [singleMap_apply] at h1 h2
  rw [h1, h2]
  rfl

/-- Stateful execution of `ICO.LabelledQueryTree.Tree`. -/
def runStatefulLabelledTree {L R A₀ M O : Type} [DecidableEq L] [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (oracles : L → Channel (R × A₀) (R × A₀))
    {s : Finset L} {B : Type} [Fintype B] [DecidableEq B]
    (tree : ICO.LabelledQueryTree.Tree L (A₀ × M) O s B) : MatrixMap (R × B) O := by
  induction tree with
  | terminal channel => exact channel.map.comp (Channel.traceOutLeft R _).map
  | query i _ _ ih => exact ih.comp (liftEnvCall M (oracles i)).map
  | node instrument _ ih =>
      exact ∑ k, (ih k).comp (singleMap (liftEnvOp R (instrument.op k)))

@[simp] private theorem runStatefulLabelledTree_terminal {L R A₀ M O B : Type} [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (oracles : L → Channel (R × A₀) (R × A₀)) (channel : Channel B O) :
    runStatefulLabelledTree (M := M) oracles
      (ICO.LabelledQueryTree.Tree.terminal (L := L) (H := A₀ × M) channel) =
      channel.map.comp (Channel.traceOutLeft R B).map := rfl

@[simp] private theorem runStatefulLabelledTree_query {L R A₀ M O : Type} [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (oracles : L → Channel (R × A₀) (R × A₀)) {s : Finset L} (i : L) (hi : i ∈ s)
    (after : ICO.LabelledQueryTree.Tree L (A₀ × M) O (s.erase i) (A₀ × M)) :
    runStatefulLabelledTree oracles (ICO.LabelledQueryTree.Tree.query i hi after) =
      (runStatefulLabelledTree oracles after).comp (liftEnvCall M (oracles i)).map := rfl

@[simp] private theorem runStatefulLabelledTree_node {L R A₀ M O B C K : Type} [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K]
    (oracles : L → Channel (R × A₀) (R × A₀)) {s : Finset L}
    (instrument : Instrument B C K)
    (next : K → ICO.LabelledQueryTree.Tree L (A₀ × M) O s C) :
    runStatefulLabelledTree oracles (ICO.LabelledQueryTree.Tree.node instrument next) =
      ∑ k, (runStatefulLabelledTree oracles (next k)).comp
        (singleMap (liftEnvOp R (instrument.op k))) := rfl

/-- Stateful execution of `ICO.FirstLabelledQuery.Cut`. -/
def runStatefulCut {L R A₀ M O B : Type} [DecidableEq L] [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B] {s : Finset L}
    (cut : ICO.FirstLabelledQuery.Cut L (A₀ × M) O s B)
    (oracles : L → Channel (R × A₀) (R × A₀)) : MatrixMap (R × B) O :=
  ∑ j : cut.Branch, (runStatefulLabelledTree oracles (cut.post j)).comp
    ((liftEnvCall M (oracles (cut.label j))).map.comp
      (singleMap (liftEnvOp R (cut.pre.op j))))

theorem runStatefulCut_prepend {L R A₀ M O B C K : Type} [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K]
    {s : Finset L} (I : Instrument B C K)
    (next : K → ICO.FirstLabelledQuery.Cut L (A₀ × M) O s C)
    (oracles : L → Channel (R × A₀) (R × A₀)) :
    runStatefulCut (ICO.FirstLabelledQuery.Cut.prepend I next) oracles =
      ∑ l, (runStatefulCut (next l) oracles).comp (singleMap (liftEnvOp R (I.op l))) := by
  ext X o₁ o₂
  simp only [runStatefulCut, ICO.FirstLabelledQuery.Cut.prepend, LinearMap.sum_apply,
    LinearMap.comp_apply, Matrix.sum_apply, liftEnvOp_mul, singleMap_mul]
  exact Fintype.sum_sigma _

theorem first_stateful {L R A₀ M O B : Type} [DecidableEq L] [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L (A₀ × M) O s B) (hs : s.Nonempty)
    (oracles : L → Channel (R × A₀) (R × A₀)) :
    runStatefulCut (ICO.FirstLabelledQuery.first tree hs) oracles =
      runStatefulLabelledTree oracles tree := by
  induction tree with
  | terminal channel => exact (Finset.not_nonempty_empty hs).elim
  | query i hi after _ =>
    ext X o₁ o₂
    have h1 : liftEnvOp R (1 : CMatrix (A₀ × M)) = 1 := Matrix.one_kronecker_one
    simp [ICO.FirstLabelledQuery.first, ICO.FirstLabelledQuery.Cut.immediate,
      runStatefulCut, singleMap_apply, h1]
  | node instrument next ih =>
    change runStatefulCut (ICO.FirstLabelledQuery.Cut.prepend instrument
      (fun j => ICO.FirstLabelledQuery.first (next j) hs)) oracles = _
    rw [runStatefulCut_prepend, runStatefulLabelledTree_node]
    simp_rw [ih]

theorem adaptiveCompile_stateful {L R A₀ M O B : Type} [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {s : Finset L} (tree : ICO.LabelledQueryTree.Tree L (A₀ × M) O s B)
    (q : ℕ) (hq : s.card = q) (Ψ : Channel (R × A₀) (R × A₀)) :
    runStatefulProtocol Ψ (ICO.AdaptiveSequentialProtocol.compile tree q hq) =
      runStatefulLabelledTree (fun _ => Ψ) tree := by
  induction q generalizing B s with
  | zero =>
    have hs : s = ∅ := Finset.card_eq_zero.mp hq
    subst hs
    ext X o₁ o₂
    change (MatrixMap.ofKraus (erasedKraus
      (ICO.ClassicalDilation.channelIsometry
        (tree.channel (fun _ => Channel.idChannel (A₀ × M))))))
      (partialTraceA X) o₁ o₂ = _
    rw [erasedKraus_apply, ICO.ClassicalDilation.channelIsometry_output]
    have hnoquery : ∀ {s' : Finset L} (hs' : s' = ∅) {C : Type} [Fintype C] [DecidableEq C]
        (t : ICO.LabelledQueryTree.Tree L (A₀ × M) O s' C) (Y : CMatrix (R × C)),
        (t.channel (fun _ => Channel.idChannel (A₀ × M))).map (partialTraceA Y) =
          runStatefulLabelledTree (fun _ => Ψ) t Y := by
      intro s' hs' C _ _ t
      induction t with
      | terminal ch => intro Y; rfl
      | query i hi _ _ => subst hs'; simp at hi
      | node I next ih' =>
        intro Y
        rw [ICO.LabelledQueryTree.Tree.channel_map, ICO.LabelledQueryTree.Tree.map_node,
          runStatefulLabelledTree_node]
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, branchMap_apply, singleMap_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [← ICO.LabelledQueryTree.Tree.channel_map, ← partialTraceA_liftEnvOp, ih' k hs']
    rw [hnoquery rfl tree X]
  | succ q ih =>
    have hs : s.Nonempty := Finset.card_pos.mp (by omega)
    let cut := ICO.FirstLabelledQuery.first tree hs
    ext X o₁ o₂
    change runStatefulProtocol Ψ
      (Protocol.instrumentQuery cut.pre (fun j =>
        ICO.AdaptiveSequentialProtocol.compile (cut.post j) q
          (by rw [Finset.card_erase_of_mem (cut.member j), hq]; omega))) X o₁ o₂ = _
    rw [runStatefulProtocol_instrumentQuery, ← first_stateful tree hs (fun _ => Ψ)]
    simp only [runStatefulCut, LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]

theorem idChannel_prod_slice {R B C : Type} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (Φ : Channel B C) (X : CMatrix (R × B)) (r₁ r₂ : R) :
    (fun c₁ c₂ => ((Channel.idChannel R).prod Φ).map X (r₁, c₁) (r₂, c₂)) =
      Φ.map (fun b₁ b₂ => X (r₁, b₁) (r₂, b₂)) := by
  have hid (Z : CMatrix R) : (Channel.idChannel R).map Z = Z := by
    simp [Channel.idChannel, MatrixMap.ofKraus]
  ext c₁ c₂
  have hΦ := congrFun (congrFun
    (MatrixMap.map_eq_sum_single Φ.map (fun b₁ b₂ => X (r₁, b₁) (r₂, b₂))) c₁) c₂
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hΦ
  rw [hΦ]
  change MatrixMap.kron (Channel.idChannel R).map Φ.map X (r₁, c₁) (r₂, c₂) = _
  simp only [MatrixMap.kron, LinearMap.coe_mk, AddHom.coe_mk, hid]
  apply Finset.sum_congr rfl; intro b₁ _
  apply Finset.sum_congr rfl; intro b₂ _
  rw [Finset.sum_eq_single r₁]
  · rw [Finset.sum_eq_single r₂]
    · simp [Matrix.single]
    · intro s _ hne; simp [Matrix.single, hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro s _ hne; simp [Matrix.single, hne]
  · intro h; exact (h (Finset.mem_univ _)).elim

theorem idChannel_prod_ofKraus {R B C I : Type} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype I]
    (Φ : Channel B C) (K : I → Matrix C B ℂ) (hK : Φ.map = MatrixMap.ofKraus K)
    (X : CMatrix (R × B)) :
    ((Channel.idChannel R).prod Φ).map X =
      ∑ i, singleMap (liftEnvOp R (K i)) X := by
  ext ⟨r₁, c₁⟩ ⟨r₂, c₂⟩
  rw [congrFun (congrFun (idChannel_prod_slice Φ X r₁ r₂) c₁) c₂, hK]
  simp only [Matrix.sum_apply, MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk]
  symm
  apply Finset.sum_congr rfl
  intro i _
  simpa only [singleMap_apply] using
    congrFun (congrFun (singleMap_liftEnvOp_slice (K i) X r₁ r₂) c₁) c₂

theorem sum_liftEnvOp_channelKraus {R B C : Type} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (Φ : Channel B C) (X : CMatrix (R × B)) :
    (∑ k, singleMap (liftEnvOp R (channelKraus Φ k)) X) =
      ((Channel.idChannel R).prod Φ).map X :=
  (idChannel_prod_ofKraus Φ (channelKraus Φ) (channelKraus_map Φ) X).symm

theorem partialTraceA_idChannel_prod {R B C : Type} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (Φ : Channel B C) (X : CMatrix (R × B)) :
    partialTraceA (((Channel.idChannel R).prod Φ).map X) = Φ.map (partialTraceA X) := by
  have hsum (f : (B × C) → CMatrix (R × C)) :
      partialTraceA (∑ k, f k) = ∑ k, partialTraceA (f k) := by
    ext c₁ c₂
    simp only [partialTraceA, Matrix.sum_apply]
    rw [Finset.sum_comm]
  rw [← sum_liftEnvOp_channelKraus, hsum]
  simp only [singleMap_apply, partialTraceA_liftEnvOp]
  rw [channelKraus_map Φ]
  rfl

theorem idChannel_prod_isometry {R B C : Type} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (W : Matrix C B ℂ) (hW : W.conjTranspose * W = 1) (X : CMatrix (R × B)) :
    ((Channel.idChannel R).prod (ICO.ClassicalDilation.isometryChannel W hW)).map X =
      liftEnvOp R W * X * (liftEnvOp R W).conjTranspose := by
  ext ⟨r₁, c₁⟩ ⟨r₂, c₂⟩
  rw [congrFun (congrFun (idChannel_prod_slice
    (ICO.ClassicalDilation.isometryChannel W hW) X r₁ r₂) c₁) c₂]
  simpa only [ICO.ClassicalDilation.isometryChannel_apply, singleMap_apply] using
    (congrFun (congrFun (singleMap_liftEnvOp_slice W X r₁ r₂) c₁) c₂).symm

theorem idChannel_prod_comp {R B C D : Type} [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (Φ : Channel C D) (Θ : Channel B C) (X : CMatrix (R × B)) :
    ((Channel.idChannel R).prod (Φ.comp Θ)).map X =
      ((Channel.idChannel R).prod Φ).map (((Channel.idChannel R).prod Θ).map X) := by
  ext ⟨r₁, d₁⟩ ⟨r₂, d₂⟩
  rw [congrFun (congrFun (idChannel_prod_slice (Φ.comp Θ) X r₁ r₂) d₁) d₂,
    congrFun (congrFun (idChannel_prod_slice Φ _ r₁ r₂) d₁) d₂,
    idChannel_prod_slice Θ X r₁ r₂]
  rfl

theorem liftEnvKraus_commutes_queryEmbedding {R A₀ M N : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (e : M ↪ N) (G : CMatrix (R × A₀)) :
    liftEnvKraus N G * liftEnvOp R (ICO.MemoryEmbedding.queryEmbedding (A := A₀) e) =
      liftEnvOp R (ICO.MemoryEmbedding.queryEmbedding (A := A₀) e) * liftEnvKraus M G := by
  ext ⟨r₁, a₁, n₁⟩ ⟨r₂, a₂, m₂⟩
  simp only [liftEnvKraus, liftEnvOp, ICO.MemoryEmbedding.queryEmbedding,
    ICO.MemoryEmbedding.embedding, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Equiv.prodAssoc_symm_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, one_mul, mul_one, zero_mul, mul_zero]
  trans (G (r₁, a₁) (r₂, a₂) * if n₁ = e m₂ then 1 else 0)
  · rw [Finset.sum_eq_single r₂]
    · simp only [ite_true]
      rw [Finset.sum_eq_single a₂]
      · simp only [ite_true]
        rw [Finset.sum_eq_single n₁]
        · simp
        · intro n' _ hne; simp [Ne.symm hne]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · intro a' _ hne; simp [hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intro r' _ hne; simp [hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · symm
    rw [Finset.sum_eq_single r₁]
    · simp only [ite_true]
      rw [Finset.sum_eq_single a₁]
      · simp only [ite_true]
        rw [Finset.sum_eq_single m₂]
        · simp [mul_comm]
        · intro m' _ hne; simp [hne]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · intro a' _ hne; simp [Ne.symm hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intro r' _ hne; simp [Ne.symm hne]
    · intro h; exact (h (Finset.mem_univ _)).elim

theorem liftEnvCall_queryEmbed {R A₀ M N : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (e : M ↪ N) (Ψ : Channel (R × A₀) (R × A₀)) (X : CMatrix (R × (A₀ × M))) :
    (liftEnvCall N Ψ).map
      (((Channel.idChannel R).prod (ICO.AllChannelPadding.queryEmbedChannel (A := A₀) e)).map X) =
      ((Channel.idChannel R).prod (ICO.AllChannelPadding.queryEmbedChannel (A := A₀) e)).map
        ((liftEnvCall M Ψ).map X) := by
  dsimp only [ICO.AllChannelPadding.queryEmbedChannel]
  rw [idChannel_prod_isometry, idChannel_prod_isometry,
    liftEnvCall_kraus_apply, liftEnvCall_kraus_apply, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  let GN := liftEnvKraus N (ICO.BudgetPreparation.kraus Ψ k)
  let GM := liftEnvKraus M (ICO.BudgetPreparation.kraus Ψ k)
  let E := liftEnvOp R (ICO.MemoryEmbedding.queryEmbedding (A := A₀) e)
  have hc : GN * E = E * GM :=
    liftEnvKraus_commutes_queryEmbedding (R := R) (A₀ := A₀) e (ICO.BudgetPreparation.kraus Ψ k)
  have hct : E.conjTranspose * GN.conjTranspose = GM.conjTranspose * E.conjTranspose := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hc
  calc GN * (E * X * E.conjTranspose) * GN.conjTranspose
      = (GN * (E * X)) * E.conjTranspose * GN.conjTranspose := by
          rw [← Matrix.mul_assoc GN (E * X) E.conjTranspose]
    _ = ((GN * E) * X) * E.conjTranspose * GN.conjTranspose := by
          rw [← Matrix.mul_assoc GN E X]
    _ = ((E * GM) * X) * E.conjTranspose * GN.conjTranspose := by
          rw [hc]
    _ = ((E * GM) * X) * (E.conjTranspose * GN.conjTranspose) := by
          rw [Matrix.mul_assoc ((E * GM) * X) E.conjTranspose GN.conjTranspose]
    _ = ((E * GM) * X) * (GM.conjTranspose * E.conjTranspose) := by
          rw [hct]
    _ = (((E * GM) * X) * GM.conjTranspose) * E.conjTranspose := by
          rw [← Matrix.mul_assoc ((E * GM) * X) GM.conjTranspose E.conjTranspose]
    _ = ((E * (GM * X)) * GM.conjTranspose) * E.conjTranspose := by
          rw [Matrix.mul_assoc E GM X]
    _ = E * (GM * X * GM.conjTranspose) * E.conjTranspose := by
          rw [Matrix.mul_assoc E (GM * X) GM.conjTranspose]

theorem queryRetraction_queryEmbed_stateful {R A₀ M N : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (e : M ↪ N) (a₀ : A₀) (m₀ : M) (Y : CMatrix (R × (A₀ × M))) :
    ((Channel.idChannel R).prod (ICO.MemoryEmbedding.queryRetraction e a₀ m₀)).map
      (((Channel.idChannel R).prod (ICO.AllChannelPadding.queryEmbedChannel (A := A₀) e)).map Y) =
      Y := by
  ext ⟨r₁, am₁⟩ ⟨r₂, am₂⟩
  rw [congrFun (congrFun (idChannel_prod_slice
    (ICO.MemoryEmbedding.queryRetraction e a₀ m₀) _ r₁ r₂) am₁) am₂,
    idChannel_prod_slice (ICO.AllChannelPadding.queryEmbedChannel (A := A₀) e) Y r₁ r₂]
  dsimp only [ICO.AllChannelPadding.queryEmbedChannel]
  rw [ICO.ClassicalDilation.isometryChannel_apply, ICO.MemoryEmbedding.queryRetraction_identity]

theorem labelledPrepend_stateful {L R A₀ M O B₁ B₂ : Type} [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    [Fintype B₁] [DecidableEq B₁] [Fintype B₂] [DecidableEq B₂]
    {s : Finset L} (C : Channel B₁ B₂)
    (tree : ICO.LabelledQueryTree.Tree L (A₀ × M) O s B₂)
    (oracles : L → Channel (R × A₀) (R × A₀)) (X : CMatrix (R × B₁)) :
    runStatefulLabelledTree oracles (ICO.LabelledCircuitComposition.prepend C tree) X =
      runStatefulLabelledTree oracles tree (((Channel.idChannel R).prod C).map X) := by
  simp only [ICO.LabelledCircuitComposition.prepend, runStatefulLabelledTree_node,
    ICO.LabelledCircuitComposition.channelInstrument, LinearMap.sum_apply,
    LinearMap.comp_apply, ← map_sum, sum_liftEnvOp_channelKraus]

theorem partialTraceA_partialTraceA_liftEnvCall {R A₀ O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype O] [DecidableEq O]
    (Ψ : Channel (R × A₀) (R × A₀)) (Z : CMatrix (R × (A₀ × O))) :
    partialTraceA (partialTraceA ((liftEnvCall O Ψ).map Z)) =
      partialTraceA (partialTraceA Z) := by
  ext o₁ o₂
  have hslice :
      (∑ r : R, ∑ a : A₀, ((liftEnvCall O Ψ).map Z) (r, (a, o₁)) (r, (a, o₂))) =
        (Ψ.map (Matrix.of (fun u₁ u₂ : R × A₀ => Z (u₁.1, (u₁.2, o₁)) (u₂.1, (u₂.2, o₂))))).trace := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro a _
    rw [liftEnvCall_apply]
    rfl
  simp only [partialTraceA]
  rw [Finset.sum_comm, hslice, Ψ.tracePreserving]
  rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem dummy_stateful_traceOut {R A₀ M O : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (a₀ : A₀) (o₀ : O) (Ψ : Channel (R × A₀) (R × A₀)) (X : CMatrix (R × O)) :
    partialTraceA
      (((Channel.idChannel R).prod (ICO.PadLabelledCircuit.dummyPost (M := M) a₀ o₀)).map
        ((liftEnvCall (M ⊕ O) Ψ).map
          (((Channel.idChannel R).prod (ICO.PadLabelledCircuit.dummyPre (M := M) a₀)).map X))) =
      partialTraceA X := by
  dsimp only [ICO.PadLabelledCircuit.dummyPre, ICO.PadLabelledCircuit.dummyPost]
  rw [idChannel_prod_comp, idChannel_prod_comp, liftEnvCall_queryEmbed,
    queryRetraction_queryEmbed_stateful, partialTraceA_idChannel_prod]
  change MatrixMap.ofKraus (ICO.OraclePadding.discardKraus (A := A₀) (C := O))
    (partialTraceA ((liftEnvCall O Ψ).map
      (((Channel.idChannel R).prod
        (ICO.ClassicalDilation.isometryChannel
          (ICO.OraclePadding.pad a₀) (ICO.OraclePadding.pad_isometry a₀))).map X))) = _
  rw [ICO.OraclePadding.discard_apply, partialTraceA_partialTraceA_liftEnvCall,
    partialTraceA_idChannel_prod, ICO.ClassicalDilation.isometryChannel_apply,
    ICO.OraclePadding.pad, ICO.OraclePadding.tensorVector_sandwich, partialTraceA_kronecker]
  have htr : (rankOneMatrix (ICO.OraclePadding.basisVector a₀)).trace = 1 := by
    simp [ICO.OraclePadding.basisVector, rankOneMatrix, Matrix.trace, Matrix.diag_apply,
      Matrix.vecMulVec_apply]
  rw [htr]
  exact one_smul ℂ (partialTraceA X)

theorem remaining_stateful {L R A₀ M O : Type} [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (a₀ : A₀) (o₀ : O) (s : Finset L)
    (oracles : L → Channel (R × A₀) (R × A₀)) (X : CMatrix (R × O)) :
    runStatefulLabelledTree oracles (ICO.PadLabelledCircuit.remaining (M := M) a₀ o₀ s) X =
      partialTraceA X := by
  by_cases hs : s.Nonempty
  · rw [ICO.PadLabelledCircuit.remaining, dif_pos hs, labelledPrepend_stateful]
    change runStatefulLabelledTree oracles
      (ICO.LabelledCircuitComposition.prepend (ICO.PadLabelledCircuit.dummyPost a₀ o₀)
        (ICO.PadLabelledCircuit.remaining a₀ o₀ (s.erase hs.choose)))
      ((liftEnvCall (M ⊕ O) (oracles hs.choose)).map
        (((Channel.idChannel R).prod (ICO.PadLabelledCircuit.dummyPre (M := M) a₀)).map X)) = _
    rw [labelledPrepend_stateful,
      remaining_stateful a₀ o₀ (s.erase hs.choose) oracles,
      dummy_stateful_traceOut]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst he
    rw [ICO.PadLabelledCircuit.remaining, dif_neg hs]
    change (Channel.idChannel O).map (partialTraceA X) = partialTraceA X
    ext o₁ o₂
    simp [Channel.idChannel, MatrixMap.ofKraus]
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem hs.choose_spec

/-- Stateful execution of `ICO.AtMostLabelledQueryTree.Tree`. -/
def runStatefulAtMostTree {L R A₀ M O : Type} [DecidableEq L] [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (oracles : L → Channel (R × A₀) (R × A₀))
    {s : Finset L} {B : Type} [Fintype B] [DecidableEq B]
    (tree : ICO.AtMostLabelledQueryTree.Tree L (A₀ × M) O s B) : MatrixMap (R × B) O := by
  induction tree with
  | terminal channel => exact channel.map.comp (Channel.traceOutLeft R _).map
  | query i _ _ ih => exact ih.comp (liftEnvCall M (oracles i)).map
  | node instrument _ ih =>
      exact ∑ k, (ih k).comp (singleMap (liftEnvOp R (instrument.op k)))

theorem padCompile_stateful {L R A₀ M O B : Type} [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (a₀ : A₀) (m₀ : M) (o₀ : O) {s : Finset L}
    (tree : ICO.AtMostLabelledQueryTree.Tree L (A₀ × M) O s B)
    (oracles : L → Channel (R × A₀) (R × A₀)) :
    runStatefulLabelledTree oracles (ICO.PadLabelledCircuit.compile a₀ m₀ o₀ tree) =
      runStatefulAtMostTree oracles tree := by
  induction tree with
  | terminal channel =>
    ext X o₁ o₂
    change runStatefulLabelledTree oracles
      (ICO.LabelledCircuitComposition.prepend channel (ICO.PadLabelledCircuit.remaining a₀ o₀ _))
      X o₁ o₂ = _
    rw [labelledPrepend_stateful, remaining_stateful, partialTraceA_idChannel_prod]
    rfl
  | query i hi after ih =>
    ext X o₁ o₂
    change runStatefulLabelledTree oracles
      (ICO.LabelledCircuitComposition.prepend
        (ICO.AllChannelPadding.queryEmbedChannel ICO.PadLabelledCircuit.leftMemory)
        (ICO.LabelledQueryTree.Tree.query i hi
          (ICO.LabelledCircuitComposition.prepend
            (ICO.MemoryEmbedding.queryRetraction ICO.PadLabelledCircuit.leftMemory a₀ m₀)
            (ICO.PadLabelledCircuit.compile a₀ m₀ o₀ after)))) X o₁ o₂ = _
    rw [labelledPrepend_stateful]
    change runStatefulLabelledTree oracles
      (ICO.LabelledCircuitComposition.prepend
        (ICO.MemoryEmbedding.queryRetraction ICO.PadLabelledCircuit.leftMemory a₀ m₀)
        (ICO.PadLabelledCircuit.compile a₀ m₀ o₀ after))
      ((liftEnvCall (M ⊕ O) (oracles i)).map
        (((Channel.idChannel R).prod
          (ICO.AllChannelPadding.queryEmbedChannel ICO.PadLabelledCircuit.leftMemory)).map X))
      o₁ o₂ = _
    rw [labelledPrepend_stateful, liftEnvCall_queryEmbed,
      queryRetraction_queryEmbed_stateful, ih]
    rfl
  | node instrument next ih =>
    change (∑ k, (runStatefulLabelledTree oracles
      (ICO.PadLabelledCircuit.compile a₀ m₀ o₀ (next k))).comp
      (singleMap (liftEnvOp R (instrument.op k)))) = _
    simp_rw [ih]
    rfl

theorem coincidentLabel_stateful {L R A₀ M O B : Type} [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A₀ × M) O q B)
    (Ψ : Channel (R × A₀) (R × A₀)) (s : Finset L) (hs : q ≤ s.card) :
    runStatefulAtMostTree (fun _ => Ψ) (ICO.CoincidentBudgetLabels.label tree s hs) =
      runStatefulTree Ψ Ψ tree := by
  induction tree generalizing s with
  | stop after => rfl
  | @query q b after ih =>
    let hn : s.Nonempty := Finset.card_pos.mp (by omega)
    ext X o₁ o₂
    change runStatefulAtMostTree (fun _ => Ψ)
      (ICO.CoincidentBudgetLabels.label after (s.erase hn.choose) _)
      ((liftEnvCall M Ψ).map X) o₁ o₂ = _
    rw [ih]
    cases b <;> rfl
  | node I next ih =>
    change (∑ l, (runStatefulAtMostTree (fun _ => Ψ)
      (ICO.CoincidentBudgetLabels.label (next l) s hs)).comp
      (singleMap (liftEnvOp R (I.op l)))) = _
    simp_rw [ih]
    rfl

theorem treePrepend_stateful {R A₀ M O B₁ B₂ : Type}
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    [Fintype B₁] [DecidableEq B₁] [Fintype B₂] [DecidableEq B₂]
    {q : ℕ} (C : Channel B₁ B₂) (tree : BudgetQueryTree.Tree (A₀ × M) O q B₂)
    (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀)) (X : CMatrix (R × B₁)) :
    runStatefulTree Φ₀ Φ₁ (ICO.C6ChoiceCompiler.prepend C tree) X =
      runStatefulTree Φ₀ Φ₁ tree (((Channel.idChannel R).prod C).map X) := by
  simp only [ICO.C6ChoiceCompiler.prepend, runStatefulTree_node,
    ICO.LabelledCircuitComposition.channelInstrument, LinearMap.sum_apply,
    LinearMap.comp_apply, ← map_sum, sum_liftEnvOp_channelKraus]

theorem choice_retract_stateful {R A₀ M : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M]
    (b : Bool) (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀)) (X : CMatrix (R × (A₀ × M))) :
    ((Channel.idChannel R).prod (ICO.C6ChoiceOracle.eraseChoice (A := A₀) (M := M))).map
      ((liftEnvCall M (choiceEnvCall Φ₀ Φ₁)).map
        (((Channel.idChannel R).prod
          (ICO.C6ChoiceOracle.embedChoice (A := A₀) (M := M) b)).map X)) =
      (liftEnvCall M (if b then Φ₁ else Φ₀)).map X := by
  have hce (c : Bool) :
      ICO.C6ChoiceOracle.choiceEmbedding (A := A₀) (M := M) c =
        basisEmbedding (fun p : A₀ × M => ((p.1, c), p.2)) := by
    ext y x
    simp [ICO.C6ChoiceOracle.choiceEmbedding, ICO.MemoryEmbedding.embedding,
      basisEmbedding, Matrix.one_apply]
  set Y := ((Channel.idChannel R).prod
    (ICO.C6ChoiceOracle.embedChoice (A := A₀) (M := M) b)).map X
  have hY_same (r' r'' : R) (a' a'' : A₀) (d : Bool) (m' m'' : M) :
      Y (r', ((a', d), m')) (r'', ((a'', d), m'')) =
        if d = b then X (r', (a', m')) (r'', (a'', m'')) else 0 := by
    dsimp only [Y]
    rw [congrFun (congrFun (idChannel_prod_slice
      (ICO.C6ChoiceOracle.embedChoice (A := A₀) (M := M) b) X r' r'')
      ((a', d), m')) ((a'', d), m'')]
    rw [ICO.C6ChoiceOracle.embedChoice, ICO.ClassicalDilation.isometryChannel_apply]
    let W : CMatrix (A₀ × M) := fun p₁ p₂ => X (r', p₁) (r'', p₂)
    change (ICO.C6ChoiceOracle.choiceEmbedding (A := A₀) (M := M) b * W *
        (ICO.C6ChoiceOracle.choiceEmbedding (A := A₀) (M := M) b).conjTranspose).submatrix
        (fun p : A₀ × M => ((p.1, d), p.2)) (fun p : A₀ × M => ((p.1, d), p.2))
        (a', m') (a'', m'') = _
    rw [← basisEmbedding_compression, ← hce d]
    let Ed := ICO.C6ChoiceOracle.choiceEmbedding (A := A₀) (M := M) d
    let Eb := ICO.C6ChoiceOracle.choiceEmbedding (A := A₀) (M := M) b
    have horth : Ed.conjTranspose * (Eb * W * Eb.conjTranspose) * Ed =
        if d = b then W else 0 := by
      calc Ed.conjTranspose * (Eb * W * Eb.conjTranspose) * Ed
          = ((Ed.conjTranspose * Eb) * W) * (Eb.conjTranspose * Ed) := by
              rw [← Matrix.mul_assoc Ed.conjTranspose (Eb * W) Eb.conjTranspose,
                ← Matrix.mul_assoc Ed.conjTranspose Eb W,
                Matrix.mul_assoc ((Ed.conjTranspose * Eb) * W) Eb.conjTranspose Ed]
        _ = if d = b then W else 0 := by
              by_cases hdb : d = b
              · subst hdb
                simp [Ed, Eb, ICO.C6ChoiceOracle.choiceEmbedding_isometry]
              · simp [Ed, Eb, ICO.C6ChoiceOracle.choiceEmbedding_orthogonal, hdb, Ne.symm hdb]
    rw [horth]
    split_ifs <;> rfl
  set Z := (liftEnvCall M (choiceEnvCall Φ₀ Φ₁)).map Y
  have hZ (r₁ r₂ : R) (a₁ a₂ : A₀) (c : Bool) (m₁ m₂ : M) :
      Z (r₁, ((a₁, c), m₁)) (r₂, ((a₂, c), m₂)) =
        if c = b then ((liftEnvCall M (if b then Φ₁ else Φ₀)).map X)
          (r₁, (a₁, m₁)) (r₂, (a₂, m₂)) else 0 := by
    dsimp only [Z]
    rw [liftEnvCall_apply]
    simp only [choiceEnvCall, Channel.comp, LinearMap.comp_apply, ICO.C6ReindexChannel.apply,
      sector_apply, isometryChannel_apply, Matrix.submatrix_apply,
      Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Fintype.sum_bool]
    have hcomp (d : Bool) :
        ((inclusion (H := fun _ : Bool => R × A₀) d).conjTranspose *
          (Matrix.of (fun u₁ u₂ : R × (A₀ × Bool) => Y (u₁.1, (u₁.2, m₁)) (u₂.1, (u₂.2, m₂)))).submatrix
            (fun y : Σ _ : Bool, R × A₀ => (y.2.1, (y.2.2, y.1)))
            (fun y : Σ _ : Bool, R × A₀ => (y.2.1, (y.2.2, y.1))) *
          inclusion d) =
        if d = b then Matrix.of (fun u₁ u₂ : R × A₀ => X (u₁.1, (u₁.2, m₁)) (u₂.1, (u₂.2, m₂)))
        else 0 := by
      rw [inclusion, basisEmbedding_compression]
      ext u₁ u₂
      simp only [Matrix.submatrix_apply, Matrix.of_apply, hY_same]
      split_ifs <;> rfl
    rw [Matrix.add_apply, inclusion_sandwich_apply, inclusion_sandwich_apply,
      hcomp true, hcomp false]
    cases c <;> cases b <;> simp [liftEnvCall_apply]
  ext ⟨r₁, a₁, m₁⟩ ⟨r₂, a₂, m₂⟩
  rw [congrFun (congrFun (idChannel_prod_slice
    (ICO.C6ChoiceOracle.eraseChoice (A := A₀) (M := M)) Z r₁ r₂) (a₁, m₁)) (a₂, m₂)]
  simp only [ICO.C6ChoiceOracle.eraseChoice, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.conjTranspose_conjTranspose, Fintype.sum_bool]
  let Zslice : CMatrix ((A₀ × Bool) × M) := fun x₁ x₂ => Z (r₁, x₁) (r₂, x₂)
  have h1 (d : Bool) :
      (((ICO.C6ChoiceOracle.choiceEmbedding (A := A₀) (M := M) d).conjTranspose * Zslice *
        ICO.C6ChoiceOracle.choiceEmbedding d : CMatrix (A₀ × M)) (a₁, m₁) (a₂, m₂)) =
      Z (r₁, ((a₁, d), m₁)) (r₂, ((a₂, d), m₂)) := by
    rw [hce d, basisEmbedding_compression]
    rfl
  change (((ICO.C6ChoiceOracle.choiceEmbedding (A := A₀) (M := M) true).conjTranspose * Zslice *
      ICO.C6ChoiceOracle.choiceEmbedding true +
    (ICO.C6ChoiceOracle.choiceEmbedding (A := A₀) (M := M) false).conjTranspose * Zslice *
      ICO.C6ChoiceOracle.choiceEmbedding false : CMatrix (A₀ × M)) (a₁, m₁) (a₂, m₂)) = _
  rw [Matrix.add_apply, h1 true, h1 false, hZ, hZ]
  cases b <;> simp

theorem choiceCompile_stateful {R A₀ M O B : Type}
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A₀ × M) O q B)
    (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀)) :
    runStatefulTree (choiceEnvCall Φ₀ Φ₁) (choiceEnvCall Φ₀ Φ₁)
        (ICO.C6ChoiceCompiler.compile tree) =
      runStatefulTree Φ₀ Φ₁ tree := by
  induction tree with
  | stop after => rfl
  | query b after ih =>
    ext X o₁ o₂
    change runStatefulTree (choiceEnvCall Φ₀ Φ₁) (choiceEnvCall Φ₀ Φ₁)
      (ICO.C6ChoiceCompiler.prepend (ICO.C6ChoiceOracle.embedChoice b)
        (BudgetQueryTree.Tree.query false
          (ICO.C6ChoiceCompiler.prepend ICO.C6ChoiceOracle.eraseChoice
            (ICO.C6ChoiceCompiler.compile after)))) X o₁ o₂ = _
    rw [treePrepend_stateful]
    change runStatefulTree (choiceEnvCall Φ₀ Φ₁) (choiceEnvCall Φ₀ Φ₁)
      (ICO.C6ChoiceCompiler.prepend ICO.C6ChoiceOracle.eraseChoice
        (ICO.C6ChoiceCompiler.compile after))
      ((liftEnvCall M (choiceEnvCall Φ₀ Φ₁)).map
        (((Channel.idChannel R).prod (ICO.C6ChoiceOracle.embedChoice b)).map X)) o₁ o₂ = _
    rw [treePrepend_stateful, choice_retract_stateful, ih]
    rfl
  | node instrument next ih =>
    change (∑ j, (runStatefulTree (choiceEnvCall Φ₀ Φ₁) (choiceEnvCall Φ₀ Φ₁)
      (ICO.C6ChoiceCompiler.compile (next j))).comp
      (singleMap (liftEnvOp R (instrument.op j)))) = _
    simp_rw [ih]
    rfl

theorem sequential_stateful {R A₀ M O B : Type}
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (a₀ : A₀) (m₀ : M) (o₀ : O) (tree : BudgetQueryTree.Tree (A₀ × M) O q B)
    (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀)) :
    runStatefulProtocol (choiceEnvCall Φ₀ Φ₁)
        (ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ tree) =
      runStatefulTree Φ₀ Φ₁ tree := by
  rw [ICO.C6ChoiceCompiler.sequential, ICO.AdaptiveSequentialProtocol.budget,
    adaptiveCompile_stateful, ICO.CoincidentBudgetLabels.exactQueries,
    padCompile_stateful, coincidentLabel_stateful, choiceCompile_stateful]

theorem prepare_stateful {R A₀ M O B : Type}
    [Fintype R] [DecidableEq R] [Fintype A₀] [DecidableEq A₀]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A₀ × M) O q B) (ρ : State B)
    (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀)) (R₀ : CMatrix R) :
    runStatefulTree Φ₀ Φ₁ (ICO.BudgetPreparation.prepare tree ρ)
        (Matrix.kronecker R₀ (rankOneMatrix (fun _ : PUnit => (1 : ℂ)))) =
      runStatefulTree Φ₀ Φ₁ tree (Matrix.kronecker R₀ ρ.matrix) := by
  rw [ICO.BudgetPreparation.prepare, ICO.BudgetPreparation.precompose,
    runStatefulTree_node, LinearMap.sum_apply]
  simp only [ICO.BudgetPreparation.instrument, LinearMap.comp_apply]
  rw [← map_sum, ← idChannel_prod_ofKraus (Channel.prepare (fun _ : PUnit => ρ))
    (ICO.BudgetPreparation.kraus _) (ICO.BudgetPreparation.kraus_map _).symm]
  congr 1
  ext ⟨r₁, b₁⟩ ⟨r₂, b₂⟩
  rw [congrFun (congrFun (idChannel_prod_slice
    (Channel.prepare (fun _ : PUnit => ρ)) _ r₁ r₂) b₁) b₂]
  have hsl : (fun u₁ u₂ : PUnit =>
      Matrix.kronecker R₀ (rankOneMatrix (fun _ : PUnit => (1 : ℂ))) (r₁, u₁) (r₂, u₂)) =
      R₀ r₁ r₂ • rankOneMatrix (fun _ : PUnit => (1 : ℂ)) := by
    ext u₁ u₂
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [hsl, map_smul]
  have hp : (Channel.prepare (fun _ : PUnit => ρ)).map
      (rankOneMatrix (fun _ : PUnit => (1 : ℂ))) = ρ.matrix := by
    simp [Channel.prepare, Channel.prepareMap, rankOneMatrix, Matrix.vecMulVec]
  rw [hp]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]

private theorem cacheHiddenInitialMatrix_zero_zero (Q : ℕ)
    (p₁ p₂ : TensorPowerProfile (A × A) 0) :
    cacheHiddenInitialMatrix (A := A) Q ⟨0, p₁⟩ ⟨0, p₂⟩ = 1 := by
  have hp₁ : p₁ = emptyPairProfile (A := A) := emptyPairProfile_unique _ _
  have hp₂ : p₂ = emptyPairProfile (A := A) := emptyPairProfile_unique _ _
  subst hp₁
  subst hp₂
  simp [cacheHiddenInitialMatrix, cacheHiddenVacuum, rankOneMatrix_apply]

private theorem cacheHiddenInitialMatrix_ne_zero (Q : ℕ)
    (u₁ u₂ : CacheHidden A Q) (h : u₁.1 ≠ 0 ∨ u₂.1 ≠ 0) :
    cacheHiddenInitialMatrix (A := A) Q u₁ u₂ = 0 := by
  simp only [cacheHiddenInitialMatrix, rankOneMatrix_apply]
  rcases h with h1 | h2
  · have hn1 : u₁ ≠ cacheHiddenVacuum (A := A) Q := fun he => h1 (congrArg Sigma.fst he)
    rw [if_neg hn1, zero_mul]
  · have hn2 : u₂ ≠ cacheHiddenVacuum (A := A) Q := fun he => h2 (congrArg Sigma.fst he)
    rw [if_neg hn2, star_zero, mul_zero]

theorem initial_submatrix_eq_cacheTrajectoryInitial [Nontrivial A] {M O : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (v : (A × Bool) × M → ℂ) (Q : ℕ) :
    (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) Q) (rankOneMatrix v)).submatrix
      (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory 0)).symm
      (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory 0)).symm =
      ICO.C6CacheTrajectory.initial Q (ICO.C6RawWeightedEndpoint.cacheInput tail v) := by
  ext ⟨s₁, ⟨a₁, p₁⟩, ⟨b₁, m₁⟩⟩ ⟨s₂, ⟨a₂, p₂⟩, ⟨b₂, m₂⟩⟩
  rw [ICO.C6CacheTrajectory.initial, embed, conjugate_inclusion_apply]
  have hvec (x : Cache (A := A) (M := Bool × tail.tailMemory 0) 0) :
      (basisEmbedding ICO.C6ModeFockVacuum.vacuumCache *ᵥ
        ICO.C6RawDecoded.smallInput (ICO.C6RawWeightedEndpoint.physicalInput tail v)) x =
      v ((x.1.1, x.2.1), x.2.2) := by
    have hx : x = ICO.C6ModeFockVacuum.vacuumCache (x.1.1, x.2) := by
      rcases x with ⟨⟨a, p⟩, bm⟩
      exact Prod.ext (Prod.ext rfl (ICO.C6ModeFockVacuum.profile_zero_unique _ _)) rfl
    simp only [Matrix.mulVec, dotProduct, basisEmbedding, Matrix.submatrix_apply,
      Matrix.one_apply, id_eq, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (x.1.1, x.2)]
    · rw [if_pos hx]
      rfl
    · intro z _ hne
      rw [if_neg]
      intro hxz
      apply hne
      exact Prod.ext (congrArg (fun u => u.1.1) hxz).symm (congrArg Prod.snd hxz).symm
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hz0 : (0 : Fin (Q + 1)) = ⟨0, Nat.zero_lt_succ Q⟩ := rfl
  by_cases h1 : s₁ = 0
  · subst h1
    by_cases h2 : s₂ = 0
    · subst h2
      rw [dif_pos hz0, dif_pos hz0]
      simp only [Matrix.submatrix_apply, hiddenChoiceGradedEquiv, Equiv.coe_fn_symm_mk,
        Matrix.kronecker, Matrix.kroneckerMap_apply,
        cacheHiddenInitialMatrix_zero_zero, one_mul,
        ICO.C6RawWeightedEndpoint.cacheInput, rankOneMatrix_apply, hvec]
      rfl
    · have h2' : s₂ ≠ ⟨0, Nat.zero_lt_succ Q⟩ := h2
      rw [dif_pos hz0, dif_neg h2']
      simp only [Matrix.submatrix_apply, hiddenChoiceGradedEquiv, Equiv.coe_fn_symm_mk,
        Matrix.kronecker, Matrix.kroneckerMap_apply]
      rw [cacheHiddenInitialMatrix_ne_zero Q ⟨0, p₁⟩ ⟨s₂, p₂⟩ (Or.inr h2), zero_mul]
  · have h1' : s₁ ≠ ⟨0, Nat.zero_lt_succ Q⟩ := h1
    rw [dif_neg h1']
    simp only [Matrix.submatrix_apply, hiddenChoiceGradedEquiv, Equiv.coe_fn_symm_mk,
      Matrix.kronecker, Matrix.kroneckerMap_apply]
    rw [cacheHiddenInitialMatrix_ne_zero Q ⟨s₁, p₁⟩ ⟨s₂, p₂⟩ (Or.inl h1), zero_mul]

theorem output_submatrix_eq_partialTraceA [Nontrivial A] {M : Type}
    [Fintype M] [DecidableEq M] (Q : ℕ)
    (Y : CMatrix (CacheHidden A Q × ((A × Bool) × M))) :
    (ICO.C6CacheVisibleOutput.output Q).map
      (Y.submatrix (hiddenChoiceGradedEquiv (A := A) Q M).symm
        (hiddenChoiceGradedEquiv (A := A) Q M).symm) =
      partialTraceA Y := by
  ext ⟨⟨a₁, b₁⟩, m₁⟩ ⟨⟨a₂, b₂⟩, m₂⟩
  rw [ICO.C6CacheVisibleOutput.output_apply, Matrix.submatrix_apply,
    ICO.C6CacheVisible.visible_apply, Matrix.sum_apply, partialTraceA, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [ICO.C6CacheVisible.sectorVisible_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [embed, inclusion, basisEmbedding_compression]
  rfl

theorem runStatefulTail_submatrix_eq_gradedRun [Nontrivial A] {M O : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q) (Q : ℕ)
    (Φ₀ Φ₁ : Channel (CacheHidden A Q × A) (CacheHidden A Q × A))
    (v : (A × Bool) × M → ℂ) (t : ℕ) :
    (runStatefulTail tail (choiceEnvCall Φ₀ Φ₁)
      (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) Q) (rankOneMatrix v)) t).submatrix
      (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory t)).symm
      (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory t)).symm =
    ICO.C6ChannelTrajectory.run
      (fun i =>
        (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory (i + 1))).symm).comp
          ((statefulChoiceStep Φ₀ Φ₁
              (ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
              (ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i))).comp
            (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory i)))))
      (ICO.C6CacheTrajectory.initial Q (ICO.C6RawWeightedEndpoint.cacheInput tail v)) t := by
  induction t with
  | zero => exact initial_submatrix_eq_cacheTrajectoryInitial tail v Q
  | succ t ih =>
    dsimp only [runStatefulTail, ICO.C6ChannelTrajectory.run]
    rw [← ih]
    dsimp only [Channel.comp, LinearMap.comp_apply, statefulChoiceStep]
    rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply, isometryChannel_apply]
    have hsub :
        (((runStatefulTail tail (choiceEnvCall Φ₀ Φ₁)
            (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) Q) (rankOneMatrix v)) t).submatrix
          (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory t)).symm
          (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory t)).symm).submatrix
          (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory t))
          (hiddenChoiceGradedEquiv (A := A) Q (tail.tailMemory t))) =
        runStatefulTail tail (choiceEnvCall Φ₀ Φ₁)
          (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) Q) (rankOneMatrix v)) t := by
      ext u₁ u₂; simp
    have hK : (ICO.C6RawFlagSlices.smallKnown (tail.tailKnown t)).submatrix
        (Equiv.prodAssoc A Bool (tail.tailMemory (t + 1)))
        (Equiv.prodAssoc A Bool (tail.tailMemory t)) = tail.tailKnown t := by
      ext u₁ u₂; simp [ICO.C6RawFlagSlices.smallKnown]
    rw [hsub, hK]

/-- **Unpadded `BudgetQueryTree` ↔ compiled `protocolLabelCacheDensity` bridge**:
running an adaptive `tree` with mixed input `ρ` directly against the explicit label cache of
Definition `def:cache` produces the exact same output state as applying the compiled sequential
protocol's terminal channel to `protocolLabelCacheDensity` (with zero dummy-padding distortion). -/
theorem treeLabelCacheDensity_eq_compiled [Nontrivial A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : BudgetQueryTree.Tree (A × M) O (q + 1) B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ) (hqd : q + 1 ≤ Fintype.card A) :
    let p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ)
    p.heading.tail.terminalChannel.map
      (protocolLabelCacheDensity p.heading.tail H
        (p.heading.pre *ᵥ (fun _ : PUnit => (1 : ℂ))) (q + 1) hqd) =
      treeLabelCacheDensity tree ρ H hqd := by
  dsimp only [treeLabelCacheDensity]
  rw [← prepare_stateful, ← sequential_stateful a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ),
    ← runStatefulProtocol_heading]
  set p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ)
  set v := p.heading.pre *ᵥ (fun _ : PUnit => (1 : ℂ))
  have hinit :
      liftEnvOp (CacheHidden A (q + 1)) p.heading.pre *
        Matrix.kronecker (cacheHiddenInitialMatrix (A := A) (q + 1))
          (rankOneMatrix (fun _ : PUnit => (1 : ℂ))) *
        (liftEnvOp (CacheHidden A (q + 1)) p.heading.pre).conjTranspose =
      Matrix.kronecker (cacheHiddenInitialMatrix (A := A) (q + 1)) (rankOneMatrix v) := by
    simp only [liftEnvOp, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one,
      ← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  rw [hinit]
  congr 1
  rw [Channel.traceOutLeft_map,
    ← output_submatrix_eq_partialTraceA (q + 1),
    runStatefulTail_submatrix_eq_gradedRun p.heading.tail (q + 1)]
  rfl

/-- Unpadded `BudgetQueryTree` ↔ compiled `protocolReferenceCacheDensity` bridge. -/
theorem treeReferenceCacheDensity_eq_compiled [Nontrivial A] {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (a₀ : A) (m₀ : M) (o₀ : O)
    (tree : BudgetQueryTree.Tree (A × M) O (q + 1) B) (ρ : State B)
    (hqd : q + 1 ≤ Fintype.card A) :
    let p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ)
    p.heading.tail.terminalChannel.map
      (protocolReferenceCacheDensity p.heading.tail
        (p.heading.pre *ᵥ (fun _ : PUnit => (1 : ℂ))) (q + 1) hqd) =
      treeReferenceCacheDensity tree ρ hqd := by
  dsimp only [treeReferenceCacheDensity]
  rw [← prepare_stateful, ← sequential_stateful a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ),
    ← runStatefulProtocol_heading]
  set p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ)
  set v := p.heading.pre *ᵥ (fun _ : PUnit => (1 : ℂ))
  have hinit :
      liftEnvOp (CacheHidden A (q + 1)) p.heading.pre *
        Matrix.kronecker (cacheHiddenInitialMatrix (A := A) (q + 1))
          (rankOneMatrix (fun _ : PUnit => (1 : ℂ))) *
        (liftEnvOp (CacheHidden A (q + 1)) p.heading.pre).conjTranspose =
      Matrix.kronecker (cacheHiddenInitialMatrix (A := A) (q + 1)) (rankOneMatrix v) := by
    simp only [liftEnvOp, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one,
      ← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  rw [hinit]
  congr 1
  rw [Channel.traceOutLeft_map,
    ← output_submatrix_eq_partialTraceA (q + 1),
    runStatefulTail_submatrix_eq_gradedRun p.heading.tail (q + 1)]
  rfl

theorem empty_memory_runStatefulTree {R A₀ M O B : Type} [Fintype R] [DecidableEq R]
    [Fintype A₀] [DecidableEq A₀] [Fintype M] [DecidableEq M] [IsEmpty M]
    [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A₀ × M) O q B)
    (Φ₀ Φ₁ : Channel (R × A₀) (R × A₀))
    (Ψ₀ Ψ₁ : Channel (A₀ × M) (A₀ × M))
    (R₀ : CMatrix R) (hR₀ : R₀.trace = 1) (X : CMatrix B) :
    runStatefulTree Φ₀ Φ₁ tree (Matrix.kronecker R₀ X) =
      (tree.channel Ψ₀ Ψ₁).map X := by
  induction tree with
  | stop after =>
    change after.map (partialTraceA (Matrix.kronecker R₀ X)) = after.map X
    rw [partialTraceA_kronecker, hR₀]
    congr 1
    exact one_smul ℂ X
  | query b after ih =>
    have h1 : (liftEnvCall M (if b then Φ₁ else Φ₀)).map (Matrix.kronecker R₀ X) =
        Matrix.kronecker R₀ (0 : CMatrix (A₀ × M)) := by
      ext ⟨_, _, m⟩ _; exact isEmptyElim m
    have h2 : (if b then Ψ₁ else Ψ₀).map X = (0 : CMatrix (A₀ × M)) := by
      ext ⟨_, m⟩ _; exact isEmptyElim m
    change runStatefulTree Φ₀ Φ₁ after
      ((liftEnvCall M (if b then Φ₁ else Φ₀)).map (Matrix.kronecker R₀ X)) =
      (after.channel Ψ₀ Ψ₁).map ((if b then Ψ₁ else Ψ₀).map X)
    rw [h1, h2, ih 0]
  | node I next ih =>
    rw [runStatefulTree_node, LinearMap.sum_apply]
    change (∑ l, ((runStatefulTree Φ₀ Φ₁ (next l)).comp
        (singleMap (liftEnvOp R (I.op l)))) (Matrix.kronecker R₀ X)) =
      adaptiveMap I (fun l => (next l).channel Ψ₀ Ψ₁) X
    rw [adaptiveMap_apply]
    simp only [LinearMap.comp_apply, singleMap_apply]
    apply Finset.sum_congr rfl
    intro l _
    have hk : liftEnvOp R (I.op l) * Matrix.kronecker R₀ X *
        (liftEnvOp R (I.op l)).conjTranspose =
      Matrix.kronecker R₀ (I.op l * X * (I.op l).conjTranspose) := by
      simp only [liftEnvOp, Matrix.kronecker, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul, Matrix.mul_one]
    rw [hk, ih l]

end StatefulCompiler

end Bridges

/-! ## 3. Proposition `prop:cache` (`eq:eps-cache`): Single-Experiment Cache Approximation -/

section PropCache

/-- Haar recording error term `ε_rec` of `eq:eps-cache` in Proposition `prop:cache`. -/
def epsRec (q d : ℕ) : ℝ :=
  9 * (2 * (q : ℝ)) * (2 * (q : ℝ) + 1) / (d : ℝ) ^ ((1 : ℝ) / 8)

/-- Forward Fock-deletion error term `ε_2` of `eq:eps-cache` in Proposition `prop:cache`. -/
def eps2 (q d : ℕ) : ℝ :=
  ICO.C6Bounds.forwardError q d

/-- Polar-defect error term `ε_3` of `eq:eps-cache` in Proposition `prop:cache`. -/
def eps3 (q d : ℕ) : ℝ :=
  7 * (q : ℝ) * ICO.C6Bounds.creatorError (2 * (q : ℝ)) d

/-- Fresh-subspace inverse error term `ε_4` of `eq:eps-cache` in Proposition `prop:cache`. -/
def eps4 (q d : ℕ) : ℝ :=
  ICO.C6Bounds.birthError q d

/-- Raw-birth + uniform-history error term `ε_5` of `eq:eps-cache` in Proposition `prop:cache`. -/
def eps5 (q d : ℕ) : ℝ :=
  (q : ℝ) * ((q : ℝ) - 1) / (d : ℝ)

/-- Total error `ε_rec + ε_2 + ε_3 + ε_4 + ε_5` of Proposition `prop:cache` (`eq:eps-cache`). -/
def epsCache (q d : ℕ) : ℝ :=
  epsRec q d + eps2 q d + eps3 q d + eps4 q d + eps5 q d

/-- Exact 1-based index check matching `ε_2` in `eq:eps-cache`:
`ICO.C6Bounds.forwardError q d = ∑_{t=1}^q √(2(2t - 1) / (d - 2(t - 1)))`. -/
theorem eps2_eq_Icc (q d : ℕ) :
    eps2 q d =
      ∑ t ∈ Finset.Icc 1 q,
        Real.sqrt (2 * (2 * (t : ℝ) - 1) / ((d : ℝ) - 2 * ((t : ℝ) - 1))) := by
  dsimp only [eps2, ICO.C6Bounds.forwardError]
  refine Finset.sum_bij (fun (i : Fin q) _ => i.val + 1) ?_ ?_ ?_ ?_
  · intro i _
    dsimp only
    have := i.isLt
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i₁ _ i₂ _ h
    dsimp only at h
    exact Fin.ext (by omega)
  · intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨ht1, htq⟩
    exact ⟨⟨t - 1, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
  · intro i _
    dsimp only
    simp only [Nat.cast_add, Nat.cast_one]
    congr 1
    ring

/-- Exact formula check matching `ε_3` in `eq:eps-cache`:
`7 q (√(4 q (2q + 1) / d) + 2q / d)`. -/
theorem eps3_eq_formula (q d : ℕ) :
    eps3 q d =
      7 * (q : ℝ) *
        (Real.sqrt (4 * (q : ℝ) * (2 * (q : ℝ) + 1) / (d : ℝ)) +
          2 * (q : ℝ) / (d : ℝ)) := by
  dsimp only [eps3, ICO.C6Bounds.creatorError]
  ring_nf

/-- Exact 1-based index check matching `ε_4` in `eq:eps-cache`:
`ICO.C6Bounds.birthError q d = ∑_{t=2}^q (√((2t - 3) / (d - t + 2)) + √((2t - 2) / (d - t + 1)))`. -/
theorem eps4_eq_Icc (q d : ℕ) :
    eps4 q d =
      ∑ t ∈ Finset.Icc 2 q,
        (Real.sqrt ((2 * (t : ℝ) - 3) / ((d : ℝ) - (t : ℝ) + 2)) +
          Real.sqrt ((2 * (t : ℝ) - 2) / ((d : ℝ) - (t : ℝ) + 1))) := by
  dsimp only [eps4, ICO.C6Bounds.birthError]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add]
  refine Finset.sum_bij (fun (i : Fin q) _ => i.val + 1) ?_ ?_ ?_ ?_
  · intro i hi
    dsimp only
    have := i.isLt
    have hne : ¬ i.val = 0 := (Finset.mem_filter.mp hi).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i₁ _ i₂ _ h
    dsimp only at h
    exact Fin.ext (by omega)
  · intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨ht2, htq⟩
    exact ⟨⟨t - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩,
      by dsimp only; omega⟩
  · intro i _
    dsimp only
    simp only [Nat.cast_add, Nat.cast_one]
    congr 1 <;> congr 1 <;> ring

theorem protocolLabelCacheDensity_pos {A M O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A × Bool) × M → ℂ)
    (n : ℕ) (hQ : n ≤ Fintype.card A) :
    (protocolLabelCacheDensity tail H v n hQ).PosSemidef := by
  have hp : (ICO.C6CacheTrajectory.initial n
      (ICO.C6RawWeightedEndpoint.cacheInput tail v)).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) _
      (ICO.C6SharedPairBound.cacheInput_pos tail v)
  exact (ICO.C6CacheVisibleOutput.output n).mapsPositive _
    (ICO.C6ChannelTrajectory.run_pos _ _ hp n)

theorem protocolReferenceCacheDensity_pos {A M O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (v : (A × Bool) × M → ℂ) (n : ℕ) (hQ : n ≤ Fintype.card A) :
    (protocolReferenceCacheDensity tail v n hQ).PosSemidef := by
  have hp : (ICO.C6CacheTrajectory.initial n
      (ICO.C6RawWeightedEndpoint.cacheInput tail v)).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive _ (conjugate_cp _) _
      (ICO.C6SharedPairBound.cacheInput_pos tail v)
  exact (ICO.C6CacheVisibleOutput.output n).mapsPositive _
    (ICO.C6ChannelTrajectory.run_pos _ _ hp n)

/-- **Proposition `prop:cache` (`eq:eps-cache`), purified sequential protocol form**:
for any sequential protocol `tail`, any relative unitary `H : Matrix.unitaryGroup A ℂ`
(covering `H = 1` for `(Δ_U, Δ_U)` and arbitrary `H` for `(Δ_U, Δ_{UH})`), any normalized initial
state `v`, and `1 ≤ n` with `4 * n ≤ d`, the Haar-averaged actual visible state `haarDensity` is
within `ε_rec + ε_2 + ε_3 + ε_4 + ε_5` of the explicit Definition `def:cache` label-cache state
`protocolLabelCacheDensity`. -/
theorem prop_cache_protocol_distance {A M O : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A × Bool) × M → ℂ)
    (hv : ‖WithLp.toLp 2 v‖ = 1) (n : ℕ) (hn : 1 ≤ n) (hfour : 4 * n ≤ Fintype.card A) :
    normalizedTraceDistance
        (ICO.C6SharedEndpoint.haarDensity tail H v n)
        (protocolLabelCacheDensity tail H v n (by omega)) ≤
      9 * (2 * (n : ℝ)) * (2 * (n : ℝ) + 1) / (Fintype.card A : ℝ) ^ ((1 : ℝ) / 8) +
        ICO.C6Bounds.forwardError n (Fintype.card A) +
        7 * (n : ℝ) * ICO.C6Bounds.creatorError (2 * (n : ℝ)) (Fintype.card A) +
        ICO.C6Bounds.birthError n (Fintype.card A) +
        (n : ℝ) * ((n : ℝ) - 1) / (Fintype.card A : ℝ) := by
  have hpos : 0 < n := by omega
  have hQ : n < Fintype.card A := by omega
  have hnd : 2 * n < Fintype.card A := by omega
  let T := 2 * Fintype.card (A × A) + 2 * n + 1
  have hT : 2 * Fintype.card (A × A) ≤ T := by dsimp [T]; omega
  have h : 2 * n + 1 ≤ T := by dsimp [T]; omega
  let R : ℝ := (Fintype.card A : ℝ) ^ ((1 : ℝ) / 8)
  have hd_pos : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos (α := A)
  have hR : 1 ≤ R :=
    Real.one_le_rpow (by exact_mod_cast Fintype.card_pos (α := A)) (by norm_num)
  have hdim : (Fintype.card A : ℝ) = R ^ 8 := by
    dsimp only [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd_pos.le]
    norm_num
  have h1 := ICO.C6PhysicalFresh.shared_haar_fresh tail H v hv n hT h hfour R hR hdim
  rw [ICO.C6PhysicalCosts.deletionCost_sum, ICO.C6PhysicalCosts.freshCost_sum,
    ICO.C6PhysicalCosts.delta_creatorError] at h1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h1
  have h2 := ICO.C6FreshRawEndpoint.fresh_raw_distance tail H v hv.le n h hnd
  rw [ICO.C6WeightedHistoryOutput.sum_deficit_cost,
    ICO.C6RawWeightedEndpoint.rawDensity_weighted tail H v n hpos hQ h hnd] at h2
  have h3 := weighted_cacheDensity_labelCache_distance tail H v hv n hpos hQ
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  rw [hsub] at h2 h3
  have ht1 := normalizedTraceDistance_triangle
    (ICO.C6SharedEndpoint.haarDensity tail H v n)
    (ICO.C6PhysicalFresh.freshDensity tail H v n h)
    (ICO.C6RawWeightedEndpoint.cacheDensity tail H v n hpos hQ)
  have ht2 := normalizedTraceDistance_triangle
    (ICO.C6SharedEndpoint.haarDensity tail H v n)
    (ICO.C6RawWeightedEndpoint.cacheDensity tail H v n hpos hQ)
    (protocolLabelCacheDensity tail H v n hQ.le)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnn : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) / (Fintype.card A : ℝ) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hd_pos.le
  dsimp only [R] at h1
  have h5 : (n : ℝ) * ((n : ℝ) - 1) / (2 * (Fintype.card A : ℝ)) +
      (n : ℝ) * ((n : ℝ) - 1) / (4 * (Fintype.card A : ℝ)) ≤
      (n : ℝ) * ((n : ℝ) - 1) / (Fintype.card A : ℝ) := by
    have heq : (n : ℝ) * ((n : ℝ) - 1) / (2 * (Fintype.card A : ℝ)) +
        (n : ℝ) * ((n : ℝ) - 1) / (4 * (Fintype.card A : ℝ)) =
        (3 / 4 : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) / (Fintype.card A : ℝ)) := by ring
    rw [heq]
    linarith
  linarith

theorem epsCache_nonneg (q d : ℕ) (hq : 1 ≤ q) :
    0 ≤ epsCache q d := by
  dsimp only [epsCache, epsRec, eps2, eps3, eps4, eps5]
  unfold ICO.C6Bounds.forwardError ICO.C6Bounds.creatorError ICO.C6Bounds.birthError
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h5 : 0 ≤ (q : ℝ) * ((q : ℝ) - 1) / (d : ℝ) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (Nat.cast_nonneg d)
  have h1 : 0 ≤ 9 * (2 * (q : ℝ)) * (2 * (q : ℝ) + 1) / (d : ℝ) ^ ((1 : ℝ) / 8) := by positivity
  have h2 : 0 ≤ ∑ i : Fin q, Real.sqrt (2 * (2 * (i : ℝ) + 1) / ((d : ℝ) - 2 * (i : ℝ))) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have h3 : 0 ≤ 7 * (q : ℝ) *
      (Real.sqrt (2 * (2 * (q : ℝ)) * (2 * (q : ℝ) + 1) / (d : ℝ)) + 2 * (q : ℝ) / (d : ℝ)) := by
    positivity
  have h4 : 0 ≤ ∑ i : Fin q, (if i.val = 0 then 0 else
      Real.sqrt ((2 * (i : ℝ) - 1) / ((d : ℝ) - (i : ℝ) + 1)) +
        Real.sqrt (2 * (i : ℝ) / ((d : ℝ) - (i : ℝ)))) := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  linarith

/-- **Proposition `prop:cache` (`eq:eps-cache`), adaptive `BudgetQueryTree` mixed-input form**:
for any adaptive `BudgetQueryTree.Tree (A × M) O q B`, any mixed input state `ρ : State B`,
any relative basis `H : Matrix.unitaryGroup A ℂ` (both `H = 1` for `(Δ_U, Δ_U)` and any `H` for
`(Δ_U, Δ_{UH})`), and `1 ≤ q` with `4 * q ≤ d`, the Haar-averaged output state `mubDensity tree ρ H`
and the direct unpadded label-cache output state `treeLabelCacheDensity tree ρ H` satisfy
`TD(ρ_actual, ρ_cache) ≤ ε_rec + ε_2 + ε_3 + ε_4 + ε_5`. -/
theorem prop_cache_tree_distance {A M O B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A × M) O q B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ) (hq : 1 ≤ q) (hfour : 4 * q ≤ Fintype.card A) :
    normalizedTraceDistance
        (mubDensity tree ρ H)
        (treeLabelCacheDensity tree ρ H (by omega)) ≤
      9 * (2 * (q : ℝ)) * (2 * (q : ℝ) + 1) / (Fintype.card A : ℝ) ^ ((1 : ℝ) / 8) +
        ICO.C6Bounds.forwardError q (Fintype.card A) +
        7 * (q : ℝ) * ICO.C6Bounds.creatorError (2 * (q : ℝ)) (Fintype.card A) +
        ICO.C6Bounds.birthError q (Fintype.card A) +
        (q : ℝ) * ((q : ℝ) - 1) / (Fintype.card A : ℝ) := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hm =>
    letI := hm
    have hmub : mubDensity tree ρ H =
        (tree.channel (hidden (1 : Matrix.unitaryGroup A ℂ))
          (hidden (1 : Matrix.unitaryGroup A ℂ))).map ρ.matrix := by
      unfold mubDensity
      have hconst (U : Matrix.unitaryGroup A ℂ) :
          (tree.channel (hidden U) (hidden (U * H))).map ρ.matrix =
            (tree.channel (hidden (1 : Matrix.unitaryGroup A ℂ))
              (hidden (1 : Matrix.unitaryGroup A ℂ))).map ρ.matrix := by
        rw [ICO.C6OperationalDecision.empty_channel_unique (hidden (M := M) U)
              (hidden (M := M) 1),
          ICO.C6OperationalDecision.empty_channel_unique (hidden (M := M) (U * H))
              (hidden (M := M) 1)]
      simp_rw [hconst]
      simp
    have htree : treeLabelCacheDensity tree ρ H (by omega) =
        (tree.channel (hidden (1 : Matrix.unitaryGroup A ℂ))
          (hidden (1 : Matrix.unitaryGroup A ℂ))).map ρ.matrix :=
      empty_memory_runStatefulTree tree _ _ _ _
        (cacheHiddenInitialMatrix (A := A) q) (cacheHiddenInitialMatrix_trace q) ρ.matrix
    rw [hmub, htree, normalizedTraceDistance_self]
    exact epsCache_nonneg q (Fintype.card A) hq
  | inr hm =>
    letI := hm
    letI : Nonempty O := ((tree.channel (hidden (1 : Matrix.unitaryGroup A ℂ))
      (hidden (1 : Matrix.unitaryGroup A ℂ))).applyState ρ).nonempty
    letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    cases q with
    | zero => omega
    | succ q' =>
      let a₀ : A := Classical.arbitrary A
      let m₀ : M := Classical.arbitrary M
      let o₀ : O := Classical.arbitrary O
      let p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ)
      let v := p.heading.pre *ᵥ (fun _ : PUnit => (1 : ℂ))
      have hv : ‖WithLp.toLp 2 v‖ = 1 :=
        ICO.C6SharedOutput.prepared_norm_eq p _ ICO.BudgetPreparation.initial_mass
      rw [← ICO.C6SharedOutput.mixed_tree_output a₀ m₀ o₀ tree ρ H,
        ← treeLabelCacheDensity_eq_compiled a₀ m₀ o₀ tree ρ H (by omega)]
      refine (ICO.RecordingDistance.distance_contract
        p.heading.tail.terminalChannel.map
        p.heading.tail.terminalChannel.traceNonincreasingCP_map _ _
        (ICO.C6SharedOutput.haarDensity_pos p.heading.tail H v (q' + 1))
        (protocolLabelCacheDensity_pos p.heading.tail H v (q' + 1) (by omega))).trans ?_
      exact prop_cache_protocol_distance p.heading.tail H v hv (q' + 1) (by omega) hfour

/-- Specialization of `prop_cache_tree_distance` to `H = 1` (`sameDensity` vs `treeSameLabelCacheDensity`). -/
theorem prop_cache_same_tree_distance {A M O B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A × M) O q B) (ρ : State B)
    (hq : 1 ≤ q) (hfour : 4 * q ≤ Fintype.card A) :
    normalizedTraceDistance
        (sameDensity tree ρ)
        (treeSameLabelCacheDensity tree ρ (by omega)) ≤
      epsCache q (Fintype.card A) := by
  have h1 : sameDensity tree ρ = mubDensity tree ρ 1 := by
    simp only [mubDensity, sameDensity, mul_one]
  rw [h1]
  exact prop_cache_tree_distance tree ρ 1 hq hfour

end PropCache

/-! ## 4. Lemma `lem:reference-invariant` and Reference-Cache Distance (`sec:invariant`) -/

section ReferenceInvariant

/-- First-quantized decoding of `ν` symmetric pairs together with any accessible register `B`
into `(ν stored labels) × (ν stored images × B)`. -/
def pairRegisterDecode {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ν : ℕ) :
    Matrix (TensorPower A ν × (TensorPower A ν × B))
      (TensorPowerProfile (A × A) ν × B) ℂ :=
  (Matrix.kronecker
      ((occupationEmbedding (a := A × A) ν).submatrix
        (ICO.C6WordSplit.labelImageEquiv (A := A) ν).symm id)
      (1 : CMatrix B)).submatrix
    (Equiv.prodAssoc (TensorPower A ν) (TensorPower A ν) B).symm id

theorem pairRegisterDecode_gram {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ν : ℕ) :
    (pairRegisterDecode (A := A) (B := B) ν).conjTranspose *
      pairRegisterDecode (A := A) (B := B) ν = 1 := by
  have hp : (((occupationEmbedding (a := A × A) ν).submatrix
        (ICO.C6WordSplit.labelImageEquiv (A := A) ν).symm id).conjTranspose *
      ((occupationEmbedding (a := A × A) ν).submatrix
        (ICO.C6WordSplit.labelImageEquiv (A := A) ν).symm id)) = 1 := by
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ id (ICO.C6WordSplit.labelImageEquiv (A := A) ν).symm id,
      occupationEmbedding_gram, Matrix.submatrix_id_id]
  rw [pairRegisterDecode, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ id
      (Equiv.prodAssoc (TensorPower A ν) (TensorPower A ν) B).symm id]
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, hp, Matrix.one_mul, Matrix.one_kronecker_one,
    Matrix.submatrix_id_id]

theorem pairRegisterDecode_intertwine {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (T : Matrix.unitaryGroup A ℂ) (ν : ℕ) :
    commonRotation (Z := TensorPower A ν × B) T ν * pairRegisterDecode (A := A) (B := B) ν =
      pairRegisterDecode (A := A) (B := B) ν *
        Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν) (1 : CMatrix B) := by
  have hocc := ICO.C6WordSplit.occupation_label_intertwine T ν
  have hk := congrArg (fun M => (Matrix.kronecker M (1 : CMatrix B)).submatrix
    (Equiv.prodAssoc (TensorPower A ν) (TensorPower A ν) B).symm id) hocc
  dsimp only at hk
  have hkr {X Y Z : Type} [Fintype Y] (M₁ : Matrix X Y ℂ) (M₂ : Matrix Y Z ℂ) :
      Matrix.kronecker (M₁ * M₂) (1 : CMatrix B) =
        Matrix.kronecker M₁ (1 : CMatrix B) * Matrix.kronecker M₂ (1 : CMatrix B) := by
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [hkr _ _, hkr _ _,
    ← Matrix.submatrix_mul_equiv _ _
      (Equiv.prodAssoc (TensorPower A ν) (TensorPower A ν) B).symm
      (Equiv.prodAssoc (TensorPower A ν) (TensorPower A ν) B).symm id,
    ← Matrix.submatrix_mul_equiv _ _
      (Equiv.prodAssoc (TensorPower A ν) (TensorPower A ν) B).symm (Equiv.refl _) id] at hk
  have hrot :
      (Matrix.kronecker
        (Matrix.kronecker (unitaryTensorPowerMatrix T ν : CMatrix (TensorPower A ν))
          (1 : CMatrix (TensorPower A ν)))
        (1 : CMatrix B)).submatrix
        (Equiv.prodAssoc (TensorPower A ν) (TensorPower A ν) B).symm
        (Equiv.prodAssoc (TensorPower A ν) (TensorPower A ν) B).symm =
      commonRotation (Z := TensorPower A ν × B) T ν := by
    ext ⟨w₁, v₁, b₁⟩ ⟨w₂, v₂, b₂⟩
    simp only [commonRotation, Matrix.submatrix_apply,
      Equiv.prodAssoc_symm_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
    by_cases hv : v₁ = v₂
    · subst hv
      by_cases hb : b₁ = b₂
      · subst hb; simp
      · simp [hb]
    · simp [hv]
  rw [hrot] at hk
  exact hk

theorem pairRegisterDecode_commonInvariant {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ν : ℕ) (X : CMatrix (TensorPowerProfile (A × A) ν × B))
    (hX : ∀ T : Matrix.unitaryGroup A ℂ,
      Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν) (1 : CMatrix B) * X =
        X * Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν) (1 : CMatrix B)) :
    CommonInvariant ν
      (pairRegisterDecode (A := A) (B := B) ν * X *
        (pairRegisterDecode (A := A) (B := B) ν).conjTranspose) := by
  intro T
  let U_in : Matrix.unitaryGroup (TensorPowerProfile (A × A) ν × B) ℂ :=
    tensorUnitary (symmetricRotation (leftEdgeUnitary T 1) ν) 1
  let U_out : Matrix.unitaryGroup (TensorPower A ν × (TensorPower A ν × B)) ℂ :=
    ICO.MHWordRotation.tensorUnitary (unitaryTensorPowerMatrix T ν) 1
  exact encode_invariant (pairRegisterDecode (A := A) (B := B) ν) U_in U_out
    (pairRegisterDecode_intertwine T ν) X (hX T)

private theorem storedRotation_submatrix_externalEquiv {A M : Type} [Fintype A] [DecidableEq A]
    [Nontrivial A] [Fintype M] [DecidableEq M]
    (T : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    (storedRotation (M := M) T n :
      CMatrix (Cache (A := A) (M := M) n)).submatrix
      (ICO.C6CacheKnownOperation.externalEquiv n M).symm
      (ICO.C6CacheKnownOperation.externalEquiv n M).symm =
    Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) n)
      (1 : CMatrix (A × M)) := by
  ext ⟨p₁, a₁, m₁⟩ ⟨p₂, a₂, m₂⟩
  by_cases ha : a₁ = a₂
  · subst ha
    by_cases hm : m₁ = m₂
    · subst hm
      simp [storedRotation, outputRotation, tensorUnitary, symmetricRotation,
        ICO.C6CacheKnownOperation.externalEquiv, Matrix.kronecker, Matrix.kroneckerMap_apply]
    · simp [storedRotation, outputRotation, tensorUnitary, symmetricRotation,
        ICO.C6CacheKnownOperation.externalEquiv, Matrix.kronecker, Matrix.kroneckerMap_apply, hm]
  · simp [storedRotation, outputRotation, tensorUnitary, symmetricRotation,
      ICO.C6CacheKnownOperation.externalEquiv, Matrix.kronecker, Matrix.kroneckerMap_apply, ha]

/-- **Lemma `lem:reference-invariant` (one-step sequential form)**:
a single reference-cache call followed by any isometric strategy operation `K` preserves
common label-rotation invariance (`ICO.C6GradedCache.Invariant Q`) on `Graded Q (Bool × M)`. -/
theorem reference_cache_step_invariant {A M N : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A)
    (K : Matrix (A × (Bool × N)) (A × (Bool × M)) ℂ) (hK : K.conjTranspose * K = 1)
    (X : CMatrix (Graded (A := A) Q (Bool × M)))
    (hi : ICO.C6GradedCache.Invariant Q X) :
    ICO.C6GradedCache.Invariant Q
      (((ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q N).symm).comp
        ((statefulChoiceStep
            (referenceCacheCall (A := A) Q hQ.le)
            (referenceCacheCall (A := A) Q hQ.le) K hK).comp
          (ICO.C6ReindexChannel.channel (hiddenChoiceGradedEquiv (A := A) Q M)))).map X) := by
  rw [statefulChoiceStep_reference_eq_choiceStep Q hpos hQ K hK]
  exact ICO.C6CacheTrajectoryAfter.reference_step_invariant Q hpos hQ K hK X hi

/-- **Lemma `lem:reference-invariant` (`reference_cache_invariant`, sequential run & sector form)**:
when a strategy runs against the reference cache (`referenceCacheStages`, with depolarizing `Ω`
in place of `Δ` in every retrieval), at every time step `t` the graded state satisfies
`ICO.C6GradedCache.Invariant Q` and every counter sector `ν : Fin (Q + 1)` commutes with
the common label rotation `storedRotation T ν.val` (`I_{query} ⊗ T^{⊗ ν} ⊗ I_{memory}`) for
every unitary `T : Matrix.unitaryGroup A ℂ`. -/
theorem reference_cache_invariant {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    {μ : ℕ → Type} [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A)
    (K : ∀ i, Matrix (A × (Bool × μ (i + 1))) (A × (Bool × μ i)) ℂ)
    (hK : ∀ i, (K i).conjTranspose * K i = 1)
    (X : CMatrix (Cache (A := A) (M := Bool × μ 0) 0)) (t : ℕ) :
    let Y := ICO.C6ChannelTrajectory.run (referenceCacheStages Q hQ.le K hK)
      (ICO.C6CacheTrajectory.initial Q X) t
    ICO.C6GradedCache.Invariant Q Y ∧
      ∀ ν : Fin (Q + 1),
        StoredInvariant ν.val ((embed Q ν).conjTranspose * Y * embed Q ν) := by
  dsimp only
  have hs : referenceCacheStages Q hQ.le K hK =
      ICO.C6CacheTrajectoryAfter.stages Q hpos hQ (fun _ _ => none) K hK :=
    funext (fun i => referenceCacheStages_eq_afterStages Q hpos hQ K hK i)
  rw [hs]
  have hinv := ICO.C6CacheTrajectoryAfter.reference_run_invariant Q hpos hQ K hK X t
  exact ⟨hinv, fun ν => ICO.C6GradedCacheReference.decode_invariant Q ν _ hinv⟩

/-- First-quantized `T^{⊗ ν}` (`CommonInvariant ν`) form of `reference_cache_invariant`:
at every time step `t` and every counter value `ν`, after isometrically decoding the `ν` symmetric
stored pairs into `(ℂ^d)^{⊗ ν}_{labels} ⊗ (ℂ^d)^{⊗ ν}_{images}`, the joint state of the `ν` stored
labels with `(stored images, query, memory)` commutes with `T^{⊗ ν} ⊗ I` for all `T ∈ U(d)`. -/
theorem reference_cache_decoded_invariant {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
    {μ : ℕ → Type} [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    (Q : ℕ) (hpos : 0 < Q) (hQ : Q < Fintype.card A)
    (K : ∀ i, Matrix (A × (Bool × μ (i + 1))) (A × (Bool × μ i)) ℂ)
    (hK : ∀ i, (K i).conjTranspose * K i = 1)
    (X : CMatrix (Cache (A := A) (M := Bool × μ 0) 0)) (t : ℕ) (ν : Fin (Q + 1)) :
    let Yν := ((embed Q ν).conjTranspose *
      ICO.C6ChannelTrajectory.run (referenceCacheStages Q hQ.le K hK)
        (ICO.C6CacheTrajectory.initial Q X) t * embed Q ν).submatrix
        (ICO.C6CacheKnownOperation.externalEquiv ν.val (Bool × μ t)).symm
        (ICO.C6CacheKnownOperation.externalEquiv ν.val (Bool × μ t)).symm
    CommonInvariant ν.val
      (pairRegisterDecode (A := A) (B := A × (Bool × μ t)) ν.val * Yν *
        (pairRegisterDecode (A := A) (B := A × (Bool × μ t)) ν.val).conjTranspose) := by
  dsimp only
  have hst := (reference_cache_invariant Q hpos hQ K hK X t).2 ν
  apply pairRegisterDecode_commonInvariant
  intro T
  have hcomm := commutation_reindex
    (ICO.C6CacheKnownOperation.externalEquiv ν.val (Bool × μ t)).symm _ _ (hst T)
  simpa only [storedRotation_submatrix_externalEquiv] using hcomm

/-- Counter-diagonal common label-rotation invariance for an arbitrary joint state of
`CacheHidden A Q` and an accessible strategy register `B`. -/
def HiddenStoredInvariant {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (Q : ℕ) (X : CMatrix (CacheHidden A Q × B)) : Prop :=
  (∀ s₁ s₂ : Fin (Q + 1), s₁ ≠ s₂ → ∀ p₁ p₂ b₁ b₂,
    X (⟨s₁, p₁⟩, b₁) (⟨s₂, p₂⟩, b₂) = 0) ∧
  ∀ (ν : Fin (Q + 1)) (T : Matrix.unitaryGroup A ℂ),
    Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν.val) (1 : CMatrix B) *
      Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) ν.val × B) =>
        X (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2)) =
    Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) ν.val × B) =>
        X (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2)) *
      Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν.val) (1 : CMatrix B)

/-- Counter support bound `ν ≤ k` on `CacheHidden A Q × B`. -/
def HiddenCounterBound {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (Q k : ℕ) (X : CMatrix (CacheHidden A Q × B)) : Prop :=
  ∀ (s₁ s₂ : Fin (Q + 1)) (p₁ p₂) (b₁ b₂ : B),
    (k < s₁.val ∨ k < s₂.val) → X (⟨s₁, p₁⟩, b₁) (⟨s₂, p₂⟩, b₂) = 0

/-- Reachability relation: `ReferenceTreeVisits Q hQ tree₀ X₀ tree X` holds whenever `(tree, X)`
is reached at some node starting from `(tree₀, X₀)` when running against the reference cache. -/
inductive ReferenceTreeVisits {A M O : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (Q : ℕ) (hQ : Q ≤ Fintype.card A) :
    ∀ {r₀ : ℕ} {B₀ : Type} [Fintype B₀] [DecidableEq B₀],
      BudgetQueryTree.Tree (A × M) O r₀ B₀ → CMatrix (CacheHidden A Q × B₀) →
      ∀ {r : ℕ} {B : Type} [Fintype B] [DecidableEq B],
        BudgetQueryTree.Tree (A × M) O r B → CMatrix (CacheHidden A Q × B) → Prop
  | refl {r : ℕ} {B : Type} [Fintype B] [DecidableEq B]
      (tree : BudgetQueryTree.Tree (A × M) O r B) (X : CMatrix (CacheHidden A Q × B)) :
      ReferenceTreeVisits Q hQ tree X tree X
  | query {r r' : ℕ} {B' : Type} [Fintype B'] [DecidableEq B']
      (b : Bool) (after : BudgetQueryTree.Tree (A × M) O r (A × M))
      (X : CMatrix (CacheHidden A Q × (A × M)))
      (target : BudgetQueryTree.Tree (A × M) O r' B') (Y : CMatrix (CacheHidden A Q × B')) :
      ReferenceTreeVisits Q hQ after
        ((liftEnvCall M (referenceCacheCall (A := A) Q hQ)).map X) target Y →
      ReferenceTreeVisits Q hQ (.query b after) X target Y
  | node {r r' : ℕ} {B C B' : Type} [Fintype B] [DecidableEq B]
      [Fintype C] [DecidableEq C] [Fintype B'] [DecidableEq B']
      {J : Type} [Fintype J] [DecidableEq J]
      (I : Instrument B C J) (next : J → BudgetQueryTree.Tree (A × M) O r C) (j : J)
      (X : CMatrix (CacheHidden A Q × B))
      (target : BudgetQueryTree.Tree (A × M) O r' B') (Y : CMatrix (CacheHidden A Q × B')) :
      ReferenceTreeVisits Q hQ (next j)
        (singleMap (liftEnvOp (CacheHidden A Q) (I.op j)) X) target Y →
      ReferenceTreeVisits Q hQ (.node I next) X target Y

theorem hiddenStoredInvariant_initial {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] (Q : ℕ) (X : CMatrix B) :
    HiddenStoredInvariant Q (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) Q) X) ∧
      HiddenCounterBound Q 0 (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) Q) X) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro s₁ s₂ hne p₁ p₂ b₁ b₂
    have h0 : (⟨s₁, p₁⟩ : CacheHidden A Q).1 ≠ 0 ∨ (⟨s₂, p₂⟩ : CacheHidden A Q).1 ≠ 0 := by
      by_cases h1 : s₁ = 0
      · exact Or.inr (fun h2 => hne (h1.trans h2.symm))
      · exact Or.inl h1
    rw [Matrix.kronecker, Matrix.kroneckerMap_apply,
      cacheHiddenInitialMatrix_ne_zero (A := A) Q ⟨s₁, p₁⟩ ⟨s₂, p₂⟩ h0, zero_mul]
  · intro ν T
    by_cases hν : ν = 0
    · have hrot : occupationRotation (leftEdgeUnitary T 1) ν.val = 1 := by
        subst hν
        exact ICO.MHFockEmptyRotation.occupationRotation_zero (leftEdgeUnitary T 1)
      simp only [hrot, Matrix.kronecker, Matrix.one_kronecker_one, Matrix.one_mul, Matrix.mul_one]
    · have hzero : Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) ν.val × B) =>
          (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) Q) X)
            (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2)) = 0 := by
        ext pb₁ pb₂
        rw [Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
          cacheHiddenInitialMatrix_ne_zero (A := A) Q ⟨ν, pb₁.1⟩ ⟨ν, pb₂.1⟩ (Or.inl hν),
          zero_mul, Matrix.zero_apply]
      rw [hzero, Matrix.mul_zero, Matrix.zero_mul]
  · intro s₁ s₂ p₁ p₂ b₁ b₂ hk
    have h0 : (⟨s₁, p₁⟩ : CacheHidden A Q).1 ≠ 0 ∨ (⟨s₂, p₂⟩ : CacheHidden A Q).1 ≠ 0 :=
      hk.imp (fun h e => by dsimp only at e; rw [e] at h; exact Nat.lt_irrefl 0 h)
        (fun h e => by dsimp only at e; rw [e] at h; exact Nat.lt_irrefl 0 h)
    rw [Matrix.kronecker, Matrix.kroneckerMap_apply,
      cacheHiddenInitialMatrix_ne_zero (A := A) Q ⟨s₁, p₁⟩ ⟨s₂, p₂⟩ h0, zero_mul]

theorem hiddenStoredInvariant_liftEnvOp {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (Q k : ℕ) (W : Matrix C B ℂ) (X : CMatrix (CacheHidden A Q × B))
    (hinv : HiddenStoredInvariant Q X) (hbnd : HiddenCounterBound Q k X) :
    HiddenStoredInvariant Q (singleMap (liftEnvOp (CacheHidden A Q) W) X) ∧
      HiddenCounterBound Q k (singleMap (liftEnvOp (CacheHidden A Q) W) X) := by
  have hslice (s₁ s₂ : Fin (Q + 1)) (p₁ : TensorPowerProfile (A × A) s₁.val)
      (p₂ : TensorPowerProfile (A × A) s₂.val) (c₁ c₂ : C) :
      singleMap (liftEnvOp (CacheHidden A Q) W) X (⟨s₁, p₁⟩, c₁) (⟨s₂, p₂⟩, c₂) =
        (W * Matrix.of (fun b₁ b₂ => X (⟨s₁, p₁⟩, b₁) (⟨s₂, p₂⟩, b₂)) * W.conjTranspose) c₁ c₂ := by
    simpa only [singleMap_apply] using
      congrFun (congrFun (singleMap_liftEnvOp_slice W X ⟨s₁, p₁⟩ ⟨s₂, p₂⟩) c₁) c₂
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro s₁ s₂ hne p₁ p₂ c₁ c₂
    rw [hslice]
    have hz : Matrix.of (fun b₁ b₂ => X (⟨s₁, p₁⟩, b₁) (⟨s₂, p₂⟩, b₂)) = 0 := by
      ext b₁ b₂; exact hinv.1 s₁ s₂ hne p₁ p₂ b₁ b₂
    simp [hz]
  · intro ν T
    let Xν : CMatrix (TensorPowerProfile (A × A) ν.val × B) :=
      Matrix.of (fun pb₁ pb₂ => X (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2))
    have hblock :
        Matrix.of (fun (pc₁ pc₂ : TensorPowerProfile (A × A) ν.val × C) =>
          singleMap (liftEnvOp (CacheHidden A Q) W) X (⟨ν, pc₁.1⟩, pc₁.2) (⟨ν, pc₂.1⟩, pc₂.2)) =
        Matrix.kronecker (1 : CMatrix (TensorPowerProfile (A × A) ν.val)) W * Xν *
          (Matrix.kronecker (1 : CMatrix (TensorPowerProfile (A × A) ν.val)) W).conjTranspose := by
      ext ⟨p₁, c₁⟩ ⟨p₂, c₂⟩
      rw [Matrix.of_apply, hslice]
      simpa only [liftEnvOp, singleMap_apply, Xν, Matrix.of_apply] using
        (congrFun (congrFun (singleMap_liftEnvOp_slice W Xν p₁ p₂) c₁) c₂).symm
    rw [hblock]
    have hinter :
        Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν.val) (1 : CMatrix C) *
          Matrix.kronecker (1 : CMatrix (TensorPowerProfile (A × A) ν.val)) W =
        Matrix.kronecker (1 : CMatrix (TensorPowerProfile (A × A) ν.val)) W *
          Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν.val) (1 : CMatrix B) := by
      simp only [Matrix.kronecker]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
    let U_in : Matrix.unitaryGroup (TensorPowerProfile (A × A) ν.val × B) ℂ :=
      tensorUnitary (symmetricRotation (leftEdgeUnitary T 1) ν.val) 1
    let U_out : Matrix.unitaryGroup (TensorPowerProfile (A × A) ν.val × C) ℂ :=
      tensorUnitary (symmetricRotation (leftEdgeUnitary T 1) ν.val) 1
    exact encode_invariant _ U_in U_out hinter Xν (hinv.2 ν T)
  · intro s₁ s₂ p₁ p₂ c₁ c₂ hk
    rw [hslice]
    have hz : Matrix.of (fun b₁ b₂ => X (⟨s₁, p₁⟩, b₁) (⟨s₂, p₂⟩, b₂)) = 0 := by
      ext b₁ b₂; exact hbnd s₁ s₂ p₁ p₂ b₁ b₂ hk
    simp [hz]

private def constTensorPower {X : Type*} (x : X) : (n : ℕ) → TensorPower X n
  | 0 => PUnit.unit
  | n + 1 => (x, constTensorPower x n)

theorem subsingleton_occupationRotation_scalar {A : Type} [Fintype A] [DecidableEq A]
    [Nonempty A] [Subsingleton A] (T : Matrix.unitaryGroup A ℂ) (ν : ℕ) :
    ∃ c : ℂ, occupationRotation (leftEdgeUnitary T 1) ν = c • 1 := by
  haveI : Subsingleton (A × A) := inferInstance
  haveI : Subsingleton (TensorPower (A × A) ν) := by
    induction ν with
    | zero => exact ⟨fun x y => by cases x; cases y; rfl⟩
    | succ m ih => exact @instSubsingletonProd _ _ inferInstance ih
  let a₀ : A := Classical.arbitrary A
  let w₀ : TensorPower (A × A) ν := constTensorPower (a₀, a₀) ν
  refine ⟨(unitaryTensorPowerMatrix (leftEdgeUnitary T 1) ν :
    CMatrix (TensorPower (A × A) ν)) w₀ w₀, ?_⟩
  have hsc : (unitaryTensorPowerMatrix (leftEdgeUnitary T 1) ν :
      CMatrix (TensorPower (A × A) ν)) =
      (unitaryTensorPowerMatrix (leftEdgeUnitary T 1) ν :
        CMatrix (TensorPower (A × A) ν)) w₀ w₀ • 1 := by
    ext w₁ w₂
    rw [Subsingleton.elim w₁ w₀, Subsingleton.elim w₂ w₀]
    simp
  have hinter := occupationRotation_intertwine (leftEdgeUnitary T 1) ν
  have hmul := congrArg ((occupationEmbedding (a := A × A) ν).conjTranspose * ·) hinter
  dsimp only at hmul
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, occupationEmbedding_gram, Matrix.one_mul,
    hsc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, occupationEmbedding_gram] at hmul
  exact hmul.symm

private theorem hiddenStoredInvariant_referenceQuery_diag_bnd {A M : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [DecidableEq M]
    {Q k : ℕ} (hkQ : k < Q) (hQ : Q ≤ Fintype.card A)
    (X : CMatrix (CacheHidden A Q × (A × M))) (hbnd : HiddenCounterBound Q k X) :
    let Y := (liftEnvCall M (referenceCacheCall (A := A) Q hQ)).map X
    (∀ s₁ s₂ : Fin (Q + 1), s₁ ≠ s₂ → ∀ p₁ p₂ b₁ b₂,
      Y (⟨s₁, p₁⟩, b₁) (⟨s₂, p₂⟩, b₂) = 0) ∧
    HiddenCounterBound Q (k + 1) Y := by
  dsimp only
  set Y := (liftEnvCall M (referenceCacheCall (A := A) Q hQ)).map X
  have hdite_zero (s₁ s₂ t : Fin (Q + 1)) (hnot : ¬ (s₁ = t ∧ s₂ = t))
      (f : s₁ = t → s₂ = t → ℂ) :
      (if h₁ : s₁ = t then if h₂ : s₂ = t then f h₁ h₂ else 0 else 0) = 0 := by
    by_cases e1 : s₁ = t
    · rw [dif_pos e1, dif_neg (fun e2 => hnot ⟨e1, e2⟩)]
    · rw [dif_neg e1]
  have hY_entry (s₁ s₂ : Fin (Q + 1)) (p₁ : TensorPowerProfile (A × A) s₁.val)
      (p₂ : TensorPowerProfile (A × A) s₂.val) (a₁ a₂ : A) (m₁ m₂ : M) :
      Y (⟨s₁, p₁⟩, (a₁, m₁)) (⟨s₂, p₂⟩, (a₂, m₂)) =
        ((sectorChannel (labelCacheSectorStep (A := A) Q hQ
            (ICO.RecordingDepolarizing.depolarizing (α := A)))).map
          (Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
            X (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂)))))
          ⟨s₁, (a₁, p₁)⟩ ⟨s₂, (a₂, p₂)⟩ := by
    dsimp only [Y, referenceCacheCall]
    exact liftEnvCall_labelCacheCall_apply Q hQ
      (ICO.RecordingDepolarizing.depolarizing (α := A)) X s₁ s₂ p₁ p₂ a₁ a₂ m₁ m₂
  have hsec_zero (r : Fin (Q + 1)) (hr : k < r.val) (m₁ m₂ : M) :
      ((inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r).conjTranspose *
        Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          X (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂))) *
        inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r) = 0 := by
    rw [inclusion, basisEmbedding_compression]
    ext ⟨a₁, p₁⟩ ⟨a₂, p₂⟩
    exact hbnd r r p₁ p₂ (a₁, m₁) (a₂, m₂) (Or.inl hr)
  have hconj_out (t s₁ s₂ : Fin (Q + 1)) (Z : CMatrix (Sector (A := A) t.val))
      (c₁ : Sector (A := A) s₁.val) (c₂ : Sector (A := A) s₂.val) :
      (conjugate (inclusion (H := fun u : Fin (Q + 1) => Sector (A := A) u.val) t) Z)
        ⟨s₁, c₁⟩ ⟨s₂, c₂⟩ =
        if h₁ : s₁ = t then
          if h₂ : s₂ = t then Z (h₁ ▸ c₁) (h₂ ▸ c₂) else 0
        else 0 := by
    rw [conjugate_apply]
    exact inclusion_sandwich_apply (H := fun u : Fin (Q + 1) => Sector (A := A) u.val)
      t s₁ s₂ Z c₁ c₂
  refine ⟨?_, ?_⟩
  · intro s₁ s₂ hne p₁ p₂ ⟨a₁, m₁⟩ ⟨a₂, m₂⟩
    rw [hY_entry, sector_apply, Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hrk : k < r.val
    · rw [hsec_zero r hrk, map_zero, Matrix.zero_apply]
    · have hrQ : r.val < Q := by omega
      rw [labelCacheSectorStep_lt_map Q hQ _ r hrQ, Matrix.add_apply, hconj_out, hconj_out]
      have h1 : ¬ (s₁ = r ∧ s₂ = r) := fun ⟨e1, e2⟩ => hne (e1.trans e2.symm)
      have h2 : ¬ (s₁ = ⟨r.val + 1, Nat.succ_lt_succ hrQ⟩ ∧
          s₂ = ⟨r.val + 1, Nat.succ_lt_succ hrQ⟩) :=
        fun ⟨e1, e2⟩ => hne (e1.trans e2.symm)
      rw [hdite_zero s₁ s₂ r h1,
        hdite_zero s₁ s₂ ⟨r.val + 1, Nat.succ_lt_succ hrQ⟩ h2, add_zero]
  · intro s₁ s₂ p₁ p₂ ⟨a₁, m₁⟩ ⟨a₂, m₂⟩ hk1
    rw [hY_entry, sector_apply, Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hrk : k < r.val
    · rw [hsec_zero r hrk, map_zero, Matrix.zero_apply]
    · have hrQ : r.val < Q := by omega
      rw [labelCacheSectorStep_lt_map Q hQ _ r hrQ, Matrix.add_apply, hconj_out, hconj_out]
      have h1 : ¬ (s₁ = r ∧ s₂ = r) := by
        rintro ⟨rfl, rfl⟩; omega
      have h2 : ¬ (s₁ = ⟨r.val + 1, Nat.succ_lt_succ hrQ⟩ ∧
          s₂ = ⟨r.val + 1, Nat.succ_lt_succ hrQ⟩) := by
        rintro ⟨rfl, rfl⟩
        dsimp only at hk1
        omega
      rw [hdite_zero s₁ s₂ r h1,
        hdite_zero s₁ s₂ ⟨r.val + 1, Nat.succ_lt_succ hrQ⟩ h2, add_zero]

private theorem hiddenStoredInvariant_referenceQuery_lt {A M : Type}
    [Fintype A] [DecidableEq A] [Nontrivial A] [Fintype M] [DecidableEq M]
    {Q k : ℕ} (hkQ : k < Q) (hQ : Q ≤ Fintype.card A) (hQd : Q < Fintype.card A)
    (X : CMatrix (CacheHidden A Q × (A × M))) (hinv : HiddenStoredInvariant Q X)
    (ν : Fin (Q + 1)) (T : Matrix.unitaryGroup A ℂ) :
    let Y := (liftEnvCall M (referenceCacheCall (A := A) Q hQ)).map X
    Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν.val) (1 : CMatrix (A × M)) *
      Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) ν.val × (A × M)) =>
        Y (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2)) =
    Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) ν.val × (A × M)) =>
        Y (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2)) *
      Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν.val) (1 : CMatrix (A × M)) := by
  set Y := (liftEnvCall M (referenceCacheCall (A := A) Q hQ)).map X
  have hpos : 0 < Q := by omega
  let Xr (r : Fin (Q + 1)) : CMatrix (Cache (A := A) (M := M) r.val) :=
    Matrix.of (fun x₁ x₂ => X (⟨r, x₁.1.2⟩, (x₁.1.1, x₁.2)) (⟨r, x₂.1.2⟩, (x₂.1.1, x₂.2)))
  have hXr_inv (r : Fin (Q + 1)) : StoredInvariant r.val (Xr r) := by
    intro U
    apply commutation_of_reindex (ICO.C6CacheKnownOperation.externalEquiv r.val M).symm
    rw [storedRotation_submatrix_externalEquiv]
    exact hinv.2 r U
  set Xg : CMatrix (Graded (A := A) Q M) :=
    X.submatrix (hiddenGradedEquiv (A := A) Q M).symm (hiddenGradedEquiv (A := A) Q M).symm
  have hXg_eq : Xg = ∑ r : Fin (Q + 1), conjugate (embed (A := A) (M := M) Q r) (Xr r) := by
    ext ⟨s₁, ⟨a₁, p₁⟩, m₁⟩ ⟨s₂, ⟨a₂, p₂⟩, m₂⟩
    rw [Matrix.sum_apply]
    by_cases hs : s₁ = s₂
    · subst hs
      rw [Finset.sum_eq_single s₁]
      · rw [conjugate_embed_apply, dif_pos rfl, dif_pos rfl]
        rfl
      · intro r _ hne
        rw [conjugate_embed_apply, dif_neg hne.symm]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · trans (0 : ℂ)
      · exact hinv.1 s₁ s₂ hs p₁ p₂ (a₁, m₁) (a₂, m₂)
      · symm
        apply Finset.sum_eq_zero
        intro r _
        rw [conjugate_embed_apply]
        by_cases e1 : s₁ = r
        · rw [dif_pos e1, dif_neg (fun e2 => hs (e1.trans e2.symm))]
        · rw [dif_neg e1]
  have hXg_inv : ICO.C6GradedCache.Invariant Q Xg := by
    rw [hXg_eq]
    exact ICO.C6GradedCacheReference.invariant_sum Q _
      (fun r => ICO.C6GradedCacheReference.encode_invariant Q r (Xr r) (hXr_inv r))
  have hYg_inv : ICO.C6GradedCache.Invariant Q
      ((ICO.C6GradedCache.query (A := A) (M := M) Q hpos hQd none).map Xg) :=
    ICO.C6GradedCacheReference.reference_invariant Q hpos hQd Xg hXg_inv
  have hY_eq_Yg :
      Y.submatrix (hiddenGradedEquiv (A := A) Q M).symm
        (hiddenGradedEquiv (A := A) Q M).symm =
      (ICO.C6GradedCache.query (A := A) (M := M) Q hpos hQd none).map Xg := by
    have hq := congrArg (fun C => C.map Xg)
      (referenceCacheCall_eq_gradedQuery (A := A) (M := M) Q hpos hQd)
    dsimp only [Channel.comp, LinearMap.comp_apply] at hq
    rw [ICO.C6ReindexChannel.apply, ICO.C6ReindexChannel.apply] at hq
    have hsub : (Xg.submatrix (hiddenGradedEquiv (A := A) Q M)
        (hiddenGradedEquiv (A := A) Q M)) = X := by
      ext u₁ u₂
      simp [Xg]
    rw [hsub] at hq
    exact hq
  rw [← hY_eq_Yg] at hYg_inv
  have hsec := ICO.C6GradedCacheReference.decode_invariant Q ν _ hYg_inv T
  have hcomm := commutation_reindex
    (ICO.C6CacheKnownOperation.externalEquiv ν.val M).symm _ _ hsec
  have hmat :
      ((embed (A := A) (M := M) Q ν).conjTranspose *
        Y.submatrix (hiddenGradedEquiv (A := A) Q M).symm
          (hiddenGradedEquiv (A := A) Q M).symm *
        embed (A := A) (M := M) Q ν).submatrix
        (ICO.C6CacheKnownOperation.externalEquiv ν.val M).symm
        (ICO.C6CacheKnownOperation.externalEquiv ν.val M).symm =
      Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) ν.val × (A × M)) =>
        Y (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2)) := by
    rw [embed, inclusion, basisEmbedding_compression]
    ext ⟨p₁, a₁, m₁⟩ ⟨p₂, a₂, m₂⟩
    rfl
  simpa only [storedRotation_submatrix_externalEquiv, hmat] using hcomm

private theorem hiddenStoredInvariant_referenceQuery_eq {A M : Type}
    [Fintype A] [DecidableEq A] [Nontrivial A] [Fintype M] [DecidableEq M]
    {Q k : ℕ} (hkQ : k < Q) (hQ : Q ≤ Fintype.card A) (hQeq : Q = Fintype.card A)
    (X : CMatrix (CacheHidden A Q × (A × M)))
    (hinv : HiddenStoredInvariant Q X) (hbnd : HiddenCounterBound Q k X)
    (ν : Fin (Q + 1)) (T : Matrix.unitaryGroup A ℂ) :
    let Y := (liftEnvCall M (referenceCacheCall (A := A) Q hQ)).map X
    Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν.val) (1 : CMatrix (A × M)) *
      Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) ν.val × (A × M)) =>
        Y (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2)) =
    Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) ν.val × (A × M)) =>
        Y (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2)) *
      Matrix.kronecker (occupationRotation (leftEdgeUnitary T 1) ν.val) (1 : CMatrix (A × M)) := by
  dsimp only
  set Y := (liftEnvCall M (referenceCacheCall (A := A) Q hQ)).map X
  let Xr (r : Fin (Q + 1)) : CMatrix (Cache (A := A) (M := M) r.val) :=
    Matrix.of (fun x₁ x₂ => X (⟨r, x₁.1.2⟩, (x₁.1.1, x₁.2)) (⟨r, x₂.1.2⟩, (x₂.1.1, x₂.2)))
  have hXr_inv (r : Fin (Q + 1)) : StoredInvariant r.val (Xr r) := by
    intro U
    apply commutation_of_reindex (ICO.C6CacheKnownOperation.externalEquiv r.val M).symm
    rw [storedRotation_submatrix_externalEquiv]
    exact hinv.2 r U
  have hY_entry (s₁ s₂ : Fin (Q + 1)) (p₁ : TensorPowerProfile (A × A) s₁.val)
      (p₂ : TensorPowerProfile (A × A) s₂.val) (a₁ a₂ : A) (m₁ m₂ : M) :
      Y (⟨s₁, p₁⟩, (a₁, m₁)) (⟨s₂, p₂⟩, (a₂, m₂)) =
        ((sectorChannel (labelCacheSectorStep (A := A) Q hQ
            (ICO.RecordingDepolarizing.depolarizing (α := A)))).map
          (Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
            X (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂)))))
          ⟨s₁, (a₁, p₁)⟩ ⟨s₂, (a₂, p₂)⟩ := by
    dsimp only [Y, referenceCacheCall]
    exact liftEnvCall_labelCacheCall_apply Q hQ
      (ICO.RecordingDepolarizing.depolarizing (α := A)) X s₁ s₂ p₁ p₂ a₁ a₂ m₁ m₂
  have hsec_zero (r : Fin (Q + 1)) (hr : k < r.val) (m₁ m₂ : M) :
      ((inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r).conjTranspose *
        Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
          X (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂))) *
        inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r) = 0 := by
    rw [inclusion, basisEmbedding_compression]
    ext ⟨a₁, p₁⟩ ⟨a₂, p₂⟩
    exact hbnd r r p₁ p₂ (a₁, m₁) (a₂, m₂) (Or.inl hr)
  have hconj_out (t s₁ s₂ : Fin (Q + 1)) (Z : CMatrix (Sector (A := A) t.val))
      (c₁ : Sector (A := A) s₁.val) (c₂ : Sector (A := A) s₂.val) :
      (conjugate (inclusion (H := fun u : Fin (Q + 1) => Sector (A := A) u.val) t) Z)
        ⟨s₁, c₁⟩ ⟨s₂, c₂⟩ =
        if h₁ : s₁ = t then
          if h₂ : s₂ = t then Z (h₁ ▸ c₁) (h₂ ▸ c₂) else 0
        else 0 := by
    rw [conjugate_apply]
    exact inclusion_sandwich_apply (H := fun u : Fin (Q + 1) => Sector (A := A) u.val)
      t s₁ s₂ Z c₁ c₂
  rcases ν with ⟨n, hn⟩
  dsimp only
  cases n with
  | zero =>
    have hzero_blk :
        Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) 0 × (A × M)) =>
          Y (⟨⟨0, hn⟩, pb₁.1⟩, pb₁.2) (⟨⟨0, hn⟩, pb₂.1⟩, pb₂.2)) = 0 := by
      ext ⟨p₁, a₁, m₁⟩ ⟨p₂, a₂, m₂⟩
      rw [Matrix.of_apply, Matrix.zero_apply, hY_entry, sector_apply, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro r _
      by_cases hrk : k < r.val
      · rw [hsec_zero r hrk, map_zero, Matrix.zero_apply]
      · have hrQ : r.val < Q := by omega
        rw [labelCacheSectorStep_lt_map Q hQ _ r hrQ, Matrix.add_apply, hconj_out, hconj_out]
        have hne2 : (⟨0, hn⟩ : Fin (Q + 1)) ≠ ⟨r.val + 1, Nat.succ_lt_succ hrQ⟩ := by
          intro he; have := congrArg Fin.val he; dsimp at this; omega
        rw [dif_neg hne2, add_zero]
        by_cases e1 : (⟨0, hn⟩ : Fin (Q + 1)) = r
        · have hr0 : r = ⟨0, hn⟩ := e1.symm
          subst hr0
          rw [dif_pos rfl, dif_pos rfl]
          simp only [labelCacheRetrieval_zero, LinearMap.zero_apply, Matrix.zero_apply]
        · rw [dif_neg e1]
    rw [hzero_blk, Matrix.mul_zero, Matrix.zero_mul]
  | succ m =>
    have hmQ : m < Q := by omega
    let r_bir : Fin (Q + 1) := ⟨m, Nat.lt_succ_of_lt hmQ⟩
    let r_ret : Fin (Q + 1) := ⟨m + 1, hn⟩
    have hsplit_sum (p₁ p₂ : TensorPowerProfile (A × A) (m + 1))
        (a₁ a₂ : A) (m₁ m₂ : M) :
        Y (⟨r_ret, p₁⟩, (a₁, m₁)) (⟨r_ret, p₂⟩, (a₂, m₂)) =
          (if hlt : m + 1 < Q then
            labelCacheRetrieval (A := A) (ICO.RecordingDepolarizing.depolarizing (α := A)) (m + 1)
              (Matrix.of (fun c₁ c₂ : Sector (A := A) (m + 1) =>
                Xr r_ret (c₁, m₁) (c₂, m₂)))
              (a₁, p₁) (a₂, p₂)
          else 0) +
          labelCacheBirth (A := A) m
            (Matrix.of (fun c₁ c₂ : Sector (A := A) m =>
              Xr r_bir (c₁, m₁) (c₂, m₂)))
            (a₁, p₁) (a₂, p₂) := by
      rw [hY_entry, sector_apply, Matrix.sum_apply]
      have hne_br : r_bir ≠ r_ret := by
        intro he; have := congrArg Fin.val he; dsimp [r_bir, r_ret] at this; omega
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r_ret),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne_br, Finset.mem_univ r_bir⟩)]
      have hrest :
          (∑ r ∈ (Finset.univ.erase r_ret).erase r_bir,
            ((labelCacheSectorStep (A := A) Q hQ
                (ICO.RecordingDepolarizing.depolarizing (α := A)) r).map
              ((inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r).conjTranspose *
                Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
                  X (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂))) *
                inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) r))
              ⟨r_ret, (a₁, p₁)⟩ ⟨r_ret, (a₂, p₂)⟩) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr_mem
        have hr_ne_bir : r ≠ r_bir := (Finset.mem_erase.mp hr_mem).1
        have hr_ne_ret : r ≠ r_ret := (Finset.mem_erase.mp (Finset.mem_erase.mp hr_mem).2).1
        by_cases hrQ : r.val < Q
        · have hne_succ : r_ret ≠ ⟨r.val + 1, Nat.succ_lt_succ hrQ⟩ := by
            intro he
            apply hr_ne_bir
            ext
            have := congrArg Fin.val he
            dsimp [r_bir, r_ret] at this ⊢
            omega
          rw [labelCacheSectorStep_lt_map Q hQ _ r hrQ, Matrix.add_apply, hconj_out, hconj_out,
            dif_neg hr_ne_ret.symm, dif_neg hne_succ, add_zero]
        · rw [labelCacheSectorStep_not_lt_map Q hQ _ r hrQ, hconj_out, dif_neg hr_ne_ret.symm]
      rw [hrest, add_zero]
      congr 1
      · by_cases hlt : m + 1 < Q
        · have hne_succ : r_ret ≠ ⟨r_ret.val + 1, Nat.succ_lt_succ hlt⟩ := by
            intro he; have := congrArg Fin.val he; dsimp [r_ret] at this; omega
          rw [labelCacheSectorStep_lt_map Q hQ _ r_ret hlt, Matrix.add_apply,
            hconj_out, hconj_out, dif_pos rfl, dif_pos rfl, dif_neg hne_succ,
            add_zero, dif_pos hlt]
          dsimp only [r_ret]
          suffices hin :
              (inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val)
                  ⟨m + 1, hn⟩).conjTranspose *
                Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
                  X (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂))) *
                inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val) ⟨m + 1, hn⟩ =
              Matrix.of (fun c₁ c₂ : Sector (A := A) (m + 1) =>
                Xr ⟨m + 1, hn⟩ (c₁, m₁) (c₂, m₂)) by
            rw [hin]
          rw [inclusion, basisEmbedding_compression]
          ext ⟨a₁', p₁'⟩ ⟨a₂', p₂'⟩
          rfl
        · by_cases hmk : k < m + 1
          · rw [hsec_zero r_ret hmk, map_zero, Matrix.zero_apply, dif_neg hlt]
          · omega
      · have hne_same : r_ret ≠ r_bir := hne_br.symm
        have hsucc_eq : r_ret = ⟨r_bir.val + 1, Nat.succ_lt_succ hmQ⟩ := rfl
        rw [labelCacheSectorStep_lt_map Q hQ _ r_bir hmQ, Matrix.add_apply,
          hconj_out, hconj_out, dif_neg hne_same, zero_add,
          dif_pos hsucc_eq, dif_pos hsucc_eq]
        dsimp only [r_bir, r_ret]
        suffices hin :
            (inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val)
                ⟨m, Nat.lt_succ_of_lt hmQ⟩).conjTranspose *
              Matrix.of (fun (u₁ u₂ : Σ t : Fin (Q + 1), Sector (A := A) t.val) =>
                X (⟨u₁.1, u₁.2.2⟩, (u₁.2.1, m₁)) (⟨u₂.1, u₂.2.2⟩, (u₂.2.1, m₂))) *
              inclusion (H := fun t : Fin (Q + 1) => Sector (A := A) t.val)
                ⟨m, Nat.lt_succ_of_lt hmQ⟩ =
            Matrix.of (fun c₁ c₂ : Sector (A := A) m =>
              Xr ⟨m, Nat.lt_succ_of_lt hmQ⟩ (c₁, m₁) (c₂, m₂)) by
          rw [hin]
        rw [inclusion, basisEmbedding_compression]
        ext ⟨a₁', p₁'⟩ ⟨a₂', p₂'⟩
        rfl
    cases m with
    | zero =>
      let Z₁ : CMatrix (Cache (A := A) (M := M) 1) :=
        (if hlt : 1 < Q then
          retrieval (memoryPolar (A := A) (M := M) 0) (uniformChannel 0) (Xr r_ret)
        else 0) +
        (vacuumStep (A := A) (M := M) (by omega)).map (Xr r_bir)
      have hblk_eq :
          Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) 1 × (A × M)) =>
            Y (⟨⟨1, hn⟩, pb₁.1⟩, pb₁.2) (⟨⟨1, hn⟩, pb₂.1⟩, pb₂.2)) =
          Z₁.submatrix
            (ICO.C6CacheKnownOperation.externalEquiv 1 M).symm
            (ICO.C6CacheKnownOperation.externalEquiv 1 M).symm := by
        ext ⟨p₁, a₁, m₁⟩ ⟨p₂, a₂, m₂⟩
        rw [Matrix.of_apply]
        change Y (⟨r_ret, p₁⟩, (a₁, m₁)) (⟨r_ret, p₂⟩, (a₂, m₂)) = _
        rw [hsplit_sum, Matrix.submatrix_apply]
        dsimp only [Z₁, ICO.C6CacheKnownOperation.externalEquiv, Equiv.coe_fn_symm_mk]
        rw [Matrix.add_apply]
        congr 1
        · split_ifs with hlt
          · rw [retrieval_apply, memoryPolar_conjugate_eq_kron, uniformChannel_eq_withMemory_kron,
              memoryPolar_adj_conjugate_eq_kron]
            simp_rw [MatrixMap.kron_idChannel_apply_slice]
            rfl
          · rfl
        · rw [labelCacheBirth_zero]
          simp only [vacuumStep, Channel.comp, LinearMap.comp_apply, isometryChannel_apply]
          rw [memoryPolar_conjugate_eq_kron, uniformChannel_eq_withMemory_kron]
          simp_rw [MatrixMap.kron_idChannel_apply_slice]
          rfl
      have hZ₁_inv : StoredInvariant 1 Z₁ := by
        intro U
        dsimp only [Z₁]
        rw [Matrix.mul_add, Matrix.add_mul]
        congr 1
        · split_ifs with hlt
          · exact reference_retrieval_stored (by omega) _ (hXr_inv r_ret) U
          · rw [Matrix.mul_zero, Matrix.zero_mul]
        · exact vacuum_stored (by omega) _ U
      rw [hblk_eq]
      have hcomm := commutation_reindex
        (ICO.C6CacheKnownOperation.externalEquiv 1 M).symm _ _ (hZ₁_inv T)
      simpa only [storedRotation_submatrix_externalEquiv] using hcomm
    | succ m' =>
      let Z₂ : CMatrix (Cache (A := A) (M := M) (m' + 2)) :=
        (if hlt : m' + 2 < Q then
          retrieval (memoryPolar (A := A) (M := M) (m' + 1))
            (uniformChannel (m' + 1)) (Xr r_ret)
        else 0) +
        birth (memoryPolar (A := A) (M := M) m')
          (memoryPolar (A := A) (M := M) (m' + 1))
          (uniformChannel (m' + 1)) (Xr r_bir)
      have hblk_eq :
          Matrix.of (fun (pb₁ pb₂ : TensorPowerProfile (A × A) (m' + 2) × (A × M)) =>
            Y (⟨⟨m' + 2, hn⟩, pb₁.1⟩, pb₁.2) (⟨⟨m' + 2, hn⟩, pb₂.1⟩, pb₂.2)) =
          Z₂.submatrix
            (ICO.C6CacheKnownOperation.externalEquiv (m' + 2) M).symm
            (ICO.C6CacheKnownOperation.externalEquiv (m' + 2) M).symm := by
        ext ⟨p₁, a₁, m₁⟩ ⟨p₂, a₂, m₂⟩
        rw [Matrix.of_apply]
        change Y (⟨r_ret, p₁⟩, (a₁, m₁)) (⟨r_ret, p₂⟩, (a₂, m₂)) = _
        rw [hsplit_sum, Matrix.submatrix_apply]
        dsimp only [Z₂, ICO.C6CacheKnownOperation.externalEquiv, Equiv.coe_fn_symm_mk]
        rw [Matrix.add_apply]
        congr 1
        · split_ifs with hlt
          · rw [retrieval_apply, memoryPolar_conjugate_eq_kron, uniformChannel_eq_withMemory_kron,
              memoryPolar_adj_conjugate_eq_kron]
            simp_rw [MatrixMap.kron_idChannel_apply_slice]
            rfl
          · rfl
        · rw [birth_apply, memoryPolar_conjugate_eq_kron, uniformChannel_eq_withMemory_kron,
            complement_memoryPolar_eq_kron]
          simp_rw [MatrixMap.kron_idChannel_apply_slice]
          rfl
      have hZ₂_inv : StoredInvariant (m' + 2) Z₂ := by
        intro U
        dsimp only [Z₂]
        rw [Matrix.mul_add, Matrix.add_mul]
        congr 1
        · split_ifs with hlt
          · exact reference_retrieval_stored (by omega) _ (hXr_inv r_ret) U
          · rw [Matrix.mul_zero, Matrix.zero_mul]
        · exact reference_birth_stored (by omega) (by omega) _ (hXr_inv r_bir) U
      rw [hblk_eq]
      have hcomm := commutation_reindex
        (ICO.C6CacheKnownOperation.externalEquiv (m' + 2) M).symm _ _ (hZ₂_inv T)
      simpa only [storedRotation_submatrix_externalEquiv] using hcomm

theorem hiddenStoredInvariant_referenceQuery {A M : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] {Q k : ℕ} (hkQ : k < Q) (hQ : Q ≤ Fintype.card A)
    (X : CMatrix (CacheHidden A Q × (A × M)))
    (hinv : HiddenStoredInvariant Q X) (hbnd : HiddenCounterBound Q k X) :
    HiddenStoredInvariant Q ((liftEnvCall M (referenceCacheCall (A := A) Q hQ)).map X) ∧
      HiddenCounterBound Q (k + 1) ((liftEnvCall M (referenceCacheCall (A := A) Q hQ)).map X) := by
  have hdb := hiddenStoredInvariant_referenceQuery_diag_bnd hkQ hQ X hbnd
  refine ⟨⟨hdb.1, ?_⟩, hdb.2⟩
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · letI := hsub
    intro ν T
    obtain ⟨c, hc⟩ := subsingleton_occupationRotation_scalar (A := A) T ν.val
    rw [hc]
    simp only [Matrix.kronecker, Matrix.smul_kronecker, Matrix.one_kronecker_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · letI := hnt
    intro ν T
    by_cases hQd : Q < Fintype.card A
    · exact hiddenStoredInvariant_referenceQuery_lt hkQ hQ hQd X hinv ν T
    · exact hiddenStoredInvariant_referenceQuery_eq hkQ hQ (by omega) X hinv hbnd ν T

theorem referenceTreeVisits_invariant_aux {A M O : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (Q : ℕ) (hQ : Q ≤ Fintype.card A)
    {r₀ : ℕ} {B₀ : Type} [Fintype B₀] [DecidableEq B₀]
    (tree₀ : BudgetQueryTree.Tree (A × M) O r₀ B₀) (X₀ : CMatrix (CacheHidden A Q × B₀))
    {r : ℕ} {B : Type} [Fintype B] [DecidableEq B]
    (target : BudgetQueryTree.Tree (A × M) O r B) (Y : CMatrix (CacheHidden A Q × B))
    (hvis : ReferenceTreeVisits Q hQ tree₀ X₀ target Y)
    (hr₀ : r₀ ≤ Q)
    (hinv : HiddenStoredInvariant Q X₀) (hbnd : HiddenCounterBound Q (Q - r₀) X₀) :
    HiddenStoredInvariant Q Y ∧ HiddenCounterBound Q (Q - r) Y := by
  induction hvis with
  | refl _ _ => exact ⟨hinv, hbnd⟩
  | @query r_sub r' B' _ _ b after X target' Y' _ ih =>
    have hkQ : Q - (r_sub + 1) < Q := by omega
    obtain ⟨hinv', hbnd'⟩ := hiddenStoredInvariant_referenceQuery hkQ hQ X hinv hbnd
    have hsub : Q - (r_sub + 1) + 1 = Q - r_sub := by omega
    rw [hsub] at hbnd'
    exact ih (by omega) hinv' hbnd'
  | node I next j X target' Y' _ ih =>
    obtain ⟨hinv', hbnd'⟩ := hiddenStoredInvariant_liftEnvOp Q _ (I.op j) X hinv hbnd
    exact ih hr₀ hinv' hbnd'

/-- **Lemma `lem:reference-invariant` (`reference_cache_tree_invariant`, adaptive `BudgetQueryTree` form)**:
for any adaptive strategy `tree : BudgetQueryTree.Tree (A × M) O q B₀` with budget `q ≤ d` and any
mixed initial state `ρ : State B₀`, at every visited node `(sub, Y)` when running against the
reference cache (`Ω` in place of `Δ` in every retrieval), the joint state `Y` is counter-diagonal
with counter `ν ≤ q - r` and, for every counter value `ν` and every unitary `T ∈ U(d)`, the joint
state of the accessible strategy register (query + memory) and the `ν` stored pairs is invariant
under the common label rotation `T^{⊗ ν}` (both in symmetric occupation coordinates and, via
`pairRegisterDecode`, as `CommonInvariant ν.val` on `(ℂ^d)^{⊗ ν}_{labels}`). -/
theorem reference_cache_tree_invariant {A M O B₀ B : Type}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    [Fintype B₀] [DecidableEq B₀] [Fintype B] [DecidableEq B]
    {q r : ℕ} (hq : q ≤ Fintype.card A)
    (tree : BudgetQueryTree.Tree (A × M) O q B₀) (ρ : State B₀)
    (sub : BudgetQueryTree.Tree (A × M) O r B) (Y : CMatrix (CacheHidden A q × B))
    (hvis : ReferenceTreeVisits q hq tree
      (Matrix.kronecker (cacheHiddenInitialMatrix (A := A) q) ρ.matrix) sub Y) :
    HiddenStoredInvariant q Y ∧
      HiddenCounterBound q (q - r) Y ∧
      ∀ ν : Fin (q + 1),
        CommonInvariant ν.val
          (pairRegisterDecode (A := A) (B := B) ν.val *
            Matrix.of (fun pb₁ pb₂ => Y (⟨ν, pb₁.1⟩, pb₁.2) (⟨ν, pb₂.1⟩, pb₂.2)) *
            (pairRegisterDecode (A := A) (B := B) ν.val).conjTranspose) := by
  obtain ⟨hinv₀, hbnd₀⟩ := hiddenStoredInvariant_initial (A := A) q ρ.matrix
  have hsub0 : q - q = 0 := Nat.sub_self q
  obtain ⟨hinv, hbnd⟩ := referenceTreeVisits_invariant_aux q hq tree _ sub Y hvis le_rfl
    hinv₀ (hsub0.symm ▸ hbnd₀)
  exact ⟨hinv, hbnd, fun ν => pairRegisterDecode_commonInvariant ν.val _ (hinv.2 ν)⟩

/-- **Reference-cache distance (`cache_reference_protocol_distance`, Section 5.5)**:
replacing depolarizing `Ω` by basis dephasing `Δ` one call at a time (via `reference_run_invariant`
and `invariant_basis_bound` at cost `3 (n - 1) / d` per call) bounds the trace distance between
the uniform label-cache output `protocolLabelCacheDensity` (`ρ^{cache}`) and the basis-independent
reference-cache output `protocolReferenceCacheDensity` (`τ_ref`) by `3 n (n - 1) / d`. -/
theorem cache_reference_protocol_distance {A M O : Type}
    [Fintype A] [DecidableEq A] [Nontrivial A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] {q : ℕ}
    (tail : Protocol (A × Bool) ((A × Bool) × M) O q)
    (H : Matrix.unitaryGroup A ℂ) (v : (A × Bool) × M → ℂ)
    (hv : ‖WithLp.toLp 2 v‖ = 1) (n : ℕ) (hn : 1 ≤ n) (hQ : n < Fintype.card A) :
    normalizedTraceDistance
        (protocolLabelCacheDensity tail H v n hQ.le)
        (protocolReferenceCacheDensity tail v n hQ.le) ≤
      3 * (n : ℝ) * ((n : ℝ) - 1) / (Fintype.card A : ℝ) := by
  have hpos : 0 < n := by omega
  rw [← cacheDensity_eq_labelCache_output tail H v n hpos hQ,
    ← referenceDensity_eq_referenceCache_output tail v n hpos hQ]
  have hd := ICO.C6CacheOutputComparisonAfter.density_reference_distance n hpos hQ
    (fun _ b => ICO.C6ActualResidualWeight.outcomeBasis H b)
    (fun i => ICO.C6RawFlagSlices.smallKnown (tail.tailKnown i))
    (fun i => ICO.C6SharedPairBound.smallKnown_isometry i _ (tail.tailKnown_isometry i))
    (ICO.C6RawWeightedEndpoint.cacheInput tail v)
    (ICO.C6SharedPairBound.cacheInput_pos tail v) n
    (ICO.C6CacheVisibleOutput.output n).map
    (ICO.C6CacheVisibleOutput.output n).traceNonincreasingCP_map
  rw [ICO.C6SharedPairBound.cacheInput_trace tail v hv, Complex.one_re, mul_one] at hd
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  unfold ICO.C6GradedCacheBound.rate at hd
  rw [hsub] at hd
  have heq : (n : ℝ) * (6 * ((n : ℝ) - 1) / (Fintype.card A : ℝ)) / 2 =
      3 * (n : ℝ) * ((n : ℝ) - 1) / (Fintype.card A : ℝ) := by ring
  linarith

/-- **Reference-cache distance (`cache_reference_distance`, adaptive `BudgetQueryTree` form)**:
for any adaptive strategy `tree` with mixed input `ρ`, relative basis `H`, `1 ≤ q`, and `q < d`,
`TD(ρ^{cache}, τ_ref) ≤ 3 q (q - 1) / d`. -/
theorem cache_reference_distance {A M O B : Type}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    {q : ℕ} (tree : BudgetQueryTree.Tree (A × M) O q B) (ρ : State B)
    (H : Matrix.unitaryGroup A ℂ) (hq : 1 ≤ q) (hqd : q < Fintype.card A) :
    normalizedTraceDistance
        (treeLabelCacheDensity tree ρ H hqd.le)
        (treeReferenceCacheDensity tree ρ hqd.le) ≤
      3 * (q : ℝ) * ((q : ℝ) - 1) / (Fintype.card A : ℝ) := by
  have hd_pos : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos (α := A)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hrhs_nn : 0 ≤ 3 * (q : ℝ) * ((q : ℝ) - 1) / (Fintype.card A : ℝ) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hd_pos.le
  classical
  cases isEmpty_or_nonempty M with
  | inl hm =>
    letI := hm
    have h1 : treeLabelCacheDensity tree ρ H hqd.le =
        (tree.channel (hidden (1 : Matrix.unitaryGroup A ℂ))
          (hidden (1 : Matrix.unitaryGroup A ℂ))).map ρ.matrix :=
      empty_memory_runStatefulTree tree _ _ _ _
        (cacheHiddenInitialMatrix (A := A) q) (cacheHiddenInitialMatrix_trace q) ρ.matrix
    have h2 : treeReferenceCacheDensity tree ρ hqd.le =
        (tree.channel (hidden (1 : Matrix.unitaryGroup A ℂ))
          (hidden (1 : Matrix.unitaryGroup A ℂ))).map ρ.matrix :=
      empty_memory_runStatefulTree tree _ _ _ _
        (cacheHiddenInitialMatrix (A := A) q) (cacheHiddenInitialMatrix_trace q) ρ.matrix
    rw [h1, h2, normalizedTraceDistance_self]
    exact hrhs_nn
  | inr hm =>
    letI := hm
    letI : Nonempty O := ((tree.channel (hidden (1 : Matrix.unitaryGroup A ℂ))
      (hidden (1 : Matrix.unitaryGroup A ℂ))).applyState ρ).nonempty
    letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    cases q with
    | zero => omega
    | succ q' =>
      let a₀ : A := Classical.arbitrary A
      let m₀ : M := Classical.arbitrary M
      let o₀ : O := Classical.arbitrary O
      let p := ICO.C6ChoiceCompiler.sequential a₀ m₀ o₀ (ICO.BudgetPreparation.prepare tree ρ)
      let v := p.heading.pre *ᵥ (fun _ : PUnit => (1 : ℂ))
      have hv : ‖WithLp.toLp 2 v‖ = 1 :=
        ICO.C6SharedOutput.prepared_norm_eq p _ ICO.BudgetPreparation.initial_mass
      rw [← treeLabelCacheDensity_eq_compiled a₀ m₀ o₀ tree ρ H hqd.le,
        ← treeReferenceCacheDensity_eq_compiled a₀ m₀ o₀ tree ρ hqd.le]
      refine (ICO.RecordingDistance.distance_contract
        p.heading.tail.terminalChannel.map
        p.heading.tail.terminalChannel.traceNonincreasingCP_map _ _
        (protocolLabelCacheDensity_pos p.heading.tail H v (q' + 1) hqd.le)
        (protocolReferenceCacheDensity_pos p.heading.tail v (q' + 1) hqd.le)).trans ?_
      exact cache_reference_protocol_distance p.heading.tail H v hv (q' + 1) (by omega) hqd

end ReferenceInvariant

end

end ICO.C6LabelCache



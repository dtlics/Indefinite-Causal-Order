import ICO.PathRecordingSupport
import ICO.RecordingDistance
import QIT.Classical.CQState
import QIT.Channels.Diamond

/-!
# Erasure of relation coherences in the fresh-output step

A copied query coordinate, unchanged right record, and enlarged left record
jointly identify both the old source and the fresh output. This module turns
that injectivity statement into a finite matrix channel identity with arbitrary
quantum side memory. The domain consists explicitly of fresh-query sources.
-/

namespace ICO.RecordingFreshOutput

open QIT ICO.PathRecordingSupport
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {α β a : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] [Fintype a] [DecidableEq a]

abbrev FreshSource (α β : Type*) [DecidableEq α] [DecidableEq β] :=
  {s : α × Relation α β × Relation α β // FreshLeft s.1 s.2.1}

/-- Private records after copying the query and appending the new left edge. -/
def environment (s : FreshSource α β) (y : β) :
    α × Relation α β × Relation α β :=
  (s.val.1, s.val.2.2, insert (s.val.1, y) s.val.2.1)

omit [Fintype α] [Fintype β] in
/-- Equality of all discarded records forces equal old sources and equal
    output labels. No classical-mixture assumption is made about the input. -/
theorem environment_injective {s t : FreshSource α β} {y z : β}
    (h : environment s y = environment t z) : s = t ∧ y = z := by
  have hx := congrArg (fun v : α × Relation α β × Relation α β => v.1) h
  change s.val.1 = t.val.1 at hx
  have hr := congrArg (fun v : α × Relation α β × Relation α β => v.2.1) h
  change s.val.2.2 = t.val.2.2 at hr
  have hl : insert (s.val.1, y) s.val.2.1 = insert (s.val.1, z) t.val.2.1 := by
    simpa only [environment, hx] using congrArg (fun v => v.2.2) h
  have htf : FreshLeft s.val.1 t.val.2.1 := hx.symm ▸ t.property
  obtain ⟨hy, hL⟩ := fresh_insert_injective s.property htf hl
  exact ⟨Subtype.ext (Prod.ext hx (Prod.ext hL hr)), hy⟩

omit [Fintype α] [Fintype β] in
theorem environment_eq_iff (s t : FreshSource α β) (y z : β) :
    environment s y = environment t z ↔ s = t ∧ y = z := by
  constructor
  · exact environment_injective
  · rintro ⟨rfl, rfl⟩
    rfl

variable {ι ε : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq ε]

/-- The remaining-memory diagonal block for a source recording label. -/
def memoryBlock (ρ : CMatrix (ι × a)) (s : ι) :
    CMatrix a := fun i j => ρ (s, i) (s, j)

omit [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι] in
theorem memoryBlock_posSemidef (ρ : CMatrix (ι × a))
    (hρ : ρ.PosSemidef) (s : ι) : (memoryBlock ρ s).PosSemidef :=
  hρ.submatrix (fun i => (s, i))

omit [DecidableEq a] [DecidableEq ι] in
theorem memoryBlock_mass (ρ : CMatrix (ι × a)) :
    ∑ s, (memoryBlock ρ s).trace.re = ρ.trace.re := by
  simp only [Matrix.trace, Matrix.diag, memoryBlock, Complex.re_sum, Fintype.sum_prod_type]

/-- Exact matrix kernel obtained by erasing the copied query and both records.
    The equality of environment labels is the partial-trace selection rule. -/
def erasedKernel (env : ι → β → ε) (amplitude : ι → β → ℂ)
    (ρ : CMatrix (ι × a)) : CMatrix (β × a) :=
  fun u v => ∑ s, ∑ t,
    if env s u.1 = env t v.1 then
      amplitude s u.1 * star (amplitude t v.1) * ρ (s, u.2) (t, v.2) else 0

omit [Fintype a] [DecidableEq a] in
/-- All relation coherences disappear: the output is a positive-memory
    block mixture with weights equal to squared insertion amplitudes. -/
theorem erasedKernel_eq_blocks (env : ι → β → ε)
    (hEnv : ∀ s t y z, env s y = env t z ↔ s = t ∧ y = z)
    (amplitude : ι → β → ℂ) (ρ : CMatrix (ι × a)) :
    erasedKernel env amplitude ρ = QIT.Classical.blockDiagonal
      (fun y => ∑ s, ((Complex.normSq (amplitude s y) : ℝ) : ℂ) • memoryBlock ρ s) := by
  classical
  ext u v
  rcases u with ⟨y, i⟩
  rcases v with ⟨z, j⟩
  by_cases hy : y = z
  · subst z
    have hb := congrFun (congrFun (QIT.Classical.blockDiagonal_block_self
      (fun y => ∑ s, ((Complex.normSq (amplitude s y) : ℝ) : ℂ) • memoryBlock ρ s)
      y) i) j
    simp only [QIT.Classical.block] at hb
    rw [hb]
    simp only [erasedKernel, hEnv, and_true, Finset.sum_ite_eq,
      Matrix.sum_apply, Matrix.smul_apply, memoryBlock, smul_eq_mul,
      Complex.star_def, Complex.mul_conj, Finset.mem_univ, if_true]
  · have hb := congrFun (congrFun (QIT.Classical.blockDiagonal_block_ne
      (fun y => ∑ s, ((Complex.normSq (amplitude s y) : ℝ) : ℂ) • memoryBlock ρ s)
      hy) i) j
    simp only [QIT.Classical.block, Matrix.zero_apply] at hb
    rw [hb]
    simp [erasedKernel, hEnv, hy]

/-- Kraus operators for writing a private environment label and then erasing
    that private register. These maps are not assumed trace preserving. -/
def recordingKraus (env : ι → β → ε) (amplitude : ι → β → ℂ) (e : ε) :
    Matrix β ι ℂ := fun y s => if env s y = e then amplitude s y else 0

variable [Fintype ε]

omit [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι] in
theorem recordingKraus_trace_rule (env : ι → β → ε) (amplitude : ι → β → ℂ)
    (s t : ι) (y z : β) :
    (∑ e, recordingKraus env amplitude e y s * star (recordingKraus env amplitude e z t)) =
      if env s y = env t z then amplitude s y * star (amplitude t z) else 0 := by
  classical
  rw [Finset.sum_eq_single (env s y)]
  · by_cases he : env s y = env t z
    · simp [recordingKraus, he]
    · simp [recordingKraus, he, Ne.symm he]
  · intro e _ he
    simp [recordingKraus, Ne.symm he]
  · intro hn
    simp at hn

omit [DecidableEq ε] in
/-- Entrywise Kraus action with the environment sum collected into its Gram
    coefficient. This is an exact matrix identity, not a physical premise. -/
theorem ofKraus_entry (K : ε → Matrix β ι ℂ) (X : CMatrix ι) (y z : β) :
    MatrixMap.ofKraus K X y z =
      ∑ s, ∑ t, (∑ e, K e y s * star (K e z t)) * X s t := by
  change (∑ e, K e * X * (K e).conjTranspose) y z = _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  calc
    (∑ e, ∑ t, ∑ s, K e y s * X s t * star (K e z t)) =
        ∑ t, ∑ s, ∑ e, K e y s * X s t * star (K e z t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_comm
    _ = ∑ s, ∑ t, ∑ e, K e y s * X s t * star (K e z t) := Finset.sum_comm
    _ = ∑ s, ∑ t, ∑ e, K e y s * star (K e z t) * X s t := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := rfl

/-- The kernel is exactly the channel given by the recording Kraus operators,
    tensored with the identity on arbitrary quantum memory. -/
theorem erasedKernel_eq_quantum_map (env : ι → β → ε) (amplitude : ι → β → ℂ)
    (ρ : CMatrix (ι × a)) :
    MatrixMap.kron (MatrixMap.ofKraus (recordingKraus env amplitude))
      (Channel.idChannel a).map ρ = erasedKernel env amplitude ρ := by
  ext u v
  rw [MatrixMap.kron_idChannel_apply_slice, ofKraus_entry]
  simp only [recordingKraus_trace_rule, erasedKernel, ite_mul, zero_mul]

omit [Fintype a] [DecidableEq a] [DecidableEq ι] in
theorem blockDiagonal_sum (T : ι → β → CMatrix a) :
    QIT.Classical.blockDiagonal (fun y => ∑ s, T s y) =
      ∑ s, QIT.Classical.blockDiagonal (T s) := by
  ext u v
  simp only [QIT.Classical.blockDiagonal, Matrix.sum_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype a] [DecidableEq a] [DecidableEq ι] in
theorem memoryBlock_sum (ρ : CMatrix (ι × a)) :
    (∑ s, memoryBlock ρ s) = QIT.partialTraceA ρ := by
  ext i j
  simp only [memoryBlock, Matrix.sum_apply, QIT.partialTraceA]

omit [Fintype a] [DecidableEq a] [DecidableEq ι] in
theorem memoryOutput_sum (p : β → ℝ) (T : ι → CMatrix a) :
    RecordingDistance.memoryOutput p (∑ s, T s) =
      ∑ s, RecordingDistance.memoryOutput p (T s) := by
  unfold RecordingDistance.memoryOutput
  simp_rw [Finset.smul_sum]
  exact blockDiagonal_sum _

/-- The normalized fresh-output amplitude in the published insertion rule. -/
def freshAmplitude (forbidden : ι → Finset β) (s : ι) (y : β) : ℂ :=
  if y ∈ forbidden s then 0 else
    (((Real.sqrt ((Fintype.card β : ℝ) - ((forbidden s).card : ℝ)))⁻¹ : ℝ) : ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem freshAmplitude_normSq (forbidden : ι → Finset β) (s : ι) (y : β)
    (hs : (forbidden s).card < Fintype.card β) :
    Complex.normSq (freshAmplitude forbidden s y) =
      FreshOutputDistance.uniformOutside (forbidden s) y := by
  have hlt : ((forbidden s).card : ℝ) < Fintype.card β := by exact_mod_cast hs
  have hd : (0 : ℝ) ≤ (Fintype.card β : ℝ) - (forbidden s).card := by linarith
  by_cases hy : y ∈ forbidden s
  · simp [freshAmplitude, FreshOutputDistance.uniformOutside, hy]
  · simp [freshAmplitude, FreshOutputDistance.uniformOutside, hy,
      Complex.normSq_ofReal, Real.mul_self_sqrt hd]

/-- Complete fresh-output trace-distance estimate for the explicit recording
    Kraus map with arbitrary quantum memory. The environmental injectivity
    premise is supplied for finite relations by `environment_eq_iff` above. -/
theorem fresh_recording_map_distance (env : ι → β → ε)
    (hEnv : ∀ s t y z, env s y = env t z ↔ s = t ∧ y = z)
    (forbidden : ι → Finset β) (ρ : CMatrix (ι × a))
    (hρ : ρ.PosSemidef) (hmass : ρ.trace.re ≤ 1)
    (m : ℕ) (hsize : ∀ s, (forbidden s).card ≤ m) (hmd : m < Fintype.card β) :
    normalizedTraceDistance
      (MatrixMap.kron (MatrixMap.ofKraus (recordingKraus env (freshAmplitude forbidden)))
        (Channel.idChannel a).map ρ)
      (RecordingDistance.memoryOutput (fun _ : β => 1 / (Fintype.card β : ℝ))
        (QIT.partialTraceA ρ)) ≤ (m : ℝ) / (Fintype.card β : ℝ) := by
  rw [erasedKernel_eq_quantum_map, erasedKernel_eq_blocks env hEnv]
  have hamp (s : ι) (y : β) := freshAmplitude_normSq forbidden s y
    (lt_of_le_of_lt (hsize s) hmd)
  simp_rw [hamp]
  rw [blockDiagonal_sum, ← memoryBlock_sum ρ, memoryOutput_sum]
  exact RecordingDistance.fresh_record_mixture_distance forbidden (memoryBlock ρ)
    (memoryBlock_posSemidef ρ hρ) (by rwa [memoryBlock_mass]) m hsize hmd

/-- The finite support immediately before the growing-only insertion. -/
abbrev ActiveSource (α : Type*) [DecidableEq α] (m : ℕ) :=
  {s : FreshSource α α // s.val.2.1.card + s.val.2.2.card ≤ m}

instance activeSourceFintype (m : ℕ) : Fintype (ActiveSource α m) := Fintype.ofFinite _

instance activeSourceDecidableEq (m : ℕ) : DecidableEq (ActiveSource α m) :=
  Classical.decEq _

def activeEnvironment (m : ℕ) (s : ActiveSource α m) (y : α) := environment s.val y

def outputForbidden (m : ℕ) (s : ActiveSource α m) : Finset α :=
  (s.val.val.2.1 ∪ s.val.val.2.2).image Prod.snd

omit [Fintype α] in
theorem activeEnvironment_eq_iff (m : ℕ) (s t : ActiveSource α m) (y z : α) :
    activeEnvironment m s y = activeEnvironment m t z ↔ s = t ∧ y = z := by
  rw [activeEnvironment, activeEnvironment, environment_eq_iff]
  constructor
  · rintro ⟨hst, hyz⟩
    exact ⟨Subtype.ext hst, hyz⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

omit [Fintype α] in
theorem outputForbidden_card_le (m : ℕ) (s : ActiveSource α m) :
    (outputForbidden m s).card ≤ m := by
  apply le_trans Finset.card_image_le
  exact le_trans (Finset.card_union_le _ _) s.property

/-- The finite relation insertion channel itself satisfies the dimension-only
    fresh-output bound, including coherent relation inputs and quantum memory.
    The input type records exactly the support invariant used by C5. -/
theorem active_recording_fresh_distance (m : ℕ) (hmd : m < Fintype.card α)
    (ρ : CMatrix (ActiveSource α m × a)) (hρ : ρ.PosSemidef) (hmass : ρ.trace.re ≤ 1) :
    normalizedTraceDistance
      (MatrixMap.kron (MatrixMap.ofKraus
        (recordingKraus (activeEnvironment m) (freshAmplitude (outputForbidden m))))
        (Channel.idChannel a).map ρ)
      (RecordingDistance.memoryOutput (fun _ : α => 1 / (Fintype.card α : ℝ))
        (QIT.partialTraceA ρ)) ≤ (m : ℝ) / (Fintype.card α : ℝ) :=
  fresh_recording_map_distance (activeEnvironment m) (activeEnvironment_eq_iff m)
    (outputForbidden m) ρ hρ hmass m (outputForbidden_card_le m) hmd

omit [Fintype ι] in
/-- Orthogonality of discarded environment labels and normalized amplitudes
    give the exact trace-preserving Kraus identity. -/
theorem recordingKraus_complete (env : ι → β → ε)
    (hEnv : ∀ s t y z, env s y = env t z ↔ s = t ∧ y = z)
    (amplitude : ι → β → ℂ) (hnorm : ∀ s, ∑ y, Complex.normSq (amplitude s y) = 1) :
    MatrixMap.krausAdjoint (recordingKraus env amplitude) (1 : CMatrix β) = 1 := by
  classical
  ext s t
  simp only [MatrixMap.krausAdjoint, Matrix.mul_one, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  have hi (y : β) :
      (∑ e, star (recordingKraus env amplitude e y s) * recordingKraus env amplitude e y t) =
        if s = t then ((Complex.normSq (amplitude s y) : ℝ) : ℂ) else 0 := by
    have hswap :
        (∑ e, star (recordingKraus env amplitude e y s) * recordingKraus env amplitude e y t) =
          ∑ e, recordingKraus env amplitude e y t * star (recordingKraus env amplitude e y s) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [hswap, recordingKraus_trace_rule]
    by_cases hst : s = t
    · subst t
      simp [Complex.mul_conj]
    · simp [hEnv, hst, Ne.symm hst]
  simp_rw [hi]
  by_cases hst : s = t
  · subst t
    simp only [ite_true, Matrix.one_apply_eq]
    rw [← Complex.ofReal_sum, hnorm, Complex.ofReal_one]
  · simp [hst]

/-- The normalized fresh-record map is an actual CPTP channel on its explicit
    fresh-source domain, rather than a subnormalized branch. -/
def freshRecordingChannel (env : ι → β → ε)
    (hEnv : ∀ s t y z, env s y = env t z ↔ s = t ∧ y = z)
    (forbidden : ι → Finset β) (hfree : ∀ s, (forbidden s).card < Fintype.card β) :
    Channel ι β where
  map := MatrixMap.ofKraus (recordingKraus env (freshAmplitude forbidden))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  mapsPositive := MatrixMap.ofKraus_mapsPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (recordingKraus_complete env hEnv _ (by
      intro s
      simp_rw [freshAmplitude_normSq forbidden s _ (hfree s)]
      exact FreshOutputDistance.uniformOutside_sum (forbidden s) (hfree s)))

end
end ICO.RecordingFreshOutput

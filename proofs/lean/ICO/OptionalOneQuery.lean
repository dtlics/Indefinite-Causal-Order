import ICO.LiftQueryMemory

/-! # A physical one-query realization for an adaptive tree that may omit its query -/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.ClassicalDilation ICO.OraclePadding

namespace ICO.OptionalOneQuery

set_option maxHeartbeats 350000
noncomputable section
universe u

structure NormalForm (A B O : Type u) [Fintype A] [Fintype B] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq O] where
  Memory : Type u
  [finite : Fintype Memory]
  [decide : DecidableEq Memory]
  [nonempty : Nonempty Memory]
  form : ICO.OneQueryTree.NormalForm B (A × Memory) O

attribute [instance] NormalForm.finite NormalForm.decide NormalForm.nonempty

variable {A B C M O L : Type u}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype M] [Fintype O] [Fintype L]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq M]
variable [DecidableEq O] [DecidableEq L]

def terminalOp (a₀ : A) (Φ : Channel B O) (k : B × O) : Matrix (A × O) B ℂ :=
  pad (C := O) a₀ * channelKraus Φ k

theorem terminalOp_complete (a₀ : A) (Φ : Channel B O) :
    (∑ k, (terminalOp a₀ Φ k).conjTranspose * terminalOp a₀ Φ k) = 1 := by
  unfold terminalOp
  have hK : (∑ k, (channelKraus Φ k).conjTranspose * channelKraus Φ k) = 1 := by
    have h := MatrixMap.krausAdjoint_one_of_tracePreserving (channelKraus Φ)
      (by rw [← channelKraus_map]; exact Φ.tracePreserving)
    simpa [MatrixMap.krausAdjoint] using h
  have hterm (k : B × O) :
      (pad (C := O) a₀ * channelKraus Φ k).conjTranspose * (pad (C := O) a₀ * channelKraus Φ k) =
        (channelKraus Φ k).conjTranspose * channelKraus Φ k := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (pad (C := O) a₀).conjTranspose, pad_isometry]
    simp
  simpa only [hterm] using hK

def NormalForm.terminal [Nonempty O] (a₀ : A) (Φ : Channel B O) : NormalForm A B O where
  Memory := O
  form :=
    { Branch := B × O
      pre := { op := terminalOp a₀ Φ, complete := terminalOp_complete a₀ Φ }
      post := fun _ => discardChannel }
set_option maxHeartbeats 500000 in
theorem NormalForm.terminal_map [Nonempty O] (a₀ : A) (Φ : Channel B O)
    (U : Matrix.unitaryGroup A ℂ) :
    ((NormalForm.terminal a₀ Φ).form.channel (oracleChannel U)).map = Φ.map := by
  ext X i j
  rw [ICO.OneQueryTree.NormalForm.channel_apply]
  conv_rhs => rw [channelKraus_map Φ]
  simp only [NormalForm.terminal, terminalOp, MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact congrFun (congrFun (discarded_oracle_precomposed U a₀ (channelKraus Φ k) X) i) j

def NormalForm.call [Nonempty M] (after : Channel (A × M) O) : NormalForm A (A × M) O where
  Memory := M
  form := ICO.OneQueryTree.NormalForm.immediate after

def branchMemoryInjection (next : L → NormalForm A C O) (l : L) :
    (next l).Memory ↪ Option ((l : L) × (next l).Memory) where
  toFun m := some ⟨l, m⟩
  inj' := by intro x y h; simpa using h

def NormalForm.prepend (a₀ : A) (I : Instrument B C L) (next : L → NormalForm A C O) :
    NormalForm A B O where
  Memory := Option ((l : L) × (next l).Memory)
  form := ICO.OneQueryTree.NormalForm.prepend I (fun l =>
    ICO.LiftQueryMemory.liftNormalForm (next l).form (branchMemoryInjection next l)
      a₀ (Classical.choice (next l).nonempty))

theorem NormalForm.prepend_map (a₀ : A) (I : Instrument B C L)
    (next : L → NormalForm A C O) (U : Matrix.unitaryGroup A ℂ) :
    ((NormalForm.prepend a₀ I next).form.channel (oracleChannel U)).map =
      (adaptiveChannel I (fun l => (next l).form.channel (oracleChannel U))).map := by
  unfold NormalForm.prepend
  rw [ICO.OneQueryTree.NormalForm.prepend_map]
  ext X i j
  simp only [ICO.OneQueryTree.adaptiveChannel_apply,
    ICO.LiftQueryMemory.liftNormalForm_map]

inductive QueryTree (A M O : Type u) [Fintype A] [Fintype M] [Fintype O]
    [DecidableEq A] [DecidableEq M] [DecidableEq O] :
    (B : Type u) → [Fintype B] → [DecidableEq B] → Type (u + 1) where
  | stop {B : Type u} [Fintype B] [DecidableEq B] (after : Channel B O) : QueryTree A M O B
  | call (after : ICO.InstrumentCompression.Tree O (A × M)) : QueryTree A M O (A × M)
  | node {B C L : Type u} [Fintype B] [Fintype C] [Fintype L]
      [DecidableEq B] [DecidableEq C] [DecidableEq L]
      (I : Instrument B C L) (next : L → QueryTree A M O C) : QueryTree A M O B

def QueryTree.channel (tree : QueryTree A M O B) (oracle : Channel (A × M) (A × M)) :
    Channel B O := by
  induction tree with
  | stop after => exact after
  | call after => exact after.toChannel.comp oracle
  | node I next ih => exact adaptiveChannel I ih

def QueryTree.normalForm [Nonempty M] [Nonempty O] (a₀ : A) (tree : QueryTree A M O B) :
    NormalForm A B O := by
  induction tree with
  | stop after => exact NormalForm.terminal a₀ after
  | call after => exact NormalForm.call after.toChannel
  | node I next ih => exact NormalForm.prepend a₀ I ih

/-- Every optional query is realized by exactly one physical query. Omitted
calls act on discarded registers, and all branch memories are embedded into
one common finite memory with a proved channel retraction. -/
theorem QueryTree.normalForm_correct [Nonempty M] [Nonempty O] (a₀ : A)
    (tree : QueryTree A M O B) (U : Matrix.unitaryGroup A ℂ) :
    ((tree.normalForm a₀).form.channel (oracleChannel U)).map =
      (tree.channel (oracleChannel U)).map := by
  induction tree with
  | stop after => exact NormalForm.terminal_map a₀ after U
  | call after =>
    change ((ICO.OneQueryTree.NormalForm.immediate after.toChannel).channel
      (oracleChannel U)).map = (after.toChannel.comp (oracleChannel U)).map
    exact ICO.OneQueryTree.NormalForm.immediate_map _ _
  | node I next ih =>
    change ((NormalForm.prepend a₀ I (fun l => (next l).normalForm a₀)).form.channel
      (oracleChannel U)).map = _
    rw [NormalForm.prepend_map]
    ext X i j
    simp only [ICO.OneQueryTree.adaptiveChannel_apply, ih, QueryTree.channel]

end
end ICO.OptionalOneQuery



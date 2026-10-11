import ICO.C6RetainedHistory
import ICO.C6ResidualCoordinates

/-! Chronological coordinates of the actual privately copied history. -/
namespace ICO.C6HistoryCoordinates
open Matrix QIT ICO.C6RetainedHistory ICO.C6ResidualCoordinates ICO.C6ChoiceMeasurement
  ICO.RecordingPurifiedProtocol
noncomputable section
set_option maxHeartbeats 1100000
set_option Elab.async false

def historyEquiv (J:Type*) : (q:ℕ)→History J q≃(Fin q→J)
  | 0=>by change PUnit≃(Fin 0→J); exact Equiv.ofUnique _ _
  | q+1=>(Equiv.prodCongr (Equiv.refl J) (historyEquiv J q)).trans (Fin.snocEquiv (fun _:Fin (q+1)=>J))

theorem historyEquiv_succ (J:Type*) (q:ℕ) (j:J) (η:History J q) :
    historyEquiv J (q+1) (j,η)=Fin.snoc (historyEquiv J q η) j := rfl

def prefixHistory {J:Type*} {q:ℕ} (η:History J q) (s:ℕ) (hs:s≤q) : History J s :=
  (historyEquiv J s).symm (fun i=>historyEquiv J q η ⟨i.val,lt_of_lt_of_le i.isLt hs⟩)

theorem prefixHistory_coords {J:Type*} {q:ℕ} (η:History J q) (s:ℕ) (hs:s≤q) :
    historyEquiv J s (prefixHistory η s hs)=
      fun i=>historyEquiv J q η ⟨i.val,lt_of_lt_of_le i.isLt hs⟩ :=
  (historyEquiv J s).apply_symm_apply _

variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem vectors_coords (H:Matrix.unitaryGroup A ℂ) (q:ℕ) (η:History (A×Bool) q)
    (i:Fin q) : vectors H q η i=
      WithLp.toLp 2 (queryVector H ((historyEquiv (A×Bool) q η i).2,
        (historyEquiv (A×Bool) q η i).1)) := by
  induction q with
  | zero=>exact Fin.elim0 i
  | succ q ih=>
    rcases η with ⟨j,η⟩
    cases i using Fin.lastCases with
    | last=>simp only [vectors,historyEquiv_succ,Fin.snoc_last]
    | cast i=>simpa only [vectors,historyEquiv_succ,Fin.snoc_castSucc] using ih η i

theorem vectors_prefix (H:Matrix.unitaryGroup A ℂ) {q:ℕ}
    (η:History (A×Bool) q) (s:ℕ) (hs:s≤q) :
    vectors H s (prefixHistory η s hs)=historyPrefix (vectors H q η) s hs := by
  ext i a
  simp only [vectors_coords,historyPrefix,prefixHistory_coords]

#print axioms vectors_prefix
end
end ICO.C6HistoryCoordinates

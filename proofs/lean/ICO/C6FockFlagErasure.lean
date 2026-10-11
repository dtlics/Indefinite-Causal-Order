import ICO.C6PermanentErasure
import ICO.MHFockKnownOperation

/-! Private occupation flags on the literal Fock register may be adjoined
without changing the accessible output once their permanent support is proved. -/
namespace ICO.C6FockFlagErasure
open Matrix QIT ICO.C6PermanentErasure ICO.MHBoundedRecording ICO.MHFockKnownOperation
  ICO.MHDecompressionErasure
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M J:Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Fintype J] [DecidableEq J]

theorem coherent_fock_erasure (T:ℕ) (tag:Records (α:=A) T→J)
    (v:J→InputCutoff (α:=A) T×M→ℂ)
    (hv:∀j i,v j i≠0→tag (records i.1)=j) :
    fockVisible T (∑j,v j)=∑j,fockVisible T (v j) := by
  let e:=queryMemoryFirst (α:=A) T M
  have hh:=coherent_family_erasure tag (fun j=>v j ∘ e.symm) (by
    intro j i hi
    exact hv j (e.symm i) hi)
  have he:(∑j,v j) ∘ e.symm=∑j,v j ∘ e.symm := by funext i; simp
  change partialTraceB (rankOneMatrix ((∑j,v j) ∘ e.symm))=_
  rw [he]
  exact hh

theorem number_flags_erasure {I:Type*} [Fintype I] [DecidableEq I]
    (T:ℕ) (N:I→Records (α:=A) T→ℕ)
    (v:(I→Bool)→InputCutoff (α:=A) T×M→ℂ)
    (hv:∀b i,v b i≠0→∀s,N s (records i.1)=if b s then 1 else 0) :
    fockVisible T (∑b,v b)=∑b,fockVisible T (v b) := by
  apply coherent_fock_erasure T (fun R s=>decide (N s R=1)) v
  intro b i hi
  funext s
  rw [hv b i hi s]
  cases b s <;> simp

#print axioms number_flags_erasure
end
end ICO.C6FockFlagErasure

import ICO.C6AcceptedIndices
import ICO.C6HistoryConjugation

namespace ICO.C6AcceptedModes
open Matrix QIT ICO.C6AcceptedIndices ICO.C6FlagCount ICO.C6HistoryCoordinates
  ICO.C6ResidualModes ICO.RecordingPurifiedProtocol
noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

theorem prior_snoc_cast {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A)
    (i:Fin n) : prior (Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) v x) i.castSucc=prior v i := by
  funext j
  change Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) v x
    (⟨j.val,by omega⟩:Fin n).castSucc=v ⟨j.val,by omega⟩
  rw [Fin.snoc_castSucc]

theorem residual_snoc_cast {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A)
    (i:Fin n) : residual (Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) v x) i.castSucc=residual v i := by
  rw [ICO.C6ResidualModes.residual,prior_snoc_cast,Fin.snoc_castSucc]
  rfl

theorem mode_snoc_cast {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A)
    (i:Fin n) : mode (Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) v x) i.castSucc=mode v i := by
  simp only [mode,residual_snoc_cast]

def Valid {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (κ:History Bool n) : Prop :=
  ∀i,historyEquiv Bool n κ i=true→ residual v i≠0

def modes {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (κ:History Bool n) :
    Fin (flagCount n κ)→EuclideanSpace ℂ A := fun i=>mode v (selected n κ i)

def activeIndices {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (κ:History Bool n)
    (hv:Valid v κ) : Fin (flagCount n κ)→Active v :=
  fun i=>⟨selected n κ i,hv _ (selected_flag n κ i)⟩

theorem activeIndices_injective {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (κ:History Bool n)
    (hv:Valid v κ) : Function.Injective (activeIndices v κ hv) := by
  intro i j hij
  exact selected_injective n κ (congrArg Subtype.val hij)

theorem modes_orthonormal {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (κ:History Bool n)
    (hv:Valid v κ) : Orthonormal ℂ (modes v κ) :=
  (mode_orthonormal v).comp (activeIndices v κ hv) (activeIndices_injective v κ hv)

theorem valid_snoc {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A)
    (κ:History Bool n) (f:Bool) :
    Valid (Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) v x) (n:=n+1) (f,κ) ↔
      Valid v κ ∧ (f=true→ residual (Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) v x) (Fin.last n)≠0) := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hh:=h i.castSucc (by simpa only [historyEquiv_succ,Fin.snoc_castSucc] using hi)
      simpa only [residual_snoc_cast] using hh
    · intro hf
      exact h (Fin.last n) (by simpa only [historyEquiv_succ,Fin.snoc_last] using hf)
  · rintro ⟨h,hf⟩ i hi
    cases i using Fin.lastCases with
    | last=>exact hf (by simpa only [historyEquiv_succ,Fin.snoc_last] using hi)
    | cast i=>
      rw [residual_snoc_cast]
      exact h i (by simpa only [historyEquiv_succ,Fin.snoc_castSucc] using hi)

theorem modes_false {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A)
    (κ:History Bool n) (i:Fin (flagCount n κ)) :
    modes (Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) v x) (n:=n+1) (false,κ) (Fin.cast (flagCount_false n κ).symm i)=
      modes v κ i := by
  unfold modes
  rw [selected_false,mode_snoc_cast]

theorem modes_true {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A)
    (κ:History Bool n) (i:Fin (flagCount n κ+1)) :
    modes (Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) v x) (n:=n+1) (true,κ) (Fin.cast (flagCount_true n κ).symm i)=
      Fin.cons (α:=fun _:Fin (flagCount n κ+1)=>EuclideanSpace ℂ A) (mode (Fin.snoc (α:=fun _:Fin (n+1)=>EuclideanSpace ℂ A) v x) (Fin.last n)) (modes v κ) i := by
  unfold modes
  rw [selected_true]
  cases i using Fin.cases with
  | zero=>rw [Fin.cons_zero,Fin.cons_zero]
  | succ i=>rw [Fin.cons_succ,Fin.cons_succ,mode_snoc_cast]

#print axioms modes_orthonormal
#print axioms modes_true
end
end ICO.C6AcceptedModes

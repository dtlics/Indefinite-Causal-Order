import ICO.RecordingPurifiedProtocol
import ICO.C6ChannelTrajectory

/-! Two literal private histories, for outcomes and for birth/retrieval flags.
Every branch is a matrix map, so zero-weight branches remain defined. Erasure
is performed only at the endpoint by summing the classical blocks. -/
namespace ICO.C6ClassicalHistoryRun
open QIT Matrix ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
universe u v w
variable {J : Type u} {F : Type v} [Fintype J] [DecidableEq J]
  [Fintype F] [DecidableEq F]
  {H : ℕ→Type w} [∀i,Fintype (H i)] [∀i,DecidableEq (H i)]

abbrev Branches := ∀i,History J i→History F i→J→F→MatrixMap (H i) (H (i+1))

def run (S : Branches (J:=J) (F:=F) (H:=H)) (X:CMatrix (H 0)) :
    (i:ℕ)→History J i→History F i→CMatrix (H i)
  | 0,_,_=>X
  | i+1,η,κ=>S i η.2 κ.2 η.1 κ.1 (run S X i η.2 κ.2)

def erase (i:ℕ) (X:History J i→History F i→CMatrix (H i)) : CMatrix (H i) :=
  ∑η,∑κ,X η κ

theorem sum_succ (i:ℕ) (X:History J (i+1)→History F (i+1)→CMatrix (H (i+1))) :
    erase (i+1) X=∑η:History J i,∑κ:History F i,∑j:J,∑f:F,X (j,η) (f,κ) := by
  change (∑η:J×History J i,∑κ:F×History F i,X η κ)=_
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  simp_rw [Finset.sum_comm (f:=fun f κ=>X (_,η) (f,κ))]
  rw [Finset.sum_comm]

theorem run_pos (S : Branches (J:=J) (F:=F) (H:=H))
    (hS:∀i η κ j f,MatrixMap.IsCompletelyPositive (S i η κ j f))
    (X:CMatrix (H 0)) (hX:X.PosSemidef) (n:ℕ)
    (η:History J n) (κ:History F n) : (run S X n η κ).PosSemidef := by
  induction n with
  | zero=>exact hX
  | succ n ih=>
    exact MatrixMap.isCompletelyPositive_mapsPositive _ (hS n _ _ _ _)
      _ (ih η.2 κ.2)

theorem erase_uniform (S : Branches (J:=J) (F:=F) (H:=H))
    (Φ:∀i,Channel (H i) (H (i+1)))
    (hS:∀i η κ,(∑j,∑f,S i η κ j f)=(Φ i).map)
    (X:CMatrix (H 0)) (n:ℕ) :
    erase n (run S X n)=ICO.C6ChannelTrajectory.run Φ X n := by
  induction n with
  | zero=>simp [erase,run,History,ICO.C6ChannelTrajectory.run]
  | succ n ih=>
    rw [sum_succ]
    simp only [run]
    have hs (η:History J n) (κ:History F n) :
        (∑j,∑f,S n η κ j f (run S X n η κ))=
          (Φ n).map (run S X n η κ) := by
      simpa only [LinearMap.sum_apply] using
        congrArg (fun ψ:MatrixMap (H n) (H (n+1))=>ψ (run S X n η κ)) (hS n η κ)
    simp_rw [hs]
    calc
      _ = (Φ n).map (erase n (run S X n)) := by simp only [erase,map_sum]
      _ = _ := by rw [ih]; rfl

theorem run_difference_pos (S T : Branches (J:=J) (F:=F) (H:=H))
    (hS:∀i η κ j f,MatrixMap.IsCompletelyPositive (S i η κ j f))
    (hT:∀i η κ j f,MatrixMap.IsCompletelyPositive (T i η κ j f))
    (hD:∀i η κ j f,MatrixMap.IsCompletelyPositive (S i η κ j f-T i η κ j f))
    (X:CMatrix (H 0)) (hX:X.PosSemidef) (n:ℕ)
    (η:History J n) (κ:History F n) :
    (run S X n η κ-run T X n η κ).PosSemidef := by
  induction n with
  | zero=>simpa only [run,sub_self] using (Matrix.PosSemidef.zero (n:=H 0) (R:=ℂ))
  | succ n ih=>
    let V:=run S X n η.2 κ.2
    let W:=run T X n η.2 κ.2
    have hp:=MatrixMap.isCompletelyPositive_mapsPositive _ (hS n η.2 κ.2 η.1 κ.1)
      _ (ih η.2 κ.2)
    have hd:=MatrixMap.isCompletelyPositive_mapsPositive _ (hD n η.2 κ.2 η.1 κ.1)
      _ (run_pos T hT X hX n η.2 κ.2)
    have he : run S X (n+1) η κ-run T X (n+1) η κ=
      S n η.2 κ.2 η.1 κ.1 (V-W)+
        (S n η.2 κ.2 η.1 κ.1-T n η.2 κ.2 η.1 κ.1) W := by
      simp only [V,W,run,map_sub,LinearMap.sub_apply]
      abel
    rw [he]
    exact hp.add hd

#print axioms erase_uniform
#print axioms run_difference_pos
end
end ICO.C6ClassicalHistoryRun

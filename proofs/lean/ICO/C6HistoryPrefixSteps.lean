import ICO.C6HistoryCoordinates

namespace ICO.C6HistoryPrefixSteps
open ICO.C6HistoryCoordinates ICO.RecordingPurifiedProtocol
noncomputable section
set_option maxHeartbeats 900000
set_option Elab.async false

theorem prefixHistory_succ {J:Type*} {q:ℕ} (η:History J q) (n:ℕ) (hn:n+1≤q) :
    prefixHistory η (n+1) hn=
      (historyEquiv J q η ⟨n,by omega⟩,prefixHistory η n (by omega)) := by
  apply (historyEquiv J (n+1)).injective
  rw [prefixHistory_coords,historyEquiv_succ]
  ext i
  cases i using Fin.lastCases with
  | last=>rw [Fin.snoc_last]; rfl
  | cast i=>rw [Fin.snoc_castSucc,prefixHistory_coords]; rfl

def pastFlag {n:ℕ} (κ:History Bool n) (i:ℕ) : Bool :=
  if hi:i<n then historyEquiv Bool n κ ⟨i,hi⟩ else false

theorem pastFlag_zero (κ:History Bool 0) (i:ℕ) : pastFlag κ i=false := by
  simp [pastFlag]

theorem pastFlag_succ {n:ℕ} (κ:History Bool n) (b:Bool) (i:ℕ) :
    pastFlag (n:=n+1) (b,κ) i=if i=n then b else pastFlag κ i := by
  rcases lt_trichotomy i n with hi|hi|hi
  · have hn:i<n+1:=Nat.lt_succ_of_lt hi
    simp only [pastFlag,dif_pos hn,dif_pos hi,if_neg (Nat.ne_of_lt hi),historyEquiv_succ]
    have he:(⟨i,hn⟩:Fin (n+1))=(⟨i,hi⟩:Fin n).castSucc:=rfl
    rw [he,Fin.snoc_castSucc]
  · subst i
    simp only [pastFlag,dif_pos (Nat.lt_succ_self n),ite_true,historyEquiv_succ]
    exact Fin.snoc_last _ _
  · have hni:¬i<n:=by omega
    have hni':¬i<n+1:=by omega
    simp only [pastFlag,dif_neg hni,dif_neg hni',if_neg (Ne.symm (Nat.ne_of_lt hi))]

theorem pastFlag_self {n:ℕ} (κ:History Bool n) : pastFlag κ n=false := by
  simp [pastFlag]

theorem pastFlag_succ_false {n:ℕ} (κ:History Bool n) (i:ℕ) :
    pastFlag (n:=n+1) (false,κ) i=pastFlag κ i := by
  rw [pastFlag_succ]
  by_cases hi:i=n
  · subst i; simp [pastFlag_self]
  · simp [hi]

#print axioms prefixHistory_succ
#print axioms pastFlag_succ
end
end ICO.C6HistoryPrefixSteps


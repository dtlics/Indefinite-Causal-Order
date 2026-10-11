import ICO.LabelledQueryTree

open QIT
namespace ICO.QueryOracleMaps
variable {A L R : Type*} [Fintype A] [DecidableEq A]

@[simp] theorem channel_sum_elim (U V : Channel A A) :
    (fun i : L ⊕ R => (Sum.elim (fun _ => U) (fun _ => V) i).map) =
      Sum.elim (fun _ => U.map) (fun _ => V.map) := by
  funext i
  cases i <;> rfl

end ICO.QueryOracleMaps

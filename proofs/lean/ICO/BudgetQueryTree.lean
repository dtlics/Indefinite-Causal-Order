import ICO.InstrumentCompression

/-! # Adaptive circuits with a budget on total actual oracle calls -/

open Matrix QIT ICO.InstrumentCompression

namespace ICO.BudgetQueryTree
set_option maxHeartbeats 400000
noncomputable section
universe u

/-- `q` counts both oracle types together. A terminal may stop early; adaptive
instrument outcomes may select different types and different stopping times. -/
inductive Tree (H O : Type u) [Fintype H] [Fintype O] [DecidableEq H] [DecidableEq O] :
    ℕ → (B : Type u) → [Fintype B] → [DecidableEq B] → Type (u + 1) where
  | stop {q : ℕ} {B : Type u} [Fintype B] [DecidableEq B]
      (after : Channel B O) : Tree H O q B
  | query {q : ℕ} (second : Bool) (after : Tree H O q H) : Tree H O (q + 1) H
  | node {q : ℕ} {B C L : Type u} [Fintype B] [Fintype C] [Fintype L]
      [DecidableEq B] [DecidableEq C] [DecidableEq L]
      (I : Instrument B C L) (next : L → Tree H O q C) : Tree H O q B

variable {H O B : Type u} [Fintype H] [Fintype O] [Fintype B]
variable [DecidableEq H] [DecidableEq O] [DecidableEq B]

def Tree.channel {q : ℕ} (tree : Tree H O q B) (first second : Channel H H) : Channel B O := by
  induction tree with
  | stop after => exact after
  | query b after ih => exact ih.comp (if b then second else first)
  | node I next ih => exact adaptiveChannel I ih

theorem Tree.stop_map {q : ℕ} (after : Channel B O) (first second : Channel H H) :
    ((Tree.stop after : Tree H O q B).channel first second).map = after.map := rfl

theorem Tree.query_map {q : ℕ} (b : Bool) (after : Tree H O q H) (first second : Channel H H) :
    ((Tree.query b after).channel first second).map =
      (after.channel first second).map.comp (if b then second else first).map := rfl

end
end ICO.BudgetQueryTree

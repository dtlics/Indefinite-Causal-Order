import ICO.RecordingPurifiedProtocol

namespace ICO.C6FlagCount
open ICO.RecordingPurifiedProtocol

/-- True is a fresh birth; false is a retrieval. -/
def flagCount : (n:ℕ)→History Bool n→ℕ
  | 0,_=>0
  | n+1,κ=>flagCount n κ.2 + if κ.1 then 1 else 0

@[simp] theorem flagCount_zero (κ:History Bool 0) : flagCount 0 κ=0 := rfl

@[simp] theorem flagCount_false (n:ℕ) (κ:History Bool n) :
    flagCount (n+1) (false,κ)=flagCount n κ := by simp [flagCount]

@[simp] theorem flagCount_true (n:ℕ) (κ:History Bool n) :
    flagCount (n+1) (true,κ)=flagCount n κ+1 := by simp [flagCount]

theorem flagCount_le (n:ℕ) (κ:History Bool n) : flagCount n κ≤n := by
  induction n with
  | zero=>exact le_rfl
  | succ n ih=>
    have h:=ih κ.2
    change flagCount n κ.2 + (if κ.1 then 1 else 0)≤n+1
    cases κ.1 <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

theorem flagCount_lt {n Q:ℕ} (h:n<Q) (κ:History Bool n) : flagCount n κ<Q :=
  lt_of_le_of_lt (flagCount_le n κ) h

#print axioms flagCount_le
end ICO.C6FlagCount

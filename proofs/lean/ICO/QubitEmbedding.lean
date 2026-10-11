import ICO.PositiveSupport

namespace ICO.QubitEmbedding
open Matrix
open scoped BigOperators ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section

def index {d : Nat} (hd : 2 ≤ d) (a : Fin 2) : Fin d := ⟨a.val, by omega⟩

theorem index_injective {d : Nat} (hd : 2 ≤ d) : Function.Injective (index hd) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin d => x.val) h

def encode {d : Nat} (hd : 2 ≤ d) : Matrix (Fin d) (Fin 2) ℂ :=
  fun i a => if i = index hd a then 1 else 0

theorem encode_isometry {d : Nat} (hd : 2 ≤ d) : (encode hd)ᴴ * encode hd = 1 := by
  ext a b
  simp [encode, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    apply_ite, ite_mul, mul_ite, (index_injective hd).eq_iff, eq_comm]

def complement {d : Nat} (r : Fin d) : Matrix (Fin 2) (Fin d) ℂ :=
  fun a i => if 2 ≤ r.val ∧ a=0 ∧ i=r then 1 else 0

def decode {d : Nat} (hd : 2 ≤ d) : Option (Fin d) → Matrix (Fin 2) (Fin d) ℂ
  | none => (encode hd)ᴴ
  | some r => complement r

theorem complement_encode {d : Nat} (hd : 2 ≤ d) (r : Fin d) :
    complement r * encode hd = 0 := by
  ext a b
  by_cases hr : 2 ≤ r.val
  · have hn : r ≠ index hd b := by intro h; have hh := congrArg Fin.val h; dsimp [index] at hh; omega
    simp [complement, encode, Matrix.mul_apply, hr, hn, Ne.symm hn, ite_mul, mul_ite]
  · simp [complement, Matrix.mul_apply, hr]

theorem decode_encode {d : Nat} (hd : 2 ≤ d) (r : Option (Fin d)) :
    decode hd r * encode hd = if r=none then 1 else 0 := by
  cases r with
  | none => simpa [decode] using encode_isometry hd
  | some r => simpa [decode] using complement_encode hd r

theorem complement_sum {d : Nat} :
    (∑ r : Fin d, (complement r)ᴴ * complement r) =
      fun i j => if i=j ∧ 2 ≤ i.val then (1 : ℂ) else 0 := by
  ext i j
  simp [complement, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, apply_ite, ite_mul, mul_ite, ite_and]
  rw [Finset.sum_eq_single j]
  · by_cases h : i=j
    · subst j
      by_cases hi : 2 ≤ i.val <;> simp [hi]
    · simp [h,Ne.symm h]
  · intro r hr hrj
    simp [Ne.symm hrj]
  · simp

theorem encode_projection {d : Nat} (hd : 2 ≤ d) :
    encode hd * (encode hd)ᴴ = fun i j => if i=j ∧ i.val<2 then (1 : ℂ) else 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, encode, Fin.sum_univ_two,
    apply_ite, star_one, star_zero, mul_ite, mul_zero, mul_one]
  have hzero (i : Fin d) : i = index hd 0 ↔ i.val=0 := by
    simp [index,Fin.ext_iff]
  have hone (i : Fin d) : i = index hd 1 ↔ i.val=1 := by
    simp [index,Fin.ext_iff]
  simp only [hzero,hone,Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem decode_complete {d : Nat} (hd : 2 ≤ d) :
    (∑ r : Option (Fin d), (decode hd r)ᴴ * decode hd r) = 1 := by
  rw [Fintype.sum_option]
  simp only [decode,Matrix.conjTranspose_conjTranspose]
  rw [complement_sum,encode_projection]
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply]
  split_ifs <;> simp_all <;> omega

def extend {d : Nat} (hd : 2 ≤ d) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (r : Option (Fin d)) : Matrix (Fin d) (Fin d) ℂ := encode hd * U * decode hd r

theorem extend_on_code {d : Nat} (hd : 2 ≤ d) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (r : Option (Fin d)) :
    extend hd U r * encode hd = if r=none then encode hd * U else 0 := by
  unfold extend
  rw [Matrix.mul_assoc, decode_encode]
  split_ifs <;> simp

theorem extended_complete {d : Nat} (hd : 2 ≤ d) {I : Type*} [Fintype I]
    (U : I → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∑ i, (U i)ᴴ * U i = 1) :
    (∑ i, ∑ r : Option (Fin d), (extend hd (U i) r)ᴴ * extend hd (U i) r) = 1 := by
  rw [Finset.sum_comm]
  have hh (r : Option (Fin d)) :
      (∑ i, (extend hd (U i) r)ᴴ * extend hd (U i) r) = (decode hd r)ᴴ * decode hd r := by
    calc
      _ = (decode hd r)ᴴ * (∑ i, (U i)ᴴ * ((encode hd)ᴴ * encode hd) * U i) * decode hd r := by
        simp only [extend, Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = _ := by rw [encode_isometry]; simp only [Matrix.mul_one]; rw [hU]; simp
  simp_rw [hh]
  exact decode_complete hd

/-- Both controlled orders preserve their common decoder environment labels.
Only the same distinguished branch survives on encoded qubit inputs. -/
theorem composed_on_code {d : Nat} (hd : 2 ≤ d)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (r s : Option (Fin d)) :
    extend hd V s * extend hd U r * encode hd =
      if r=none ∧ s=none then encode hd * (V*U) else 0 := by
  rw [Matrix.mul_assoc,extend_on_code]
  by_cases hr : r=none
  · simp only [hr,if_true,true_and]
    rw [← Matrix.mul_assoc,extend_on_code]
    split_ifs <;> simp [Matrix.mul_assoc]
  · simp [hr]

#print axioms extended_complete
#print axioms composed_on_code
end
end ICO.QubitEmbedding

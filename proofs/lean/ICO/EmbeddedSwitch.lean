import ICO.QubitEmbedding
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace ICO.EmbeddedSwitch
open Matrix ICO.QubitEmbedding
open scoped BigOperators
set_option maxHeartbeats 700000
noncomputable section

def orderedPair {d : Nat} (U V : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × Fin d) (Fin d) ℂ :=
  fun o p => if o.1=0 then (V*U) o.2 p else (U*V) o.2 p

def outputEncode {d : Nat} (hd : 2≤d) : Matrix (Fin 2 × Fin d) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (encode hd)

def outputDecode {d : Nat} (hd : 2≤d) (r : Option (Fin d)) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin d) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (decode hd r)

theorem orderedPair_mul {d n : Nat} (U V : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin n) ℂ) (c : Fin 2) (o : Fin d) (p : Fin n) :
    (orderedPair U V*X) (c,o) p = if c=0 then (V*U*X) o p else (U*V*X) o p := by
  by_cases hc : c=0 <;> simp [orderedPair,Matrix.mul_apply,hc]

theorem encode_orderedPair {d : Nat} (hd : 2≤d)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (c : Fin 2) (o : Fin d) (p : Fin 2) :
    (outputEncode hd*orderedPair U V) (c,o) p =
      if c=0 then (encode hd*(V*U)) o p else (encode hd*(U*V)) o p := by
  fin_cases c <;>
    simp [outputEncode,orderedPair,Matrix.mul_apply,Matrix.kronecker,
      Matrix.kroneckerMap_apply,Matrix.one_apply,Fintype.sum_prod_type]

/-- Both causal orders preserve the same surviving decoder labels. -/
theorem orderedPair_on_code {d : Nat} (hd : 2≤d)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (r s : Option (Fin d)) :
    orderedPair (extend hd U r) (extend hd V s)*encode hd =
      if r=none ∧ s=none then outputEncode hd*orderedPair U V else 0 := by
  ext ⟨c,o⟩ p
  rw [orderedPair_mul,composed_on_code,composed_on_code]
  by_cases hr : r=none <;> by_cases hs : s=none <;>
    simp [hr,hs,encode_orderedPair]

theorem output_decode_encode {d : Nat} (hd : 2≤d) (r : Option (Fin d)) :
    outputDecode hd r*outputEncode hd = if r=none then 1 else 0 := by
  unfold outputDecode outputEncode
  have hh : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (decode hd r) *
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (encode hd) =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (decode hd r*encode hd) := by
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 (decode hd r) (encode hd)).symm
  rw [hh,decode_encode]
  by_cases hr : r=none <;> simp [hr]

theorem decoded_orderedPair {d : Nat} (hd : 2≤d)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (r s t : Option (Fin d)) :
    outputDecode hd t*orderedPair (extend hd U r) (extend hd V s)*encode hd =
      if r=none ∧ s=none ∧ t=none then orderedPair U V else 0 := by
  rw [Matrix.mul_assoc,orderedPair_on_code]
  by_cases hr : r=none <;> by_cases hs : s=none <;> by_cases ht : t=none <;>
    simp [hr,hs,ht,← Matrix.mul_assoc,output_decode_encode]

/-- Fixed-plus-control switch Kraus matrix, including its physical amplitude. -/
def switchKraus {d : Nat} (U V : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × Fin d) (Fin d) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • orderedPair U V

theorem decoded_switchKraus {d : Nat} (hd : 2≤d)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (r s t : Option (Fin d)) :
    outputDecode hd t*switchKraus (extend hd U r) (extend hd V s)*encode hd =
      if r=none ∧ s=none ∧ t=none then switchKraus U V else 0 := by
  simp only [switchKraus,Matrix.mul_smul,Matrix.smul_mul,decoded_orderedPair]
  split_ifs <;> simp

/-- After encoding and decoding, the higher-dimensional switch extension has
exactly the original qubit-channel output, including off-diagonal control. -/
theorem decoded_switch_output {d : Nat} (hd : 2≤d)
    (U V X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ r : Option (Fin d), ∑ s : Option (Fin d), ∑ t : Option (Fin d),
      (outputDecode hd t*switchKraus (extend hd U r) (extend hd V s)*encode hd) * X *
        (outputDecode hd t*switchKraus (extend hd U r) (extend hd V s)*encode hd)ᴴ) =
      switchKraus U V*X*(switchKraus U V)ᴴ := by
  simp only [decoded_switchKraus]
  simp [Fintype.sum_option]

#print axioms decoded_switch_output
end
end ICO.EmbeddedSwitch

import ICO.QubitCircuitMatrix
import ICO.QubitLink

namespace ICO.QubitCircuitLink
open ICO.QubitCircuitMatrix ICO.CausalTensorRows ICO.OrderedCombSemantics ICO.PositiveSupport
open Matrix
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
noncomputable section

theorem link_encode (U V : Matrix (Fin 2) (Fin 2) ℂ) (p : Fin 2) (f : Fin 4)
    (x : SixWires (Fin 2) (Fin 2) (Fin 4)) :
    QubitLink.linkMatrix U V (finProdFinEquiv (p,f)) (encode6 x) =
      if p = x.1.1.1.1.1 ∧ f = x.2 then U x.1.1.1.2 x.1.1.1.1.2 * V x.1.2 x.1.1.2 else 0 := by
  rcases x with ⟨⟨⟨⟨⟨p',ai⟩,ao⟩,bi⟩,bo⟩,f'⟩
  have hai : QubitLink.bit (encode6 (((((p',ai),ao),bi),bo),f')).val 32 = ai := by
    apply Fin.ext; dsimp [QubitLink.bit, encode6]; omega
  have hao : QubitLink.bit (encode6 (((((p',ai),ao),bi),bo),f')).val 16 = ao := by
    apply Fin.ext; dsimp [QubitLink.bit, encode6]; omega
  have hbi : QubitLink.bit (encode6 (((((p',ai),ao),bi),bo),f')).val 8 = bi := by
    apply Fin.ext; dsimp [QubitLink.bit, encode6]; omega
  have hbo : QubitLink.bit (encode6 (((((p',ai),ao),bi),bo),f')).val 4 = bo := by
    apply Fin.ext; dsimp [QubitLink.bit, encode6]; omega
  have hout : QubitLink.outputIndex (encode6 (((((p',ai),ao),bi),bo),f')) =
      finProdFinEquiv (p',f') := by
    apply Fin.ext
    dsimp [QubitLink.outputIndex, ICO.UnitaryTestCertificates.outIndex, encode6, finProdFinEquiv]
    omega
  simp only [QubitLink.linkMatrix, hai, hao, hbi, hbo, hout, Equiv.apply_eq_iff_eq,
    Prod.mk.injEq]

theorem link_sum (U V : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 128 → ℂ) (p : Fin 2) (f : Fin 4) :
    (QubitLink.linkMatrix U V *ᵥ v) (finProdFinEquiv (p,f)) =
      ∑ ai : Fin 2, ∑ ao : Fin 2, ∑ bi : Fin 2, ∑ bo : Fin 2,
        U ao ai * V bo bi * v (encode6 (((((p,ai),ao),bi),bo),f)) := by
  rw [Matrix.mulVec, dotProduct, ← wireEquiv.sum_comp]
  simp only [wireEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, link_encode]
  simp [ite_and, ite_mul, eq_comm]

variable {M N K : Type*} [Fintype M] [Fintype N] [Fintype K]
  [DecidableEq M] [DecidableEq N] [DecidableEq K]

def postKraus (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) (k : K) : Matrix (Fin 4) (Fin 2 × N) ℂ :=
  fun f bn => post (f,k) bn

def circuitKraus (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (k : K) : Matrix (Fin 4) (Fin 2) ℂ :=
  postKraus post k * Matrix.kronecker V (1 : Matrix N N ℂ) * mid *
    Matrix.kronecker U (1 : Matrix M M ℂ) * pre

theorem mul_kronecker_identity_entry {R : Type*}
    (X : Matrix R (Fin 2 × M) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (r : R) (a : Fin 2) (m : M) :
    (X * Matrix.kronecker U (1 : Matrix M M ℂ)) r (a,m) =
      ∑ b : Fin 2, X r (b,m) * U b a := by
  simp [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type]

theorem circuitKraus_entry (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (k : K) (f : Fin 4) (p : Fin 2) :
    circuitKraus pre mid post U V k f p =
      ∑ ai : Fin 2, ∑ m : M, ∑ ao : Fin 2, ∑ bi : Fin 2, ∑ n : N, ∑ bo : Fin 2,
        post (f,k) (bo,n) * V bo bi * mid (bi,n) (ao,m) * U ao ai * pre (ai,m) p := by
  have hm (ao : Fin 2) (m : M) :
      ((postKraus post k * Matrix.kronecker V (1 : Matrix N N ℂ)) * mid) f (ao,m) =
        ∑ bi : Fin 2, ∑ n : N, ∑ bo : Fin 2,
          post (f,k) (bo,n) * V bo bi * mid (bi,n) (ao,m) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp_rw [mul_kronecker_identity_entry]
    simp only [postKraus, Finset.sum_mul]
  unfold circuitKraus
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [mul_kronecker_identity_entry, hm]
  simp only [Finset.sum_mul]

theorem circuitVectors_entry (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) (k : K)
    (p ai ao bi bo : Fin 2) (f : Fin 4) :
    circuitVectors pre mid post k (encode6 (((((p,ai),ao),bi),bo),f)) =
      ∑ n : N, ∑ m : M, post (f,k) (bo,n) * mid (bi,n) (ao,m) * pre (ai,m) p := by
  simp [circuitVectors, decode_encode, postLift, preMiddle, insertWire,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem linked_circuitVector (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (k : K) (p : Fin 2) (f : Fin 4) :
    (QubitLink.linkMatrix U V *ᵥ circuitVectors pre mid post k) (finProdFinEquiv (p,f)) =
      circuitKraus pre mid post U V k f p := by
  rw [link_sum, circuitKraus_entry]
  simp only [circuitVectors_entry, Finset.mul_sum]
  let perm : (Fin 2 × Fin 2 × Fin 2 × Fin 2 × N × M) ≃
      (Fin 2 × M × Fin 2 × Fin 2 × N × Fin 2) :=
    { toFun := fun x => (x.1,x.2.2.2.2.2,x.2.1,x.2.2.1,x.2.2.2.2.1,x.2.2.2.1)
      invFun := fun x => (x.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.2,x.2.2.2.2.1,x.2.1)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hs := perm.sum_comp (fun x => post (f,k) (x.2.2.2.2.2,x.2.2.2.2.1) *
    V x.2.2.2.2.2 x.2.2.2.1 * mid (x.2.2.2.1,x.2.2.2.2.1) (x.2.2.1,x.2.1) *
    U x.2.2.1 x.1 * pre (x.1,x.2.1) p)
  simp only [Fintype.sum_prod_type, perm, Equiv.coe_fn_mk] at hs
  rw [← hs]
  repeat' apply Finset.sum_congr rfl <;> intro _ _
  ring

def vectorize (T : Matrix (Fin 4) (Fin 2) ℂ) : Fin 8 → ℂ :=
  fun o => T ((finProdFinEquiv (m := 2) (n := 4)).symm o).2
    ((finProdFinEquiv (m := 2) (n := 4)).symm o).1

theorem linked_circuitVector_eq (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (k : K) :
    QubitLink.linkMatrix U V *ᵥ circuitVectors pre mid post k =
      vectorize (circuitKraus pre mid post U V k) := by
  funext o
  obtain ⟨⟨p,f⟩,rfl⟩ := (finProdFinEquiv (m := 2) (n := 4)).surjective o
  simpa only [vectorize, Equiv.symm_apply_apply] using linked_circuitVector pre mid post U V k p f

/-- The linked process matrix is precisely the output Choi matrix of the
ordinary circuit, with its final environment discarded. -/
theorem linked_circuitMatrix (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    QubitLink.linkMatrix U V * circuitMatrix pre mid post * (QubitLink.linkMatrix U V)ᴴ =
      ∑ k, rankOne (vectorize (circuitKraus pre mid post U V k)) := by
  rw [matrix_decomposition, sum_rankOne_sandwich]
  simp_rw [linked_circuitVector_eq]

def swapWireEquiv : SixWires (Fin 2) (Fin 2) (Fin 4) ≃ SixWires (Fin 2) (Fin 2) (Fin 4) where
  toFun := swapWires
  invFun := swapWires
  left_inv := swapWires_twice
  right_inv := swapWires_twice

def swapEquiv : Fin 128 ≃ Fin 128 :=
  wireEquiv.symm.trans (swapWireEquiv.trans wireEquiv)

theorem link_swap (U V : Matrix (Fin 2) (Fin 2) ℂ) (o : Fin 8) (i : Fin 128) :
    QubitLink.linkMatrix U V o i = QubitLink.linkMatrix V U o (swapEquiv i) := by
  obtain ⟨⟨p,f⟩,rfl⟩ := (finProdFinEquiv (m := 2) (n := 4)).surjective o
  obtain ⟨x,rfl⟩ := wireEquiv.surjective i
  change QubitLink.linkMatrix U V (finProdFinEquiv (p,f)) (encode6 x) =
    QubitLink.linkMatrix V U (finProdFinEquiv (p,f)) (encode6 (swapWires (decode6 (encode6 x).val)))
  rw [decode_encode, link_encode, link_encode]
  simp only [swapWires]
  split_ifs <;> ring

theorem reverseVectors_swap (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ) (k : K) (i : Fin 128) :
    reverseVectors pre mid post k i = circuitVectors pre mid post k (swapEquiv i) := by
  simp [reverseVectors, circuitVectors, swapEquiv, swapWireEquiv, wireEquiv, decode_encode]

theorem linked_reverseVector_eq (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (k : K) :
    QubitLink.linkMatrix U V *ᵥ reverseVectors pre mid post k =
      vectorize (circuitKraus pre mid post V U k) := by
  rw [← linked_circuitVector_eq]
  funext o
  simp only [Matrix.mulVec, dotProduct, link_swap U V, reverseVectors_swap]
  exact swapEquiv.sum_comp (fun i : Fin 128 =>
    QubitLink.linkMatrix V U o i * circuitVectors pre mid post k i)

theorem linked_reverseMatrix (pre : Matrix (Fin 2 × M) (Fin 2) ℂ)
    (mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ)
    (post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    QubitLink.linkMatrix U V * reverseMatrix pre mid post * (QubitLink.linkMatrix U V)ᴴ =
      ∑ k, rankOne (vectorize (circuitKraus pre mid post V U k)) := by
  rw [reverse_decomposition, sum_rankOne_sandwich]
  simp_rw [linked_reverseVector_eq]

#print axioms linked_circuitVector
#print axioms linked_circuitMatrix
#print axioms linked_reverseMatrix
end
end ICO.QubitCircuitLink

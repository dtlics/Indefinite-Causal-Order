import ICO.MHInsertionIsometry

/-! Query-vector compression of the actual unrestricted-multiset fresh
insertion. This is the finite-sector estimate behind C6's forward deletion.
Repeated pairs and arbitrary spectator records are permitted. -/
namespace ICO.C6ProjectedInsertion
open Matrix QIT ICO.MHOccupationCounts ICO.MHOccupationSupport ICO.MHBadInsertion
open ICO.MHFreshInsertion ICO.MHERecordingApprox ICO.MHSparseNorm
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem increment_symbol_injective {n : ℕ} (p : TensorPowerProfile (A×A) n) :
    Function.Injective (fun z : A×A => incrementProfile z p) := by
  intro z w h
  by_contra hn
  have he := congrArg (fun q : TensorPowerProfile (A×A) (n+1) => q.val z) h
  simp [incrementProfile_apply,hn,Ne.symm hn] at he

def support {n : ℕ} (i : Input (α:=A) n) : Finset (TensorPowerProfile (A×A) (n+1)) :=
  Finset.univ.image (fun y => incrementProfile (i.1,y) i.2)

def compressedAdjoint {n r : ℕ} (q : TensorPowerProfile (A×A) r) (ψ : A→ℂ) :
    Matrix (Input (α:=A) n) (TensorPowerProfile (A×A) (n+1)) ℂ := fun i o =>
  ∑ y : A, if o=incrementProfile (i.1,y) i.2 ∧ y∉usedOutputs i.2 q then
    ψ y / (Real.sqrt ((Fintype.card A:ℝ)-(usedOutputs i.2 q).card):ℂ) else 0

theorem increment_y_injective {n : ℕ} (i : Input (α:=A) n) :
    Function.Injective (fun y => incrementProfile (i.1,y) i.2) := by
  intro y z h
  exact congrArg Prod.snd (increment_symbol_injective i.2 h)

theorem compressedAdjoint_entry {n r : ℕ} (q : TensorPowerProfile (A×A) r)
    (ψ : A→ℂ) (i : Input (α:=A) n) (y : A) :
    compressedAdjoint q ψ i (incrementProfile (i.1,y) i.2) =
      if y∉usedOutputs i.2 q then
        ψ y / (Real.sqrt ((Fintype.card A:ℝ)-(usedOutputs i.2 q).card):ℂ) else 0 := by
  unfold compressedAdjoint
  simp only [(increment_y_injective i).eq_iff, ite_and]
  simp

theorem compressedAdjoint_support {n r : ℕ} (q : TensorPowerProfile (A×A) r)
    (ψ : A→ℂ) (i : Input (α:=A) n) (o : TensorPowerProfile (A×A) (n+1))
    (ho : o∉support i) : compressedAdjoint q ψ i o=0 := by
  apply Finset.sum_eq_zero
  intro y hy
  rw [if_neg]
  intro h
  exact ho (Finset.mem_image.mpr ⟨y,Finset.mem_univ _,h.1.symm⟩)

theorem compressedAdjoint_row {n r : ℕ} (q : TensorPowerProfile (A×A) r)
    (ψ : A→ℂ) (hψ : ∑ y, ‖ψ y‖^2≤1) (hsize : n+r<Fintype.card A)
    (i : Input (α:=A) n) :
    (∑ o∈support i, ‖compressedAdjoint q ψ i o‖^2)≤
      1/((Fintype.card A:ℝ)-n-r) := by
  have hcard := usedOutputs_card_le i.2 q
  have hd : (0:ℝ)<Fintype.card A-n-r := by
    have hh : (n:ℝ)+r<Fintype.card A := by exact_mod_cast hsize
    linarith
  have hden : Fintype.card A-(n:ℝ)-r≤(Fintype.card A:ℝ)-(usedOutputs i.2 q).card := by
    have hc : ((usedOutputs i.2 q).card:ℝ)≤(n:ℝ)+r := by exact_mod_cast hcard
    linarith
  have hden0 := hd.trans_le hden
  rw [support, Finset.sum_image]
  · simp only [compressedAdjoint_entry]
    have hnorm (y:A) : ‖ψ y / (Real.sqrt ((Fintype.card A:ℝ)-(usedOutputs i.2 q).card):ℂ)‖^2 =
        ‖ψ y‖^2/((Fintype.card A:ℝ)-(usedOutputs i.2 q).card) := by
      rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hden0.le]
    calc
      _ ≤ ∑ y:A, ‖ψ y‖^2/((Fintype.card A:ℝ)-(usedOutputs i.2 q).card) := by
        apply Finset.sum_le_sum
        intro y hy
        split_ifs <;> simp only [hnorm,norm_zero,zero_pow (by decide:2≠0)]
        all_goals first | exact le_rfl | positivity
      _ = (∑ y:A, ‖ψ y‖^2)/((Fintype.card A:ℝ)-(usedOutputs i.2 q).card) :=
        (Finset.sum_div ..).symm
      _ ≤ 1/((Fintype.card A:ℝ)-(usedOutputs i.2 q).card) :=
        div_le_div_of_nonneg_right hψ hden0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hd hden
  · intro y _ z _ h
    exact increment_y_injective i h

theorem predecessor_count {n : ℕ} (o : TensorPowerProfile (A×A) (n+1)) :
    (∑ x:A, ∑ y:A, ∑ p:TensorPowerProfile (A×A) n,
      if o=incrementProfile (x,y) p then (1:ℕ) else 0)≤n+1 := by
  calc
    _ ≤ ∑ x:A, ∑ y:A, o.val (x,y) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      apply le_trans _ (predecessor_weight_sum_le (x,y) o)
      apply Finset.sum_le_sum
      intro p hp
      split_ifs <;> omega
    _ = n+1 := by
      rw [←Fintype.sum_prod_type]
      exact tensorPowerTypeProfile_sum_of_mem_profiles (n+1) o.property

theorem support_column {n : ℕ} (o : TensorPowerProfile (A×A) (n+1)) :
    (∑ i:Input (α:=A) n, if o∈support i then (1:ℝ) else 0)≤n+1 := by
  have hi (i:Input (α:=A) n) : (if o∈support i then (1:ℕ) else 0)≤
      ∑ y:A, if o=incrementProfile (i.1,y) i.2 then 1 else 0 := by
    split_ifs with h
    · obtain ⟨y,_,hy⟩ := Finset.mem_image.mp h
      have hh := Finset.single_le_sum (f:=fun z:A => if o=incrementProfile (i.1,z) i.2 then (1:ℕ) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
      simpa [hy] using hh
    · exact Nat.zero_le _
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hi i)
  simp only [Fintype.sum_prod_type] at hh
  have he : (∑ x:A, ∑ p:TensorPowerProfile (A×A) n, ∑ y:A,
      if o=incrementProfile (x,y) p then (1:ℕ) else 0)=
      ∑ x:A, ∑ y:A, ∑ p:TensorPowerProfile (A×A) n,
      if o=incrementProfile (x,y) p then (1:ℕ) else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    exact Finset.sum_comm
  rw [he] at hh
  have hb := hh.trans (predecessor_count o)
  simp only [Fintype.sum_prod_type]
  exact_mod_cast hb

theorem compressedAdjoint_norm {n r : ℕ} (q : TensorPowerProfile (A×A) r)
    (ψ : A→ℂ) (hψ : ∑ y, ‖ψ y‖^2≤1) (hsize : n+r<Fintype.card A) :
    ‖compressedAdjoint (n:=n) q ψ‖≤
      Real.sqrt ((n+1:ℝ)/((Fintype.card A:ℝ)-n-r)) := by
  have hd : (0:ℝ)<Fintype.card A-n-r := by
    have hh : (n:ℝ)+r<Fintype.card A := by exact_mod_cast hsize
    linarith
  have h := matrix_norm_le_sqrt (compressedAdjoint (n:=n) q ψ) support
    (1/((Fintype.card A:ℝ)-n-r)) (n+1) (by positivity) (by positivity)
    (compressedAdjoint_support q ψ) (compressedAdjoint_row q ψ hψ hsize) support_column
  have he : (1/((Fintype.card A:ℝ)-n-r))*(n+1) =
      (n+1)/((Fintype.card A:ℝ)-n-r) := by ring
  rw [he] at h
  exact h

def queryEmbedding {n : ℕ} (ψ : A→ℂ) :
    Matrix (Input (α:=A) n) (TensorPowerProfile (A×A) n) ℂ :=
  fun i p => if i.2=p then ψ i.1 else 0

theorem actual_compressed_adjoint {n r : ℕ} (q : TensorPowerProfile (A×A) r)
    (ψ : A→ℂ) :
    (fullInsertion (n:=n) q).conjTranspose * queryEmbedding ψ = compressedAdjoint q ψ := by
  ext i o
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    queryEmbedding, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold compressedAdjoint
  apply Finset.sum_congr rfl
  intro y hy
  have he : (i∈freshSupport q (y,o)) ↔ o=incrementProfile (i.1,y) i.2 ∧ y∉usedOutputs i.2 q := by
    simp [freshSupport]
  by_cases h : i∈freshSupport q (y,o)
  · have hh := he.mp h
    simp only [fullInsertion, if_pos h, if_pos hh]
    have hs : star ((Real.sqrt ((Fintype.card A:ℝ)-(usedOutputs i.2 q).card):ℂ)⁻¹)=
        (Real.sqrt ((Fintype.card A:ℝ)-(usedOutputs i.2 q).card):ℂ)⁻¹ := by simp
    rw [hs]
    ring
  · have hh := not_congr he |>.mp h
    simp only [fullInsertion, if_neg h, if_neg hh, star_zero, zero_mul]

theorem actual_compressed_norm {n r : ℕ} (q : TensorPowerProfile (A×A) r)
    (ψ : A→ℂ) (hψ : ∑ y, ‖ψ y‖^2≤1) (hsize : n+r<Fintype.card A) :
    ‖(fullInsertion (n:=n) q).conjTranspose * queryEmbedding ψ‖≤
      Real.sqrt ((n+1:ℝ)/((Fintype.card A:ℝ)-n-r)) := by
  rw [actual_compressed_adjoint]
  exact compressedAdjoint_norm q ψ hψ hsize

#print axioms compressedAdjoint_norm
#print axioms actual_compressed_norm
end
end ICO.C6ProjectedInsertion

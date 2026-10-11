import ICO.MHSymmetric
import ICO.MemoryEmbedding
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Common-unitary invariance of labels, with an unrestricted reference register.
The occupation selection rule below is derived from actual unitary invariance,
rather than postulated as a classicality condition. -/

namespace ICO.C6LabelSymmetry
open QIT Matrix
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

variable {A Z : Type*} [Fintype A] [DecidableEq A] [Fintype Z] [DecidableEq Z]

def labelCount (j : A) : (n : ℕ) → TensorPower A n → ℕ
  | 0, _ => 0
  | n + 1, w => (if w.1 = j then 1 else 0) + labelCount j n w.2

theorem labelCount_le (j : A) (n : ℕ) (w : TensorPower A n) : labelCount j n w ≤ n := by
  induction n with
  | zero => simp [labelCount]
  | succ n ih =>
    change (if w.1 = j then 1 else 0) + labelCount j n w.2 ≤ n + 1
    have h := ih w.2
    split_ifs <;> omega

def phaseUnitary (j : A) (ζ : ℂ) (hζ : star ζ * ζ = 1) : Matrix.unitaryGroup A ℂ :=
  ⟨Matrix.diagonal (fun x => if x = j then ζ else 1), by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    have hζ' : (starRingEnd ℂ) ζ * ζ = 1 := by simpa only [Complex.star_def] using hζ
    ext x y
    by_cases h : x = j <;> simp [Matrix.diagonal_apply, h, hζ', Matrix.one_apply]⟩

theorem phase_tensor (j : A) (ζ : ℂ) (hζ : star ζ * ζ = 1) (n : ℕ) :
    (unitaryTensorPowerMatrix (phaseUnitary j ζ hζ) n : CMatrix (TensorPower A n)) =
      Matrix.diagonal (fun w => ζ ^ labelCount j n w) := by
  induction n with
  | zero =>
    ext x y
    have h : x = y := by cases x; cases y; rfl
    simp [h, labelCount]
  | succ n ih =>
    rw [unitaryTensorPowerMatrix_succ]
    change Matrix.kronecker _ _ = _
    rw [ih]
    ext x y
    rcases x with ⟨a, w⟩
    rcases y with ⟨b, v⟩
    change (if a = b then (if a = j then ζ else 1) else 0) *
      (if w = v then ζ ^ labelCount j n w else 0) =
      if (a, w) = (b, v) then ζ ^ ((if a = j then 1 else 0) + labelCount j n w) else 0
    by_cases hab : a = b <;> by_cases hwv : w = v <;>
      by_cases haj : a = j <;>
      simp [Prod.mk.injEq, hab, hwv, haj, pow_add]

def commonRotation (U : Matrix.unitaryGroup A ℂ) (n : ℕ) :
    CMatrix (TensorPower A n × Z) :=
  Matrix.kronecker (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n)) 1

def CommonInvariant (n : ℕ) (ω : CMatrix (TensorPower A n × Z)) : Prop :=
  ∀ U : Matrix.unitaryGroup A ℂ, commonRotation U n * ω = ω * commonRotation U n

theorem phase_commonRotation (j : A) (ζ : ℂ) (hζ : star ζ * ζ = 1) (n : ℕ) :
    commonRotation (Z := Z) (phaseUnitary j ζ hζ) n =
      Matrix.diagonal (fun w => ζ ^ labelCount j n w.1) := by
  unfold commonRotation
  rw [phase_tensor]
  ext x y
  by_cases h : x.1 = y.1 <;> by_cases hz : x.2 = y.2 <;>
    simp [Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Prod.ext_iff, h, hz]

theorem diagonal_commutation_entry {H : Type*} [Fintype H] [DecidableEq H]
    (f : H → ℂ) (ω : CMatrix H)
    (h : Matrix.diagonal f * ω = ω * Matrix.diagonal f) (x y : H) :
    (f x - f y) * ω x y = 0 := by
  have he := congrArg (fun M : CMatrix H => M x y) h
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  linear_combination he

theorem occupation_selection (n : ℕ) (ω : CMatrix (TensorPower A n × Z))
    (hω : CommonInvariant n ω) (j : A) (x y : TensorPower A n × Z)
    (hxy : labelCount j n x.1 ≠ labelCount j n y.1) : ω x y = 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((n + 1 : ℕ) : ℂ))
  have hroot : IsPrimitiveRoot ζ (n + 1) :=
    Complex.isPrimitiveRoot_exp _ (Nat.succ_ne_zero n)
  have hnorm : ‖ζ‖ = 1 := hroot.norm'_eq_one (Nat.succ_ne_zero n)
  have hζ : star ζ * ζ = 1 := by
    change (starRingEnd ℂ) ζ * ζ = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hc := hω (phaseUnitary j ζ hζ)
  rw [phase_commonRotation] at hc
  have he := diagonal_commutation_entry _ ω hc x y
  have hpow : ζ ^ labelCount j n x.1 ≠ ζ ^ labelCount j n y.1 := by
    intro heq
    exact hxy (hroot.pow_inj (by have := labelCount_le j n x.1; omega)
      (by have := labelCount_le j n y.1; omega) heq)
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hpow)

def tensorPerm (e : Equiv.Perm A) : (n : ℕ) → Equiv.Perm (TensorPower A n)
  | 0 => Equiv.refl _
  | n + 1 => e.prodCongr (tensorPerm e n)

def basisPermutation (e : Equiv.Perm A) : Matrix.unitaryGroup A ℂ :=
  ⟨ICO.MemoryEmbedding.embedding ⟨e, e.injective⟩,
    Matrix.mem_unitaryGroup_iff'.mpr (ICO.MemoryEmbedding.embedding_isometry _)⟩

theorem permutation_tensor (e : Equiv.Perm A) (n : ℕ) :
    (unitaryTensorPowerMatrix (basisPermutation e) n : CMatrix (TensorPower A n)) =
      ICO.MemoryEmbedding.embedding ⟨tensorPerm e n, (tensorPerm e n).injective⟩ := by
  induction n with
  | zero =>
    ext x y
    simp [tensorPerm, ICO.MemoryEmbedding.embedding, Matrix.one_apply, eq_comm]
  | succ n ih =>
    rw [unitaryTensorPowerMatrix_succ]
    change Matrix.kronecker _ _ = _
    rw [ih]
    ext x y
    rcases x with ⟨a, w⟩
    rcases y with ⟨b, v⟩
    change (if a = e b then (1 : ℂ) else 0) *
      (if w = tensorPerm e n v then 1 else 0) =
      if (a, w) = (e b, tensorPerm e n v) then 1 else 0
    by_cases h : a = e b <;> by_cases ht : w = tensorPerm e n v <;>
      simp [Prod.mk.injEq, h, ht]

theorem permutation_commonRotation (e : Equiv.Perm A) (n : ℕ) :
    commonRotation (Z := Z) (basisPermutation e) n =
      ICO.MemoryEmbedding.embedding
        ⟨(tensorPerm e n).prodCongr (Equiv.refl Z),
          ((tensorPerm e n).prodCongr (Equiv.refl Z)).injective⟩ := by
  unfold commonRotation
  rw [permutation_tensor]
  ext x y
  by_cases h : x.1 = tensorPerm e n y.1 <;> by_cases hz : x.2 = y.2 <;>
    simp [Matrix.kronecker_apply, ICO.MemoryEmbedding.embedding,
      Matrix.one_apply, Prod.ext_iff, h, hz]

theorem embedding_commutation_entry {H : Type*} [Fintype H] [DecidableEq H]
    (e : Equiv.Perm H) (ω : CMatrix H)
    (h : ICO.MemoryEmbedding.embedding ⟨e, e.injective⟩ * ω =
      ω * ICO.MemoryEmbedding.embedding ⟨e, e.injective⟩) (x y : H) :
    ω (e x) (e y) = ω x y := by
  have he := congrArg (fun M : CMatrix H => M (e x) y) h
  simp only [Matrix.mul_apply, ICO.MemoryEmbedding.embedding] at he
  simpa [ite_mul, mul_ite, e.injective.eq_iff] using he.symm

theorem permutation_invariance (n : ℕ) (ω : CMatrix (TensorPower A n × Z))
    (hω : CommonInvariant n ω) (e : Equiv.Perm A) (x y : TensorPower A n × Z) :
    ω (tensorPerm e n x.1, x.2) (tensorPerm e n y.1, y.2) = ω x y := by
  have hc := hω (basisPermutation e)
  rw [permutation_commonRotation] at hc
  exact embedding_commutation_entry _ ω hc x y

#print axioms occupation_selection
#print axioms permutation_invariance
end
end ICO.C6LabelSymmetry

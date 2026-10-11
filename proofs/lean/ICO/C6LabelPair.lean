import ICO.C6InvariantTwirl
import ICO.MHWordRotation

/-! Split any selected remaining label and the first label from the
common tensor rotation. All other labels and the reference are spectators. -/
namespace ICO.C6LabelPair
open QIT Matrix ICO.C6LabelSymmetry ICO.MHWordRotation
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
universe u
variable {A Z : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype Z] [DecidableEq Z]

abbrev Other {n : ℕ} (i : Fin n) := {j : Fin n // j ≠ i}
abbrev Spectator (A Z : Type u) {n : ℕ} (i : Fin n) := (Other i → A) × Z

def assemble {n : ℕ} (i : Fin n) (f : Other i → A) (a : A) : Fin n → A :=
  fun j => if h : j = i then a else f ⟨j, h⟩

@[simp] theorem assemble_at {n : ℕ} (i : Fin n) (f : Other i → A) (a : A) :
    assemble i f a i = a := by simp [assemble]

@[simp] theorem assemble_other {n : ℕ} (i : Fin n) (f : Other i → A) (a : A)
    (j : Other i) : assemble i f a j.val = f j := by simp [assemble, j.property]

def pairEquiv {n : ℕ} (i : Fin n) :
    (TensorPower A (n + 1) × Z) ≃ (Spectator A Z i × (A × A)) where
  toFun x := ((fun j => tensorPowerEquiv n x.1.2 j.val, x.2),
    (x.1.1, tensorPowerEquiv n x.1.2 i))
  invFun x := ((x.2.1, (tensorPowerEquiv n).symm (assemble i x.1.1 x.2.2)), x.1.2)
  left_inv x := by
    rcases x with ⟨⟨a, w⟩, z⟩
    change ((a, (tensorPowerEquiv n).symm
      (assemble i (fun j => tensorPowerEquiv n w j.val) (tensorPowerEquiv n w i))), z) = ((a, w), z)
    have he : assemble i (fun j => tensorPowerEquiv n w j.val) (tensorPowerEquiv n w i) =
        tensorPowerEquiv n w := by
      funext j
      by_cases h : j = i <;> simp [assemble, h]
    rw [he, Equiv.symm_apply_apply]
  right_inv x := by
    rcases x with ⟨⟨f, z⟩, a, b⟩
    simp only [Equiv.apply_symm_apply, assemble_at, assemble_other]

def spectatorRotation {n : ℕ} (i : Fin n) (U : Matrix.unitaryGroup A ℂ) :
    Matrix.unitaryGroup (Spectator A Z i) ℂ :=
  tensorUnitary (piUnitary (fun _ : Other i => U)) 1

theorem common_pair_factor {n : ℕ} (i : Fin n) (U : Matrix.unitaryGroup A ℂ) :
    commonRotation (Z := Z) U (n + 1) =
      (Matrix.kronecker (spectatorRotation (Z := Z) i U : CMatrix (Spectator A Z i))
        (ICO.EqualityTwirl.sameTensor U)).submatrix (pairEquiv i) (pairEquiv i) := by
  ext x y
  rcases x with ⟨⟨a, w⟩, z⟩
  rcases y with ⟨⟨b, v⟩, t⟩
  change ((U : CMatrix A) a b *
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower A n)) w v) *
      (1 : CMatrix Z) z t = _
  rw [unitaryTensorPowerMatrix_apply_eq_fin_prod,
    Fintype.prod_eq_mul_prod_subtype_ne _ i]
  change ((U : CMatrix A) a b *
      ((U : CMatrix A) (tensorPowerEquiv n w i) (tensorPowerEquiv n v i) *
        ∏ j : Other i, (U : CMatrix A) (tensorPowerEquiv n w j.val) (tensorPowerEquiv n v j.val))) *
      (1 : CMatrix Z) z t =
    ((∏ j : Other i, (U : CMatrix A) (tensorPowerEquiv n w j.val) (tensorPowerEquiv n v j.val)) *
      (1 : CMatrix Z) z t) *
      ((U : CMatrix A) a b * (U : CMatrix A) (tensorPowerEquiv n w i) (tensorPowerEquiv n v i))
  ring

def pairEquality {n : ℕ} (i : Fin n) : CMatrix (TensorPower A (n + 1) × Z) :=
  (ICO.MHSpectatorTwirl.lift (Γ := Spectator A Z i)
    (ICO.EqualityTwirl.equalityProjector (A := A))).submatrix (pairEquiv i) (pairEquiv i)

theorem trace_reindex {X Y : Type u} [Fintype X] [Fintype Y]
    (e : Y ≃ X) (M : CMatrix X) : (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact e.sum_comp (fun x => M x x)

theorem pair_equality_bound {n : ℕ} (i : Fin n)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) (hpos : ω.PosSemidef)
    (hω : CommonInvariant (n + 1) ω) :
    (ω * pairEquality (Z := Z) i).trace.re ≤
      (2 / ((Fintype.card A : ℝ) + 1)) * ω.trace.re := by
  let e := pairEquiv (A := A) (Z := Z) i
  let σ := ω.submatrix e.symm e.symm
  have hσ : σ.PosSemidef := hpos.submatrix _
  have hi (U : Matrix.unitaryGroup A ℂ) :
      Matrix.kronecker (spectatorRotation (Z := Z) i U : CMatrix (Spectator A Z i))
          (ICO.EqualityTwirl.sameTensor U) * σ =
      σ * Matrix.kronecker (spectatorRotation (Z := Z) i U : CMatrix (Spectator A Z i))
          (ICO.EqualityTwirl.sameTensor U) := by
    have he := congrArg (fun M : CMatrix (TensorPower A (n + 1) × Z) =>
      M.submatrix e.symm e.symm) (hω U)
    dsimp only at he
    rw [common_pair_factor i U] at he
    rw [← Matrix.submatrix_mul_equiv _ ω e.symm e.symm e.symm,
      ← Matrix.submatrix_mul_equiv ω _ e.symm e.symm e.symm] at he
    simpa only [e, σ, Matrix.submatrix_submatrix, Function.comp_def, Equiv.apply_symm_apply,
      Matrix.submatrix_id_id] using he
  have hb := ICO.C6InvariantTwirl.invariant_equality_trace_le σ hσ
    (spectatorRotation (Z := Z) i) hi
  have ht : σ.trace = ω.trace := trace_reindex e.symm ω
  have hp : (σ * ICO.MHSpectatorTwirl.lift (Γ := Spectator A Z i)
      (ICO.EqualityTwirl.equalityProjector (A := A))).trace =
      (ω * pairEquality (Z := Z) i).trace := by
    rw [← trace_reindex e (σ * _), ← Matrix.submatrix_mul_equiv _ _ e e e]
    simp only [σ, e, Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_apply_apply,
      Matrix.submatrix_id_id, pairEquality]
    rfl
  rwa [hp, ht] at hb

#print axioms common_pair_factor
#print axioms pair_equality_bound
end
end ICO.C6LabelPair

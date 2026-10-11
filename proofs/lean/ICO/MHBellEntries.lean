import ICO.MHWordDistinct

/-! Exact normalized Bell-projector entries with arbitrary spectator records. -/
namespace ICO.MHBellEntries
open Matrix QIT ICO.MHBellBlocks ICO.MHBellProjectors ICO.MHWordDistinct
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
variable {A Γ : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype Γ] [DecidableEq Γ]

theorem bellProjection_apply (p q : Γ × (A × A)) :
    bellProjection (A := A) (Γ := Γ) p q =
      if p.1=q.1 ∧ p.2.1=p.2.2 ∧ q.2.1=q.2.2 then (Fintype.card A : ℂ)⁻¹ else 0 := by
  have hs : star (bellScale (A := A) : ℂ)=(bellScale (A := A) : ℂ) := by simp
  have hc : (bellScale (A := A) : ℂ)*(bellScale (A := A) : ℂ)=(Fintype.card A : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul]
    have hh : bellScale (A := A)*bellScale (A := A)=(Fintype.card A : ℝ)⁻¹ := by
      simpa only [pow_two] using bellScale_sq (A := A)
    simpa only [Complex.ofReal_inv,Complex.ofReal_natCast] using congrArg Complex.ofReal hh
  simp only [bellProjection,Matrix.mul_apply,Matrix.conjTranspose_apply,bellColumns,
    bellVector,and_true,apply_ite,star_zero,hs,ite_mul,mul_ite,zero_mul,mul_zero]
  by_cases hγ : p.1=q.1
  · by_cases hp : p.2.1=p.2.2
    · by_cases hq : q.2.1=q.2.2
      · simp [hγ,hp,hq,hc]
      · simp [hγ,hp,hq]
    · simp [hγ,hp]
  · have hne : q.1≠p.1 := Ne.symm hγ
    simp [hγ,hne]

theorem slotBell_apply {J : Type*} [Fintype J] [DecidableEq J]
    (j : J) (p q : WordBasis A J) :
    slotBell j p q = if (slotEquiv j p).1=(slotEquiv j q).1 ∧
      p.1=(p.2 j).1 ∧ q.1=(q.2 j).1 then (Fintype.card A : ℂ)⁻¹ else 0 := by
  exact bellProjection_apply (slotEquiv j p) (slotEquiv j q)

#print axioms bellProjection_apply
end
end ICO.MHBellEntries

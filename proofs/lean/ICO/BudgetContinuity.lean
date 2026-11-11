import ICO.BudgetKnownOracle
import ICO.SamplingOrdinary
import Mathlib.Topology.Instances.Matrix

/-! Continuity of the literal adaptive output, including both independently
varying hidden measurement bases. -/
namespace ICO.BudgetContinuity
open Matrix QIT ICO.InstrumentCompression ICO.BudgetQueryTree
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
variable {H O B Ω : Type} [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B] [TopologicalSpace Ω]

theorem output_continuous {q : ℕ} (tree : Tree H O q B)
    (first second : Ω → Channel H H)
    (hfirst : Continuous (fun p : Ω×CMatrix H => (first p.1).map p.2))
    (hsecond : Continuous (fun p : Ω×CMatrix H => (second p.1).map p.2))
    (X : Ω→CMatrix B) (hX : Continuous X) :
    Continuous (fun ω => (tree.channel (first ω) (second ω)).map (X ω)) := by
  induction tree with
  | stop after => exact after.map.continuous_of_finiteDimensional.comp hX
  | query b after ih =>
    apply ih
    cases b
    · exact hfirst.comp (continuous_id.prodMk hX)
    · exact hsecond.comp (continuous_id.prodMk hX)
  | node I next ih =>
    change Continuous (fun ω => adaptiveMap I (fun j => (next j).channel (first ω) (second ω)) (X ω))
    simp_rw [adaptiveMap_apply]
    apply continuous_finset_sum
    intro j hj
    apply ih
    exact (continuous_const.matrix_mul hX).matrix_mul continuous_const

theorem map_continuous_of_choi_continuous (Φ : Ω → Channel H H)
    (hΦ : Continuous (fun ω => MatrixMap.choi (Φ ω).map)) :
    Continuous (fun p : Ω × CMatrix H => (Φ p.1).map p.2) := by
  apply continuous_matrix
  intro j j'
  have he (p : Ω × CMatrix H) : (Φ p.1).map p.2 j j' =
      ∑ i : H, ∑ i' : H, p.2 i i' * MatrixMap.choi (Φ p.1).map (i, j) (i', j') := by
    rw [MatrixMap.map_eq_sum_single (Φ p.1).map p.2]
    simp [MatrixMap.choi, Matrix.sum_apply, Matrix.smul_apply]
  simp_rw [he]
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro i' _
  exact (continuous_snd.matrix_elem i i').mul
    ((hΦ.comp continuous_fst).matrix_elem (i, j) (i', j'))

theorem _root_.ICO.BudgetQueryTree.Tree.channel_choi_continuous {q : ℕ} (tree : Tree H O q B)
    (first second : Ω → Channel H H)
    (hfirst : Continuous (fun ω => MatrixMap.choi (first ω).map))
    (hsecond : Continuous (fun ω => MatrixMap.choi (second ω).map)) :
    Continuous (fun ω => MatrixMap.choi (tree.channel (first ω) (second ω)).map) := by
  apply continuous_matrix
  intro ij kl
  have h := output_continuous tree first second
    (map_continuous_of_choi_continuous first hfirst)
    (map_continuous_of_choi_continuous second hsecond)
    (fun _ => Matrix.single ij.1 kl.1 (1 : ℂ)) continuous_const
  exact h.matrix_elem ij.2 kl.2

theorem _root_.ICO.BudgetQueryTree.uniformChannel_choi_continuous {r : ℕ} [NeZero r]
    (oracles : Ω → Fin r → Channel H H)
    (horacles : ∀ i, Continuous (fun ω => MatrixMap.choi (oracles ω i).map)) :
    Continuous (fun ω => MatrixMap.choi (ICO.SamplingOrdinary.uniformChannel (oracles ω)).map) := by
  apply continuous_matrix
  intro ij kl
  have he (ω : Ω) : MatrixMap.choi (ICO.SamplingOrdinary.uniformChannel (oracles ω)).map ij kl =
      (r : ℂ)⁻¹ * ∑ i : Fin r, MatrixMap.choi (oracles ω i).map ij kl := by
    simp [MatrixMap.choi, ICO.SamplingOrdinary.uniformChannel_map,
      LinearMap.smul_apply, LinearMap.sum_apply, Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [he]
  exact continuous_const.mul (continuous_finset_sum _ (fun i _ => (horacles i).matrix_elem ij kl))

variable {A M : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M]

def hidden (U : Matrix.unitaryGroup A ℂ) : Channel (A×M) (A×M) :=
  ICO.AllChannelDilation.oracleChannel
    (ICO.SwitchObservable.basisProjection (U:CMatrix A))
    (ICO.SwitchObservable.hidden_basis_kraus_complete _ U.property.1 U.property.2)

theorem hidden_continuous :
    Continuous (fun p : Matrix.unitaryGroup A ℂ×CMatrix (A×M) => (hidden p.1).map p.2) := by
  have hp (a : A) : Continuous (fun U : Matrix.unitaryGroup A ℂ =>
      ICO.SwitchObservable.basisProjection (U:CMatrix A) a) := by
    exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  have hk (a : A) : Continuous (fun p : Matrix.unitaryGroup A ℂ×CMatrix (A×M) =>
      Matrix.kronecker (ICO.SwitchObservable.basisProjection (p.1:CMatrix A) a) (1:CMatrix M)) := by
    apply continuous_matrix
    intro o i
    exact (((hp a).comp continuous_fst).matrix_elem o.1 i.1).mul continuous_const
  change Continuous (fun p : Matrix.unitaryGroup A ℂ×CMatrix (A×M) =>
    ∑ a, Matrix.kronecker (ICO.SwitchObservable.basisProjection (p.1:CMatrix A) a) (1:CMatrix M)*
      p.2*(Matrix.kronecker (ICO.SwitchObservable.basisProjection (p.1:CMatrix A) a) (1:CMatrix M)).conjTranspose)
  exact continuous_finsetSum _ (fun a _ =>
    ((hk a).matrix_mul continuous_snd).matrix_mul (hk a).matrix_conjTranspose)

theorem hidden_parameter_continuous (U : Ω→Matrix.unitaryGroup A ℂ) (hU : Continuous U) :
    Continuous (fun p : Ω×CMatrix (A×M) => (hidden (U p.1)).map p.2) := by
  have hc := hidden_continuous (A:=A) (M:=M)
  have hg : Continuous (fun p : Ω×CMatrix (A×M) => (U p.1,p.2)) :=
    (hU.comp continuous_fst).prodMk continuous_snd
  have hcomp := hc.comp hg
  simpa only [Function.comp_def] using hcomp

theorem fixed_continuous (Φ : Channel H H) :
    Continuous (fun p : Ω×CMatrix H => Φ.map p.2) :=
  Φ.map.continuous_of_finiteDimensional.comp continuous_snd

theorem luders_output_continuous {q : ℕ} (tree : Tree (A×M) O q B) (X : CMatrix B) :
    Continuous (fun U => (ICO.BudgetHaarBound.ludersCircuit tree U).map X) :=
  output_continuous tree hidden hidden hidden_continuous hidden_continuous _ continuous_const

theorem independent_output_continuous {q : ℕ} (tree : Tree (A×M) O q B) (X : CMatrix B) :
    Continuous (fun p : Matrix.unitaryGroup A ℂ×Matrix.unitaryGroup A ℂ =>
      (tree.channel (hidden p.1) (hidden p.2)).map X) :=
  output_continuous tree _ _ (hidden_parameter_continuous _ continuous_fst)
    (hidden_parameter_continuous _ continuous_snd) _ continuous_const

#print axioms independent_output_continuous
end
end ICO.BudgetContinuity

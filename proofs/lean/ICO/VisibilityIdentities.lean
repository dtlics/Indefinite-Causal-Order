import ICO.LudersPromise
import ICO.RecordingDepolarizing

/-!
# Visibility identities and Haar-averaged dephasing (`\label{sec:visibility}`, `\label{sec:switch-test}`)

This module formalizes the general visibility and Haar-averaging identities from
Section 2.5 (`\label{sec:visibility}`) and Section 5.1 (`\label{sec:switch-test}`) of the
manuscript:

1. **Equation `eq:basis-visibility`** (`basis_dephasing_visibility`): for every pair of
   unitaries `U, U' ∈ U(d)`, the switch visibility of the projective dephasing channels
   `Δ_U` and `Δ_{U'}` equals `(1 / d) ∑_{j, k} |⟨j | U† U' | k⟩|^4`.
2. **Commutator Hilbert–Schmidt identity** (`one_sub_interference_eq_commutator_hs`,
   `one_sub_interference_eq_commutator_entry_sq`, and
   `one_sub_interference_eq_commutator_hilbertSchmidtSq`): for arbitrary finite complete
   Kraus families `(E_i)` and `(F_j)`,
   `1 - v(E, F) = (1 / (2 d)) ∑_{i, j} ‖[E_i, F_j]‖_{HS}^2`.
3. **Haar dephasing twirl `eq:validation-pair`** (`haar_average_dephasing_eq_depolarizing`
   and `haar_average_dephasing_eq_depolarizingChannel`): averaging `Δ_U` over the Haar
   measure on `U(d)` yields the depolarizing channel `Λ = (id + d Ω) / (d + 1)`.
-/

namespace ICO.VisibilityIdentities

open Matrix QIT MeasureTheory
open ICO.SwitchObservable ICO.HaarMoments ICO.HaarSecondMoment ICO.LudersPromise
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 1200000
set_option Elab.async false

local instance visibilityCMatrixContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) :=
  SeminormedAddGroup.toContinuousENorm

/-! ## 1. Equation `eq:basis-visibility`: visibility of two projective dephasing channels -/

/-- Matrix-level overlap formula for `interference (basisProjection U) (basisProjection U')`
expressed directly with fourth powers of norms `‖(Uᴴ * U') j k‖ ^ 4`. -/
theorem basis_dephasing_visibility_matrix {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (U U' : CMatrix A) :
    ICO.SwitchObservable.interference
      (ICO.SwitchObservable.basisProjection U)
      (ICO.SwitchObservable.basisProjection U') =
    (1 / (Fintype.card A : ℝ)) *
      ∑ j : A, ∑ k : A, ‖(U.conjTranspose * U') j k‖ ^ 4 := by
  rw [ICO.LudersPromise.basis_interference, div_eq_inv_mul, one_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_eq_norm_sq]
  ring

/-- **Equation `eq:basis-visibility`** (Section 2.5, `\label{sec:visibility}`):
For every pair of unitaries `U, U' : Matrix.unitaryGroup A ℂ`,
`v(Δ_U, Δ_{U'}) = (1 / d) ∑_{j, k} |⟨j | U† U' | k⟩|^4`. -/
theorem basis_dephasing_visibility {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (U U' : Matrix.unitaryGroup A ℂ) :
    ICO.SwitchObservable.interference
      (ICO.SwitchObservable.basisProjection (U : CMatrix A))
      (ICO.SwitchObservable.basisProjection (U' : CMatrix A)) =
    (1 / (Fintype.card A : ℝ)) *
      ∑ j : A, ∑ k : A, ‖((U : CMatrix A).conjTranspose * (U' : CMatrix A)) j k‖ ^ 4 :=
  basis_dephasing_visibility_matrix (U : CMatrix A) (U' : CMatrix A)

/-! ## 2. General Kraus commutator identity `1 - v(E, F) = (1 / (2 d)) ∑_{i,j} ‖[E_i, F_j]‖_{HS}^2` -/

/-- For any single pair of matrices `P, Q`, expanding `Tr((P Q - Q P)† (P Q - Q P))`
and applying trace cyclicity isolates `2 Re Tr(Q P Q† P†)`. -/
theorem commutator_conjTranspose_mul_self_trace_re {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) :
    (((P * Q - Q * P).conjTranspose * (P * Q - Q * P)).trace).re =
      (((P.conjTranspose * P) * (Q * Q.conjTranspose)).trace).re +
        (((Q.conjTranspose * Q) * (P * P.conjTranspose)).trace).re -
        2 * ((Q * P * Q.conjTranspose * P.conjTranspose).trace).re := by
  have hexp :
      (P * Q - Q * P).conjTranspose * (P * Q - Q * P) =
        Q.conjTranspose * (P.conjTranspose * P) * Q +
          P.conjTranspose * (Q.conjTranspose * Q) * P -
          Q.conjTranspose * P.conjTranspose * Q * P -
          P.conjTranspose * Q.conjTranspose * P * Q := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    noncomm_ring
  have h1 :
      (Q.conjTranspose * (P.conjTranspose * P) * Q).trace =
        ((P.conjTranspose * P) * (Q * Q.conjTranspose)).trace := by
    calc
      (Q.conjTranspose * (P.conjTranspose * P) * Q).trace =
          (Q.conjTranspose * ((P.conjTranspose * P) * Q)).trace := by
            simp only [Matrix.mul_assoc]
      _ = (((P.conjTranspose * P) * Q) * Q.conjTranspose).trace :=
            Matrix.trace_mul_comm Q.conjTranspose ((P.conjTranspose * P) * Q)
      _ = ((P.conjTranspose * P) * (Q * Q.conjTranspose)).trace := by
            simp only [Matrix.mul_assoc]
  have h2 :
      (P.conjTranspose * (Q.conjTranspose * Q) * P).trace =
        ((Q.conjTranspose * Q) * (P * P.conjTranspose)).trace := by
    calc
      (P.conjTranspose * (Q.conjTranspose * Q) * P).trace =
          (P.conjTranspose * ((Q.conjTranspose * Q) * P)).trace := by
            simp only [Matrix.mul_assoc]
      _ = (((Q.conjTranspose * Q) * P) * P.conjTranspose).trace :=
            Matrix.trace_mul_comm P.conjTranspose ((Q.conjTranspose * Q) * P)
      _ = ((Q.conjTranspose * Q) * (P * P.conjTranspose)).trace := by
            simp only [Matrix.mul_assoc]
  have h3 :
      (Q.conjTranspose * P.conjTranspose * Q * P).trace =
        (Q * P * Q.conjTranspose * P.conjTranspose).trace := by
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm (Q.conjTranspose * P.conjTranspose) (Q * P)
  have h4 :
      (P.conjTranspose * Q.conjTranspose * P * Q).trace =
        star ((Q * P * Q.conjTranspose * P.conjTranspose).trace) := by
    rw [← h3, ← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hexp]
  simp only [Matrix.trace_sub, Matrix.trace_add, h1, h2, h3, h4,
    Complex.sub_re, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- The real trace `Re Tr(M† M)` equals the sum of squared entry norms `∑_{a,b} ‖M_{a,b}‖^2`. -/
theorem trace_conjTranspose_mul_self_re_eq_sum_norm_sq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) :
    ((M.conjTranspose * M).trace).re = ∑ a : n, ∑ b : n, ‖M a b‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Section 2.5 commutator identity (trace form)**:
For arbitrary finite complete Kraus families `E : ι → Matrix n n ℂ` and
`F : κ → Matrix n n ℂ` satisfying `∑_i E_i† E_i = I` and `∑_j F_j† F_j = I`,
`1 - v(E, F) = (1 / (2 d)) ∑_{i, j} Re Tr([E_i, F_j]† [E_i, F_j])`. -/
theorem one_sub_interference_eq_commutator_hs
    {n ι κ : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype ι] [Fintype κ]
    (E : ι → Matrix n n ℂ) (F : κ → Matrix n n ℂ)
    (hE : ∑ i, (E i).conjTranspose * E i = 1)
    (hF : ∑ j, (F j).conjTranspose * F j = 1) :
    1 - ICO.SwitchObservable.interference E F =
      (1 / (2 * (Fintype.card n : ℝ))) *
        ∑ i : ι, ∑ j : κ,
          (((E i * F j - F j * E i).conjTranspose * (E i * F j - F j * E i)).trace).re := by
  have hsum1 :
      (∑ i : ι, ∑ j : κ,
        ((((E i).conjTranspose * E i) * (F j * (F j).conjTranspose)).trace).re) =
      (Fintype.card n : ℝ) := by
    rw [Finset.sum_comm]
    have hinner (j : κ) :
        (∑ i : ι, ((((E i).conjTranspose * E i) * (F j * (F j).conjTranspose)).trace).re) =
          (((F j).conjTranspose * F j).trace).re := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hE, Matrix.one_mul,
        Matrix.trace_mul_comm]
    simp_rw [hinner]
    rw [← Complex.re_sum, ← Matrix.trace_sum, hF, Matrix.trace_one, Complex.natCast_re]
  have hsum2 :
      (∑ i : ι, ∑ j : κ,
        ((((F j).conjTranspose * F j) * (E i * (E i).conjTranspose)).trace).re) =
      (Fintype.card n : ℝ) := by
    have hinner (i : ι) :
        (∑ j : κ, ((((F j).conjTranspose * F j) * (E i * (E i).conjTranspose)).trace).re) =
          (((E i).conjTranspose * E i).trace).re := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hF, Matrix.one_mul,
        Matrix.trace_mul_comm]
    simp_rw [hinner]
    rw [← Complex.re_sum, ← Matrix.trace_sum, hE, Matrix.trace_one, Complex.natCast_re]
  have hsum3 :
      (∑ i : ι, ∑ j : κ,
        2 * ((F j * E i * (F j).conjTranspose * (E i).conjTranspose).trace).re) =
      2 * (ICO.SwitchObservable.rawInterference E F).re := by
    unfold ICO.SwitchObservable.rawInterference
    simp only [← Finset.mul_sum, Complex.re_sum]
  have htot :
      (∑ i : ι, ∑ j : κ,
        (((E i * F j - F j * E i).conjTranspose * (E i * F j - F j * E i)).trace).re) =
      2 * (Fintype.card n : ℝ) - 2 * (ICO.SwitchObservable.rawInterference E F).re := by
    simp_rw [commutator_conjTranspose_mul_self_trace_re, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [hsum1, hsum2, hsum3]
    ring
  rw [htot]
  unfold ICO.SwitchObservable.interference
  have hd : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hd]

/-- **Section 2.5 commutator identity (entrywise squared Hilbert–Schmidt norm form)**:
For arbitrary finite complete Kraus families `E` and `F`,
`1 - v(E, F) = (1 / (2 d)) ∑_{i, j} ∑_{a, b} ‖[E_i, F_j]_{a,b}‖^2`. -/
theorem one_sub_interference_eq_commutator_entry_sq
    {n ι κ : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype ι] [Fintype κ]
    (E : ι → Matrix n n ℂ) (F : κ → Matrix n n ℂ)
    (hE : ∑ i, (E i).conjTranspose * E i = 1)
    (hF : ∑ j, (F j).conjTranspose * F j = 1) :
    1 - ICO.SwitchObservable.interference E F =
      (1 / (2 * (Fintype.card n : ℝ))) *
        ∑ i : ι, ∑ j : κ, ∑ a : n, ∑ b : n, ‖(E i * F j - F j * E i) a b‖ ^ 2 := by
  rw [one_sub_interference_eq_commutator_hs E F hE hF]
  simp_rw [trace_conjTranspose_mul_self_re_eq_sum_norm_sq]

/-- **Section 2.5 commutator identity (`QIT.hilbertSchmidtSq` form)**:
For arbitrary finite complete Kraus families `E` and `F`,
`1 - v(E, F) = (1 / (2 d)) ∑_{i, j} hilbertSchmidtSq (E_i F_j - F_j E_i)`. -/
theorem one_sub_interference_eq_commutator_hilbertSchmidtSq
    {n ι κ : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype ι] [Fintype κ]
    (E : ι → Matrix n n ℂ) (F : κ → Matrix n n ℂ)
    (hE : ∑ i, (E i).conjTranspose * E i = 1)
    (hF : ∑ j, (F j).conjTranspose * F j = 1) :
    1 - ICO.SwitchObservable.interference E F =
      (1 / (2 * (Fintype.card n : ℝ))) *
        ∑ i : ι, ∑ j : κ, QIT.hilbertSchmidtSq (E i * F j - F j * E i) := by
  rw [one_sub_interference_eq_commutator_hs E F hE hF]
  rfl

/-! ## 3. Haar average of projective dephasing `Λ = E_U Δ_U = (id + d Ω) / (d + 1)` -/

/-- Continuity of `U ↦ Δ_U(X)` on the compact unitary group `U(A)`. -/
theorem dephasing_apply_continuous {A : Type*} [Fintype A] [DecidableEq A]
    (X : CMatrix A) :
    Continuous (fun U : Matrix.unitaryGroup A ℂ =>
      (QIT.MatrixMap.ofKraus (ICO.SwitchObservable.basisProjection (U : CMatrix A))) X) := by
  change Continuous (fun U : Matrix.unitaryGroup A ℂ =>
    ∑ j : A, ICO.SwitchObservable.basisProjection (U : CMatrix A) j * X *
      (ICO.SwitchObservable.basisProjection (U : CMatrix A) j).conjTranspose)
  apply continuous_finsetSum _
  intro j _
  have hP : Continuous (fun U : Matrix.unitaryGroup A ℂ =>
      ICO.SwitchObservable.basisProjection (U : CMatrix A) j) :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  exact (hP.matrix_mul continuous_const).matrix_mul hP.matrix_conjTranspose

/-- Matrix-entry expansion of `(Δ_U(X))_{a,b}` into products of four entries of `U`. -/
theorem dephasing_apply_entry_quartic {A : Type*} [Fintype A] [DecidableEq A]
    (U : CMatrix A) (X : CMatrix A) (a b : A) :
    (QIT.MatrixMap.ofKraus (ICO.SwitchObservable.basisProjection U) X) a b =
      ∑ j : A, ∑ c : A, ∑ e : A,
        X c e * ((U a j * U e j) * star (U c j * U b j)) := by
  change (∑ j : A, ICO.SwitchObservable.basisProjection U j * X *
      (ICO.SwitchObservable.basisProjection U j).conjTranspose) a b = _
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ICO.SwitchObservable.basisProjection_hermitian,
    ICO.LudersPromise.basisProjection_rankOne]
  simp only [Matrix.mul_apply, rankOneMatrix_apply, Finset.sum_mul, star_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **Haar dephasing average (`eq:validation-pair`, Sections 1.1 and 5.1)**:
For every finite nonempty index type `A` (`d = Fintype.card A ≥ 1`) and every matrix `X`,
integrating the projective dephasing channel `Δ_U` over `QIT.unitaryHaarMeasure` gives
`Λ(X) = (1 / (d + 1)) X + (d / (d + 1)) ((1 / d) (Tr X) I)`. -/
theorem haar_average_dephasing_eq_depolarizing
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (X : CMatrix A) :
    ∫ U : Matrix.unitaryGroup A ℂ,
      (QIT.MatrixMap.ofKraus (ICO.SwitchObservable.basisProjection (U : CMatrix A))) X
      ∂QIT.unitaryHaarMeasure =
    ((1 / ((Fintype.card A : ℝ) + 1) : ℝ) : ℂ) • X +
      (((Fintype.card A : ℝ) / ((Fintype.card A : ℝ) + 1) : ℝ) : ℂ) •
        (((1 / (Fintype.card A : ℝ) : ℝ) : ℂ) • (Matrix.trace X) • (1 : CMatrix A)) := by
  let μ := QIT.unitaryHaarMeasure (a := A)
  have hf_int : Integrable
      (fun U : Matrix.unitaryGroup A ℂ =>
        (QIT.MatrixMap.ofKraus (ICO.SwitchObservable.basisProjection (U : CMatrix A))) X) μ :=
    (dephasing_apply_continuous X).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  by_cases hnt : Nontrivial A
  · ext a b
    have hentry :
        (∫ U : Matrix.unitaryGroup A ℂ,
          (QIT.MatrixMap.ofKraus (ICO.SwitchObservable.basisProjection (U : CMatrix A))) X
          ∂μ) a b =
        ∫ U : Matrix.unitaryGroup A ℂ,
          ((QIT.MatrixMap.ofKraus (ICO.SwitchObservable.basisProjection (U : CMatrix A))) X) a b
          ∂μ := by
      simpa [cMatrixEntryCLM] using
        ((cMatrixEntryCLM (ι := A) a b).integral_comp_comm hf_int).symm
    rw [hentry]
    simp_rw [dephasing_apply_entry_quartic]
    have hq_int (j c e : A) : Integrable
        (fun U : Matrix.unitaryGroup A ℂ =>
          X c e * (((U : CMatrix A) a j * (U : CMatrix A) e j) *
            star ((U : CMatrix A) c j * (U : CMatrix A) b j))) μ := by
      exact (continuous_const.mul
        (((entry_continuous a j).mul (entry_continuous e j)).mul
          ((entry_continuous c j).mul (entry_continuous b j)).star)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun c _ =>
      integrable_finsetSum _ (fun e _ => hq_int j c e)))]
    have hterm_j (j : A) :
        (∫ U : Matrix.unitaryGroup A ℂ,
          (∑ c : A, ∑ e : A,
            X c e * (((U : CMatrix A) a j * (U : CMatrix A) e j) *
              star ((U : CMatrix A) c j * (U : CMatrix A) b j))) ∂μ) =
        ∑ c : A, ∑ e : A, X c e * fourthMoment a e j j c b j j := by
      rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ (fun e _ => hq_int j c e))]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [integral_finsetSum _ (fun e _ => hq_int j c e)]
      refine Finset.sum_congr rfl fun e _ => ?_
      exact integral_const_mul (X c e) _
    simp_rw [hterm_j]
    have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hm : (Fintype.card A : ℂ) - 1 ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast (ne_of_gt (@Fintype.one_lt_card A _ hnt))
    have hp : (Fintype.card A : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (Fintype.card A)
    have hs : (Fintype.card A : ℂ) ^ 2 - 1 ≠ 0 := by
      rw [show (Fintype.card A : ℂ) ^ 2 - 1 =
        ((Fintype.card A : ℂ) - 1) * ((Fintype.card A : ℂ) + 1) by ring]
      exact mul_ne_zero hm hp
    have hfourth (j c e : A) :
        fourthMoment a e j j c b j j =
          (delta a c * delta e b + delta a b * delta e c) /
            ((Fintype.card A : ℂ) * ((Fintype.card A : ℂ) + 1)) := by
      have hfm := @fourthMoment_delta A _ _ hnt a e j j c b j j
      rw [hfm]
      simp only [delta, ↓reduceIte, mul_one, one_mul]
      field_simp [hd, hm, hp, hs]
      ring
    simp_rw [hfourth]
    have hsum_ce :
        (∑ c : A, ∑ e : A,
          X c e * ((delta a c * delta e b + delta a b * delta e c) /
            ((Fintype.card A : ℂ) * ((Fintype.card A : ℂ) + 1)))) =
        (X a b + Matrix.trace X * (if a = b then 1 else 0)) /
          ((Fintype.card A : ℂ) * ((Fintype.card A : ℂ) + 1)) := by
      simp_rw [← mul_div_assoc, ← Finset.sum_div]
      congr 1
      have hsplit (c e : A) :
          X c e * (delta a c * delta e b + delta a b * delta e c) =
            X c e * delta a c * delta e b + delta a b * (X c e * delta e c) := by ring
      simp_rw [hsplit, Finset.sum_add_distrib]
      have hs1 : (∑ c : A, ∑ e : A, X c e * delta a c * delta e b) = X a b := by
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · simp [delta]
          · intro e _ heb; simp [delta, heb]
          · simp
        · intro c _ hca
          apply Finset.sum_eq_zero
          intro e _
          simp [delta, hca.symm]
        · simp
      have hs2 :
          (∑ c : A, ∑ e : A, delta a b * (X c e * delta e c)) =
            Matrix.trace X * (if a = b then 1 else 0) := by
        simp_rw [← Finset.mul_sum]
        have htr : (∑ c : A, ∑ e : A, X c e * delta e c) = Matrix.trace X := by
          unfold Matrix.trace
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_eq_single c]
          · simp [delta]
          · intro e _ hec; simp [delta, hec]
          · simp
        rw [htr, mul_comm]
        simp [delta]
      rw [hs1, hs2]
    simp_rw [hsum_ce]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    push_cast
    field_simp [hd, hp]
  · haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hnt
    let a₀ : A := Classical.arbitrary A
    haveI : Unique A := uniqueOfSubsingleton a₀
    have hconst (U : Matrix.unitaryGroup A ℂ) :
        (QIT.MatrixMap.ofKraus (ICO.SwitchObservable.basisProjection (U : CMatrix A))) X = X := by
      change (∑ j : A, ICO.SwitchObservable.basisProjection (U : CMatrix A) j * X *
          (ICO.SwitchObservable.basisProjection (U : CMatrix A) j).conjTranspose) = X
      have hP1 : ICO.SwitchObservable.basisProjection (U : CMatrix A) default = 1 := by
        have hc := ICO.SwitchObservable.basisProjection_complete (U : CMatrix A) U.property.2
        rwa [Fintype.sum_unique] at hc
      rw [Fintype.sum_unique, hP1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    simp_rw [hconst]
    rw [integral_const, probReal_univ, one_smul]
    ext a b
    have ha : a = default := Subsingleton.elim a default
    have hb : b = default := Subsingleton.elim b default
    subst ha hb
    have hcard : Fintype.card A = 1 := Fintype.card_unique
    have htr : Matrix.trace X = X default default := by
      simp [Matrix.trace]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, ↓reduceIte,
      smul_eq_mul, hcard, htr]
    push_cast
    norm_num
    ring

/-- Equivalent channel-form statement of `haar_average_dephasing_eq_depolarizing` directly in
terms of the completely depolarizing channel `Ω = ICO.RecordingDepolarizing.depolarizing`:
`∫_U Δ_U(X) dU = (1 / (d + 1)) X + (d / (d + 1)) Ω(X)`. -/
theorem haar_average_dephasing_eq_depolarizingChannel
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (X : CMatrix A) :
    ∫ U : Matrix.unitaryGroup A ℂ,
      (QIT.MatrixMap.ofKraus (ICO.SwitchObservable.basisProjection (U : CMatrix A))) X
      ∂QIT.unitaryHaarMeasure =
    ((1 / ((Fintype.card A : ℝ) + 1) : ℝ) : ℂ) • X +
      (((Fintype.card A : ℝ) / ((Fintype.card A : ℝ) + 1) : ℝ) : ℂ) •
        (ICO.RecordingDepolarizing.depolarizing (α := A)).map X := by
  rw [haar_average_dephasing_eq_depolarizing]
  congr 2
  ext a b
  rw [ICO.RecordingDepolarizing.depolarizing_entry]
  by_cases hab : a = b <;>
    simp [hab, Matrix.smul_apply, smul_eq_mul, one_div]

end

end ICO.VisibilityIdentities

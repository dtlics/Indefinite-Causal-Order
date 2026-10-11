import ICO.C6CacheHistorySpan
import ICO.C6BosonicFreshRotated

/-! The matrix projection onto a literal history span, with no chosen-basis
assumption. Projection containment follows from geometric span containment. -/
namespace ICO.C6CacheSpanProjection
open QIT Module Submodule ICO.C6CacheHistorySpan ICO.C6BosonicFreshRotated
  ICO.C6BosonicFockRotated ICO.MHProtocolOverlap
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2300000
variable {A : Type*} [Fintype A] [DecidableEq A]

def selectedSpan (U : Matrix.unitaryGroup A ℂ) (S : Finset A) :
    Submodule ℂ (EuclideanSpace ℂ A) :=
  Submodule.span ℂ (Set.range (fun i : S => column U i))

def spanProjection (U : Matrix.unitaryGroup A ℂ) (S : Finset A) : CMatrix A :=
  (U:CMatrix A)*coordinateProjection S*(U:CMatrix A).conjTranspose

theorem coordinate_projection (S : Finset A) : IsStarProjection (coordinateProjection S) := by
  constructor
  · change coordinateProjection S*coordinateProjection S=coordinateProjection S
    rw [coordinateProjection,Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  · change (coordinateProjection S).conjTranspose=coordinateProjection S
    rw [coordinateProjection,Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp only [Function.comp_apply,Pi.star_apply]
    split_ifs <;> simp

theorem spanProjection_projection (U : Matrix.unitaryGroup A ℂ) (S : Finset A) :
    IsStarProjection (spanProjection U S) :=
  unitary_projection U _ (coordinate_projection S)

theorem act_coordinate (S : Finset A) (x : EuclideanSpace ℂ A) (i : A) :
    act (coordinateProjection S) x i=if i∈S then x i else 0 := by
  change (Matrix.diagonal (fun j : A => if j∈S then (1:ℂ) else 0)).mulVec (⇑x) i=_
  rw [Matrix.mulVec_diagonal]
  by_cases hi : i∈S <;> simp [hi]

theorem act_unitary_column (U : Matrix.unitaryGroup A ℂ) (j : A) :
    act (U:CMatrix A) (EuclideanSpace.single j 1)=column U j := by
  ext i
  change (∑ k,(U:CMatrix A) i k*(EuclideanSpace.single j (1:ℂ)) k)=_
  simp [PiLp.single_apply,column]

theorem projection_column (U : Matrix.unitaryGroup A ℂ) (S : Finset A) (j : A) :
    act (spanProjection U S) (column U j)=if j∈S then column U j else 0 := by
  have hu : (U:CMatrix A).conjTranspose*(U:CMatrix A)=1 := U.property.1
  rw [←act_unitary_column U j,←act_mul]
  unfold spanProjection
  rw [Matrix.mul_assoc,Matrix.mul_assoc,hu,Matrix.mul_one,act_mul]
  have hd : act (coordinateProjection S) (EuclideanSpace.single j 1)=
      if j∈S then EuclideanSpace.single j 1 else 0 := by
    ext i
    rw [act_coordinate]
    by_cases hi : i=j
    · subst j
      split_ifs <;> rfl
    · by_cases hj : j∈S <;> simp [hi,hj,EuclideanSpace.single_apply]
  rw [hd]
  split_ifs <;> simp [act_unitary_column]

theorem projection_fixes (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    (x : EuclideanSpace ℂ A) (hx : x∈selectedSpan U S) :
    act (spanProjection U S) x=x := by
  apply Submodule.span_induction (p:=fun x _ => act (spanProjection U S) x=x) _ _ _ _ hx
  · rintro _ ⟨i,rfl⟩
    rw [projection_column,if_pos i.property]
  · exact map_zero _
  · intro a b _ _ ha hb
    rw [map_add,ha,hb]
  · intro c x _ hx
    rw [map_smul,hx]

theorem unitary_sum (U : Matrix.unitaryGroup A ℂ) (x : EuclideanSpace ℂ A) :
    act (U:CMatrix A) x=∑ j,x j • column U j := by
  ext i
  change (∑ j,(U:CMatrix A) i j*x j)=_
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,
    column,WithLp.ofLp_toLp,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem projection_mem (U : Matrix.unitaryGroup A ℂ) (S : Finset A)
    (x : EuclideanSpace ℂ A) : act (spanProjection U S) x∈selectedSpan U S := by
  simp only [spanProjection,act_mul]
  rw [unitary_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [act_coordinate]
  by_cases h : j∈S
  · rw [if_pos h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j,h⟩,rfl⟩)
  · rw [if_neg h,zero_smul]
    exact Submodule.zero_mem _

theorem projection_containment (U V : Matrix.unitaryGroup A ℂ) (S T : Finset A)
    (h : selectedSpan U S≤selectedSpan V T) :
    spanProjection V T*spanProjection U S=spanProjection U S := by
  apply (Matrix.toEuclideanCLM (n:=A) (𝕜:=ℂ)).injective
  apply ContinuousLinearMap.ext
  intro x
  change act (spanProjection V T*spanProjection U S) x=act (spanProjection U S) x
  rw [act_mul]
  exact projection_fixes V T _ (h (projection_mem U S x))

theorem projection_unique (U V : Matrix.unitaryGroup A ℂ) (S T : Finset A)
    (h : selectedSpan U S=selectedSpan V T) : spanProjection U S=spanProjection V T := by
  have h1 := projection_containment U V S T h.le
  have h2 := projection_containment V U T S h.ge
  have hs1 : (spanProjection U S).conjTranspose=spanProjection U S :=
    (spanProjection_projection U S).isSelfAdjoint.star_eq
  have hs2 : (spanProjection V T).conjTranspose=spanProjection V T :=
    (spanProjection_projection V T).isSelfAdjoint.star_eq
  have hh := congrArg Matrix.conjTranspose h1
  rw [Matrix.conjTranspose_mul,hs1,hs2,h2] at hh
  exact hh.symm

theorem projection_trace (U : Matrix.unitaryGroup A ℂ) (S : Finset A) :
    (spanProjection U S).trace=(S.card:ℂ) := by
  have hu : (U:CMatrix A).conjTranspose*(U:CMatrix A)=1 := U.property.1
  rw [spanProjection,Matrix.trace_mul_comm,←Matrix.mul_assoc,hu,Matrix.one_mul]
  simp [coordinateProjection,Matrix.trace_diagonal]

def historyUnitary {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) : Matrix.unitaryGroup A ℂ :=
  (history_coordinates v).choose

def historyIndices {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) : Finset A :=
  (history_coordinates v).choose_spec.choose

theorem history_realization {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) :
    selectedSpan (historyUnitary v) (historyIndices v)=historySpan v ∧
      (historyIndices v).card≤s := (history_coordinates v).choose_spec.choose_spec

def historyProjection {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) : CMatrix A :=
  spanProjection (historyUnitary v) (historyIndices v)

theorem historyProjection_trace {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) :
    (historyProjection v).trace.re≤s := by
  rw [historyProjection,projection_trace,Complex.natCast_re]
  exact_mod_cast (history_realization v).2

theorem historyProjection_contains {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) (i : Fin s) :
    act (historyProjection v) (v i)=v i := by
  apply projection_fixes
  rw [(history_realization v).1]
  exact historySpan_contains v i

theorem historyProjection_snoc {s : ℕ} (v : Fin s → EuclideanSpace ℂ A)
    (x : EuclideanSpace ℂ A) :
    historyProjection (Fin.snoc v x)*historyProjection v=historyProjection v := by
  apply projection_containment
  rw [(history_realization v).1,(history_realization (Fin.snoc v x)).1,historySpan_snoc]
  exact le_sup_left

#print axioms projection_containment
#print axioms historyProjection_trace
#print axioms historyProjection_snoc
end
end ICO.C6CacheSpanProjection
